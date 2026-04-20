# -*- coding: utf-8 -*-
"""
从新浪财经「公司公告 → 年度报告」栏目批量下载沪深主板 A 股年报 PDF。

- 股票范围：上证主板 A 股 + 深证主板 A 股（不含科创板、创业板、B 股、北交所；由 akshare 官方列表筛选）。
- 报告期年份：由文件顶部常量 REPORT_YEAR_START / REPORT_YEAR_END 控制（默认均为当前日历年减 1，与常见披露节奏一致），也可用命令行 --year-start / --year-end 覆盖。
- 公告标题：须含「年」字；含「摘要」的条目不下载。
- 缓存目录与是否刷新缓存：常量 CACHE_DIR_STR、REFRESH_CACHE（命令行可覆盖）。
  **重要**：`--cache-dir` 下 `http_get/` 仅存**新浪网页正文**（`<sha256>.txt` UTF-8，配套同名 `.json` 元数据；用于解析 PDF 链接），**不是**年报 PDF 原件。
- PDF 输出根目录：常量 OUTPUT_DIR_STR（命令行 `--output` 可覆盖）；**PDF 原件**路径形如「输出根/行业/公司名-代码-报告期年份.pdf」（行业下不再有年份子目录）。
- 新浪 PDF 若 404/410：在**同一输出根目录**追加写入 `missing_pdfs.log`（UTF-8 TSV，含代码、公告标题、PDF URL、目标路径等）。
- 网络拉取均带 tqdm 字节/步骤进度条；`--no-progress` 可关闭。
- `--sleep`（股票阶段末）：仅当该股本次「年报列表或公告详情」发生过真实 HTTP 时才休眠；若全文均命中磁盘缓存则不休眠。**下载 PDF 成功后**仍会按 `--sleep` 休眠一次（针对文件服务器）。
- 新浪可能返回 HTTP 456（非标准码，多为限流/风控）：网页请求间有最小间隔与抖动；遇 456/429/502/503 等会**写日志并抛出**，请加大 `--http-interval` 与 `--sleep` 后重跑。
- 存储：输出目录下按行业分子文件夹，其内直接存放年报 PDF；文件名为「公司名称-股票代码-年份.pdf」（行业来自新浪财经行业分类接口，缓存于 cache-dir/akshare/）。
- 断点续传：
  - 已完成 PDF：目标 .pdf 已存在且大于 0 字节则跳过下载；若你设定的报告期年份区间内、该股票对应路径下的 PDF **全部**已存在，则**不再读取**该股年报列表（含缓存），以加快重跑；
  - 未完成 PDF：使用 .pdf.part + HTTP Range 续传；
  - 公告列表/详情页：写入 `cache-dir/http_get/`（`<sha256>.txt` + `.json`；便于断点续跑），**与 PDF 输出路径无关**；
  - akshare 拉取的股票列表 / 代码简称映射：默认落盘缓存，命中则不再请求网络。

依赖：akshare（仅用于拉取证券列表）、requests（抓取新浪页面与 PDF）、tqdm（进度条）、logging（错误与运行日志）。
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import random
import re
import sys
import time
from datetime import date
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, Optional
from urllib.parse import urljoin, urlparse

import pandas as pd
import requests
from tqdm import tqdm

try:
    import akshare as ak
except ImportError as e:  # pragma: no cover
    print("请先安装依赖: pip install -r requirements.txt", file=sys.stderr)
    raise e

SINA_HOST = "http://vip.stock.finance.sina.com.cn"
BULLETIN_NDBG = (
    SINA_HOST + "/corp/go.php/vCB_Bulletin/stockid/{code}/page_type/ndbg.phtml"
)
DETAIL_PATH = "/corp/view/vCB_AllBulletinDetail.php"

DEFAULT_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
)

# ---------------------------------------------------------------------------
# 运行策略（可直接改这里；命令行参数若给出则覆盖对应项）
# ---------------------------------------------------------------------------
_cy = date.today().year
_default_report_year = _cy - 1
# 年报「报告期」年份闭区间；默认「本年-1」；历史区间如 2018～2023 可改起止
REPORT_YEAR_START: int = _default_report_year
REPORT_YEAR_END: int = _default_report_year

# 网络缓存根目录（其下含 `http_get/` 网页快照、`akshare/` 证券列表缓存；可为绝对路径）
CACHE_DIR_STR: str = r"D:\Annual-Report-Tracker\.cache\sina_annual_reports"
# 年报 PDF 输出根目录（可为绝对路径；其下 行业/公司名称-代码-年份.pdf）
OUTPUT_DIR_STR: str = r"D:\Annual_Report_Output"
# 新浪 PDF 404/410 等缺失时追加写入输出根目录（与 --output 一致，默认即 D:\\Annual_Report_Output）
MISSING_PDF_LOG_FILENAME: str = "missing_pdfs.log"
# 为 True 时忽略 HTTP/akshare 磁盘缓存，强制重新请求（不删除已完成的 PDF）
REFRESH_CACHE: bool = False

# 新浪财经行业划分（传给 akshare.stock_classify_sina）。常用「申万行业」「新浪行业」「申万二级」等；见 vip.stock.finance.sina.com.cn/mkt/
SINA_INDUSTRY_CLASSIFY_SYMBOL: str = "申万行业"

# 新浪对高频请求常返回 456（非标准码，多为限流/风控）。以下为「节流 + 重试」默认值，可调大更稳、更慢。
# 两次成功 HTTP 拉取之间：间隔 = HTTP_MIN + Uniform(0, HTTP_JITTER)，即默认约 0.85～2.25 秒
HTTP_MIN_INTERVAL_SEC: float = 0.85
HTTP_JITTER_SEC: float = 1.4
# 下列状态在日志中会额外提示「常见于限流/网关」；出现即记录日志并 raise，不重试
RETRYABLE_HTTP_STATUS: frozenset[int] = frozenset({456, 429, 502, 503})
# 每只股票在**发生过网页 HTTP**后的额外休眠（秒），纯读磁盘缓存时不生效；与 HTTP 间隔叠加，减轻整批压力
DEFAULT_SLEEP_BETWEEN_STOCKS: float = 0.65

# 从公告标题解析「报告期」年度：如「2024年年度报告」「2024年度报告」
_YEAR_TITLE = re.compile(r"(20\d{2})\s*年?\s*年度\s*报告")
_YEAR_FALLBACK = re.compile(r"(20\d{2})\s*年?\s*年报")

# datelist 中每条：日期 + 详情链接 + 标题（href 可能在 target 之后）
_DATELIST_ROW = re.compile(
    r"(\d{4}-\d{2}-\d{2})(?:\s|&nbsp;)*<a[^>]*href=['\"](?P<href>[^'\"]+)['\"][^>]*>(?P<title>[^<]+)</a>",
    re.I,
)

_PDF_HREF = re.compile(
    r"""href\s*=\s*(?P<q>['"])(?P<url>https?://file\.finance\.sina\.com\.cn[^'"]+\.(?:pdf|PDF))\1""",
)

# 是否显示 tqdm（main 里可用 --no-progress 关闭）
_PROGRESS_ENABLED = True

logger = logging.getLogger(__name__)


def _log_http_failure(r: requests.Response, url: str) -> None:
    """记录非成功 HTTP 响应（含正文预览），供排查 456/429/502/503 等。"""
    hint = ""
    if r.status_code in RETRYABLE_HTTP_STATUS:
        hint = "（常见于限流 456/429 或网关/过载 502/503）"
    try:
        raw = r.content[:4096]
        preview = raw.decode("utf-8", errors="replace")
    except Exception:
        preview = repr(r.content[:512])
    logger.error(
        "HTTP 失败 status=%s reason=%s url=%s %s",
        r.status_code,
        getattr(r, "reason", "") or "",
        url,
        hint,
    )
    logger.error("响应头 Content-Type=%s Content-Length=%s", r.headers.get("Content-Type"), r.headers.get("Content-Length"))
    logger.error("响应体预览(前4KB):\n%s", preview)


def _append_missing_pdf_log(
    output_root: Path,
    *,
    reason: str,
    code: str,
    name: str,
    industry: str,
    announce_date: str,
    year: int,
    title: str,
    pdf_url: str,
    dest_path: Path,
) -> None:
    """将缺失的 PDF 一条记录追加到输出根目录下的 MISSING_PDF_LOG_FILENAME（UTF-8 TSV）。"""
    root = output_root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    path = root / MISSING_PDF_LOG_FILENAME

    def _flat(s: str) -> str:
        return s.replace("\r", " ").replace("\n", " ").replace("\t", " ")

    ts = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())
    fields = [
        ts,
        reason,
        code,
        _flat(name),
        _flat(industry),
        announce_date,
        str(year),
        _flat(title),
        pdf_url,
        str(dest_path.resolve()),
    ]
    line = "\t".join(fields) + "\n"
    with path.open("a", encoding="utf-8") as f:
        if f.tell() == 0:
            f.write(
                "时间\t原因\t代码\t简称\t行业\t公告日期\t报告期年份\t公告标题\tPDF_URL\t目标路径\n"
            )
        f.write(line)


def _tqdm(*args: Any, **kwargs: Any) -> Any:
    kwargs.setdefault("disable", not _PROGRESS_ENABLED)
    kwargs.setdefault("dynamic_ncols", True)
    return tqdm(*args, **kwargs)


def _short_url_desc(url: str, max_len: int = 42) -> str:
    """进度条标题用短字符串。"""
    try:
        p = urlparse(url)
        tail = (p.path or "") + (("?" + p.query) if p.query else "")
        if len(tail) > max_len:
            return "…" + tail[-max_len + 1 :]
        return tail or url[:max_len]
    except Exception:
        return url[:max_len]


def _parse_content_range_total(content_range: str) -> Optional[int]:
    """解析 Content-Range: bytes a-b/total 中的 total。"""
    if not content_range or "/" not in content_range:
        return None
    try:
        return int(content_range.rsplit("/", 1)[-1].strip())
    except ValueError:
        return None


class NetCache:
    """
    统一管理：HTTP 文本缓存、akshare 结果缓存。
    refresh=True 时跳过一切磁盘命中，强制走网络并覆盖缓存。
    """

    def __init__(
        self,
        root: Path,
        *,
        refresh: bool = False,
        min_http_interval: float = HTTP_MIN_INTERVAL_SEC,
        http_jitter: float = HTTP_JITTER_SEC,
    ) -> None:
        self.root = root
        self.refresh = refresh
        self._min_http_interval = max(0.0, min_http_interval)
        self._http_jitter = max(0.0, http_jitter)
        self._last_http_end: float = 0.0
        # 新浪列表/详情页：<sha256>.txt（正文 UTF-8）+ 同名 .json（url/encoding/ts）；勿与 PDF 输出混淆
        self._http_get_dir = root / "http_get"
        self._ak_dir = root / "akshare"

    def _pace_before_http(self) -> None:
        """两次成功 HTTP 之间的最小间隔 + 抖动，降低 456 触发率。"""
        if self._min_http_interval <= 0:
            return
        gap = self._min_http_interval + random.uniform(0.0, self._http_jitter)
        now = time.monotonic()
        elapsed = now - self._last_http_end
        if elapsed < gap:
            time.sleep(gap - elapsed)

    def http_get_text(
        self,
        sess: requests.Session,
        url: str,
        *,
        response_encoding: str = "gb18030",
        timeout: int = 60,
        progress_desc: Optional[str] = None,
    ) -> tuple[str, bool]:
        """GET 网页并解码为 str；网络拉取时显示字节进度条；正文以 UTF-8 写入 `http_get/<sha>.txt`，元数据写入同名 `.json`。

        返回 (正文, used_http)：后者为 True 表示本次经历了 HTTP（非磁盘缓存命中）。
        """
        self._http_get_dir.mkdir(parents=True, exist_ok=True)
        key = hashlib.sha256(url.encode("utf-8")).hexdigest()
        cache_txt = self._http_get_dir / f"{key}.txt"
        cache_meta = self._http_get_dir / f"{key}.json"
        legacy_html = self._http_get_dir / f"{key}.html"
        legacy_sina_html = self.root / "sina_html_cache"
        if not self.refresh:
            if cache_txt.exists():
                return cache_txt.read_text(encoding="utf-8"), False
            if legacy_html.exists():
                return legacy_html.read_text(encoding="utf-8"), False
            for folder, suffix in (
                (legacy_sina_html, ".txt"),
                (legacy_sina_html, ".html"),
            ):
                if folder.is_dir():
                    leg = folder / f"{key}{suffix}"
                    if leg.exists():
                        return leg.read_text(encoding="utf-8"), False

        desc = progress_desc or f"HTTP {_short_url_desc(url)}"
        self._pace_before_http()

        r = sess.get(url, stream=True, timeout=timeout)
        try:
            if not r.ok:
                _log_http_failure(r, url)
                r.raise_for_status()

            total = int(r.headers.get("content-length") or 0)
            buf = bytearray()
            with _tqdm(
                total=total if total > 0 else None,
                unit="B",
                unit_scale=True,
                unit_divisor=1024,
                desc=desc,
                miniters=1,
            ) as pbar:
                for chunk in r.iter_content(chunk_size=64 * 1024):
                    if chunk:
                        buf.extend(chunk)
                        pbar.update(len(chunk))
        finally:
            r.close()
        self._last_http_end = time.monotonic()

        text = bytes(buf).decode(response_encoding, errors="replace").replace("\r\n", "\n").replace("\r", "\n")
        cache_txt.write_text(text, encoding="utf-8", newline="\n")
        cache_meta.write_text(
            json.dumps({"url": url, "encoding": response_encoding, "ts": time.time()}, ensure_ascii=False),
            encoding="utf-8",
        )
        return text, True

    def load_mainboard_stocks(self) -> list[tuple[str, str]]:
        """缓存全市场主板列表（akshare 两次请求）。"""
        path = self._ak_dir / "mainboard_stocks.json"
        if not self.refresh and path.exists():
            raw = json.loads(path.read_text(encoding="utf-8"))
            return [(str(x[0]).zfill(6), str(x[1])) for x in raw]

        self._ak_dir.mkdir(parents=True, exist_ok=True)
        data = _load_mainboard_stocks_uncached()
        path.write_text(
            json.dumps(data, ensure_ascii=False),
            encoding="utf-8",
        )
        return data

    def load_code_industry_map(self) -> dict[str, str]:
        """新浪财经行业分类 → 六位代码→行业名称（全市场拉取一次，磁盘缓存）。"""
        path = self._ak_dir / "stock_code_industry_sina.json"
        if not self.refresh and path.exists():
            raw = json.loads(path.read_text(encoding="utf-8"))
            return {str(k).zfill(6): str(v) for k, v in raw.items()}

        self._ak_dir.mkdir(parents=True, exist_ok=True)
        data = _load_code_industry_map_uncached()
        path.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
        return data

    def lookup_mainboard_names(self, codes: list[str]) -> dict[str, str]:
        """缓存指定代码的简称查询结果。"""
        if not codes:
            return {}
        sig = hashlib.sha256(",".join(sorted(c.zfill(6) for c in codes)).encode()).hexdigest()[:16]
        path = self._ak_dir / f"names_{sig}.json"
        if not self.refresh and path.exists():
            d = json.loads(path.read_text(encoding="utf-8"))
            return {str(k).zfill(6): str(v) for k, v in d.items()}

        self._ak_dir.mkdir(parents=True, exist_ok=True)
        found = _lookup_mainboard_names_uncached(codes)
        path.write_text(json.dumps(found, ensure_ascii=False), encoding="utf-8")
        return found


def _sanitize_filename(name: str, max_len: int = 80) -> str:
    """Windows 文件名非法字符替换。"""
    bad = r'\/:*?"<>|'
    s = "".join("_" if c in bad else c for c in name.strip())
    s = re.sub(r"\s+", "_", s).strip("._") or "unknown"
    return s[:max_len]


def _sanitize_company_for_report_filename(name: str, max_len: int = 80) -> str:
    """年报文件名中「公司名称」段：避免出现 '-'，以免与公司名-代码-年份 的分隔混淆。"""
    base = _sanitize_filename(name, max_len=max_len)
    return base.replace("-", "_")


def _all_target_year_pdfs_exist(
    output_root: Path,
    code: str,
    name: str,
    industry: str,
    year_start: int,
    year_end: int,
) -> bool:
    """
    请求年份闭区间内，该股按命名规则预期的 PDF 是否均已存在且非空。
    用于重跑时跳过已无待下载任务的股票，避免反复读列表页（含磁盘缓存）。
    """
    safe_dir = _sanitize_filename(industry)
    safe_company = _sanitize_company_for_report_filename(name)
    for y in range(year_start, year_end + 1):
        p = output_root / safe_dir / f"{safe_company}-{code}-{y}.pdf"
        if not (p.exists() and p.stat().st_size > 0):
            return False
    return True


def _lookup_mainboard_names_uncached(codes: list[str]) -> dict[str, str]:
    """仅查询给定代码的简称（用于 --code，避免拉取全市场列表）。"""
    want = {c.zfill(6) for c in codes}
    found: dict[str, str] = {}
    sh_codes = {c for c in want if c.startswith("6")}
    sz_codes = want - sh_codes
    steps = int(bool(sh_codes)) + int(bool(sz_codes))
    if steps == 0:
        return found

    with _tqdm(total=steps, desc="akshare 证券简称", unit="请求") as pbar:
        if sh_codes:
            sh = ak.stock_info_sh_name_code(symbol="主板A股")
            pbar.update(1)
        else:
            sh = None
        if sz_codes:
            sz = ak.stock_info_sz_name_code(symbol="A股列表")
            pbar.update(1)
        else:
            sz = None

    if sh_codes and sh is not None:
        sh["证券代码"] = sh["证券代码"].astype(str).str.zfill(6)
        sub = sh[sh["证券代码"].isin(sh_codes)]
        for _, row in sub.iterrows():
            found[str(row["证券代码"]).zfill(6)] = str(row["证券简称"])
    if sz_codes and sz is not None:
        sz = sz[sz["板块"].astype(str).str.strip() == "主板"].copy()
        sz["A股代码"] = sz["A股代码"].astype(str).str.zfill(6)
        sub = sz[sz["A股代码"].isin(sz_codes)]
        for _, row in sub.iterrows():
            found[str(row["A股代码"]).zfill(6)] = str(row["A股简称"])
    return found


def _load_mainboard_stocks_uncached() -> list[tuple[str, str]]:
    """
    返回 [(六位代码, 简称), ...]。
    - 上证：stock_info_sh_name_code(主板A股)
    - 深证：A 股列表中「板块」为「主板」
    """
    with _tqdm(total=2, desc="akshare 主板列表", unit="请求") as pbar:
        sh = ak.stock_info_sh_name_code(symbol="主板A股")
        pbar.update(1)
        sz = ak.stock_info_sz_name_code(symbol="A股列表")
        pbar.update(1)

    sh = sh[["证券代码", "证券简称"]].copy()
    sh["证券代码"] = sh["证券代码"].astype(str).str.zfill(6)

    sz = sz[sz["板块"].astype(str).str.strip() == "主板"].copy()
    sz = sz[["A股代码", "A股简称"]].rename(
        columns={"A股代码": "证券代码", "A股简称": "证券简称"}
    )
    sz["证券代码"] = sz["证券代码"].astype(str).str.zfill(6)

    merged = pd.concat([sh, sz], ignore_index=True)
    merged = merged.drop_duplicates(subset=["证券代码"], keep="first")
    merged = merged.sort_values("证券代码")
    return list(zip(merged["证券代码"].tolist(), merged["证券简称"].tolist()))


def _load_code_industry_map_uncached() -> dict[str, str]:
    """
    新浪财经 quotes_service（与年报同一站点体系）：按 SINA_INDUSTRY_CLASSIFY_SYMBOL 展开各类别成份，
    得到六位代码 → 行业/板块名称（列 class）。同一代码若重复出现则保留首次。
    """
    df = ak.stock_classify_sina(symbol=SINA_INDUSTRY_CLASSIFY_SYMBOL)
    if df is None or df.empty:
        return {}
    df = df.copy()
    df["code"] = df["code"].astype(str).str.zfill(6)
    code_to_ind: dict[str, str] = {}
    for _, row in df.iterrows():
        c = str(row["code"]).zfill(6)
        cls = str(row["class"]).strip()
        if c and cls and c not in code_to_ind:
            code_to_ind[c] = cls
    return code_to_ind


def _session() -> requests.Session:
    s = requests.Session()
    s.headers.update(
        {
            "User-Agent": DEFAULT_UA,
            "Accept": "text/html,application/xhtml+xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "zh-CN,zh;q=0.9",
            "Referer": f"{SINA_HOST}/",
        }
    )
    return s


def fetch_ndbg_list_html(sess: requests.Session, code: str, cache: NetCache) -> tuple[str, bool]:
    url = BULLETIN_NDBG.format(code=code)
    return cache.http_get_text(
        sess,
        url,
        response_encoding="gb18030",
        timeout=60,
        progress_desc=f"年报列表 {code}",
    )


def parse_ndbg_rows(html: str) -> list[tuple[str, str, str]]:
    """
    返回 [(公告日 YYYY-MM-DD, 详情相对或绝对 URL, 标题), ...]
    """
    m = re.search(
        r'class=["\']datelist["\'][^>]*>\s*<ul[^>]*>(?P<body>.*?)</ul>',
        html,
        re.S | re.I,
    )
    if not m:
        return []
    body = m.group("body")
    out: list[tuple[str, str, str]] = []
    for row in _DATELIST_ROW.finditer(body):
        date_s, href, title = row.group(1), row.group("href"), row.group("title")
        if DETAIL_PATH not in href and "AllBulletinDetail" not in href:
            continue
        out.append((date_s, href.strip(), title.strip()))
    return out


def is_full_annual_report_title(title: str) -> bool:
    """排除年报摘要；标题须含「年」字；再按年报表述过滤（在 ndbg 列表上再保险一次）。"""
    if "摘要" in title:
        return False
    if "年" not in title:
        return False
    if _YEAR_TITLE.search(title) or _YEAR_FALLBACK.search(title):
        return True
    if "年度报告" in title and "半年" not in title:
        return True
    return False


def report_year_from_title(title: str, announce_date: str) -> Optional[int]:
    m = _YEAR_TITLE.search(title) or _YEAR_FALLBACK.search(title)
    if m:
        return int(m.group(1))
    # 极少数旧公告仅有「2016年报」类简写
    m2 = re.search(r"(20\d{2})\s*年报", title)
    if m2:
        return int(m2.group(1))
    return None


def fetch_pdf_url(
    sess: requests.Session,
    detail_url: str,
    cache: NetCache,
    *,
    stock_code: str = "",
) -> tuple[Optional[str], bool]:
    if detail_url.startswith("/"):
        detail_url = urljoin(SINA_HOST + "/", detail_url.lstrip("/"))
    hint = f" {stock_code}" if stock_code else ""
    html, used_http = cache.http_get_text(
        sess,
        detail_url,
        response_encoding="gb18030",
        timeout=60,
        progress_desc=f"公告详情{hint}",
    )
    m = _PDF_HREF.search(html)
    if not m:
        m = re.search(
            r"(https?://file\.finance\.sina\.com\.cn[^\s\"'<>]+\.(?:pdf|PDF))",
            html,
            re.I,
        )
        if m:
            return m.group(1), used_http
        return None, used_http
    return m.group("url"), used_http


def _pdf_part_paths(dest: Path) -> tuple[Path, Path]:
    """返回 (.part 临时文件, 元数据 json 路径)"""
    part = dest.with_suffix(dest.suffix + ".part")
    meta = dest.with_suffix(dest.suffix + ".part.meta.json")
    return part, meta


def _verify_is_pdf_file(path: Path) -> None:
    """校验文件头为 PDF（%PDF-）；若为 HTML 或空文件则抛 ValueError。"""
    if not path.exists():
        raise ValueError(f"文件不存在: {path}")
    size = path.stat().st_size
    if size == 0:
        raise ValueError(f"文件大小为 0: {path}")
    with path.open("rb") as f:
        head = f.read(512)
    if head.startswith(b"%PDF"):
        return
    preview = head[:256].decode("utf-8", errors="replace")
    logger.error(
        "期望 PDF 但文件头不是 %%PDF（可能返回了 HTML 或错误页）。path=%s size=%s preview=%r",
        path,
        size,
        preview,
    )
    raise ValueError(f"下载内容不是 PDF（应以 %PDF 开头）: {path}")


def download_pdf(
    sess: requests.Session,
    pdf_url: str,
    dest: Path,
    *,
    progress_desc: Optional[str] = None,
) -> bool:
    """
    流式下载 PDF；支持断点续传（.pdf.part 非空则带 Range 续传）。
    同一路径的 .part.meta.json 记录 URL，若与本次 PDF URL 不一致则清空分片重来。

    若服务端返回 404/410（对象存储上已无此文件），记录警告并返回 False，不抛异常。
    成功落盘则返回 True。
    """
    dest.parent.mkdir(parents=True, exist_ok=True)
    part, meta_path = _pdf_part_paths(dest)

    resume_from = part.stat().st_size if part.exists() else 0
    if meta_path.exists():
        try:
            meta = json.loads(meta_path.read_text(encoding="utf-8"))
            if meta.get("url") != pdf_url:
                resume_from = 0
                part.unlink(missing_ok=True)
                meta_path.unlink(missing_ok=True)
        except (json.JSONDecodeError, OSError):
            resume_from = 0
            part.unlink(missing_ok=True)
            meta_path.unlink(missing_ok=True)

    attempts = 0
    while True:
        attempts += 1
        if attempts > 5:
            raise RuntimeError(f"PDF 下载失败（反复 416 或异常）: {pdf_url[:80]}")
        headers: dict[str, str] = {}
        if resume_from > 0:
            headers["Range"] = f"bytes={resume_from}-"
        with sess.get(pdf_url, headers=headers, stream=True, timeout=300) as r:
            if r.status_code == 416:
                part.unlink(missing_ok=True)
                meta_path.unlink(missing_ok=True)
                resume_from = 0
                continue
            if r.status_code in (404, 410):
                part.unlink(missing_ok=True)
                meta_path.unlink(missing_ok=True)
                logger.warning(
                    "PDF 在新浪侧已不存在(%s)，跳过（列表链接可能过期或文件已下架）: %s",
                    r.status_code,
                    pdf_url,
                )
                return False
            if r.status_code not in (200, 206):
                _log_http_failure(r, pdf_url)
                r.raise_for_status()
            # 206 为续传片段；200 为全量（含不支持 Range 时退回全文）
            append = r.status_code == 206
            if not append:
                part.unlink(missing_ok=True)
            mode = "ab" if append else "wb"

            cr = r.headers.get("Content-Range") or ""
            total_full = _parse_content_range_total(cr)
            if total_full is None and r.headers.get("Content-Length"):
                cl = int(r.headers["Content-Length"])
                total_full = resume_from + cl if append else cl
            bar_initial = resume_from if append else 0
            pdesc = progress_desc or dest.name

            pbar_kw: dict[str, Any] = {
                "unit": "B",
                "unit_scale": True,
                "unit_divisor": 1024,
                "desc": f"PDF {pdesc}",
                "miniters": 1,
            }
            if total_full is not None:
                pbar_kw["total"] = total_full
                pbar_kw["initial"] = bar_initial
            else:
                pbar_kw["total"] = None

            with _tqdm(**pbar_kw) as pbar:
                with part.open(mode) as f:
                    for chunk in r.iter_content(chunk_size=256 * 1024):
                        if chunk:
                            f.write(chunk)
                            pbar.update(len(chunk))
        break

    try:
        _verify_is_pdf_file(part)
    except ValueError:
        part.unlink(missing_ok=True)
        meta_path.unlink(missing_ok=True)
        raise

    meta_path.write_text(
        json.dumps({"url": pdf_url, "ts": time.time()}, ensure_ascii=False),
        encoding="utf-8",
    )
    part.replace(dest)
    meta_path.unlink(missing_ok=True)
    return True


def iter_jobs(
    stocks: Iterable[tuple[str, str]],
    sess: requests.Session,
    sleep_sec: float,
    cache: NetCache,
    year_start: int,
    year_end: int,
    output_root: Path,
    industry_by_code: Mapping[str, str],
) -> Iterator[tuple[str, str, str, str, int, str, str]]:
    """
    产出 (code, name, industry, announce_date, year, title, pdf_url)。
    仅包含报告期年份在 [year_start, year_end] 闭区间内的条目。
    对股票列表使用总进度条（与「共 N 只股票」一致）。
    """
    stock_list = list(stocks)
    n_stocks = len(stock_list)
    out_root = output_root.resolve()
    with _tqdm(
        total=n_stocks,
        desc="沪深主板股票",
        unit="只",
        miniters=1,
    ) as stock_pbar:
        for code, name in stock_list:
            industry = (industry_by_code.get(code) or "").strip() or "未分类"
            stock_pbar.set_postfix_str(f"{code} {name}"[:40], refresh=False)
            if _all_target_year_pdfs_exist(out_root, code, name, industry, year_start, year_end):
                logger.debug(
                    "[跳过列表] %s %s：报告期 %s～%s 对应 PDF 均已存在",
                    code,
                    name,
                    year_start,
                    year_end,
                )
                stock_pbar.update(1)
                continue

            html, list_used_http = fetch_ndbg_list_html(sess, code, cache)

            rows = parse_ndbg_rows(html)
            if not rows:
                logger.info(
                    "[无列表] %s %s（未解析到 datelist，可能无公告或页面变更）",
                    code,
                    name,
                )
                if sleep_sec > 0 and list_used_http:
                    time.sleep(sleep_sec)
                stock_pbar.update(1)
                continue

            stock_used_http = list_used_http
            for ann, href, title in rows:
                if not is_full_annual_report_title(title):
                    continue
                year = report_year_from_title(title, ann)
                if year is None:
                    continue
                if year < year_start or year > year_end:
                    continue
                pdf_url, detail_used_http = fetch_pdf_url(sess, href, cache, stock_code=code)
                stock_used_http = stock_used_http or detail_used_http
                if not pdf_url:
                    logger.info("[无PDF] %s %s", code, title[:50])
                    if sleep_sec > 0 and detail_used_http:
                        time.sleep(sleep_sec)
                    continue
                yield code, name, industry, ann, year, title, pdf_url
            if sleep_sec > 0 and stock_used_http:
                time.sleep(sleep_sec)
            stock_pbar.update(1)


def main() -> None:
    global _PROGRESS_ENABLED

    parser = argparse.ArgumentParser(description="下载新浪财经沪深主板年报 PDF")
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=Path(OUTPUT_DIR_STR),
        help="输出根目录（默认取文件常量 OUTPUT_DIR_STR；其下 行业/年报 PDF；文件名含年份）",
    )
    parser.add_argument(
        "--year-start",
        type=int,
        default=REPORT_YEAR_START,
        help="报告期年份下限（默认取文件常量 REPORT_YEAR_START）",
    )
    parser.add_argument(
        "--year-end",
        type=int,
        default=REPORT_YEAR_END,
        help="报告期年份上限（默认取文件常量 REPORT_YEAR_END）",
    )
    parser.add_argument(
        "--cache-dir",
        type=Path,
        default=Path(CACHE_DIR_STR),
        help="网络缓存根目录（其下 http_get/ 为 *.txt + *.json 网页快照；PDF 在 --output）",
    )
    parser.add_argument(
        "--refresh",
        action=argparse.BooleanOptionalAction,
        default=REFRESH_CACHE,
        help="是否忽略缓存强制拉网（默认取文件常量 REFRESH_CACHE；可用 --no-refresh 关闭）",
    )
    parser.add_argument(
        "--sleep",
        type=float,
        default=DEFAULT_SLEEP_BETWEEN_STOCKS,
        help="反爬：仅当该股本次列表/详情发生过 HTTP 时在阶段末休眠（秒）；纯磁盘缓存则不睡（默认取 DEFAULT_SLEEP_BETWEEN_STOCKS）",
    )
    parser.add_argument(
        "--http-interval",
        type=float,
        default=HTTP_MIN_INTERVAL_SEC,
        help="两次成功 HTTP 网页请求之间的最小间隔秒数，另加随机抖动（减轻新浪 456 限流）",
    )
    parser.add_argument(
        "--http-jitter",
        type=float,
        default=HTTP_JITTER_SEC,
        help="HTTP 间隔上额外随机抖动上限（秒）",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=0,
        help="仅处理前 N 只股票（0 表示全部，用于测试）",
    )
    parser.add_argument(
        "--code",
        action="append",
        default=[],
        help="只下载指定代码，可多次指定，如 --code 600000 --code 000001",
    )
    parser.add_argument(
        "--no-progress",
        action="store_true",
        help="关闭所有 tqdm 进度条（适合重定向日志或 CI）",
    )
    parser.add_argument(
        "--log-level",
        default="INFO",
        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
        help="logging 日志级别（错误会打 logger.error 并常伴随异常抛出）",
    )
    args = parser.parse_args()

    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
        force=True,
    )

    if args.no_progress:
        _PROGRESS_ENABLED = False

    year_start, year_end = args.year_start, args.year_end
    if year_start > year_end:
        year_start, year_end = year_end, year_start
        print(f"警告：已交换年份起止为 {year_start}～{year_end}")

    sess = _session()
    cache = NetCache(
        args.cache_dir.resolve(),
        refresh=args.refresh,
        min_http_interval=args.http_interval,
        http_jitter=args.http_jitter,
    )

    if args.code:
        want_list: list[str] = []
        seen: set[str] = set()
        for c in args.code:
            z = c.zfill(6)
            if z not in seen:
                seen.add(z)
                want_list.append(z)
        want_set = set(want_list)
        names = cache.lookup_mainboard_names(want_list)
        stocks = []
        for c in want_list:
            if c in names:
                stocks.append((c, names[c]))
        missing = want_set - set(names.keys())
        if missing:
            print(f"警告：下列代码未在主板列表中找到（简称用代码代替）: {sorted(missing)}")
            for c in sorted(missing):
                stocks.append((c, c))
    else:
        logger.info("正在从 akshare 获取沪深主板股票列表（可用缓存）…")
        stocks = cache.load_mainboard_stocks()
        if args.limit > 0:
            stocks = stocks[: args.limit]

    logger.info(
        "共 %s 只股票，报告期年份: %s～%s，PDF 输出目录: %s，网页缓存根目录: %s，refresh=%s",
        len(stocks),
        year_start,
        year_end,
        args.output.resolve(),
        args.cache_dir.resolve(),
        args.refresh,
    )
    logger.info(
        "说明：年报 PDF 写入「PDF 输出目录」下「行业/」目录（文件名含报告期年份）；「网页缓存」下 http_get 内为 *.txt + *.json 快照，不是 PDF。"
    )

    logger.info(
        "正在加载股票行业映射（新浪财经 stock_classify_sina「%s」，可用 akshare 缓存）…",
        SINA_INDUSTRY_CLASSIFY_SYMBOL,
    )
    industry_map = cache.load_code_industry_map()

    ok = skip = missing_pdf = 0
    for code, name, industry, ann, year, title, pdf_url in iter_jobs(
        stocks,
        sess,
        args.sleep,
        cache,
        year_start,
        year_end,
        args.output.resolve(),
        industry_map,
    ):
        safe_ind = _sanitize_filename(industry)
        safe_company = _sanitize_company_for_report_filename(name)
        out_dir = args.output / safe_ind
        fname = f"{safe_company}-{code}-{year}.pdf"
        dest = out_dir / fname

        if dest.exists() and dest.stat().st_size > 0:
            logger.info("[跳过] 已存在 %s", dest)
            skip += 1
            continue

        logger.info(
            "[下载] %s %s %s <- %s",
            code,
            name,
            year,
            urlparse(pdf_url).path[-40:],
        )
        if download_pdf(sess, pdf_url, dest, progress_desc=f"{code} {year}"):
            ok += 1
            time.sleep(args.sleep)
        else:
            missing_pdf += 1
            out_root = args.output.resolve()
            _append_missing_pdf_log(
                out_root,
                reason="404/410",
                code=code,
                name=name,
                industry=industry,
                announce_date=ann,
                year=year,
                title=title,
                pdf_url=pdf_url,
                dest_path=dest,
            )

    logger.info("完成。成功: %s, 跳过: %s, PDF 缺失(404/410): %s", ok, skip, missing_pdf)
    if missing_pdf:
        logger.info("缺失明细文件: %s", args.output.resolve() / MISSING_PDF_LOG_FILENAME)


if __name__ == "__main__":
    main()
