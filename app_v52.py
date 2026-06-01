# ── CODERABBIT FULL REVIEW ──────────────────────────────────────────────────────
# Full codebase review for v52: summary styles (Story Arc, Feynman, Practical Playbook)
# and complete Flask book summarizer with news digest implementation.
# ─────────────────────────────────────────────────────────────────────────────────

# app_v50.py
# v50 change: final polish - hardened complete-sentence/takeaway validation, safer bullet shortening, and final style QA packaging.
# app_v45.py
# v45 change: news digest hardening - cleaned article extraction, dedupe on article body,
#             WHAT HAPPENED - ANALYSIS uses cap=min(350 words, 50% of cleaned article),
#             deterministic cap enforcement, short-output expansion retry, and offline backtest hooks.
# app_v43.py
# v43 change: news digest "WHAT HAPPENED — ANALYSIS" hardening — old policy used max(350, 50% of source);
#             v45 corrects that to min(350, 50% of cleaned article body).
# app_v41.py
# v41 change: style QA hardening; applies selected narrative style to executive/final recap prompts.
# v37 change: final quality gate, source boilerplate filtering, title/chapter cleanup, duplicate/fragment suppression, and no placeholder takeaways.
# v35 change: expose audit-trail download in the UI and keep v34 variant +20% caps/source_bytes fix.
# v34 change: variant PDFs (phone/B&W/cyan) are capped to +20%, phone density is improved, and source_bytes split bug remains fixed.
# v33 change: audit endpoint + faster default concurrency + v32 length micro-shrink + fixed smart split source_bytes bug.
# app_v20.py
# v27 change: fixes smart split source_bytes NameError, scales expansion targets, and applies compact page-cap mode for tight fixed outputs.
# v26 change: lower-bound page enforcement now retries hard and fails closed instead of returning under-length fixed summaries.
# v25 change: full-text PDF extraction now uses fast pypdf first, avoiding slow pdfplumber passes on text-layer books.
# v24 change: fast preflight/pagecount and deterministic instant suggestions; live AI suggestions disabled by default.
# v22 change: narrative is the default style; style menu reduced to Academic plus four narrative modes.
# v20 change: canonical source structure, budget-first generation, preflight feasibility, richer chapter endings, cancel/time budgets, and last-valid-PDF fallback.
# v19 change: harden fixed-page compression/PDF rebuild against stale spans and ReportLab build edge cases.
# v18 change: better deterministic section detection for report PDFs and mixed-size backtests.
# v17 change: fixed-page upper-bound enforcement with +10% hard cap and compression.
# v16 change: v15 OCR/layout hardening plus SDK-free Anthropic HTTP fallback.
# v15 change: OCR segmentation hardening, health endpoint, and accurate cover page count.
# v14 change: OCR timeout kill-path hardening.
# v13 change: OCR fallback for scanned/image PDFs, TOC parsing for image books, and real-PDF backtest hardening.

# ── Force UTF-8 ────────────────────────────────────────────────────────────────
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

import os
import re
import uuid
import json
import time
import shutil
import hashlib
import subprocess
import signal
import tempfile
import html
import math
import posixpath
import xml.etree.ElementTree as ET
from html.parser import HTMLParser
import zipfile
import threading
import traceback
import urllib.request
import urllib.parse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from io import BytesIO

from flask import Flask, request, jsonify, send_file, Response
from werkzeug.exceptions import RequestEntityTooLarge

import pdfplumber
from pypdf import PdfWriter, PdfReader
try:
    import anthropic
except Exception:  # Allows the app to run with the lightweight HTTP fallback below.
    anthropic = None
import httpx

# Optional OCR stack. The app can still run without these imports, but
# scanned/image-only PDFs require them to produce summarizable text.
try:
    import fitz  # PyMuPDF
    from PIL import Image as PILImage, ImageOps
    import pytesseract
except Exception:  # pragma: no cover - deployment dependency availability varies
    fitz = None
    PILImage = None
    ImageOps = None
    pytesseract = None

from reportlab.platypus import (
    BaseDocTemplate, PageTemplate, Frame, Paragraph, Spacer,
    PageBreak, NextPageTemplate, Image, HRFlowable, Table, TableStyle, KeepTogether,
)
from reportlab.platypus.tableofcontents import TableOfContents
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import cm, mm
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_LEFT, TA_JUSTIFY

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 100 * 1024 * 1024  # 100 MB upload limit

# Single source of truth for build identity — used by the startup banner,
# the digest cover stamp, and the /version endpoint so the running build can
# always be verified from the browser without depending on any file on disk.
BUILD_TAG   = "v52"
BUILD_LABEL = "CHAPTER-MANIFEST-LOCK BUILD"

@app.errorhandler(RequestEntityTooLarge)
def handle_too_large(e):
    return jsonify({"error": "File too large (max 100 MB)"}), 413

class BookDocTemplate(BaseDocTemplate):
    def afterFlowable(self, flowable):
        if hasattr(flowable, "toc_entry"):
            level, text, key = flowable.toc_entry
            self.notify("TOCEntry", (level, text, self.page, key))

# ── Constants ──────────────────────────────────────────────────────────────────
WORDS_PER_PAGE           = int(os.environ.get("BBC_WORDS_PER_PAGE", "420"))
CHARS_PER_CHUNK          = int(os.environ.get("BBC_CHARS_PER_CHUNK", "80000"))
MIN_CHARS_PER_CHUNK      = int(os.environ.get("BBC_MIN_CHARS_PER_CHUNK", "4500"))
MAX_SUMMARY_CHUNKS       = int(os.environ.get("BBC_MAX_SUMMARY_CHUNKS", "240"))
SUMMARY_MAX_WORKERS       = int(os.environ.get("BBC_SUMMARY_MAX_WORKERS", "6"))
MODEL_CHUNK              = os.environ.get("BBC_MODEL_CHUNK", "claude-haiku-4-5-20251001")
HAIKU_IN                 = 1.00   # Haiku input $/M tokens, used for estimates only.
HAIKU_OUT                = 5.00   # Haiku output $/M tokens, used for estimates only.
MAX_OUT_TOKENS_PER_CALL  = int(os.environ.get("BBC_MAX_OUT_TOKENS_PER_CALL", "16000"))
MIN_CHAPTER_WORDS        = int(os.environ.get("BBC_MIN_CHAPTER_WORDS", "350"))
AUDIT_EXTEND_THRESHOLD   = float(os.environ.get("BBC_AUDIT_EXTEND_THRESHOLD", "0.92"))
AUDIT_MAX_ROUNDS         = int(os.environ.get("BBC_AUDIT_MAX_ROUNDS", "4"))
HAIKU_RELIABLE_WORDS     = int(os.environ.get("BBC_HAIKU_RELIABLE_WORDS", "1400"))
TAKEAWAY_BULLETS         = int(os.environ.get("BBC_TAKEAWAY_BULLETS", "4"))
LENGTH_ENFORCE_MAX_ROUNDS= int(os.environ.get("BBC_LENGTH_ENFORCE_MAX_ROUNDS", "4"))
LENGTH_ENFORCE_MIN_RATIO = float(os.environ.get("BBC_LENGTH_ENFORCE_MIN_RATIO", "0.985"))
# Fixed-page mode is now a bounded range: by default the final PDF must be at
# least 98.5% of the request and no more than +10% of the request.
LENGTH_ENFORCE_MAX_RATIO = float(os.environ.get("BBC_LENGTH_ENFORCE_MAX_RATIO", "1.10"))
# Downloadable variants (phone, B&W, cyan) must never exceed +20% of the fixed-page request.
VARIANT_LENGTH_MAX_RATIO = float(os.environ.get("BBC_VARIANT_LENGTH_MAX_RATIO", "1.20"))
LENGTH_ENFORCE_TARGET_RATIO = float(os.environ.get("BBC_LENGTH_ENFORCE_TARGET_RATIO", "1.03"))
LENGTH_COMPRESS_MAX_ROUNDS = int(os.environ.get("BBC_LENGTH_COMPRESS_MAX_ROUNDS", "3"))
LENGTH_COMPRESS_AI = os.environ.get("BBC_LENGTH_COMPRESS_AI", "1").strip().lower() not in ("0", "false", "no", "off")
LENGTH_COMPRESS_SAFETY = float(os.environ.get("BBC_LENGTH_COMPRESS_SAFETY", "0.965"))
LENGTH_FAIL_ON_OVERSHOOT = os.environ.get("BBC_LENGTH_FAIL_ON_OVERSHOOT", "1").strip().lower() not in ("0", "false", "no", "off")

# v20: fixed-page generation should be budget-first, not final-compress-first.
# These reserve pages for cover, H1-only TOC, executive summary, faithfulness
# note, final review sheet, and back matter before allocating chapter prose.
FIXED_PAGE_WORD_RATIO = float(os.environ.get("BBC_FIXED_PAGE_WORD_RATIO", "0.68"))
FIXED_RESERVED_BASE_PAGES = int(os.environ.get("BBC_FIXED_RESERVED_BASE_PAGES", "4"))
FIXED_RESERVED_LONG_EXTRA_PAGES = int(os.environ.get("BBC_FIXED_RESERVED_LONG_EXTRA_PAGES", "2"))
SUMMARY_PROMPT_MAX_RATIO = float(os.environ.get("BBC_SUMMARY_PROMPT_MAX_RATIO", "1.03"))

# v20 optional output sections and conservative length tiers.
TOC_MAX_LEVEL = int(os.environ.get("BBC_TOC_MAX_LEVEL", "1"))
OUTPUT_EXECUTIVE_SUMMARY = os.environ.get("BBC_OUTPUT_EXECUTIVE_SUMMARY", "1").strip().lower() not in ("0", "false", "no", "off")
OUTPUT_FAITHFULNESS_NOTE = os.environ.get("BBC_OUTPUT_FAITHFULNESS_NOTE", "1").strip().lower() not in ("0", "false", "no", "off")
OUTPUT_FINAL_REVIEW_SHEET = os.environ.get("BBC_OUTPUT_FINAL_REVIEW_SHEET", "0").strip().lower() not in ("0", "false", "no", "off")
OUTPUT_FEYNMAN_STORYLINE = os.environ.get("BBC_OUTPUT_FEYNMAN_STORYLINE", "0").strip().lower() not in ("0", "false", "no", "off")
OUTPUT_SUMMARY_OF_SUMMARY = os.environ.get("BBC_OUTPUT_SUMMARY_OF_SUMMARY", "1").strip().lower() not in ("0", "false", "no", "off")
SUMMARY_OF_SUMMARY_TARGET_PAGES = int(os.environ.get("BBC_SUMMARY_OF_SUMMARY_TARGET_PAGES", "2"))
SUMMARY_OF_SUMMARY_MIN_PAGES = int(os.environ.get("BBC_SUMMARY_OF_SUMMARY_MIN_PAGES", "18"))
SUMMARY_OF_SUMMARY_WORDS_PER_PAGE = int(os.environ.get("BBC_SUMMARY_OF_SUMMARY_WORDS_PER_PAGE", "430"))
# v39: tailored length planner shows what fixed-page request approximates
# 10%-50% of the source word count. Keep this cheap enough for local use.
TAILORED_LENGTH_PCTS = [int(x) for x in os.environ.get("BBC_TAILORED_LENGTH_PCTS", "10,20,30,40,50").replace(";", ",").split(",") if str(x).strip().isdigit()] or [10, 20, 30, 40, 50]
TAILORED_MAX_PAGES = int(os.environ.get("BBC_TAILORED_MAX_PAGES", "260"))
FEYNMAN_MIN_PAGES = int(os.environ.get("BBC_FEYNMAN_MIN_PAGES", "3"))
FEYNMAN_MAX_PAGES = int(os.environ.get("BBC_FEYNMAN_MAX_PAGES", "5"))
FEYNMAN_TARGET_PAGES = int(os.environ.get("BBC_FEYNMAN_TARGET_PAGES", "4"))
FEYNMAN_MIN_SUMMARY_PAGES = int(os.environ.get("BBC_FEYNMAN_MIN_SUMMARY_PAGES", "20"))
FEYNMAN_WORDS_PER_PAGE = int(os.environ.get("BBC_FEYNMAN_WORDS_PER_PAGE", "600"))
OUTPUT_CHAPTER_PRACTICAL = os.environ.get("BBC_OUTPUT_CHAPTER_PRACTICAL", "1").strip().lower() not in ("0", "false", "no", "off")

# v37: deterministic final quality gate. Runs before main and variant PDF
# builds to block placeholder bullets, duplicated paragraphs, source
# boilerplate chapters, ugly headings, and obvious sentence fragments.
OUTPUT_QUALITY_GATE = os.environ.get("BBC_OUTPUT_QUALITY_GATE", "1").strip().lower() not in ("0", "false", "no", "off")
QUALITY_DEDUPE_WINDOW = int(os.environ.get("BBC_QUALITY_DEDUPE_WINDOW", "24"))
QUALITY_DROP_SOURCE_BOILERPLATE = os.environ.get("BBC_DROP_SOURCE_BOILERPLATE", "1").strip().lower() not in ("0", "false", "no", "off")
PDF_PULL_QUOTES = os.environ.get("BBC_PDF_PULL_QUOTES", "0").strip().lower() in ("1", "true", "yes", "on")

# v40: reader-friendly chapter layout. This does not change summary content;
# it only prevents huge walls of text and makes bare chapter headings read as
# "Chapter N: Title" when the title appears in the first child heading/body line.
PDF_AUTO_PARAGRAPHIZE = os.environ.get("BBC_PDF_AUTO_PARAGRAPHIZE", "1").strip().lower() not in ("0", "false", "no", "off")
PDF_MAX_PARAGRAPH_WORDS = int(os.environ.get("BBC_PDF_MAX_PARAGRAPH_WORDS", "115"))
PDF_MAX_PARAGRAPH_SENTENCES = int(os.environ.get("BBC_PDF_MAX_PARAGRAPH_SENTENCES", "4"))
PDF_CHAPTER_TITLE_PROMOTION = os.environ.get("BBC_PDF_CHAPTER_TITLE_PROMOTION", "1").strip().lower() not in ("0", "false", "no", "off")

# v46: style application hardening. Earlier versions passed a long style
# description to Claude, but live outputs could still collapse into the same
# generic summary voice. These settings force every non-basic style to carry
# visible prose/heading signatures and optionally rewrite weak chapters.
STYLE_AUDIT_ENABLED = os.environ.get("BBC_STYLE_AUDIT_ENABLED", "1").strip().lower() not in ("0", "false", "no", "off")
STYLE_AI_REWRITE = os.environ.get("BBC_STYLE_AI_REWRITE", "1").strip().lower() not in ("0", "false", "no", "off")
STYLE_AUDIT_MIN_SCORE = float(os.environ.get("BBC_STYLE_AUDIT_MIN_SCORE", "0.70"))
STYLE_AUDIT_MAX_REWRITES = int(os.environ.get("BBC_STYLE_AUDIT_MAX_REWRITES", "24"))
STYLE_AUDIT_SKIP_BASIC = os.environ.get("BBC_STYLE_AUDIT_SKIP_BASIC", "1").strip().lower() not in ("0", "false", "no", "off")

# v51: chapter manifest lock. Chapter detection, output H1 headings, ordering,
# coverage and budgeting now flow from a canonical manifest instead of Claude
# generated headings. This is designed to prevent PDF/EPUB chapters from being
# skipped, duplicated, reordered, or renamed during summarization.
CHAPTER_MANIFEST_LOCK_ENABLED = os.environ.get("BBC_CHAPTER_MANIFEST_LOCK", "1").strip().lower() not in ("0", "false", "no", "off")
CHAPTER_MANIFEST_DROP_ORPHANS = os.environ.get("BBC_CHAPTER_MANIFEST_DROP_ORPHANS", "1").strip().lower() not in ("0", "false", "no", "off")
CHAPTER_MANIFEST_MIN_TARGET_WORDS = int(os.environ.get("BBC_CHAPTER_MANIFEST_MIN_TARGET_WORDS", str(MIN_CHAPTER_WORDS)))
CHAPTER_MANIFEST_TINY_WORD_CAP = int(os.environ.get("BBC_CHAPTER_MANIFEST_TINY_WORD_CAP", "550"))
CHAPTER_MANIFEST_AUDIT_ENABLED = os.environ.get("BBC_CHAPTER_MANIFEST_AUDIT", "1").strip().lower() not in ("0", "false", "no", "off")
# v52: tolerate a small number of missing chapters instead of hard-failing the
# whole job. Books with quirky chapter titles (e.g. comedy memoirs) sometimes
# lose 1-2 headings to model renaming/merging; rather than refuse to build the
# PDF, allow up to this many missing chapters and just log a warning. Set to 0
# via BBC_CHAPTER_MANIFEST_MAX_MISSING to restore the old strict behavior.
CHAPTER_MANIFEST_MAX_MISSING = int(os.environ.get("BBC_CHAPTER_MANIFEST_MAX_MISSING", "2"))

# v20: generous safety budgets. These are intentionally high for local use;
# they stop infinite/hung jobs without killing normal long runs.
OCR_MAX_SECONDS = int(os.environ.get("BBC_OCR_MAX_SECONDS", "3600"))
SUMMARIZE_MAX_SECONDS = int(os.environ.get("BBC_SUMMARIZE_MAX_SECONDS", "7200"))
AUDIT_MAX_SECONDS = int(os.environ.get("BBC_AUDIT_MAX_SECONDS", "2400"))
COMPRESS_MAX_SECONDS = int(os.environ.get("BBC_COMPRESS_MAX_SECONDS", "1800"))
TOTAL_JOB_MAX_SECONDS = int(os.environ.get("BBC_TOTAL_JOB_MAX_SECONDS", "10800"))
ALLOW_OVERSIZED_FALLBACK = os.environ.get("BBC_ALLOW_OVERSIZED_FALLBACK", "0").strip().lower() in ("1", "true", "yes", "on")
OCR_ENABLED              = os.environ.get("BBC_OCR_ENABLED", "1").strip().lower() not in ("0", "false", "no", "off")
OCR_DPI                  = int(os.environ.get("BBC_OCR_DPI", "100"))
OCR_MAX_RENDER_DIM       = int(os.environ.get("BBC_OCR_MAX_RENDER_DIM", "1800"))
OCR_LANGS                = os.environ.get("BBC_OCR_LANGS", "eng+spa")
OCR_PSM                  = int(os.environ.get("BBC_OCR_PSM", "3"))
OCR_MIN_TEXT_CHARS       = int(os.environ.get("BBC_OCR_MIN_TEXT_CHARS", "500"))
OCR_MAX_PAGES            = int(os.environ.get("BBC_OCR_MAX_PAGES", "0"))  # 0 = no cap
OCR_SUGGEST_PAGES        = int(os.environ.get("BBC_OCR_SUGGEST_PAGES", "12"))
OCR_TIMEOUT_SECONDS      = int(os.environ.get("BBC_OCR_TIMEOUT_SECONDS", "12"))
OCR_AUTO_PSM             = os.environ.get("BBC_OCR_AUTO_PSM", "1").strip().lower() not in ("0", "false", "no", "off")
OCR_SECONDS_PER_PAGE_EST = int(os.environ.get("BBC_OCR_SECONDS_PER_PAGE_EST", "3"))
PAGECOUNT_TEXT_PROBE_PAGES = int(os.environ.get("BBC_PAGECOUNT_TEXT_PROBE_PAGES", "3"))
AI_SUGGESTIONS_ENABLED = os.environ.get("BBC_AI_SUGGESTIONS", "0").strip().lower() in ("1", "true", "yes", "on")
AUDIT_TRAIL_ENABLED = os.environ.get("BBC_AUDIT_TRAIL_ENABLED", "1").strip().lower() not in ("0", "false", "no", "off")
AUDIT_TRAIL_MAX_EVENTS = int(os.environ.get("BBC_AUDIT_TRAIL_MAX_EVENTS", "2000"))
CLOUD_PARENT_FOLDER      = "books"
MAX_PDF_CACHE            = 8

# News-digest controls. The WHAT HAPPENED - ANALYSIS section must never exceed
# the smaller of 350 words or half of the cleaned source article. A separate
# lower-band target nudges the model to use the available space instead of
# returning 60-word blurbs, but the upper cap is always enforced deterministically.
NEWS_ARTICLE_MAX_CHARS   = int(os.environ.get("BBC_NEWS_ARTICLE_MAX_CHARS", "50000"))
NEWS_WH_ABSOLUTE_MAX     = int(os.environ.get("BBC_NEWS_WH_ABSOLUTE_MAX", "350"))
NEWS_WH_SOURCE_MAX_RATIO = float(os.environ.get("BBC_NEWS_WH_SOURCE_MAX_RATIO", "0.50"))
NEWS_WH_TARGET_RATIO     = float(os.environ.get("BBC_NEWS_WH_TARGET_RATIO", "0.92"))
NEWS_WH_MIN_RATIO        = float(os.environ.get("BBC_NEWS_WH_MIN_RATIO", "0.76"))
NEWS_WH_RETRY_EXPAND     = os.environ.get("BBC_NEWS_WH_RETRY_EXPAND", "1").strip().lower() not in ("0", "false", "no", "off")

# Set these env vars to override automatic cloud-drive detection:
#   Windows:  setx BBC_GDRIVE_ROOT "G:\My Drive"
#   macOS/Linux: export BBC_GDRIVE_ROOT="/path/to/My Drive"
GDRIVE_ROOT_OVERRIDE   = os.environ.get("BBC_GDRIVE_ROOT",   "").strip() or None
ONEDRIVE_ROOT_OVERRIDE = os.environ.get("BBC_ONEDRIVE_ROOT", "").strip() or None

TMP_DIR = os.path.join(os.environ.get("TEMP", os.path.expanduser("~")), "book_summarizer")
os.makedirs(TMP_DIR, exist_ok=True)

HISTORY_FILE = os.path.join(TMP_DIR, "history.json")
_history_lock = threading.Lock()

def _history_load():
    try:
        with open(HISTORY_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []

def _history_save(entries):
    with open(HISTORY_FILE, "w", encoding="utf-8") as f:
        json.dump(entries, f, ensure_ascii=False, indent=2)

def _history_add(entry):
    with _history_lock:
        entries = _history_load()
        entries.insert(0, entry)
        entries = entries[:50]
        _history_save(entries)

def _history_remove(entry_id):
    with _history_lock:
        entries = _history_load()
        to_delete = [e for e in entries if e["id"] == entry_id]
        entries = [e for e in entries if e["id"] != entry_id]
        _history_save(entries)
    for e in to_delete:
        for key in ("pdf_path", "meta_path"):
            p = e.get(key)
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except Exception:
                    pass

# In-memory state
jobs   = {}
shares = {}
_pdf_cache      = {}
_pdf_cache_lock = threading.Lock()

# ── PDF Colors ─────────────────────────────────────────────────────────────────
C_BG     = colors.HexColor("#0a0a1a")
C_ACCENT = colors.HexColor("#7C3AED")
C_GOLD   = colors.HexColor("#f59e0b")
C_TEXT   = colors.HexColor("#e8e8f0")
C_WHITE  = colors.HexColor("#ffffff")
C_MUTED  = colors.HexColor("#5b5b7b")
C_CARD   = colors.HexColor("#13132a")
C_BORDER = colors.HexColor("#1f1f3a")
C_GREEN  = colors.HexColor("#10b981")

# ── Utilities ──────────────────────────────────────────────────────────────────
def safe(text):
    t = str(text)
    t = t.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    # Keep literal asterisks safe. Earlier markdown conversion could create
    # malformed ReportLab markup when source text contained unmatched footnote
    # markers such as Regional** or table notes. Literal asterisks are safer
    # than risking a failed PDF build.
    t = t.replace("*", "&#42;")
    t = "".join(ch for ch in t if ch >= " " or ch in "\n\t")
    return t

def scrub(t):
    return str(t).replace("\\", "").replace("\x00", "").replace("\r", "")

def _anthropic_text(resp):
    """Extract text from Anthropic content blocks defensively."""
    parts = []
    for block in getattr(resp, "content", []) or []:
        txt = getattr(block, "text", None)
        if txt:
            parts.append(txt)
    return "\n".join(parts).strip()


class _TextBlock:
    def __init__(self, text):
        self.text = text or ""


class _AnthropicHTTPResponse:
    def __init__(self, data):
        self.stop_reason = data.get("stop_reason")
        self.content = []
        for block in data.get("content", []) or []:
            if isinstance(block, dict) and block.get("type") == "text":
                self.content.append(_TextBlock(block.get("text", "")))


class _AnthropicHTTPStatusError(Exception):
    def __init__(self, status_code, message):
        self.status_code = int(status_code or 0)
        super().__init__(f"Anthropic HTTP {self.status_code}: {str(message)[:500]}")


class _AnthropicHTTPConnectionError(Exception):
    pass


class _AnthropicHTTPMessages:
    def __init__(self, parent):
        self.parent = parent

    def create(self, model, max_tokens, messages):
        payload = {
            "model": model,
            "max_tokens": int(max_tokens),
            "messages": messages,
        }
        headers = {
            "x-api-key": self.parent.api_key,
            "anthropic-version": "2023-06-01",
            "content-type": "application/json",
        }
        try:
            resp = self.parent.http_client.post(
                "https://api.anthropic.com/v1/messages",
                headers=headers,
                json=payload,
            )
        except (httpx.TimeoutException, httpx.NetworkError, httpx.HTTPError) as e:
            raise _AnthropicHTTPConnectionError(str(e)) from e
        if resp.status_code >= 400:
            raise _AnthropicHTTPStatusError(resp.status_code, resp.text)
        return _AnthropicHTTPResponse(resp.json())


class _AnthropicHTTPClient:
    """Tiny Anthropic Messages API client used when the official SDK is absent.

    It intentionally mimics the small subset of the SDK that this app uses:
    client.messages.create(model=..., max_tokens=..., messages=...).
    """
    def __init__(self, api_key, http_client=None):
        self.api_key = api_key
        self.http_client = http_client or httpx.Client(timeout=httpx.Timeout(180.0, connect=15.0, read=180.0, write=30.0))
        self.messages = _AnthropicHTTPMessages(self)


def _make_ai_client(api_key, timeout_seconds=180.0):
    timeout = httpx.Timeout(float(timeout_seconds), connect=15.0, read=float(timeout_seconds), write=30.0)
    http_client = httpx.Client(timeout=timeout)
    if anthropic is not None:
        return anthropic.Anthropic(api_key=api_key, http_client=http_client)
    return _AnthropicHTTPClient(api_key=api_key, http_client=http_client)


def _api_error_kind(exc):
    """Classify SDK and HTTP-fallback Anthropic errors without importing SDK classes."""
    status = getattr(exc, "status_code", None)
    name = type(exc).__name__
    if status == 429 or "RateLimit" in name:
        return "rate_limit"
    if isinstance(exc, _AnthropicHTTPConnectionError):
        return "connection"
    if isinstance(exc, (httpx.TimeoutException, httpx.NetworkError, httpx.HTTPError)):
        return "connection"
    if name in {"APIConnectionError", "APITimeoutError", "ConnectError", "ReadTimeout", "WriteTimeout", "PoolTimeout"}:
        return "connection"
    if status is not None:
        return "status"
    return "other"


def _audit_event(job_id, event, **payload):
    """Append a small JSONL audit event for diagnostics and backtests."""
    if not AUDIT_TRAIL_ENABLED or not job_id:
        return
    try:
        clean_payload = {}
        for k, v in (payload or {}).items():
            if isinstance(v, (str, int, float, bool)) or v is None:
                clean_payload[k] = v
            elif isinstance(v, (list, tuple)):
                clean_payload[k] = list(v)[:40]
            elif isinstance(v, dict):
                clean_payload[k] = {str(kk): vv for kk, vv in list(v.items())[:40] if isinstance(vv, (str, int, float, bool)) or vv is None}
            else:
                clean_payload[k] = str(v)[:500]
        row = {"ts": time.strftime("%Y-%m-%d %H:%M:%S"), "job_id": job_id, "event": str(event), **clean_payload}
        job = jobs.get(job_id)
        if job is not None:
            evs = job.setdefault("audit_events", [])
            evs.append(row)
            if len(evs) > AUDIT_TRAIL_MAX_EVENTS:
                del evs[:len(evs) - AUDIT_TRAIL_MAX_EVENTS]
        path = os.path.join(TMP_DIR, f"{job_id}_audit.jsonl")
        with open(path, "a", encoding="utf-8", errors="replace") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
    except Exception:
        pass


def fail(job_id, msg):
    clean = "".join(c for c in str(msg) if ord(c) < 128)
    if job_id in jobs:
        jobs[job_id].update({"status": "error", "error": clean})
    _audit_event(job_id, "error", message=clean)


class JobCancelled(Exception):
    """Raised when the user cancels a running job."""


class JobBudgetExceeded(Exception):
    """Raised when a job or stage exceeds a configured time budget."""


def _seconds_left(job_id, stage=None):
    job = jobs.get(job_id) or {}
    now = time.time()
    created = job.get("created_at", now)
    total_left = TOTAL_JOB_MAX_SECONDS - (now - created)
    if stage:
        started = job.get("stage_started_at", created)
        budget = {
            "ocr": OCR_MAX_SECONDS,
            "summarize": SUMMARIZE_MAX_SECONDS,
            "audit": AUDIT_MAX_SECONDS,
            "compress": COMPRESS_MAX_SECONDS,
        }.get(stage)
        if budget:
            return min(total_left, budget - (now - started))
    return total_left

def _check_job_control(job_id, stage=None):
    job = jobs.get(job_id)
    if not job:
        return
    if job.get("cancel_requested"):
        job.update({"status": "cancelled", "message": "Cancelled by user.", "last_update": time.time()})
        raise JobCancelled("Job cancelled by user.")
    if TOTAL_JOB_MAX_SECONDS and time.time() - job.get("created_at", time.time()) > TOTAL_JOB_MAX_SECONDS:
        raise JobBudgetExceeded(f"Job exceeded the total time budget of {TOTAL_JOB_MAX_SECONDS} seconds.")
    if stage:
        budget = {
            "ocr": OCR_MAX_SECONDS,
            "summarize": SUMMARIZE_MAX_SECONDS,
            "audit": AUDIT_MAX_SECONDS,
            "compress": COMPRESS_MAX_SECONDS,
        }.get(stage)
        if budget and time.time() - job.get("stage_started_at", job.get("created_at", time.time())) > budget:
            raise JobBudgetExceeded(f"Stage '{stage}' exceeded its time budget of {budget} seconds.")

def _start_stage(job_id, stage, message=None, progress=None):
    job = jobs.get(job_id)
    if not job:
        return
    now = time.time()
    update = {"stage": stage, "stage_started_at": now, "last_update": now}
    if message is not None:
        update["message"] = message
    if progress is not None:
        update["progress"] = progress
    job.update(update)
    _audit_event(job_id, "stage_start", stage=stage, message=message or "", progress=progress)
    _check_job_control(job_id, stage)

def _job_update(job_id, progress=None, message=None, stage=None, **extra):
    job = jobs.get(job_id)
    if not job:
        return
    now = time.time()
    update = {"last_update": now}
    if progress is not None:
        update["progress"] = progress
    if message is not None:
        update["message"] = message
    if stage and stage != job.get("stage"):
        update["stage"] = stage
        update["stage_started_at"] = now
    update.update(extra)
    job.update(update)
    if message is not None or stage is not None:
        _audit_event(job_id, "job_update", stage=stage or job.get("stage"), message=message or "", progress=progress)
    _check_job_control(job_id, stage or job.get("stage"))

def _record_last_valid_pdf(job_id, pdf_path, rendered_pages=None, sections=None, note=""):
    """Keep a copy of the most recent readable PDF for graceful fallback."""
    if not job_id or job_id not in jobs or not pdf_path or not os.path.exists(pdf_path):
        return
    try:
        # Verify readability before advertising this as recoverable.
        pages = len(PdfReader(pdf_path).pages)
        if pages <= 0:
            return
        rendered_pages = pages if rendered_pages is None else rendered_pages
        fallback_path = os.path.join(TMP_DIR, f"{job_id}_last_valid.pdf")
        shutil.copy2(pdf_path, fallback_path)
        jobs[job_id].update({
            "last_valid_pdf_path": fallback_path,
            "last_valid_rendered_pages": int(rendered_pages or pages),
            "last_valid_note": note,
            "last_valid_at": time.time(),
        })
        if sections is not None:
            jobs[job_id]["last_valid_sections"] = [dict(s) for s in sections]
        _audit_event(job_id, "last_valid_pdf", rendered_pages=int(rendered_pages or pages), note=note)
    except Exception:
        pass

def _restore_last_valid_pdf(job_id, out_path, requested_pages=0):
    job = jobs.get(job_id) or {}
    fallback = job.get("last_valid_pdf_path")
    if not fallback or not os.path.exists(fallback):
        return None
    rendered = int(job.get("last_valid_rendered_pages") or 0)
    if requested_pages:
        min_pages, max_pages, _target_pages = _fixed_page_bounds(requested_pages)
        if not (min_pages <= rendered <= max_pages or ALLOW_OVERSIZED_FALLBACK):
            return None
    try:
        shutil.copy2(fallback, out_path)
        return rendered
    except Exception:
        return None

def clean_title(raw):
    """Clean user/file-derived titles without preserving archive cruft."""
    c = str(raw or "").replace("\\", " ").replace("/", " ")
    c = re.sub(r"\.(pdf|epub)$", "", c, flags=re.I)
    c = re.sub(r"\s*\(\d+\)\s*$", "", c)
    for pat in [
        r"\s+--\s+.*$",
        r"\s+-\s+Anna.?s Archive.*$",
        r"\s+Anna.?s Archive.*$",
        r"\s+kindle@\S+.*$",
    ]:
        c = re.sub(pat, "", c, flags=re.I)
    c = re.sub(r"\s*_\s*", ": ", c, count=1)
    c = c.replace("_", " ")
    c = re.sub(r"https?://\S+", "", c)
    c = re.sub(r"\b(?=[0-9a-f]*\d)(?=[0-9a-f]*[a-f])[0-9a-f]{8,}\b", "", c, flags=re.IGNORECASE)
    c = re.sub(r"\s+[,;:-]+\s*$", "", c)
    c = re.sub(r"\s{2,}", " ", c).strip(" ,;:-")
    c = re.sub(r"\bBillion Dollar Whale:\s*The Man Who Fooled Wall Street,?$", "Billion Dollar Whale: The Man Who Fooled Wall Street, Hollywood, and the World", c, flags=re.I)
    return c[:120]

def _safe_title(title):
    t = re.sub(r"[^\w\s-]", "", title).strip()[:80]
    return re.sub(r"\s+", " ", t).strip()

# ── PDF Cache + OCR fallback ───────────────────────────────────────────────────
def _ocr_stack_available():
    return bool(
        fitz is not None and PILImage is not None and
        (pytesseract is not None or shutil.which("tesseract"))
    )


def _ocr_image_to_string(img, psm=None):
    """Run OCR with a hard timeout. Prefer the tesseract binary because
    a controlled subprocess lets us kill pathological pages cleanly.
    """
    psm = int(psm if psm is not None else OCR_PSM)
    if shutil.which("tesseract"):
        tmp_name = None
        proc = None
        try:
            with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as tmp:
                tmp_name = tmp.name
            img.save(tmp_name)
            cmd = [
                "tesseract", tmp_name, "stdout",
                "-l", OCR_LANGS,
                "--oem", "1",
                "--psm", str(psm),
            ]
            env = os.environ.copy()
            env.setdefault("OMP_THREAD_LIMIT", "1")
            proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                env=env,
                start_new_session=True,
            )
            try:
                stdout, _stderr = proc.communicate(timeout=OCR_TIMEOUT_SECONDS)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except Exception:
                    try:
                        proc.kill()
                    except Exception:
                        pass
                stdout, _stderr = proc.communicate()
                return ""
            if stdout or proc.returncode == 0:
                return stdout or ""
        finally:
            if tmp_name and os.path.exists(tmp_name):
                try:
                    os.remove(tmp_name)
                except Exception:
                    pass
    if pytesseract is None:
        return ""
    try:
        return pytesseract.image_to_string(
            img, lang=OCR_LANGS, config=f"--oem 1 --psm {psm}", timeout=OCR_TIMEOUT_SECONDS
        )
    except TypeError:
        return pytesseract.image_to_string(
            img, lang=OCR_LANGS, config=f"--oem 1 --psm {psm}"
        )


def _normalise_ocr_text(text):
    text = str(text or "").replace("\x00", "")
    text = re.sub(r"[ \t]+\n", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def _ocr_pdf_page_texts(pdf_bytes, total_pages, ocr_max_pages=None, job_id=None):
    """OCR a scanned/image PDF into per-page text.

    This is intentionally a fallback path: normal embedded PDF text is always
    preferred because it is faster and more accurate. OCR is used only when the
    extracted text layer is too small to summarize.
    """
    if not OCR_ENABLED:
        return [""] * total_pages, "ocr_disabled"
    if not _ocr_stack_available():
        return [""] * total_pages, "ocr_stack_unavailable"

    cap = int(ocr_max_pages or 0)
    if cap <= 0 and OCR_MAX_PAGES > 0:
        cap = OCR_MAX_PAGES

    try:
        doc = fitz.open(stream=pdf_bytes, filetype="pdf")
    except Exception as e:
        return [""] * total_pages, f"ocr_open_failed:{type(e).__name__}"

    limit = min(total_pages, doc.page_count, cap if cap > 0 else doc.page_count)
    page_texts = []
    base_scale = max(1.0, OCR_DPI / 72.0)
    status = "ocr_ok"

    log_path = os.path.join(TMP_DIR, "ocr.log")

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id or '-'}] {msg}\n")
        except Exception:
            pass

    _log(f"OCR start: pages={total_pages}, limit={limit}, dpi={OCR_DPI}, langs={OCR_LANGS}, psm={OCR_PSM}, auto_psm={OCR_AUTO_PSM}")
    _start_stage(job_id, "ocr", message="OCR text extraction...", progress=2) if job_id in jobs else None
    for page_idx in range(limit):
        _check_job_control(job_id, "ocr")
        try:
            page = doc.load_page(page_idx)
            longest_side = max(float(page.rect.width), float(page.rect.height), 1.0)
            scale = min(base_scale, max(1.0, OCR_MAX_RENDER_DIM / longest_side))
            matrix = fitz.Matrix(scale, scale)
            pix = page.get_pixmap(matrix=matrix, alpha=False)
            img = PILImage.open(BytesIO(pix.tobytes("png")))
            try:
                img = ImageOps.grayscale(img)
            except Exception:
                pass
            page_psm = OCR_PSM
            if OCR_AUTO_PSM:
                try:
                    is_landscape = float(page.rect.width) > float(page.rect.height) * 1.10
                    page_psm = 6 if is_landscape else OCR_PSM
                except Exception:
                    page_psm = OCR_PSM
            txt = _ocr_image_to_string(img, psm=page_psm)
            page_texts.append(_normalise_ocr_text(txt))
        except Exception as e:
            status = "ocr_partial"
            page_texts.append("")
            _log(f"OCR page {page_idx + 1} failed: {type(e).__name__}: {e}")

        if job_id in jobs and ((page_idx + 1) == limit or (page_idx + 1) % 3 == 0):
            _job_update(job_id, message=f"OCR text extraction... page {page_idx + 1} of {limit}", stage="ocr")

    if limit < total_pages:
        page_texts.extend([""] * (total_pages - limit))
        status = "ocr_sampled" if status == "ocr_ok" else status

    _log(f"OCR finished: status={status}, chars={sum(len(t) for t in page_texts)}")
    return page_texts, status


def _extract_pdf_text_layer(pdf_bytes):
    """Extract text from a PDF text layer.

    v39 tries PyMuPDF first because it is much faster on long text-layer
    books. pypdf/pdfplumber remain fallbacks. OCR is still handled by caller.
    """
    if fitz is not None:
        try:
            doc = fitz.open(stream=pdf_bytes, filetype="pdf")
            page_texts = []
            full_text = ""
            for page in doc:
                try:
                    t = page.get_text("text") or ""
                except Exception:
                    t = ""
                page_texts.append(t)
                full_text += t + "\n"
            return {
                "pages": doc.page_count,
                "full_text": full_text,
                "page_texts": page_texts,
                "text_extractor": "pymupdf",
            }
        except Exception:
            pass

    try:
        reader = PdfReader(BytesIO(pdf_bytes))
        page_texts = []
        full_text = ""
        for page in reader.pages:
            try:
                t = page.extract_text() or ""
            except Exception:
                t = ""
            page_texts.append(t)
            full_text += t + "\n"
        return {
            "pages": len(reader.pages),
            "full_text": full_text,
            "page_texts": page_texts,
            "text_extractor": "pypdf",
        }
    except Exception:
        pass

    full_text = ""
    page_texts = []
    with pdfplumber.open(BytesIO(pdf_bytes)) as pdf:
        total_pages = len(pdf.pages)
        for page in pdf.pages:
            t = page.extract_text() or ""
            page_texts.append(t)
            full_text += t + "\n"
    return {"pages": total_pages, "full_text": full_text, "page_texts": page_texts, "text_extractor": "pdfplumber"}


def _get_pdf_data(pdf_bytes, allow_ocr=None, ocr_max_pages=None, job_id=None):
    """Return cached {pages, full_text, page_texts} for the given PDF bytes.

    allow_ocr=False is used by lightweight routes such as /pagecount so a scanned
    100+ page book does not block the browser while the app merely counts pages.
    The background summarization job uses allow_ocr=True by default and will OCR
    scanned/image-only PDFs before chunking and summarizing.
    """
    if allow_ocr is None:
        allow_ocr = OCR_ENABLED
    mode = f"ocr:{int(bool(allow_ocr))}:max:{int(ocr_max_pages or 0)}"
    key = hashlib.sha256(pdf_bytes).hexdigest() + "|" + mode
    with _pdf_cache_lock:
        if key in _pdf_cache:
            return _pdf_cache[key]

    result = _extract_pdf_text_layer(pdf_bytes)
    result.update({"ocr_used": False, "ocr_status": "text_layer", "extraction_method": result.get("text_extractor", "embedded_text")})

    if allow_ocr and len(result["full_text"].strip()) < OCR_MIN_TEXT_CHARS:
        page_texts, status = _ocr_pdf_page_texts(
            pdf_bytes, result["pages"], ocr_max_pages=ocr_max_pages, job_id=job_id
        )
        full_text = "".join((pt or "") + "\n" for pt in page_texts)
        if len(full_text.strip()) > len(result["full_text"].strip()):
            result = {
                "pages": result["pages"],
                "full_text": full_text,
                "page_texts": page_texts,
                "ocr_used": True,
                "ocr_status": status,
                "extraction_method": "ocr",
            }
        else:
            result["ocr_status"] = status

    with _pdf_cache_lock:
        if len(_pdf_cache) >= MAX_PDF_CACHE:
            _pdf_cache.pop(next(iter(_pdf_cache)))
        _pdf_cache[key] = result
    return result


# ── EPUB extraction ────────────────────────────────────────────────────────────
def _detect_source_format(filename="", data=b""):
    """Return 'pdf' or 'epub' from extension and file signature."""
    name = str(filename or "").lower().strip()
    head = bytes(data or b"")[:64]
    if name.endswith(".epub"):
        return "epub"
    if name.endswith(".pdf"):
        return "pdf"
    if head.startswith(b"%PDF"):
        return "pdf"
    if head.startswith(b"PK"):
        try:
            with zipfile.ZipFile(BytesIO(data)) as zf:
                try:
                    mt = zf.read("mimetype").decode("utf-8", "ignore").strip()
                    if mt == "application/epub+zip":
                        return "epub"
                except Exception:
                    pass
                names = set(zf.namelist())
                if "META-INF/container.xml" in names:
                    return "epub"
        except Exception:
            pass
    return "pdf"



def _fast_pdf_preflight(pdf_bytes, text_probe_pages=None):
    """Very fast page-count probe for /pagecount and /suggest.

    This intentionally avoids full pdfplumber extraction across the entire book.
    Full extraction/OCR happens only when the user starts a summary job.
    """
    if text_probe_pages is None:
        text_probe_pages = PAGECOUNT_TEXT_PROBE_PAGES
    pages = 0
    sample_text = ""
    try:
        reader = PdfReader(BytesIO(pdf_bytes))
        pages = len(reader.pages)
    except Exception:
        # Fall back to pdfplumber only if pypdf cannot read the file.
        with pdfplumber.open(BytesIO(pdf_bytes)) as pdf:
            pages = len(pdf.pages)
    # Probe only a few pages to estimate whether OCR will be needed.
    if text_probe_pages and text_probe_pages > 0 and pages > 0:
        try:
            with pdfplumber.open(BytesIO(pdf_bytes)) as pdf:
                for page in pdf.pages[:min(text_probe_pages, len(pdf.pages))]:
                    t = page.extract_text() or ""
                    if t:
                        sample_text += t + "\n"
                    if len(sample_text) >= 2000:
                        break
        except Exception:
            sample_text = ""
    return {
        "pages": pages,
        "full_text": sample_text,
        "page_texts": [sample_text] if sample_text else [],
        "ocr_used": False,
        "ocr_status": "preflight_sample",
        "extraction_method": "preflight",
    }


def _fast_epub_preflight(epub_bytes):
    """Lightweight EPUB page estimate without full chapter extraction.

    Uses compressed container text lengths and a limited HTML text scan. Full EPUB
    parsing still happens in the background summary job.
    """
    total_text_chars = 0
    sample_text = ""
    chapter_count = 0
    try:
        with zipfile.ZipFile(BytesIO(epub_bytes)) as zf:
            names = [n for n in zf.namelist() if n.lower().endswith((".xhtml", ".html", ".htm"))]
            chapter_count = len(names)
            for name in names[:60]:
                try:
                    raw = zf.read(name)
                except Exception:
                    continue
                total_text_chars += len(raw)
                if len(sample_text) < 2500:
                    txt, _title = _epub_read_text(raw[:200000])
                    if txt:
                        sample_text += txt[:2500 - len(sample_text)] + "\n"
    except Exception:
        pass
    # HTML markup inflates raw bytes; 7 chars/word is a conservative estimate.
    est_words = max(1, int(total_text_chars / 7)) if total_text_chars else max(1, len(sample_text.split()))
    pages = max(1, int(math.ceil(est_words / max(1, WORDS_PER_PAGE))))
    return {
        "pages": pages,
        "virtual_pages": chapter_count,
        "full_text": sample_text,
        "page_texts": [sample_text] if sample_text else [],
        "chapter_list": [],
        "ocr_used": False,
        "ocr_status": "not_applicable",
        "extraction_method": "epub_preflight",
        "source_format": "epub",
        "estimated_pages": True,
    }


def _fast_document_preflight(source_bytes, source_format="pdf"):
    source_format = str(source_format or "pdf").lower()
    if source_format == "epub":
        return _fast_epub_preflight(source_bytes)
    return _fast_pdf_preflight(source_bytes)


def _deterministic_summary_suggestions(total_pages, source_format="pdf", ocr_required=False):
    """Instant suggestions: avoids a live model call during upload.

    The model-generated suggestion route was convenient, but it made the page
    count/suggestion phase feel frozen on long books and scanned PDFs. These
    ranges are deliberately simple and stable.
    """
    pages = max(1, int(total_pages or 1))
    if pages <= 10:
        vals = [max(5, pages), max(8, pages * 2), max(12, pages * 3)]
    elif pages <= 40:
        vals = [10, min(25, max(15, pages // 2)), min(50, max(25, pages))]
    elif pages <= 120:
        vals = [15, 30, 50]
    elif pages <= 250:
        vals = [25, 50, 75]
    else:
        vals = [35, 75, 100]
    # Ensure ascending and unique while preserving three options.
    vals = sorted({max(5, int(v)) for v in vals})
    while len(vals) < 3:
        vals.append(vals[-1] + 15)
    vals = vals[:3]
    kind = "EPUB" if str(source_format).lower() == "epub" else "PDF"
    ocr_note = " OCR may add runtime for scanned pages." if ocr_required else ""
    return [
        {"pages": vals[0], "reason": f"Fast orientation for this {kind}: captures the core thesis, structure, and most important takeaways without extended examples.{ocr_note}"},
        {"pages": vals[1], "reason": f"Balanced summary depth: covers all major chapters or sections with enough explanation to retain logic, transitions, and practical implications."},
        {"pages": vals[2], "reason": f"Deep-dive version: preserves more nuance, supporting arguments, examples, and chapter-level learning value while remaining shorter than the source."},
    ]

def _requested_pages_for_body_words(target_words, max_pages=None):
    """Return the fixed-page request whose body budget first reaches target_words."""
    target = max(1, int(target_words or 1))
    cap = max(10, int(max_pages or TAILORED_MAX_PAGES))
    for pages in range(1, cap + 1):
        if _fixed_body_word_target(pages) >= target:
            return pages
    return cap


def _detect_chapters_for_tailored(source_bytes, pdf_data, source_format="pdf"):
    """Fast, deterministic chapter count for the Tailored planner.

    It deliberately avoids Claude so the planner is cheap and repeatable.
    It follows the same source-structure preference as the main summarizer:
    reliable TOC first, then PDF outline, then pattern/page-title fallback.
    """
    source_format = str(source_format or "pdf").lower()
    total_pages = int(pdf_data.get("pages") or len(pdf_data.get("page_texts") or []) or 1)
    if source_format == "epub" and pdf_data.get("chapter_list"):
        chapters = _canonicalize_chapter_list(pdf_data.get("chapter_list") or [], total_pages)
        return chapters

    page_texts = pdf_data.get("page_texts") or []
    try:
        outline = _canonicalize_chapter_list(_extract_pdf_outline(source_bytes), total_pages)
    except Exception:
        outline = []
    try:
        toc = _canonicalize_chapter_list(_detect_chapters_from_toc_text(page_texts, total_pages), total_pages)
    except Exception:
        toc = []
    try:
        pattern = _canonicalize_chapter_list(detect_chapter_starts(page_texts), total_pages)
    except Exception:
        pattern = []

    toc = _enrich_chapter_titles_from_pages(toc, page_texts)
    outline = _enrich_chapter_titles_from_pages(outline, page_texts)
    pattern = _enrich_chapter_titles_from_pages(pattern, page_texts)

    toc_is_book = _looks_like_book_chapter_list(toc)
    outline_is_book = _looks_like_book_chapter_list(outline)
    pattern_is_book = _looks_like_book_chapter_list(pattern)
    # Do not let a partial TOC override a fuller outline/pattern sequence.
    fuller_baseline = max(len(outline) if outline_is_book else 0, len(pattern) if pattern_is_book else 0, 1)
    if toc_is_book and len(toc) >= max(8, int(fuller_baseline * 0.70)):
        return toc
    if outline_is_book:
        return outline
    if pattern_is_book:
        return pattern

    merged = _canonicalize_chapter_list((outline or []) + (toc or []) + (pattern or []), total_pages)
    merged = _enrich_chapter_titles_from_pages(merged, page_texts)
    if _looks_like_book_chapter_list(merged):
        return merged

    try:
        page_titles = _canonicalize_chapter_list(_detect_page_title_sections(page_texts), total_pages)
    except Exception:
        page_titles = []
    return merged or page_titles


def _tailored_length_plan(source_bytes, filename=""):
    """Return source word count, chapter count, average words/chapter, and
    fixed-page requests for 10%-50% source-word summaries.
    """
    source_format = _detect_source_format(filename, source_bytes)
    pdf_data = _get_document_data(source_bytes, source_format=source_format, allow_ocr=False)
    full_text = pdf_data.get("full_text", "") or ""
    word_count = _count_words(full_text)
    if word_count <= 0:
        raise ValueError("Could not extract enough text to calculate a tailored plan. If this is scanned, OCR will be needed during generation.")
    chapters = _detect_chapters_for_tailored(source_bytes, pdf_data, source_format=source_format)
    chapter_count = max(1, len(chapters))
    avg_words = int(round(word_count / max(1, chapter_count)))
    options = []
    for pct in TAILORED_LENGTH_PCTS:
        pct = max(1, min(100, int(pct)))
        target_words = int(round(word_count * pct / 100.0))
        pages = _requested_pages_for_body_words(target_words)
        min_pages, max_pages, target_pages = _fixed_page_bounds(pages, strictness="standard")
        options.append({
            "percent": pct,
            "target_words": target_words,
            "pages": pages,
            "allowed_min": min_pages,
            "allowed_max": max_pages,
            "target_pages": target_pages,
        })
    return {
        "source_format": source_format,
        "pages": int(pdf_data.get("pages") or 0),
        "word_count": word_count,
        "chapter_count": chapter_count,
        "avg_words_per_chapter": avg_words,
        "options": options,
        "detected_titles": [c.get("title") for c in chapters[:80]],
        "words_per_page_assumption": WORDS_PER_PAGE,
        "fixed_page_word_ratio": FIXED_PAGE_WORD_RATIO,
    }


def _source_extension(source_format):
    return ".epub" if str(source_format).lower() == "epub" else ".pdf"


def _strip_xml_ns(tag):
    return str(tag or "").split("}", 1)[-1].lower()


class _EPUBTextExtractor(HTMLParser):
    """Small dependency-free XHTML/HTML to text extractor for EPUB spine docs."""
    BLOCK_TAGS = {"p", "div", "section", "article", "aside", "blockquote", "br", "hr", "table", "tr"}
    HEADING_TAGS = {"h1": "#", "h2": "##", "h3": "###", "h4": "###", "h5": "###", "h6": "###"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
        self.skip_depth = 0
        self.in_li = False
        self.heading_tag = None
        self.heading_text = []
        self.first_heading = ""
        self.title_text = []
        self.in_title = False

    def _newline(self):
        if self.parts and not self.parts[-1].endswith("\n"):
            self.parts.append("\n")

    def handle_starttag(self, tag, attrs):
        tag = tag.lower()
        if tag in ("script", "style", "svg", "math"):
            self.skip_depth += 1
            return
        if self.skip_depth:
            return
        if tag == "title":
            self.in_title = True
            return
        if tag in self.HEADING_TAGS:
            self._newline()
            self.heading_tag = tag
            self.heading_text = []
            return
        if tag == "li":
            self._newline()
            self.parts.append("- ")
            self.in_li = True
            return
        if tag in self.BLOCK_TAGS:
            self._newline()

    def handle_endtag(self, tag):
        tag = tag.lower()
        if tag in ("script", "style", "svg", "math"):
            self.skip_depth = max(0, self.skip_depth - 1)
            return
        if self.skip_depth:
            return
        if tag == "title":
            self.in_title = False
            return
        if tag == self.heading_tag:
            text = re.sub(r"\s+", " ", "".join(self.heading_text)).strip()
            if text:
                if not self.first_heading:
                    self.first_heading = text
                self.parts.append(f"{self.HEADING_TAGS.get(tag, '##')} {text}\n")
            self.heading_tag = None
            self.heading_text = []
            return
        if tag == "li":
            self.parts.append("\n")
            self.in_li = False
            return
        if tag in self.BLOCK_TAGS:
            self._newline()

    def handle_data(self, data):
        if self.skip_depth:
            return
        txt = re.sub(r"\s+", " ", data or " ")
        if not txt.strip():
            return
        if self.in_title:
            self.title_text.append(txt)
        if self.heading_tag:
            self.heading_text.append(txt)
        else:
            self.parts.append(txt)

    def get_text(self):
        text = "".join(self.parts)
        text = re.sub(r"[ \t]+", " ", text)
        text = re.sub(r"\n{3,}", "\n\n", text)
        return text.strip()

    def get_title(self):
        if self.first_heading:
            return self.first_heading
        return re.sub(r"\s+", " ", "".join(self.title_text)).strip()


def _epub_read_text(html_bytes):
    parser = _EPUBTextExtractor()
    try:
        parser.feed(html_bytes.decode("utf-8", "replace"))
    except Exception:
        try:
            parser.feed(html_bytes.decode("latin-1", "replace"))
        except Exception:
            pass
    return parser.get_text(), parser.get_title()


def _epub_container_opf_path(zf):
    try:
        root = ET.fromstring(zf.read("META-INF/container.xml"))
        for el in root.iter():
            if _strip_xml_ns(el.tag) == "rootfile":
                path = el.attrib.get("full-path")
                if path:
                    return path
    except Exception:
        pass
    for name in zf.namelist():
        if name.lower().endswith(".opf"):
            return name
    return None


def _epub_join(base_dir, href):
    href = urllib.parse.unquote(str(href or "").split("#", 1)[0])
    return posixpath.normpath(posixpath.join(base_dir, href)).lstrip("/")


def _epub_parse_nav_titles(zf, opf_base, manifest_items):
    """Return path -> nav title from EPUB3 nav or NCX when available."""
    out = {}
    nav_paths = []
    for item in manifest_items.values():
        props = str(item.get("properties", "")).lower()
        mt = str(item.get("media_type", "")).lower()
        href = item.get("href", "")
        if "nav" in props or mt == "application/x-dtbncx+xml" or "toc" in str(item.get("id", "")).lower():
            nav_paths.append(_epub_join(opf_base, href))
    for path in nav_paths:
        if path not in zf.namelist():
            continue
        try:
            raw = zf.read(path)
        except Exception:
            continue
        # NCX is XML and easy to parse.
        if path.lower().endswith(".ncx"):
            try:
                root = ET.fromstring(raw)
                for navpoint in root.iter():
                    if _strip_xml_ns(navpoint.tag) != "navpoint":
                        continue
                    label = ""
                    src = ""
                    for el in navpoint.iter():
                        lname = _strip_xml_ns(el.tag)
                        if lname == "text" and el.text and not label:
                            label = re.sub(r"\s+", " ", el.text).strip()
                        elif lname == "content" and not src:
                            src = el.attrib.get("src", "")
                    if label and src:
                        out[_epub_join(posixpath.dirname(path), src)] = label[:160]
            except Exception:
                pass
            continue
        # EPUB3 nav is XHTML. Use a conservative anchor scrape.
        try:
            html_text = raw.decode("utf-8", "replace")
            for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', html_text, re.I | re.S):
                href, label = m.group(1), m.group(2)
                label = re.sub(r"<[^>]+>", " ", label)
                label = html.unescape(re.sub(r"\s+", " ", label)).strip()
                if label:
                    out[_epub_join(posixpath.dirname(path), href)] = label[:160]
        except Exception:
            pass
    return out


def _get_epub_data(epub_bytes, job_id=None):
    """Extract text, metadata, and a spine-based chapter list from an EPUB."""
    key = hashlib.sha256(epub_bytes).hexdigest() + "|epub"
    with _pdf_cache_lock:
        if key in _pdf_cache:
            return _pdf_cache[key]

    try:
        zf = zipfile.ZipFile(BytesIO(epub_bytes))
    except Exception as e:
        raise ValueError(f"Invalid EPUB file: {e}")

    with zf:
        opf_path = _epub_container_opf_path(zf)
        if not opf_path:
            raise ValueError("Invalid EPUB: could not locate package OPF file")
        opf_base = posixpath.dirname(opf_path)
        try:
            root = ET.fromstring(zf.read(opf_path))
        except Exception as e:
            raise ValueError(f"Invalid EPUB OPF metadata: {e}")

        title = ""
        author = ""
        for el in root.iter():
            lname = _strip_xml_ns(el.tag)
            if lname == "title" and el.text and not title:
                title = re.sub(r"\s+", " ", el.text).strip()
            elif lname in ("creator", "author") and el.text and not author:
                author = re.sub(r"\s+", " ", el.text).strip()

        manifest = {}
        for el in root.iter():
            if _strip_xml_ns(el.tag) == "item":
                item_id = el.attrib.get("id", "")
                href = el.attrib.get("href", "")
                if not item_id or not href:
                    continue
                manifest[item_id] = {
                    "id": item_id,
                    "href": href,
                    "path": _epub_join(opf_base, href),
                    "media_type": el.attrib.get("media-type", ""),
                    "properties": el.attrib.get("properties", ""),
                }

        idrefs = []
        for el in root.iter():
            if _strip_xml_ns(el.tag) == "itemref":
                ref = el.attrib.get("idref")
                if ref:
                    idrefs.append(ref)
        if not idrefs:
            idrefs = [item_id for item_id, item in manifest.items() if str(item.get("media_type", "")).lower() in ("application/xhtml+xml", "text/html")]

        nav_titles = _epub_parse_nav_titles(zf, opf_base, manifest)
        spine_docs = []
        skipped_names = {"nav", "toc", "contents", "cover", "titlepage", "copyright"}
        for ref in idrefs:
            item = manifest.get(ref)
            if not item:
                continue
            mt = str(item.get("media_type", "")).lower()
            if mt not in ("application/xhtml+xml", "text/html", "application/xml") and not item.get("path", "").lower().endswith((".xhtml", ".html", ".htm")):
                continue
            path = item["path"]
            if path not in zf.namelist():
                continue
            low_id = _norm_title_key(item.get("id", ""))
            low_path = _norm_title_key(posixpath.basename(path).split(".", 1)[0])
            if low_id in skipped_names or low_path in skipped_names:
                # Skip non-content book scaffolding unless it contains substantial text.
                pass
            try:
                text, doc_title = _epub_read_text(zf.read(path))
            except Exception:
                continue
            if _count_words(text) < 20:
                continue
            nav_title = nav_titles.get(path) or nav_titles.get(path.split("#", 1)[0])
            chapter_title = nav_title or doc_title or f"Section {len(spine_docs) + 1}"
            chapter_title = re.sub(r"\s+", " ", chapter_title).strip(" .:-")[:140] or f"Section {len(spine_docs) + 1}"
            # Ensure each spine document starts with a stable H1-like marker for deterministic detection.
            if not re.match(r"^#\s+", text):
                text = f"# {chapter_title}\n\n{text}"
            spine_docs.append({"title": chapter_title, "text": text, "path": path})
            if job_id in jobs and len(spine_docs) % 10 == 0:
                _job_update(job_id, message=f"Extracting EPUB chapters... {len(spine_docs)} sections", stage="extract")

    if not spine_docs:
        raise ValueError("Could not extract readable text from EPUB. The file may be DRM-protected or image-only.")

    page_texts = [doc["text"] for doc in spine_docs]
    full_text = "\n".join(page_texts) + "\n"
    word_count = _count_words(full_text)
    estimated_pages = max(1, int(math.ceil(word_count / max(1, WORDS_PER_PAGE))))
    chapter_list = _canonicalize_chapter_list(
        [{"title": doc["title"], "page": idx} for idx, doc in enumerate(spine_docs)],
        total_pages=len(page_texts),
    )
    if not chapter_list:
        chapter_list = [{"title": doc["title"], "page": idx} for idx, doc in enumerate(spine_docs)]

    result = {
        "pages": estimated_pages,
        "virtual_pages": len(page_texts),
        "full_text": full_text,
        "page_texts": page_texts,
        "chapter_list": chapter_list,
        "ocr_used": False,
        "ocr_status": "not_applicable",
        "extraction_method": "epub",
        "source_format": "epub",
        "metadata_title": title,
        "metadata_author": author,
    }
    with _pdf_cache_lock:
        if len(_pdf_cache) >= MAX_PDF_CACHE:
            _pdf_cache.pop(next(iter(_pdf_cache)))
        _pdf_cache[key] = result
    return result


def _get_document_data(source_bytes, source_format="pdf", allow_ocr=None, ocr_max_pages=None, job_id=None):
    source_format = str(source_format or "pdf").lower()
    if source_format == "epub":
        return _get_epub_data(source_bytes, job_id=job_id)
    return _get_pdf_data(source_bytes, allow_ocr=allow_ocr, ocr_max_pages=ocr_max_pages, job_id=job_id)

# ── Section Parser ─────────────────────────────────────────────────────────────
def parse_sections(text):
    sections      = []
    current       = None
    pending_score  = None
    pending_reason = ""
    for line in text.splitlines():
        sm = re.match(r"<!--RSCORE:(\d+)\|(.*)-->", line.strip())
        if sm:
            pending_score  = int(sm.group(1))
            pending_reason = sm.group(2).strip()
            continue
        m = re.match(r"^(#{1,3})\s+(.*)", line)
        if m:
            if current:
                sections.append(current)
            level   = len(m.group(1))
            current = {"level": level, "heading": m.group(2).strip(), "body": "",
                       "research_score": pending_score, "research_reason": pending_reason}
            pending_score  = None
            pending_reason = ""
        else:
            if current is None:
                current = {"level": 1, "heading": "", "body": "",
                           "research_score": pending_score, "research_reason": pending_reason}
                pending_score  = None
                pending_reason = ""   # fix: also reset here to avoid leaking
            current["body"] += line + "\n"
    if current:
        sections.append(current)
    return sections

# ── Google Books ───────────────────────────────────────────────────────────────
def fetch_book_cover(title, author=""):
    author_info = {"author": "", "bio": ""}
    cover_url   = None
    try:
        q = urllib.parse.quote(title)
        if author:
            q += "+" + urllib.parse.quote(f"inauthor:{author}")
        url = f"https://www.googleapis.com/books/v1/volumes?q={q}&maxResults=3"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req, timeout=10) as r:
            data = json.loads(r.read())
        items = data.get("items", [])
        for item in items:
            info      = item.get("volumeInfo", {})
            img_links = info.get("imageLinks", {})
            raw_url   = (img_links.get("large") or img_links.get("medium")
                         or img_links.get("thumbnail") or img_links.get("smallThumbnail"))
            if raw_url:
                raw_url = raw_url.replace("http://", "https://")
                if "zoom=" in raw_url:
                    raw_url = re.sub(r"zoom=\d", "zoom=0", raw_url)
                cover_url = raw_url
                author_info["author"] = (info.get("authors") or [""])[0]
                author_info["bio"]    = info.get("description", "")[:400]
                break
    except Exception:
        pass

    if not cover_url:
        try:
            q          = urllib.parse.quote(title)
            search_url = f"https://openlibrary.org/search.json?title={q}&limit=1&fields=cover_i,author_name"
            req        = urllib.request.Request(search_url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=10) as r:
                data = json.loads(r.read())
            docs = data.get("docs", [])
            if docs and docs[0].get("cover_i"):
                cover_id  = docs[0]["cover_i"]
                cover_url = f"https://covers.openlibrary.org/b/id/{cover_id}-L.jpg"
                if not author_info["author"] and docs[0].get("author_name"):
                    author_info["author"] = docs[0]["author_name"][0]
        except Exception:
            pass

    return cover_url, author_info

def download_cover(url, path):
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req, timeout=15) as r:
            data = r.read()
        if len(data) < 1000:
            return None
        with open(path, "wb") as f:
            f.write(data)
        return path
    except Exception:
        return None

# ── Cloud drive discovery ──────────────────────────────────────────────────────
def find_onedrive_root():
    if ONEDRIVE_ROOT_OVERRIDE and os.path.isdir(ONEDRIVE_ROOT_OVERRIDE):
        return ONEDRIVE_ROOT_OVERRIDE
    candidates = [
        os.environ.get("OneDriveConsumer"),
        os.environ.get("OneDrive"),
        os.environ.get("OneDriveCommercial"),
        os.path.expandvars(r"%USERPROFILE%\OneDrive"),
        os.path.expandvars(r"%USERPROFILE%\OneDrive - Personal"),
        os.path.expanduser("~/OneDrive"),
        os.path.expanduser("~/OneDrive - Personal"),
        os.path.expanduser("~/Library/CloudStorage/OneDrive-Personal"),
    ]
    for c in candidates:
        if c and os.path.isdir(c):
            return c
    return None

def find_gdrive_root():
    if GDRIVE_ROOT_OVERRIDE and os.path.isdir(GDRIVE_ROOT_OVERRIDE):
        return GDRIVE_ROOT_OVERRIDE
    candidates = [
        r"G:\My Drive",
        r"G:\My drive",
        r"H:\My Drive",
        os.path.expandvars(r"%USERPROFILE%\Google Drive\My Drive"),
        os.path.expandvars(r"%USERPROFILE%\Google Drive"),
        os.path.expandvars(r"%USERPROFILE%\My Drive"),
        os.path.expanduser("~/Library/CloudStorage/GoogleDrive-Personal/My Drive"),
        os.path.expanduser("~/Google Drive/My Drive"),
        os.path.expanduser("~/Google Drive"),
    ]
    cs = os.path.expanduser("~/Library/CloudStorage")
    if os.path.isdir(cs):
        try:
            for entry in os.listdir(cs):
                if entry.startswith("GoogleDrive-"):
                    candidates.append(os.path.join(cs, entry, "My Drive"))
        except Exception:
            pass
    for c in candidates:
        if c and os.path.isdir(c):
            return c
    return None

# ── Smart PDF Splitter ─────────────────────────────────────────────────────────
def detect_chapter_starts(page_texts: list) -> list:
    """Return list of {page, title} for detected chapter-start pages."""
    patterns = [
        re.compile(r"^(Chapter\s+\d[\w\.\:\s]{0,60})", re.IGNORECASE),
        re.compile(r"^(CHAPTER\s+[IVXLCDM\d][\w\.\:\s]{0,60})"),
        re.compile(r"^(Part\s+\d[\w\.\:\s]{0,60})", re.IGNORECASE),
        re.compile(r"^(PART\s+[IVXLCDM\d][\w\.\:\s]{0,60})"),
        re.compile(r"^(Cap[ií]tulo\s+[IVXLCDM\d][\w\.\:\s]{0,70})", re.IGNORECASE),
        re.compile(r"^(Parte\s+[IVXLCDM\d][\w\.\:\s]{0,70})", re.IGNORECASE),
        re.compile(r"^(Unidad\s+\d[\w\.\:\s]{0,70})", re.IGNORECASE),
        re.compile(r"^(Tema\s+\d[\w\.\:\s]{0,70})", re.IGNORECASE),
        re.compile(r"^(Examen\s+\d[\w\.\:\s]{0,90})", re.IGNORECASE),
        re.compile(r"^(Preface\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Foreword\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Introduction\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Introducci[oó]n\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Instrucciones\s+generales\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Prologue\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Pr[oó]logo\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Epilogue\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Ep[ií]logo\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Conclusion\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Conclusi[oó]n\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^(Afterword\b[\s\:\—\-]{0,20}\w{0,40})", re.IGNORECASE),
        re.compile(r"^((?:I|II|III|IV|V|VI|VII|VIII|IX|X|XI|XII|XIII|XIV|XV|XVI|XVII|XVIII|XIX|XX)\.\s+[A-Z][A-Za-z\s]{2,70})"),
    ]
    chapter_starts = []
    for page_idx, text in enumerate(page_texts):
        if not text:
            continue
        all_first = [ln.strip() for ln in text.strip().splitlines()[:10] if ln.strip()]
        if page_idx < 40 and any(re.match(r"^(contents|table of contents|[ií]ndice)$", ln, re.I) for ln in all_first[:3]):
            continue
        first_lines = all_first[:6]
        for line_pos, line in enumerate(first_lines):
            stripped = line.strip()
            if not stripped:
                continue
            for pat in patterns:
                m = pat.match(stripped)
                if m:
                    # Running headers often appear as "Introduction" or
                    # "Conclusion" followed by a bare page number. Do not
                    # treat those as new chapter starts.
                    if re.match(r"^(Introduction|Conclusion|Introducci[oó]n|Conclusi[oó]n)$", stripped, re.I):
                        if line_pos + 1 < len(first_lines) and re.match(r"^\d{1,4}$", first_lines[line_pos + 1]):
                            continue
                    chapter_starts.append({"page": page_idx, "title": m.group(1).strip()})
                    break
            else:
                continue
            break
    return chapter_starts

def choose_breakpoints(chapter_starts: list, total_pages: int):
    """Return (b1, b2) page indices or None to signal equal-split fallback."""
    if len(chapter_starts) < 4:
        return None

    t1 = total_pages / 3
    t2 = 2 * total_pages / 3
    candidates = chapter_starts[1:]   # exclude first chapter — always in part 1

    b1 = min(candidates, key=lambda c: abs(c["page"] - t1))["page"]

    candidates_b2 = [c for c in candidates if c["page"] > b1]
    if not candidates_b2:
        return None

    b2 = min(candidates_b2, key=lambda c: abs(c["page"] - t2))["page"]
    return (b1, b2)

def smart_split_pdf(pdf_bytes: bytes, safe_title: str, page_texts: list = None) -> list:
    """Return [(filename, bytes), ...] for 3 parts.  Falls back to equal-page split."""
    reader      = PdfReader(BytesIO(pdf_bytes))
    total_pages = len(reader.pages)
    if total_pages == 0:
        return []

    if page_texts is None:
        page_texts = []
        try:
            with pdfplumber.open(BytesIO(pdf_bytes)) as pdf:
                for page in pdf.pages:
                    page_texts.append(page.extract_text() or "")
        except Exception:
            page_texts = [""] * total_pages

    chapter_starts = detect_chapter_starts(page_texts)
    breakpoints    = choose_breakpoints(chapter_starts, total_pages)

    log_path = os.path.join(TMP_DIR, "smart_split.log")
    try:
        if breakpoints is None:
            base  = total_pages // 3
            rem   = total_pages % 3
            sizes = [base + (1 if i < rem else 0) for i in range(3)]
            start = 0
            ranges = []
            for size in sizes:
                ranges.append((start, start + size))
                start += size
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f'[{safe_title}] Equal-page fallback '
                        f'(chapters detected: {len(chapter_starts)}, total pages: {total_pages})\n')
        else:
            b1, b2 = breakpoints
            ranges = [(0, b1), (b1, b2), (b2, total_pages)]
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f'[{safe_title}] Smart split at pages {b1}, {b2} of {total_pages} '
                        f'(chapters detected: {len(chapter_starts)})\n')
    except Exception:
        base   = total_pages // 3
        rem    = total_pages % 3
        sizes  = [base + (1 if i < rem else 0) for i in range(3)]
        start  = 0
        ranges = []
        for size in sizes:
            ranges.append((start, start + size))
            start += size

    results = []
    for i, (start, end) in enumerate(ranges, 1):
        if end <= start:
            continue
        writer = PdfWriter()
        for pi in range(start, end):
            writer.add_page(reader.pages[pi])
        buf = BytesIO()
        writer.write(buf)
        filename = f"{safe_title} — PART {i} of 3.pdf"
        results.append((filename, buf.getvalue()))
    return results

# ── Bundle export ──────────────────────────────────────────────────────────────
def save_bundle_to_root(root, source_bytes, summary_pdf_path, title, splits=None, phone_path=None, source_format="pdf"):
    log_path = os.path.join(TMP_DIR, "cloud_save.log")

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}\n")
        except Exception:
            pass

    if not root:
        _log(f"SKIP: no root provided for '{title}'")
        return None

    st = _safe_title(title)
    if not st:
        _log(f"SKIP: safe_title empty for {title!r}")
        return None

    folder = os.path.join(root, CLOUD_PARENT_FOLDER, st)
    try:
        os.makedirs(folder, exist_ok=True)
    except Exception as e:
        _log(f"FAIL makedirs({folder}): {e!r}")
        return None

    try:
        ext = _source_extension(source_format)
        with open(os.path.join(folder, f"{st} — ORIGINAL{ext}"), "wb") as f:
            f.write(source_bytes)
    except Exception as e:
        _log(f"FAIL write ORIGINAL in {folder}: {e!r}")
        return None

    try:
        shutil.copy2(summary_pdf_path, os.path.join(folder, f"{st} — SUMMARY.pdf"))
    except Exception as e:
        _log(f"FAIL copy SUMMARY to {folder}: {e!r}")
        return None

    if splits is None:
        if str(source_format).lower() == "pdf":
            try:
                splits = smart_split_pdf(source_bytes, st)
            except Exception as e:
                _log(f"FAIL smart_split_pdf: {e!r}")
                splits = []
        else:
            splits = []

    for filename, part_bytes in splits:
        try:
            with open(os.path.join(folder, filename), "wb") as f:
                f.write(part_bytes)
        except Exception as e:
            _log(f"FAIL write part {filename}: {e!r}")
            # continue — ORIGINAL + SUMMARY are already saved

    if phone_path and os.path.exists(phone_path):
        try:
            shutil.copy2(phone_path, os.path.join(folder, f"{st} — PHONE.pdf"))
        except Exception as e:
            _log(f"FAIL copy PHONE to {folder}: {e!r}")

    _log(f"OK saved bundle to {folder} ({len(splits)} parts)")
    return folder

# ── Watchdog ───────────────────────────────────────────────────────────────────
def _watchdog():
    while True:
        time.sleep(60)
        now = time.time()
        for jid, job in list(jobs.items()):
            status = job.get("status")
            if status == "running":
                # v20: keep local jobs alive generously; only stop when the
                # explicit total budget is exceeded. Stage-level checks happen
                # inside the pipeline, and the UI now has a Cancel button.
                if TOTAL_JOB_MAX_SECONDS and now - job.get("created_at", now) > TOTAL_JOB_MAX_SECONDS:
                    fail(jid, f"Job timed out after {TOTAL_JOB_MAX_SECONDS // 60} minutes.")
            elif status in ("done", "error"):
                if now - job.get("created_at", now) > 3600:   # 60 min
                    out = job.get("output_path")
                    if out and os.path.exists(out):
                        try:
                            os.remove(out)
                        except Exception:
                            pass
                    op = job.get("original_path")
                    if op and os.path.exists(op):
                        try:
                            os.remove(op)
                        except Exception:
                            pass
                    for _filename, pp in job.get("part_paths", []):
                        if pp and os.path.exists(pp):
                            try:
                                os.remove(pp)
                            except Exception:
                                pass
                    jobs.pop(jid, None)
        for token, share in list(shares.items()):
            if now - share.get("created_at", now) > 7 * 86400:  # 7 days
                shares.pop(token, None)

threading.Thread(target=_watchdog, daemon=True).start()

# ── G3: Claude call wrapper with retries + continuation ───────────────────────
def _call_claude_full(ai_client, prompt, max_tokens, job_id,
                      continuation_hint=None, max_continuations=2):
    """Call Claude with retries and continuation on max_tokens stop."""
    log_path = os.path.join(TMP_DIR, "api_errors.log")

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] {msg}\n")
        except Exception:
            pass

    messages = [{"role": "user", "content": prompt}]
    full_text = ""
    continuations = 0

    while True:
        for attempt in range(5):
            try:
                _check_job_control(job_id, jobs.get(job_id, {}).get("stage"))
                if job_id in jobs:
                    jobs[job_id]["last_update"] = time.time()
                resp = ai_client.messages.create(
                    model=MODEL_CHUNK,
                    max_tokens=max_tokens,
                    messages=messages,
                )
                break
            except Exception as e:
                kind = _api_error_kind(e)
                status_code = getattr(e, "status_code", None)
                if kind == "rate_limit":
                    _log(f"RateLimitError attempt {attempt}: {e}")
                    if attempt == 4:
                        raise
                    time.sleep(20 * (attempt + 1))
                    continue
                if kind == "connection":
                    _log(f"Connection/Timeout attempt {attempt}: {e}")
                    if attempt == 4:
                        raise
                    time.sleep(10 * (attempt + 1))
                    continue
                if kind == "status" and status_code in (500, 502, 503, 529) and attempt < 4:
                    _log(f"APIStatusError {status_code} attempt {attempt}: {e}")
                    time.sleep(15 * (attempt + 1))
                    continue
                raise

        _check_job_control(job_id, jobs.get(job_id, {}).get("stage"))
        chunk_text = _anthropic_text(resp)
        full_text += chunk_text

        if resp.stop_reason != "max_tokens" or continuations >= max_continuations:
            break

        hint = continuation_hint or "Continue exactly where you left off without repeating anything."
        messages = messages + [
            {"role": "assistant", "content": chunk_text},
            {"role": "user",      "content": hint},
        ]
        continuations += 1

    return full_text


# ── G4b Layer 1: PDF outline extraction ────────────────────────────────────────
def _extract_pdf_outline(pdf_bytes):
    """Extract chapter titles from PDF bookmarks/outline."""
    try:
        reader  = PdfReader(BytesIO(pdf_bytes))
        outline = reader.outline
        if not outline:
            return []

        results = []

        def _walk(items):
            for item in items:
                if isinstance(item, list):
                    _walk(item)
                elif hasattr(item, "title") and hasattr(item, "page"):
                    try:
                        page_num = reader.get_destination_page_number(item)
                        t = item.title.strip()
                        if len(t) >= 3:
                            results.append({"title": t, "page": page_num})
                    except Exception:
                        pass

        _walk(outline)
        results.sort(key=lambda x: x["page"])
        seen = set()
        deduped = []
        for r in results:
            if r["page"] not in seen:
                seen.add(r["page"])
                deduped.append(r)
        return deduped
    except Exception:
        return []


# ── G4b Layer 3: AI chapter detection from TOC pages ──────────────────────────
def _detect_chapters_from_toc_pages(ai_client, page_texts, job_id):
    """Ask Claude to identify chapter starts from the first 20 pages."""
    sample = "\n---PAGE BREAK---\n".join(page_texts[:20])
    prompt = (
        "Below are the first pages of a book (separated by ---PAGE BREAK--- markers, 0-indexed).\n"
        "Find all chapter/section titles and their 0-indexed page numbers.\n"
        "Return ONLY a JSON array:\n"
        '[{"title": "Chapter 1: The Beginning", "page": 5}, ...]\n'
        "Include: Chapter N, Part N, Unit/Unidad N, Examen N, Tema N, Leccion N, Module/Modulo N, Preface, Introduction, Foreword, Prologue, Epilogue, Conclusion.\n"
        "If no chapters found, return [].\n\n"
        f"Pages:\n{sample[:8000]}"
    )
    try:
        result   = _call_claude_full(ai_client, prompt, 2000, job_id)
        m        = re.search(r"\[.*?\]", result, re.DOTALL)
        if not m:
            return []
        chapters = json.loads(m.group(0))
        out = []
        for c in chapters:
            if isinstance(c, dict) and "title" in c and "page" in c:
                try:
                    out.append({"title": str(c["title"]).strip(), "page": int(c["page"])})
                except (ValueError, TypeError):
                    pass
        return out
    except Exception:
        return []


# ── G4b Layer 2.5: deterministic TOC parsing ─────────────────────────────────
def _detect_chapters_from_toc_text(page_texts, total_pages):
    """Parse obvious TOC lines before spending an AI call.

    Handles lines like "Examen 1 Las personas y la vivienda 6" and
    "Chapter 3 The Argument 42". Page numbers in TOCs are usually 1-indexed,
    so we try page-1 first while keeping the result within bounds.
    """
    # Prefer actual Contents pages when present. This keeps the parser from
    # reading prose in the introduction as if it were a TOC.
    toc_page_idx = None
    for _idx, _txt in enumerate(page_texts[:35]):
        if re.search(r"(?im)^\s*(contents|table of contents|[ií]ndice)\s*$", str(_txt or "")):
            toc_page_idx = _idx
            break
    if toc_page_idx is not None:
        toc_end = min(len(page_texts), toc_page_idx + 28)
        for _j in range(toc_page_idx + 1, min(len(page_texts), toc_page_idx + 28)):
            if _count_words(page_texts[_j]) > 80:
                toc_end = _j
                break
        sample = "\n".join(page_texts[toc_page_idx:toc_end])
    else:
        sample = "\n".join(page_texts[:20])
    out = []
    seen = set()
    patterns = [
        re.compile(r"\b((?:Chapter|Part)\s+[IVXLCDM\d]+\s+.{2,90}?)\s+([ivxlcdmIVXLCDM\d]{1,8})\s*$", re.IGNORECASE),
        re.compile(r"\b((?:Cap[ií]tulo|Parte|Unidad|Tema|Examen)\s+[IVXLCDM\d]+\s+.{2,90}?)\s+([ivxlcdmIVXLCDM\d]{1,8})\s*$", re.IGNORECASE),
        re.compile(r"\b((?:Acknowledgments?|Introduction|Preface|Foreword|Prologue|Epilogue|Conclusion|References|Bibliography)\b.{0,90}?)\s+([ivxlcdmIVXLCDM\d]{1,8})\s*$", re.IGNORECASE),
        re.compile(r"\b((?:Instrucciones generales|Pautas para los ex[aá]menes|[IÍ]ndice)\b.{0,90}?)\s+([ivxlcdmIVXLCDM\d]{1,8})\s*$", re.IGNORECASE),
    ]
    def _roman_to_int(raw):
        raw = str(raw or "").strip().lower()
        if raw.isdigit():
            return int(raw)
        vals = {"i": 1, "v": 5, "x": 10, "l": 50, "c": 100, "d": 500, "m": 1000}
        if not raw or any(ch not in vals for ch in raw):
            return None
        total = 0
        prev = 0
        for ch in raw[::-1]:
            val = vals[ch]
            total += -val if val < prev else val
            prev = max(prev, val)
        return total or None

    cleaned_lines = []
    for raw in sample.splitlines():
        line = str(raw or "").replace("\x08", " ").replace("\x07", " ")
        line = re.sub(r"\.{2,}", " ", line)
        line = re.sub(r"\s+", " ", line).strip(" .:-–—\t")
        if line and len(line) <= 160:
            cleaned_lines.append(line)

    # Join common wrapped TOC entries. Handles both:
    #   "1 How Emotionally..." + "Adult Children's Lives 7"
    # and PyMuPDF output like "1" + "How Emotionally..." + "7".
    # Also join part title spreads such as "PART I" + "THE INVENTION OF JHO LOW".
    lines = []
    i = 0
    while i < len(cleaned_lines):
        line = cleaned_lines[i]
        if re.match(r"^PART\s+[IVXLCDM\d]+$", line, re.I) and i + 1 < len(cleaned_lines):
            nxt = cleaned_lines[i + 1]
            if re.match(r'^[A-Z0-9 ,:\'’"()\-]{4,90}$', nxt) and not re.match(r"^(Chapter|PART|Contents|Copyright|Dedication)\b", nxt, re.I):
                lines.append(line + ": " + nxt.title())
                i += 2
                continue
        if re.match(r"^\d{1,2}$", line) and i + 1 < len(cleaned_lines):
            parts = [line]
            j = i + 1
            found = False
            while j < len(cleaned_lines):
                nxt = cleaned_lines[j]
                if j > i + 1 and (re.match(r"^\d{1,2}$", nxt) or re.match(r"^\d{1,2}\s+\D", nxt)):
                    break
                parts.append(nxt)
                joined = " ".join(parts)
                if re.search(r"\s+\d{1,4}$", joined):
                    lines.append(joined)
                    i = j + 1
                    found = True
                    break
                j += 1
            if found:
                continue
            lines.append(line)
            i += 1
            continue
        if re.match(r"^\d{1,2}\s+\D", line) and not re.search(r"\s+\d{1,4}$", line) and i + 1 < len(cleaned_lines):
            parts = [line]
            j = i + 1
            found = False
            while j < len(cleaned_lines):
                nxt = cleaned_lines[j]
                if re.match(r"^\d{1,2}\s+\D", nxt):
                    break
                parts.append(nxt)
                joined = " ".join(parts)
                if re.search(r"\s+\d{1,4}$", joined):
                    lines.append(joined)
                    i = j + 1
                    found = True
                    break
                j += 1
            if found:
                continue
            lines.append(line)
            i += 1
            continue
        lines.append(line)
        i += 1


    for line in lines:
        if not line:
            continue

        numbered = re.match(r"^(\d{1,2})\s+(.{2,110}?)\s+(\d{1,4})$", line)
        if numbered:
            title = f"Chapter {int(numbered.group(1))}: {numbered.group(2).strip(' .:-–—')}"
            toc_page = int(numbered.group(3))
            matched = True
            needs_page_find = False
        else:
            matched = False
            title = ""
            toc_page = None
            needs_page_find = False
            for pat in patterns:
                m = pat.search(line)
                if not m:
                    continue
                title = re.sub(r"\s+", " ", m.group(1)).strip(" .:-–—")
                toc_page = _roman_to_int(m.group(2))
                matched = True
                break
            if not matched:
                m = re.match(r"^Chapter\s+(\d{1,3}|[IVXLCDM]{1,8})\s*[\.)\-:]?\s*(.{2,110})$", line, re.I)
                if m:
                    raw = m.group(1)
                    n = int(raw) if raw.isdigit() else _roman_to_int(raw)
                    rest = m.group(2).strip(" .:-–—")
                    if n is not None and rest and not re.match(r"^\d+(?:\s+\d+)+$", rest):
                        title = f"Chapter {n}: {rest}"
                        matched = True
                        needs_page_find = True
                else:
                    m = re.match(r'^(\d{1,2})\s+([A-Z][A-Za-z0-9 ,:\'’"()\-]{6,120})$', line)
                    if m and int(m.group(1)) <= 60:
                        title = f"Chapter {int(m.group(1))}: {m.group(2).strip(' .:-–—')}"
                        matched = True
                        needs_page_find = True
                    else:
                        m = re.match(r"^(Introduction|Conclusion|Prologue|Epilogue)\s*(.{2,100})$", line, re.I)
                        if m:
                            title = (m.group(1) + " " + m.group(2)).strip(" .:-–—")
                            matched = True
                            needs_page_find = True
                        else:
                            m = re.match(r"^(PART\s+[IVXLCDM\d]+)\s*[:.-]\s*(.{2,100})$", line, re.I)
                            if m:
                                title = f"{m.group(1).upper()}: {m.group(2).strip(' .:-–—')}"
                                matched = True
                                needs_page_find = True
        if not matched:
            continue
        if toc_page is not None:
            # Most TOCs are 1-indexed. Skip entries clearly outside a partial/test PDF.
            if toc_page > total_pages + 2:
                continue
            page = max(0, min(total_pages - 1, toc_page - 1))
        else:
            page = 0
        norm = re.sub(r"[^\w]", "", title.lower())
        if norm and norm not in seen and not _is_source_boilerplate_heading(title):
            seen.add(norm)
            entry = {"title": title[:140], "page": page}
            if toc_page is not None:
                entry["toc_page"] = toc_page
            if needs_page_find:
                entry["needs_page_find"] = True
            out.append(entry)

    def _norm_for_search(x):
        x = re.sub(r"^chapter\s+\d+\s*[:.-]?\s*", "", str(x or ""), flags=re.I)
        return re.sub(r"[^a-z0-9]+", " ", x.lower()).strip()

    toc_scan_start = 0
    for _idx, _txt in enumerate(page_texts[:20]):
        if re.search(r"\b(contents|table of contents|[ií]ndice)\b", str(_txt or ""), re.I):
            toc_scan_start = _idx + 1
            break

    def _find_actual_title_page(title):
        q = _norm_for_search(title)
        if len(q) < 8:
            return None
        q_tokens = [t for t in q.split() if len(t) > 2][:8]
        for idx, txt in enumerate(page_texts[toc_scan_start:], start=toc_scan_start):
            raw_txt = str(txt or "")
            # Avoid matching the TOC entry itself. TOC-only pages are very
            # short, whereas actual chapters/introductions contain body prose.
            if _count_words(raw_txt) < 60 and _chapter_number_from_title(title) is not None:
                continue
            if _count_words(raw_txt) < 60 and re.match(r"^(Introduction|Conclusion)\b", str(title or ""), re.I):
                continue
            pnorm = _norm_for_search(raw_txt[:1600])
            if q in pnorm:
                return idx
            if len(q_tokens) >= 4 and sum(1 for t in q_tokens if t in pnorm) >= min(5, len(q_tokens)):
                return idx
        return None

    for e in out:
        if e.get("needs_page_find"):
            actual = _find_actual_title_page(e.get("title", ""))
            if actual is not None:
                e["page"] = actual

    offsets = []
    for e in out:
        # Use numbered content entries to infer the printed-page to PDF-page offset.
        if _chapter_number_from_title(e.get("title", "")) is not None:
            actual = _find_actual_title_page(e.get("title", ""))
            if actual is not None:
                offsets.append(actual - (int(e.get("toc_page") or 1) - 1))
    if offsets:
        offsets.sort()
        offset = offsets[len(offsets) // 2]
        if abs(offset) >= 2:
            for e in out:
                if _chapter_number_from_title(e.get("title", "")) is not None or e.get("title", "").lower() in ("introduction", "epilogue", "conclusion"):
                    e["page"] = max(0, min(total_pages - 1, int(e.get("toc_page") or 1) - 1 + offset))

    out.sort(key=lambda x: (x["page"], x["title"].lower()))
    for e in out:
        e.pop("toc_page", None)
        e.pop("needs_page_find", None)
    return out


# ── OCR/slide/report helper: infer page-title sections when no chapters exist ─
def _detect_page_title_sections(page_texts, max_pages=90):
    """Infer page/section headings for report decks and short research notes.

    Green Street-style PDFs, slide decks, and image-to-text briefs often have no
    bookmarks and no ``Chapter N`` strings, but each content page carries a
    human-readable heading. This fallback suppresses boilerplate, legal
    disclosures, repeating headers/footers, dates, market tickers, address
    lines, analyst/contact pages, and chart labels, then chooses the most
    plausible business-section heading.
    """
    if not page_texts or len(page_texts) > max_pages:
        return []

    doc_family_titles = {
        "residential sector", "re sidential sector", "residential sector update",
        "residential insights", "debt insights", "u k student housing",
        "u k student housing", "quick take informational", "quick take earnings",
    }

    skip_fragments = [
        "brianis book club", "notebooklm", "powered by", "not for redistribution",
        "preparación diploma", "preparacion diploma", "under oath", "timeline:",
        "location & time", "the committee's allegation", "the committee’s allegation",
        "the sworn testimony", "the conclusion the mechanism", "my.greenstreet.com",
        "use of this report", "intended for use by", "may not be copied",
        "important disclosure", "green street advisors", "green street (uk) limited",
        "3rd and 4th floor", "3rd & 4th floors", "25 maddox street",
        "newport beach", "source:", "sources:", "company disclosures",
        "local statistics", "bloomberg", "frn 482269", "professional clients",
        "eligible counterparties", "researchdisclosure", "terms of use",
    ]

    def _clean_line(line):
        line = str(line or "").replace("\u00a0", " ").replace("\x00", " ")
        line = re.sub(r"\s+", " ", line).strip(" -—–•·|:;\t")
        line = re.sub(r"^[^A-Za-zÁÉÍÓÚÜÑáéíóúüñ0-9£€$]+", "", line).strip()
        return line

    def _norm(s):
        return re.sub(r"[^a-z0-9]+", " ", str(s or "").lower()).strip()

    def _is_date_line(line):
        low = line.lower()
        return bool(re.search(r"\b\d{1,2}\s*(?:jan|feb|mar|apr|may|jun|jul|aug|sep|sept|oct|nov|dec)[a-z]*\s+20\d{2}\b", low))

    def _looks_like_page_header(line):
        low = line.lower()
        if re.search(r"\b20\d{2}\b", low) and re.search(r"\b\d{1,3}$", low):
            if any(t in low for t in ["residential", "debt insights", "student housing", "green street"]):
                return True
        if re.match(r"^(residential|debt insights|u\.k\. student housing|u\. k\. student housing).*[–-]\s*\d{1,2}\s+", low):
            return True
        return False

    def _is_metadata_line(line):
        low = line.lower()
        if not line:
            return True
        if any(f in low for f in skip_fragments):
            return True
        if _is_date_line(line) or _looks_like_page_header(line):
            return True
        if re.fullmatch(r"\d+(?:\.\d+)?", line):
            return True
        if re.search(r"\b(?:gpr|stoxx|10-year|corp bond|gov.t bond|gov’t bond)\b", low):
            return True
        if re.search(r"[\w.-]+@[\w.-]+", line):
            return True
        if line.startswith(("T ", "T:", "+44", "949.")):
            return True
        if low in {"research", "european team", "sales", "advisory services", "marketing", "executive"}:
            return True
        if "senior analyst" in low or low.endswith("associate") or "managing director" in low:
            return True
        if "green street" in low and len(re.findall(r"\w+", low)) <= 5:
            return True
        return False

    def _is_disclosure_page(text):
        raw = str(text or "")
        top_lines = "\n".join(raw.splitlines()[:8]).lower()
        hard_legal = [
            "this report does not constitute investment advice",
            "green street's disclosure statement",
            "green street’s disclosure statement",
            "green street's disclosure information",
            "green street’s disclosure information",
        ]
        if any(n in top_lines for n in hard_legal):
            return True
        if len(re.findall(r"[\w.-]+@[\w.-]+", raw)) >= 5:
            return True
        return False

    def _score_title(line, idx, page_idx, lines):
        if _is_metadata_line(line):
            return -999.0
        low = line.lower()
        if low.startswith(("authors:", "author:", "note:", "legend:", "source ", "buy:", "hold:", "sell:")):
            return -999.0
        if line[:1] in ("•", "●", "-", "*"):
            return -999.0
        if line[:1].islower() or line.rstrip().endswith("/"):
            return -999.0
        words = re.findall(r"[A-Za-zÁÉÍÓÚÜÑáéíóúüñ0-9][\wÁÉÍÓÚÜÑáéíóúüñ'’/+-]*", line)
        if len(words) == 1 and line.isupper() and len(line) <= 10:
            return -999.0
        if not (1 <= len(words) <= 14):
            return -999.0
        if len(line) < 4 or len(line) > 135:
            return -999.0
        if line.endswith(".") and len(words) > 4:
            return -999.0
        if re.search(r"\b(?:UTG|GRI|GYC|VNA|LEG|TEG|BALD|KOJAMO)\b", line) and len(words) <= 6:
            return -999.0
        if re.search(r"\d+%", line) and len(words) <= 8:
            return -999.0
        alpha = sum(ch.isalpha() for ch in line)
        if alpha / max(1, len(line)) < 0.38:
            return -999.0

        score = 0.0
        norm = _norm(line)
        if norm in doc_family_titles:
            score -= 3.0
        if line.isupper() and len(words) <= 8:
            score += 2.0
        titleish_words = sum(1 for w in words if w[:1].isupper() or w.isupper())
        if titleish_words / max(1, len(words)) >= 0.5:
            score += 4.0
        if len(words) <= 7:
            score += 1.6
        if ":" in line:
            score += 1.2
        if any(ch in line for ch in "&/+-"):
            score += 0.3
        if page_idx == 0 and idx <= 5:
            score += 0.5
        score -= min(idx, 10) * 0.15
        return score

    def _quick_take_title(lines):
        if not lines or not lines[0].lower().startswith("quick take"):
            return None
        pieces = []
        for line in lines[:6]:
            if _is_date_line(line):
                break
            if line.lower().startswith("quick take"):
                continue
            if _is_metadata_line(line):
                continue
            if line:
                pieces.append(line)
        if pieces:
            return " - ".join(pieces[:2])[:120]
        return None

    sections = []
    seen_titles = set()
    for page_idx, text in enumerate(page_texts):
        if _is_disclosure_page(text):
            continue
        raw_lines = [_clean_line(line) for line in str(text or "").splitlines()[:42]]
        lines = [line for line in raw_lines if line]
        if not lines:
            continue

        qt = _quick_take_title(lines)
        if qt:
            title = qt
        else:
            scored = [(idx, line, _score_title(line, idx, page_idx, lines)) for idx, line in enumerate(lines[:40])]
            scored = [x for x in scored if x[2] >= 2.5]
            if not scored:
                continue
            top_scored = [x for x in scored if x[0] <= 6 and _norm(x[1]) not in doc_family_titles]
            if top_scored:
                top_scored.sort(key=lambda x: x[2], reverse=True)
                title = top_scored[0][1]
            else:
                scored.sort(key=lambda x: x[2], reverse=True)
                title = scored[0][1]
                if _norm(title) in doc_family_titles:
                    for _, alt, _ in scored[1:]:
                        if _norm(alt) not in doc_family_titles:
                            title = alt
                            break

        norm = _norm(title)
        if not norm or norm in seen_titles:
            continue
        seen_titles.add(norm)
        sections.append({"title": title[:120], "page": page_idx})

    if len(page_texts) <= 3 and sections:
        return sections[:1]
    return sections


def _chapter_number_from_title(title):
    raw_title = str(title or "")
    m = re.search(r"\b(?:chapter|cap[ií]tulo|examen|unit|unidad)\s+(\d+|[ivxlcdm]+)\b", raw_title, re.IGNORECASE)
    if not m:
        m = re.match(r"^\s*(\d{1,3}|[ivxlcdm]{1,8})\s*[.)-]+\s+", raw_title, re.IGNORECASE)
    if m:
        raw = m.group(1).lower()
        if raw.isdigit():
            return int(raw)
        vals = {"i": 1, "v": 5, "x": 10, "l": 50, "c": 100, "d": 500, "m": 1000}
        total = 0
        prev = 0
        for ch in raw[::-1]:
            val = vals.get(ch, 0)
            total += -val if val < prev else val
            prev = max(prev, val)
        return total or None

    # v42: Some PDFs expose notes/endnotes as bare outline entries like
    # "Chapter One", "Chapter Two" after the real book has ended. Treat
    # written-out numbers as chapter numbers so they can be deduped against
    # real "Chapter 1: Title" entries instead of becoming fake chapters.
    word_nums = {
        "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
        "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
        "eleven": 11, "twelve": 12, "thirteen": 13, "fourteen": 14,
        "fifteen": 15, "sixteen": 16, "seventeen": 17, "eighteen": 18,
        "nineteen": 19, "twenty": 20, "twentyone": 21, "twentytwo": 22,
        "twentythree": 23, "twentyfour": 24, "twentyfive": 25,
        "twentysix": 26, "twentyseven": 27, "twentyeight": 28,
        "twentynine": 29, "thirty": 30, "thirtyone": 31, "thirtytwo": 32,
        "thirtythree": 33, "thirtyfour": 34, "thirtyfive": 35,
        "thirtysix": 36, "thirtyseven": 37, "thirtyeight": 38,
        "thirtynine": 39, "forty": 40, "fortyone": 41, "fortytwo": 42,
        "fortythree": 43, "fortyfour": 44, "fortyfive": 45,
        "fortysix": 46, "fortyseven": 47, "fortyeight": 48,
        "fortynine": 49, "fifty": 50, "fiftyone": 51, "fiftytwo": 52,
    }
    wm = re.search(r"\b(?:chapter|cap[ií]tulo)\s+([a-z]+(?:[-\s][a-z]+)?)\b", raw_title, re.IGNORECASE)
    if wm:
        key = re.sub(r"[^a-z]", "", wm.group(1).lower())
        return word_nums.get(key)
    return None


# v37 source-structure hygiene -------------------------------------------------
def _source_heading_key(title):
    return re.sub(r"[^a-z0-9]+", "", str(title or "").lower())


def _is_source_boilerplate_heading(title):
    """True for book front/back matter that should not become summary chapters."""
    key = _source_heading_key(title)
    if not key:
        return True
    exact = {
        "cover", "frontmatter", "frontmatterpage", "digitalgalleyedition", "disclaimer",
        "uncorrectedpageproofs", "title", "titlepage", "halftitle", "halftitlepage",
        "copyright", "copyrightpage", "copyrightnotice", "dedication", "dedicationpage",
        "contents", "tableofcontents", "toc", "praise", "praisepage", "praisefor",
        "praiseforthisbook", "advancepraise", "reviews", "reviewblurbs",
        "notes", "endnotes", "footnotes", "index", "references",
        "bibliography", "worksconsulted", "permissions", "publishernote",
        "publishersnote", "abouttheauthor", "abouttheauthors", "anoteontheauthor", "noteontheauthor", "alsoby",
        "bythesameauthor", "alsoavailable", "readinggroupguide", "resources",
        "acknowledgments", "acknowledgements", "epigraph", "epigraphs",
    }
    if key in exact:
        return True
    low = re.sub(r"\s+", " ", str(title or "").strip().lower())
    return low.startswith((
        "praise for ", "advance praise", "also by ", "by the same author",
        "copyright ", "copyright page", "half-title", "half title", "dedication",
        "notes ", "index ", "front matter", "epigraph",
        "publisher's note", "publisher’s note", "about the author",
        "about the authors", "reading group guide", "permissions ",
        "resources ", "acknowledgments", "acknowledgements",
    ))


def _normalize_source_chapter_heading(title):
    """Normalize source-derived headings before they become H1s."""
    t = re.sub(r"\s+", " ", str(title or "").replace("\x00", " ")).strip(" .:-–—\t")
    if not t:
        return ""
    section_m = re.match(r"^(SECTION\s+\d+)\s*[:.-]?\s*(.*)$", t, flags=re.I)
    if section_m:
        # Keep bare generated SECTION labels so the final quality gate can
        # inspect the first body line and promote a real chapter title.
        rest = section_m.group(2).strip()
        if rest:
            t = rest
        else:
            return section_m.group(1).title()
    m = re.match(r'^(\d{1,3})\s+([A-Z][A-Za-z0-9 ,:\'’"()\-]{3,140})$', t)
    if m:
        n = int(m.group(1))
        if 1 <= n <= 80:
            return f"Chapter {n}: {m.group(2).strip(' .:-–—')}"[:140]
    m = re.match(r"^(\d{1,3}|[ivxlcdm]{1,8})\s*[\.)-]+\s*(.+)$", t, flags=re.I)
    if m:
        raw = m.group(1)
        if raw.isdigit():
            n = int(raw)
        else:
            n = _chapter_number_from_title(raw + ". ")
        if n is not None:
            return f"Chapter {n}: {m.group(2).strip(' .:-–—')}"[:140]
    m = re.match(r"^Chapter\s+(\d{1,3}|[ivxlcdm]{1,8})\s*[\.)\-:]?\s*(.{0,140})$", t, flags=re.I)
    if m:
        raw = m.group(1)
        n = int(raw) if raw.isdigit() else _chapter_number_from_title("Chapter " + raw)
        rest = m.group(2).strip(" .:-–—")
        return f"Chapter {n}: {rest}"[:140] if rest else f"Chapter {n}"
    # Fix rare Kindle-galley TOC strings like "Chapter110.. Fake Photos".
    m = re.match(r"^Chapter\s*(\d{1,3})(?:\d{1,3})?\.\.?\s*(.{2,140})$", t, flags=re.I)
    if m:
        return f"Chapter {int(m.group(1))}: {m.group(2).strip(' .:-–—')}"[:140]
    m = re.match(r"^(PART|Part)\s+([IVXLCDM\d]+)\s*[:.-]?\s*(.{0,140})$", t)
    if m:
        suffix = m.group(3).strip(" .:-–—")
        return f"PART {m.group(2).upper()}: {suffix}"[:140] if suffix else f"PART {m.group(2).upper()}"
    return t[:140]




def _enrich_chapter_titles_from_pages(chapters, page_texts):
    """Use the actual chapter-start page to enrich generic outline titles.

    Some PDFs expose bookmarks as just "Chapter 1." even though the page itself
    clearly says "Chapter 1" followed by "Fake Photos". This keeps the source
    structure stable while improving headings and TOC output.
    """
    enriched = []
    roman_re = r"(?:[IVXLCDM]+|\d+)"
    for item in chapters or []:
        c = dict(item)
        title = _normalize_source_chapter_heading(c.get("title", ""))
        page = int(c.get("page", 0) or 0)
        if page < 0 or page >= len(page_texts or []):
            c["title"] = title
            enriched.append(c)
            continue
        is_generic_ch = re.match(rf"^Chapter\s+{roman_re}\s*$", title, re.I) or re.match(rf"^Chapter\s+{roman_re}\s*[:.]\s*$", str(c.get("title", "")), re.I)
        is_generic_part = re.match(rf"^PART\s+{roman_re}\s*$", title, re.I)
        if not (is_generic_ch or is_generic_part):
            c["title"] = title
            enriched.append(c)
            continue
        lines = [re.sub(r"\s+", " ", ln).strip(" .:-–—") for ln in str(page_texts[page] or "").splitlines() if re.sub(r"\s+", " ", ln).strip()]
        new_title = title
        for idx, ln in enumerate(lines[:10]):
            if is_generic_ch and re.match(r"^Chapter\s+", ln, re.I):
                # Prefer the following title lines. Some PDFs split a chapter
                # title across several short lines, e.g. Adult Children.
                bits = []
                for nxt in lines[idx + 1:idx + 6]:
                    nxt = nxt.strip(" .:-–—")
                    if not nxt or _is_source_boilerplate_heading(nxt):
                        continue
                    if len(nxt) <= 2:
                        # Drop-cap/body fragments such as "E" after a title.
                        if bits:
                            break
                        continue
                    if re.match(r"^(Chapter|PART|Introduction|Conclusion|Epilogue|Prologue)\b", nxt, re.I):
                        break
                    if re.match(r"^\d{1,4}$", nxt):
                        continue
                    if re.match(r"^[A-Z]\s+[a-z]", nxt):
                        break
                    if bits and re.search(r"\b(?:January|February|March|April|May|June|July|August|September|October|November|December|Spring|Summer|Fall|Autumn|Winter)\b|\b\d{4}\b", nxt, re.I) and "," in nxt:
                        break
                    # Stop when body prose begins. Title fragments are short;
                    # body paragraphs are longer and usually lower-case starts.
                    if len(nxt.split()) > 9:
                        break
                    bits.append(nxt)
                    if sum(len(b.split()) for b in bits) >= 12:
                        break
                if bits:
                    num = _chapter_number_from_title(title)
                    if num is not None:
                        new_title = f"Chapter {num}: {' '.join(bits)}"
                break
            if is_generic_part and re.match(r"^PART\s+", ln, re.I):
                if idx + 1 < len(lines):
                    nxt = lines[idx + 1].strip(" .:-–—")
                    if 2 <= len(nxt) <= 90 and not re.match(r"^Chapter\s+", nxt, re.I):
                        new_title = f"{title}: {nxt}"
                break
        c["title"] = _normalize_source_chapter_heading(new_title)
        enriched.append(c)
    return enriched

def _first_meaningful_body_line(body):
    for ln in str(body or "").splitlines():
        st = ln.strip(" #\t")
        if st:
            return st
    return ""


def _effective_source_heading(sec):
    heading = str((sec or {}).get("heading", "") or "").strip()
    if re.match(r"^section\s+\d+$", heading, re.I) or not heading:
        first = _first_meaningful_body_line((sec or {}).get("body", ""))
        return _normalize_source_chapter_heading(first) if first else heading
    return _normalize_source_chapter_heading(heading)


def _promote_generic_section_heading(sec):
    """Promote body-first-line titles out of generic SECTION N headings."""
    sec = dict(sec)
    heading = str(sec.get("heading", "") or "").strip()
    if not re.match(r"^section\s+\d+$", heading, re.I):
        return sec
    lines = str(sec.get("body", "") or "").splitlines()
    for idx, line in enumerate(lines[:5]):
        first = line.strip()
        if not first:
            continue
        candidate = _normalize_source_chapter_heading(first)
        if candidate and len(candidate.split()) <= 10:
            sec["heading"] = candidate
            sec["body"] = "\n".join(lines[idx + 1:]).strip() + "\n"
        break
    return sec

def _looks_like_book_chapter_list(chapters):
    """Heuristic for source-structure lock: real books usually have a TOC
    sequence with Introduction/Preface plus Chapter N entries or a long
    monotonic chapter run. Report decks should not be locked this way.
    """
    titles = [str(c.get("title", "")) for c in chapters or []]
    if len(titles) < 4:
        return False
    low = " ".join(t.lower() for t in titles[:20])
    nums = [_chapter_number_from_title(t) for t in titles]
    nums = [n for n in nums if n is not None]
    if len(nums) >= 4 and nums == sorted(nums) and len(set(nums)) >= 4:
        uniq = sorted(set(nums))
        gaps = [b - a for a, b in zip(uniq, uniq[1:])]
        if uniq[0] <= 2 and (not gaps or max(gaps) <= 2):
            return True
    if any(w in low for w in ["introduction", "preface", "foreword", "prologue"]) and len(nums) >= 3:
        return True
    if len([t for t in titles if re.search(r"\b(?:examen|unidad|tema)\s+\d+", t, re.I)]) >= 4:
        return True
    return False

def _canonicalize_chapter_list(chapters, total_pages=0):
    """Normalize a chapter/section start list while preserving source titles.

    For books, this collapses duplicate/generic starts such as "Chapter 1"
    when a richer TOC title like "Chapter 1: How Emotionally..." exists near
    the same page. It also removes non-content preliminaries and trailing
    back-matter note/index subheadings that masquerade as chapters.
    """
    raw_items = list(chapters or [])
    content_pages = []
    for c in raw_items:
        try:
            pg = int(c.get("page", 0))
        except Exception:
            continue
        tt = _normalize_source_chapter_heading(c.get("title", ""))
        if _chapter_number_from_title(tt) is not None or re.search(r"\b(?:prologue|introduction|part\s+[ivxlcdm\d]+)\b", tt, re.I):
            content_pages.append(pg)
    first_content_page = min(content_pages) if content_pages else None
    backmatter_keys = {"acknowledgments", "acknowledgements", "notes", "endnotes", "index", "references", "bibliography", "photos", "newsletters", "abouttheauthor", "abouttheauthors"}
    back_start = None
    if first_content_page is not None:
        for c in raw_items:
            try:
                pg = int(c.get("page", 0))
            except Exception:
                continue
            key = _source_heading_key(c.get("title", ""))
            if key in backmatter_keys and pg > first_content_page + 5:
                back_start = pg if back_start is None else min(back_start, pg)
    clean = []
    for c in raw_items:
        try:
            page = int(c.get("page", 0))
        except Exception:
            continue
        title = _normalize_source_chapter_heading(c.get("title", ""))
        if not title or _is_source_boilerplate_heading(title):
            continue
        if back_start is not None and page >= back_start:
            continue
        if total_pages:
            page = max(0, min(total_pages - 1, page))
        clean.append({"title": title[:140], "page": page})
    clean.sort(key=lambda x: (x["page"], x["title"].lower()))

    # Prefer richer titles for the same chapter number.
    by_num = {}
    others = []
    for c in clean:
        n = _chapter_number_from_title(c["title"])
        if n is None:
            others.append(c)
            continue
        prev = by_num.get(n)
        if prev is None:
            by_num[n] = c
        else:
            # Keep the longer/non-generic title. For wildly different pages,
            # avoid false early TOC-page detections such as Chapter 14 on page 4.
            chosen = c if len(c["title"]) > len(prev["title"]) else prev
            chosen = dict(chosen)
            if abs(prev["page"] - c["page"]) > 8 and min(prev["page"], c["page"]) < 12:
                chosen["page"] = max(prev["page"], c["page"])
            else:
                chosen["page"] = min(prev["page"], c["page"])
            by_num[n] = chosen

    merged = others + list(by_num.values())
    merged.sort(key=lambda x: (x["page"], x["title"].lower()))

    rich_conclusion_pages = [
        int(c.get("page", 0) or 0) for c in merged
        if str(c.get("title", "")).strip().lower().startswith("conclusion")
        and _source_heading_key(c.get("title", "")) != "conclusion"
    ]
    out = []
    for c in merged:
        norm = _norm_title_key(c["title"])
        if not norm:
            continue
        # Drop boilerplate from source front/back matter. Substantive preliminaries
        # like Authors' Note, Cast of Characters, Preface, Prologue and
        # Introduction remain eligible.
        if _is_source_boilerplate_heading(c["title"]):
            continue
        # v42: Some e-books expose notes/endnote sections as bare "Conclusion"
        # after a richer real conclusion title. Keep the richer source conclusion
        # and drop the generic back-matter duplicate.
        if _source_heading_key(c["title"]) == "conclusion" and any(pg < int(c.get("page", 0) or 0) for pg in rich_conclusion_pages):
            continue
        duplicate = False
        for prev in out:
            if _title_matches(prev["title"], c["title"]) and abs(prev["page"] - c["page"]) <= 3:
                duplicate = True
                if len(c["title"]) > len(prev["title"]):
                    prev["title"] = c["title"]
                prev["page"] = min(prev["page"], c["page"])
                break
        if not duplicate:
            out.append(dict(c))
    out.sort(key=lambda x: (x["page"], x["title"].lower()))
    return out


# ── G4b: 3-layer chapter resolution ───────────────────────────────────────────
def _resolve_chapter_list(pdf_bytes, page_texts, ai_client, job_id):
    """Return (chapter_list, source_name) using a merged fail-closed resolver.

    v9 merges outline + pattern + AI candidates instead of accepting the first
    source that looks good enough.
    """
    total_pages = max(0, len(page_texts))

    def _norm_title(s):
        s = re.sub(r"\s+", " ", str(s or "")).strip()
        s = re.sub(r"[^\w\s]", "", s.lower())
        return re.sub(r"\s+", " ", s).strip()

    def _clean_candidates(items, source):
        out = []
        for c in items or []:
            try:
                page = int(c.get("page", -1))
            except Exception:
                continue
            title = str(c.get("title", "")).strip()
            if not title:
                continue
            # Do not turn mechanical front/back matter into required summary
            # chapters. Keep substantive matter such as Authors' Note, Cast of
            # Characters, Preface/Prologue/Introduction.
            title = _normalize_source_chapter_heading(title)
            if _is_source_boilerplate_heading(title):
                continue
            if page < 0 or page >= total_pages:
                continue
            out.append({"title": title, "page": page, "source": source})
        return out

    def _dedupe(candidates):
        candidates = sorted(candidates, key=lambda x: (x["page"], x["title"].lower()))
        merged = []
        for c in candidates:
            n = _norm_title(c["title"])
            if not n:
                continue
            matched = False
            for m in merged:
                mn = _norm_title(m["title"])
                same_title = (n == mn) or (n in mn) or (mn in n)
                close_page = abs(c["page"] - m["page"]) <= 2
                if same_title and close_page:
                    if len(c["title"]) > len(m["title"]):
                        m["title"] = c["title"]
                    if c["page"] < m["page"]:
                        m["page"] = c["page"]
                    matched = True
                    break
            if not matched:
                merged.append({"title": c["title"], "page": c["page"]})
        merged.sort(key=lambda x: (x["page"], x["title"].lower()))
        return merged

    outline = _clean_candidates(_extract_pdf_outline(pdf_bytes), "pdf_outline")
    pattern = _clean_candidates(detect_chapter_starts(page_texts), "pattern_match")
    toc     = _clean_candidates(_detect_chapters_from_toc_text(page_texts, total_pages), "toc_parse")

    # v20 source-structure lock: for books/workbooks with a reliable TOC, use
    # the TOC/outline sequence as the canonical structure. This prevents later
    # pattern/AI detections from adding duplicate H1s such as "Chapter 1" next
    # to "Chapter 1: Real Source Title".
    def _validate_toc_against_pattern(toc_items, pattern_items):
        """Keep TOC candidates only when they agree with actual chapter-start pages.

        Some converted Kindle/galley PDFs contain mangled contents lines such as
        ``Chapter110.. Fake Photos``. The TOC parser can misread these as
        chapter numbers on page zero, which then corrupts the source-structure
        lock. When real chapter-start pages are available, they are more
        trustworthy than the parsed TOC page numbers.
        """
        pattern_by_num = {}
        for item in pattern_items or []:
            num = _chapter_number_from_title(item.get("title", ""))
            if num is not None and num not in pattern_by_num:
                pattern_by_num[num] = int(item.get("page", 0))
        if len(pattern_by_num) < 5:
            return toc_items
        first_real = min(pattern_by_num.values())
        out = []
        matched_nums = set()
        for item in toc_items or []:
            title = item.get("title", "")
            page = int(item.get("page", 0))
            num = _chapter_number_from_title(title)
            low = str(title).strip().lower()
            if num is None:
                # Preserve front/back matter and part headings if they occur near
                # or after the first real content page. Drop suspicious orphan
                # titles in the early TOC pages.
                if any(x in low for x in ("prologue", "preface", "foreword", "introduction", "part ", "epilogue", "conclusion")):
                    if page >= max(0, first_real - 8):
                        out.append(item)
                continue
            actual = pattern_by_num.get(num)
            if actual is None:
                continue
            if abs(page - actual) <= 4 or page < first_real:
                fixed = dict(item)
                fixed["page"] = actual
                out.append(fixed)
                matched_nums.add(num)
        # If the TOC was mostly unrecoverable, fall back to pattern starts
        # rather than locking a corrupt structure.
        if len(matched_nums) >= max(5, int(len(pattern_by_num) * 0.65)):
            return out
        return []

    canonical_toc = _enrich_chapter_titles_from_pages(_canonicalize_chapter_list(_dedupe(_validate_toc_against_pattern(toc, pattern)), total_pages), page_texts)
    canonical_outline = _enrich_chapter_titles_from_pages(_canonicalize_chapter_list(_dedupe(outline), total_pages), page_texts)
    toc_is_book = _looks_like_book_chapter_list(canonical_toc)
    outline_is_book = _looks_like_book_chapter_list(canonical_outline)
    pattern_book = _enrich_chapter_titles_from_pages(_canonicalize_chapter_list(_dedupe(pattern), total_pages), page_texts)
    pattern_is_book = _looks_like_book_chapter_list(pattern_book)
    fuller_baseline = max(len(canonical_outline) if outline_is_book else 0, len(pattern_book) if pattern_is_book else 0, 1)
    if toc_is_book and len(canonical_toc) >= max(8, int(fuller_baseline * 0.70)):
        return canonical_toc, "toc_parse_locked"
    if outline_is_book:
        return canonical_outline, "outline_locked"
    if pattern_is_book:
        return pattern_book, "pattern_locked"

    ai = _clean_candidates(
        _detect_chapters_from_toc_pages(ai_client, page_texts, job_id), "ai_detect"
    )

    merged = _enrich_chapter_titles_from_pages(_canonicalize_chapter_list(_dedupe(outline + pattern + toc + ai), total_pages), page_texts)
    page_titles = _enrich_chapter_titles_from_pages(_dedupe(_clean_candidates(_detect_page_title_sections(page_texts), "page_title")), page_texts)

    # Report decks often have no real bookmarks and can trigger a single false
    # pattern match (for example appendix labels such as "C. Like..."). If the
    # page-title resolver finds materially broader coverage, prefer it.
    if page_titles and (
        not merged
        or len(page_titles) >= max(3, len(merged) * 2)
        or (len(merged) <= 2 and len(page_titles) >= 3)
    ):
        return page_titles, "page_title"

    if merged:
        sources = []
        if outline:
            sources.append("outline")
        if pattern:
            sources.append("pattern")
        if toc:
            sources.append("toc")
        if ai:
            sources.append("ai")
        return merged, ("merged:" + "+".join(sources))

    if page_titles:
        return page_titles, "page_title"

    return [], "none"


# ── G4a: Chapter-aware chunking ────────────────────────────────────────────────
def _build_chapter_chunks(full_text, page_texts, chapter_starts, max_chars):
    """Build chapter-aware text chunks. Returns list of dicts.

    The v9 implementation silently dropped pages before the first resolved
    chapter and could create empty chunks when duplicate starts landed on the
    same page. This version preserves front matter, clamps page ranges, and
    keeps enough metadata for per-chapter length auditing.
    """
    max_chars = max(1000, int(max_chars or CHARS_PER_CHUNK))

    def _split_text_block(title, text, page_start, page_end):
        text = (text or "").strip()
        if not text:
            return []
        if len(text) <= max_chars:
            return [{
                "title": title,
                "text": text,
                "page_start": page_start,
                "page_end": page_end,
                "part": 1,
                "n_parts": 1,
            }]

        parts = []
        pos = 0
        while pos < len(text):
            end = min(pos + max_chars, len(text))
            if end < len(text):
                # Prefer paragraph, then sentence, then whitespace boundaries.
                b = text.rfind("\n\n", pos, end)
                if b <= pos:
                    b = max(text.rfind(". ", pos, end), text.rfind("! ", pos, end), text.rfind("? ", pos, end))
                    if b > pos:
                        b += 1
                if b <= pos:
                    b = text.rfind(" ", pos, end)
                if b > pos:
                    end = b
            part_text = text[pos:end].strip()
            if part_text:
                parts.append(part_text)
            if end <= pos:
                break
            pos = end

        n_parts = max(1, len(parts))
        return [{
            "title": title,
            "text": pt,
            "page_start": page_start,
            "page_end": page_end,
            "part": pi + 1,
            "n_parts": n_parts,
        } for pi, pt in enumerate(parts)]

    total_pages = len(page_texts)
    if not chapter_starts:
        chunks = []
        start = 0
        n = 0
        while start < len(full_text):
            end = min(start + max_chars, len(full_text))
            if end < len(full_text):
                b = full_text.rfind("\n\n", start, end)
                if b <= start:
                    b = full_text.rfind(" ", start, end)
                if b > start:
                    end = b
            block = full_text[start:end].strip()
            if block:
                n += 1
                chunks.append({
                    "title": f"Section {n}",
                    "text": block,
                    "page_start": 0,
                    "page_end": max(0, total_pages - 1),
                    "part": 1,
                    "n_parts": 1,
                })
            if end <= start:
                break
            start = end
        return chunks

    # Clean, sort, clamp, and de-dupe chapter starts by page/title.
    clean_starts = []
    seen = set()
    for cs in sorted(chapter_starts, key=lambda c: (int(c.get("page", 0)), str(c.get("title", "")))):
        try:
            pg = int(cs.get("page", 0))
        except Exception:
            continue
        title = _normalize_source_chapter_heading(cs.get("title", "")) or f"Chapter starting page {pg + 1}"
        if _is_source_boilerplate_heading(title):
            continue
        pg = max(0, min(pg, max(0, total_pages - 1)))
        key = (pg, re.sub(r"\s+", " ", title).lower())
        if key in seen:
            continue
        seen.add(key)
        clean_starts.append({"title": title, "page": pg})

    if not clean_starts:
        return _build_chapter_chunks(full_text, page_texts, [], max_chars)

    # Build cumulative char offsets per page. _get_pdf_data now appends one
    # newline per page, including blank pages, so these offsets align with full_text.
    page_offsets = []
    pos = 0
    for pt in page_texts:
        page_offsets.append(pos)
        pos += len(pt or "") + 1
    page_offsets.append(pos)

    def _page_char(pg):
        pg = max(0, min(int(pg), len(page_offsets) - 1))
        return min(page_offsets[pg], len(full_text))

    ranges = []
    # v37: Do not create a generic "Front Matter" chapter. Substantive
    # front-matter sections are kept only when they are explicitly detected
    # (Authors' Note, Foreword, Prologue, Introduction, Cast of Characters).

    for i, cs in enumerate(clean_starts):
        sp = cs["page"]
        ep = clean_starts[i + 1]["page"] if i + 1 < len(clean_starts) else total_pages
        if ep <= sp:
            continue
        ranges.append({
            "title": cs["title"],
            "page_start": sp,
            "page_end": ep - 1,
        })

    result = []
    for ch in ranges:
        sp = ch["page_start"]
        ep_exclusive = ch["page_end"] + 1
        text = full_text[_page_char(sp):_page_char(ep_exclusive)]
        result.extend(_split_text_block(ch["title"], text, sp, ch["page_end"]))

    return result


# ── v51 Chapter Manifest Lock ────────────────────────────────────────────────
def _manifest_chapter_id(order, title):
    key = _norm_title_key(title)
    if not key:
        key = f"chapter{int(order or 0):03d}"
    return f"ch_{int(order or 0):03d}_{key[:48]}"


def _build_chapter_manifest(chapter_chunks, chapter_list=None, page_texts=None,
                            source_format="pdf", detection_source=""):
    """Create a canonical ordered chapter manifest from the resolved source map.

    The manifest is the source of truth for output order, H1 headings,
    coverage checks and per-chapter budgets. It is intentionally deterministic:
    Claude may summarize prose, but it may not rename, merge, or reorder H1s.
    """
    manifest = []
    seen = {}
    order = 0
    for chunk in chapter_chunks or []:
        title = _normalize_source_chapter_heading(chunk.get("title", ""))
        if not title or _is_source_boilerplate_heading(title):
            continue
        key = _norm_title_key(title)
        if not key:
            continue
        words = _count_words(chunk.get("text", ""))
        try:
            ps = int(chunk.get("page_start", 0) or 0)
            pe = int(chunk.get("page_end", ps) or ps)
        except Exception:
            ps = pe = 0
        if key not in seen:
            order += 1
            item = {
                "order": order,
                "chapter_id": _manifest_chapter_id(order, title),
                "title": title,
                "source_start": ps,
                "source_end": pe,
                "source_words": max(0, words),
                "chunks": 1,
                "parts": [int(chunk.get("part", 1) or 1)],
                "source_format": str(source_format or "pdf").lower(),
                "detection_source": detection_source or "",
            }
            seen[key] = item
            manifest.append(item)
        else:
            item = seen[key]
            item["source_start"] = min(int(item.get("source_start", ps)), ps)
            item["source_end"] = max(int(item.get("source_end", pe)), pe)
            item["source_words"] = int(item.get("source_words", 0)) + max(0, words)
            item["chunks"] = int(item.get("chunks", 1)) + 1
            item.setdefault("parts", []).append(int(chunk.get("part", 1) or 1))

    if chapter_list and manifest:
        title_order = []
        for c in chapter_list or []:
            t = _normalize_source_chapter_heading(c.get("title", ""))
            k = _norm_title_key(t)
            if k and k not in title_order:
                title_order.append(k)
        if title_order:
            rank = {k: i for i, k in enumerate(title_order)}
            manifest.sort(key=lambda m: (rank.get(_norm_title_key(m.get("title", "")), 10000 + int(m.get("order", 0))), int(m.get("source_start", 0))))
            for idx, item in enumerate(manifest, 1):
                item["order"] = idx
                item["chapter_id"] = _manifest_chapter_id(idx, item.get("title", ""))

    total_words = sum(int(m.get("source_words", 0) or 0) for m in manifest)
    for item in manifest:
        item["source_share"] = (int(item.get("source_words", 0) or 0) / total_words) if total_words else 0.0
    return manifest


def _manifest_expected_titles(manifest):
    return [str(m.get("title", "")).strip() for m in manifest or [] if str(m.get("title", "")).strip()]


def _apply_manifest_targets(chapter_targets, manifest, total_words):
    """Allocate target words by source word share, not by crude chunk count."""
    if not manifest or not chapter_targets:
        return chapter_targets
    out = {k: dict(v) for k, v in (chapter_targets or {}).items()}
    total_source_words = sum(max(0, int(m.get("source_words", 0) or 0)) for m in manifest)
    if total_source_words <= 0 or total_words <= 0:
        return out
    reserve_min = CHAPTER_MANIFEST_MIN_TARGET_WORDS
    remaining = max(0, int(total_words) - reserve_min * len(manifest))
    for item in manifest:
        key = _norm_title_key(item.get("title", ""))
        if not key:
            continue
        proportional = int(round(remaining * (int(item.get("source_words", 0) or 0) / total_source_words))) if remaining else 0
        target = max(reserve_min, reserve_min + proportional)
        if int(item.get("source_words", 0) or 0) < 800 and len(manifest) > 12:
            target = min(target, CHAPTER_MANIFEST_TINY_WORD_CAP)
        out.setdefault(key, {})
        out[key].update({
            "title": item.get("title", ""),
            "chunks": item.get("chunks", 1),
            "source_words": item.get("source_words", 0),
            "target": max(reserve_min, int(target)),
            "manifest_order": item.get("order"),
            "chapter_id": item.get("chapter_id"),
        })
    return _rebalance_chapter_targets(out, total_words)


def _force_summary_to_chunk_heading(summary, expected_title):
    """Force one model response to belong to its source manifest chapter."""
    expected_title = _normalize_source_chapter_heading(expected_title) or "Chapter"
    lines = str(summary or "").splitlines()
    out = []
    inserted = False
    for line in lines:
        if re.match(r"^#\s+", line.strip()):
            if not inserted:
                out.append(f"# {expected_title}")
                inserted = True
            else:
                out.append("## " + re.sub(r"^#+\s*", "", line).strip())
        else:
            out.append(line)
    if not inserted:
        if out and out[0].strip().startswith("<!--RSCORE:"):
            out.insert(1, f"# {expected_title}")
        else:
            out.insert(0, f"# {expected_title}")
    return "\n".join(out).strip()


def _manifest_span_map(sections, manifest):
    span_map = {}
    duplicates = []
    used_spans = set()
    spans = _h1_spans(sections, include_special=True)
    for item in manifest or []:
        title = item.get("title", "")
        matches = []
        for h1_idx, end_idx in spans:
            sec = sections[h1_idx]
            if _is_special_section(sec):
                continue
            if (h1_idx, end_idx) in used_spans:
                continue
            if _title_matches(title, sec.get("heading", "")):
                matches.append((h1_idx, end_idx))
        if matches:
            matches.sort(key=lambda sp: sp[0])
            span_map[item["chapter_id"]] = matches[0]
            used_spans.add(matches[0])
            for extra in matches[1:]:
                duplicates.append({"expected": title, "actual": sections[extra[0]].get("heading", ""), "index": extra[0]})
                used_spans.add(extra)
    return span_map, duplicates, used_spans


def _validate_manifest_order_and_coverage(sections, manifest):
    span_map, duplicates, used_spans = _manifest_span_map(sections or [], manifest or [])
    missing = []
    order_positions = []
    for item in manifest or []:
        sp = span_map.get(item.get("chapter_id"))
        if not sp:
            missing.append(item.get("title", ""))
        else:
            order_positions.append(sp[0])
    out_of_order = any(b < a for a, b in zip(order_positions, order_positions[1:]))
    orphan_headings = []
    for h1_idx, end_idx in _h1_spans(sections or [], include_special=True):
        if _is_special_section((sections or [])[h1_idx]):
            continue
        if (h1_idx, end_idx) not in used_spans:
            orphan_headings.append((sections or [])[h1_idx].get("heading", ""))
    return {
        "expected_count": len(manifest or []),
        "matched_count": len(span_map),
        "missing": missing,
        "duplicates": duplicates,
        "out_of_order": out_of_order,
        "orphan_headings": orphan_headings,
    }


def _lock_sections_to_manifest(sections, manifest, job_id=None, drop_orphans=None):
    """Return sections with normal H1 chapters in manifest order and titles."""
    if not CHAPTER_MANIFEST_LOCK_ENABLED or not manifest:
        return list(sections or []), _validate_manifest_order_and_coverage(sections or [], manifest or [])
    drop_orphans = CHAPTER_MANIFEST_DROP_ORPHANS if drop_orphans is None else bool(drop_orphans)
    src = [dict(s) for s in (sections or [])]
    span_map, duplicates, used_spans = _manifest_span_map(src, manifest)
    front_specials = []
    final_specials = []
    orphans = []
    for h1_idx, end_idx in _h1_spans(src, include_special=True):
        sec = src[h1_idx]
        heading_key = _source_heading_key(sec.get("heading", ""))
        block = src[h1_idx:end_idx]
        if _is_special_section(sec):
            if heading_key in {"summaryofthesummary", "ifyouenjoyedthisbook", "youmightalsolike"}:
                final_specials.extend(block)
            else:
                front_specials.extend(block)
            continue
        if (h1_idx, end_idx) not in used_spans:
            orphans.append({"heading": sec.get("heading", ""), "index": h1_idx})
            if not drop_orphans and not _is_source_boilerplate_heading(sec.get("heading", "")):
                final_specials.extend(block)

    body = []
    for item in manifest:
        sp = span_map.get(item.get("chapter_id"))
        if not sp:
            continue
        h1_idx, end_idx = sp
        block = [dict(s) for s in src[h1_idx:end_idx]]
        block[0]["heading"] = item.get("title", block[0].get("heading", ""))
        block[0]["chapter_id"] = item.get("chapter_id")
        block[0]["manifest_order"] = item.get("order")
        body.extend(block)

    locked = front_specials + body + final_specials
    report = _validate_manifest_order_and_coverage(locked, manifest)
    report.update({"orphans_dropped": orphans if drop_orphans else [], "duplicates_dropped": duplicates})
    _audit_event(job_id, "chapter_manifest_lock", **report)
    return locked, report


def _write_chapter_manifest_artifacts(job_id, manifest, coverage_report=None, chapter_targets=None):
    if not job_id or not CHAPTER_MANIFEST_AUDIT_ENABLED:
        return
    try:
        payload = {
            "job_id": job_id,
            "build": BUILD_TAG,
            "manifest": manifest or [],
            "coverage_report": coverage_report or {},
            "chapter_targets": chapter_targets or {},
        }
        path = os.path.join(TMP_DIR, f"{job_id}_manifest.json")
        with open(path, "w", encoding="utf-8", errors="replace") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        if job_id in jobs:
            jobs[job_id]["manifest_path"] = path
            jobs[job_id]["chapter_manifest"] = manifest or []
            jobs[job_id]["chapter_manifest_report"] = coverage_report or {}
    except Exception:
        pass


# ── G4d: Multi-part summary merger ────────────────────────────────────────────
def _merge_multipart_summaries(text):
    """Merge adjacent H1 sections with the same chapter title.

    Unlike v9, this does not throw away earlier-part takeaways. It strips the
    per-part takeaway sections from the prose, deduplicates their bullets, and
    appends one consolidated `### Key Takeaways` block to the merged chapter.
    """
    h1_pat = re.compile(r"^# (.+)$", re.MULTILINE)
    parts = h1_pat.split(text)
    if len(parts) <= 1:
        return text

    pre = parts[0]
    sections = []
    for j in range(1, len(parts), 2):
        heading = parts[j].strip() if j < len(parts) else ""
        body = parts[j + 1] if j + 1 < len(parts) else ""
        sections.append((heading, body))

    takeaway_re = re.compile(
        r"\n###\s+[^\n]*[Tt]akeaways?[^\n]*\n(?P<body>.*?)(?=\n#{1,3}\s+|\Z)",
        re.DOTALL,
    )

    def _strip_takeaways(body):
        return takeaway_re.sub("\n", body).rstrip()

    def _takeaway_bullets(body):
        bullets = []
        for m in takeaway_re.finditer(body):
            for line in m.group("body").splitlines():
                st = line.strip()
                if st.startswith("- ") or st.startswith("* "):
                    bullet = re.sub(r"^[\-*]\s+", "", st).strip()
                    if bullet:
                        bullets.append(bullet)
        return bullets

    def _dedupe_bullets(bullets, cap=8):
        out = []
        seen = set()
        for b in bullets:
            key = re.sub(r"[^a-z0-9]", "", b.lower())[:120]
            if key and key not in seen:
                seen.add(key)
                out.append(b)
            if len(out) >= cap:
                break
        return out

    merged = []
    i = 0
    while i < len(sections):
        heading, body = sections[i]
        group = [body]
        j = i + 1
        while j < len(sections) and sections[j][0] == heading:
            group.append(sections[j][1])
            j += 1

        if len(group) == 1:
            merged.append((heading, body))
        else:
            prose_parts = [_strip_takeaways(b) for b in group]
            bullets = _dedupe_bullets([x for b in group for x in _takeaway_bullets(b)])
            combined = "\n\n".join(p for p in prose_parts if p.strip()).rstrip()
            if bullets:
                combined += "\n\n### Key Takeaways\n" + "\n".join(f"- {b}" for b in bullets)
            merged.append((heading, combined + "\n"))
        i = j

    result = pre
    for heading, body in merged:
        result += f"# {heading}\n{body}"
    return result



# ── v46: Style application profiles and QA ────────────────────────────────────
STYLE_PROFILES = {
    "narrative_basic": {
        "label": "Narrative - Basic",
        "chapter_headings": ["What This Chapter Adds", "How the Argument Develops", "What It Leaves You With"],
        "signals": ["chapter adds", "the argument", "what it leaves"],
        "contract": (
            "STYLE CONTRACT - Narrative Basic. Write like a polished nonfiction author: smooth, clear, vivid, and reader-friendly. "
            "Use flowing paragraphs and natural transitions. Avoid academic stiffness, bullet-dump thinking, and generic headings. "
            "Subsection headings should sound like a book companion, for example: 'What This Chapter Adds', 'How the Argument Develops', 'What It Leaves You With'. "
            "Key Takeaways should be complete, concrete sentences that preserve the chapter's real insight."
        ),
    },
    "story_arc": {
        "label": "Story-Arc Narrative",
        "chapter_headings": ["The Setup", "The Pressure Builds", "The Turn", "What It Changes"],
        "signals": ["the setup", "pressure", "the turn", "what it changes", "at stake"],
        "contract": (
            "STYLE CONTRACT - Story-Arc Narrative. Treat every chapter as a small story, even when the source is analytical. "
            "You MUST use these H2 headings exactly where possible: 'The Setup', 'The Pressure Builds', 'The Turn', and 'What It Changes'. "
            "Open by naming what is at stake, then show how the chapter moves from situation to tension to consequence. "
            "Do not list claims mechanically; make the reader feel progression. Key Takeaways should preserve the causal movement of the chapter."
        ),
    },
    "feynman_storyteller": {
        "label": "Feynman Storyteller",
        "chapter_headings": ["The Simple Version", "Why It Works", "Where People Get Confused", "The Idea in Real Life"],
        "signals": ["simple version", "why it works", "get confused", "think of", "you can see"],
        "contract": (
            "STYLE CONTRACT - Feynman Storyteller. Explain the chapter to a smart friend from first principles. "
            "You MUST use these H2 headings exactly where possible: 'The Simple Version', 'Why It Works', 'Where People Get Confused', and 'The Idea in Real Life'. "
            "Use plain English, short paragraphs, direct 'you' address, and concrete analogies. Ask simple questions and answer them. "
            "Avoid academic language. Key Takeaways should feel like teach-back points someone could repeat aloud."
        ),
    },
    "investigative_narrative": {
        "label": "Investigative Narrative",
        "chapter_headings": ["What Happened", "The Evidence Trail", "Who Benefited", "What It Reveals"],
        "signals": ["what happened", "evidence trail", "who benefited", "what it reveals", "follow the"],
        "contract": (
            "STYLE CONTRACT - Investigative Narrative. Write like an investigative journalist following evidence, incentives, and consequences. "
            "You MUST use these H2 headings exactly where possible: 'What Happened', 'The Evidence Trail', 'Who Benefited', and 'What It Reveals'. "
            "Use names, numbers, motives, documents, overlooked warnings, and concrete consequences. Avoid vague abstractions. "
            "Key Takeaways should read like findings from an investigation, not generic lessons."
        ),
    },
    "strategic_briefing": {
        "label": "Strategic Briefing",
        "chapter_headings": ["Bottom Line", "Evidence", "Implications", "Risks / Watch Items"],
        "signals": ["bottom line", "implication", "risk", "watch item", "decision"],
        "contract": (
            "STYLE CONTRACT - Strategic Briefing. Write like a senior analyst briefing a decision-maker. "
            "You MUST use these H2 headings exactly where possible: 'Bottom Line', 'Evidence', 'Implications', and 'Risks / Watch Items'. "
            "Lead with the verdict first, then evidence, then implications. Use crisp declarative sentences. "
            "Key Takeaways should be action-oriented and decision-useful, not just descriptive."
        ),
    },
    "deep_reading": {
        "label": "Deep Reading Companion",
        "chapter_headings": ["Close Reading", "Hidden Assumptions", "Nuance and Tension", "Why This Matters in the Argument"],
        "signals": ["close reading", "hidden assumption", "nuance", "tension", "why this matters"],
        "contract": (
            "STYLE CONTRACT - Deep Reading Companion. Read beneath the surface of the chapter. "
            "You MUST use these H2 headings exactly where possible: 'Close Reading', 'Hidden Assumptions', 'Nuance and Tension', and 'Why This Matters in the Argument'. "
            "Explain not only what the author says but how the argument works, what assumptions it relies on, and what tensions remain. "
            "Preserve nuance and examples. Key Takeaways should capture interpretive depth, not headline simplification."
        ),
    },
    "practical_playbook": {
        "label": "Practical Playbook",
        "chapter_headings": ["The Core Rule", "How to Apply It", "The Trap to Avoid", "In Practice"],
        "signals": ["core rule", "apply it", "trap to avoid", "in practice", "do this"],
        "contract": (
            "STYLE CONTRACT - Practical Playbook. Turn the chapter into usable rules, behaviours, warnings, and checklists. "
            "You MUST use these H2 headings exactly where possible: 'The Core Rule', 'How to Apply It', 'The Trap to Avoid', and 'In Practice'. "
            "Use direct language and make abstract lessons operational. Key Takeaways should be rules the reader can act on immediately."
        ),
    },
    "literary_essay": {
        "label": "Literary Essay",
        "chapter_headings": ["The Deeper Argument", "The Texture of the Idea", "Where the Argument Strains", "Why It Endures"],
        "signals": ["deeper argument", "texture", "argument strains", "why it endures", "more than"],
        "contract": (
            "STYLE CONTRACT - Literary Essay. Write like a sharp essayist interpreting the chapter, not merely summarising it. "
            "You MUST use these H2 headings exactly where possible: 'The Deeper Argument', 'The Texture of the Idea', 'Where the Argument Strains', and 'Why It Endures'. "
            "Use elegant, evaluative prose. Say what the author is really doing, why it is persuasive, and where it leaves questions unresolved. "
            "Key Takeaways should be interpretive propositions, not slogans."
        ),
    },
    "academic": {
        "label": "Academic",
        "chapter_headings": ["Claim", "Evidence", "Mechanism", "Qualifications"],
        "signals": ["claim", "evidence", "mechanism", "qualification", "the argument proceeds"],
        "contract": (
            "STYLE CONTRACT - Academic. Write with scholarly precision for an intelligent non-specialist. "
            "You MUST use these H2 headings exactly where possible: 'Claim', 'Evidence', 'Mechanism', and 'Qualifications'. "
            "Define key terms, separate claims from evidence, and qualify assertions where the source qualifies them. "
            "Key Takeaways should be careful propositions, not imperatives or marketing copy."
        ),
    },
}
STYLE_ALIASES = {
    "narrative": "narrative_basic",
    "concise": "narrative_basic",
    "bullet": "feynman_storyteller",
    "narrative_explainer": "feynman_storyteller",
    "narrative_editorial": "story_arc",
    "narrative_deep": "deep_reading",
}

def _canonical_style_id(style):
    key = str(style or "narrative_basic").strip().lower()
    key = STYLE_ALIASES.get(key, key)
    return key if key in STYLE_PROFILES else "narrative_basic"

def _style_contract(style):
    key = _canonical_style_id(style)
    profile = STYLE_PROFILES[key]
    hard_outline = _style_outline_instruction(key, "medium")
    return (
        profile["contract"] + " "
        + hard_outline + " "
        "This style must be visible on the page through prose rhythm, subsection names, and takeaway framing. "
        "Do not merely write a generic summary with a style label attached. "
        "Never mention the style name in the final output. Preserve the source facts and the required summary format."
    )

def _style_expected_headings(style):
    return list(STYLE_PROFILES[_canonical_style_id(style)].get("chapter_headings", []))

def _style_headings_for_tier(style, summary_tier="medium"):
    """Return the exact H2 headings that must be visibly present for a style.

    v47 makes style application structural, not just tonal. Mini/quick outputs
    use three headings so the style is visible without wasting too much page
    budget; longer outputs may use all four.
    """
    key = _canonical_style_id(style)
    if key == "narrative_basic":
        return []
    headings = _style_expected_headings(key)
    tier = str(summary_tier or "medium").strip().lower()
    n = 3 if tier in ("mini", "small", "quick", "compact") else 4
    return headings[:max(2, min(n, len(headings)))]

def _style_outline_instruction(style, summary_tier="medium"):
    key = _canonical_style_id(style)
    if key == "narrative_basic":
        return (
            "Use natural, book-like H2 subsection headings that help the reader follow the argument. "
            "Do not create stiff labels or bullet-dump sections."
        )
    headings = _style_headings_for_tier(key, summary_tier)
    if not headings:
        return ""
    heading_text = "; ".join(f"## {h}" for h in headings)
    return (
        "HARD STYLE STRUCTURE: after the # chapter heading, include these H2 headings exactly and in this order before ### Key Takeaways: "
        f"{heading_text}. "
        "Keep them compact if the chapter is short, but do not replace them with generic headings such as Overview, Summary, Main Ideas, or Analysis. "
        "The selected style must be obvious to a reader just by scanning the chapter headings and first paragraphs."
    )

def _style_signal_details_for_markdown(markdown_text, style, summary_tier="medium"):
    key = _canonical_style_id(style)
    if key == "narrative_basic":
        return {"score": 1.0, "heading_hits": [], "missing_headings": [], "signal_hits": [], "required_headings": []}
    text = str(markdown_text or "")
    low = text.lower()
    required = _style_headings_for_tier(key, summary_tier)
    rendered_headings = []
    for m in re.finditer(r"^#{2,3}\s+(.+?)\s*$", text, flags=re.MULTILINE):
        rendered_headings.append(re.sub(r"[^a-z0-9]+", "", m.group(1).strip().lower()))
    heading_hits = []
    missing = []
    for h in required:
        hn = re.sub(r"[^a-z0-9]+", "", h.lower())
        if hn in rendered_headings or f"## {h.lower()}" in low:
            heading_hits.append(h)
        else:
            missing.append(h)
    signals = STYLE_PROFILES[key].get("signals", [])
    signal_hits = [sig for sig in signals if sig and sig.lower() in low]
    required_floor = max(2, min(3, len(required)))
    heading_component = min(1.0, len(heading_hits) / max(1, required_floor))
    signal_component = min(1.0, len(signal_hits) / 2.0) if signals else 0.0
    score = min(1.0, 0.82 * heading_component + 0.18 * signal_component)
    return {
        "score": score,
        "heading_hits": heading_hits,
        "missing_headings": missing,
        "signal_hits": signal_hits,
        "required_headings": required,
    }

def _style_signal_score_for_markdown(markdown_text, style):
    return _style_signal_details_for_markdown(markdown_text, style).get("score", 0.0)

def _split_prose_for_style_buckets(text, buckets):
    buckets = max(1, int(buckets or 1))
    text = re.sub(r"\n{3,}", "\n\n", str(text or "").strip())
    if not text:
        return [""] * buckets
    paras = [p.strip() for p in re.split(r"\n\s*\n", text) if p.strip()]
    if len(paras) >= buckets:
        out = [""] * buckets
        counts = [0] * buckets
        for p in paras:
            idx = counts.index(min(counts))
            out[idx] = (out[idx] + "\n\n" + p).strip() if out[idx] else p
            counts[idx] += len(p.split())
        return out
    if "_reader_sentence_split" in globals():
        sentences = _reader_sentence_split(text)
    else:
        sentences = re.split(r"(?<=[.!?])\s+", text)
    if not sentences:
        return [text] + [""] * (buckets - 1)
    per = max(1, math.ceil(len(sentences) / buckets))
    chunks = [" ".join(sentences[i:i+per]).strip() for i in range(0, len(sentences), per)]
    while len(chunks) < buckets:
        chunks.append("")
    return chunks[:buckets]

def _deterministic_apply_style_to_span(span_sections, style, summary_tier="medium"):
    """Last-resort structural style enforcement that does not require Claude.

    It preserves the H1 heading, source prose, and Key Takeaways, but remaps the
    prose under the style's required H2 headings. This guarantees the selected
    method is visible even if the model ignores the prompt or the live rewrite
    fails.
    """
    key = _canonical_style_id(style)
    if key == "narrative_basic" or not span_sections:
        return list(span_sections or [])
    required = _style_headings_for_tier(key, summary_tier)
    if not required:
        return list(span_sections or [])
    first = dict(span_sections[0])
    first["level"] = 1
    prose_parts = []
    takeaway_sections = []
    for idx, sec in enumerate(span_sections):
        heading = str(sec.get("heading", "") or "").strip()
        body = str(sec.get("body", "") or "").strip()
        if idx == 0:
            if body:
                prose_parts.append(body)
            continue
        lowh = heading.lower()
        if "takeaway" in lowh:
            takeaway_sections.append(dict(sec))
        elif lowh in ("practical application", "common mistake to avoid"):
            # v51 style-fix: drop generic appendices when forcing a non-basic style; they
            # contradict the style's own fixed H2 structure.
            continue
        else:
            if heading and not any(_norm_title_key(heading) == _norm_title_key(h) for h in required):
                prose_parts.append(f"{heading}. {body}".strip())
            elif body:
                prose_parts.append(body)
    prose = "\n\n".join(p for p in prose_parts if p).strip()
    chunks = _split_prose_for_style_buckets(prose, len(required))
    first["body"] = ""
    out = [first]
    for h, chunk in zip(required, chunks):
        if not chunk.strip():
            chunk = "This part of the chapter reinforces the source argument in a style-specific frame while preserving the original meaning."
        out.append({
            "level": 2,
            "heading": h,
            "body": chunk.strip() + "\n",
            "research_score": first.get("research_score"),
            "research_reason": first.get("research_reason", ""),
            "special": False,
        })
    if takeaway_sections:
        ta = dict(takeaway_sections[0])
        ta["level"] = 3
        ta["heading"] = "Key Takeaways"
        out.append(ta)
    return out

def _section_span_markdown(sections, start, end):
    return "\n".join(_section_to_markdown(s) for s in sections[start:end]).strip()

def _chapter_spans_for_style(sections):
    h1s = [i for i, s in enumerate(sections or []) if int(s.get("level", 1) or 1) == 1]
    spans = []
    for pos, start in enumerate(h1s):
        end = h1s[pos + 1] if pos + 1 < len(h1s) else len(sections)
        spans.append((start, end))
    return spans

def _rewrite_span_in_style(ai_client, span_md, book_title, style, style_desc, job_id, max_words):
    profile = STYLE_PROFILES[_canonical_style_id(style)]
    heading_list = ", ".join(profile.get("chapter_headings", [])[:4])
    prompt = (
        f'Rewrite the following generated summary section from "{book_title}" so the selected style is unmistakable on the page.\n\n'
        f'{style_desc}\n\n'
        f'STYLE VISIBILITY REQUIREMENTS:\n'
        f'- Preserve the same # chapter heading and all source facts.\n'
        f'- Use the following H2 headings EXACTLY and in this order before Key Takeaways: {heading_list}.\n'
        f'- Keep the required ### Key Takeaways section.\n'
        f'- All bullets must be complete sentences.\n'
        f'- Keep the same approximate length, no more than {max_words} words.\n'
        f'- Do not add unsupported facts or decorative language.\n'
        f'- Do not use generic headings like Overview, Summary, Analysis, or Main Ideas.\n'
        f'- Return ONLY markdown for the rewritten section.\n\n'
        f'Original generated section:\n{span_md[:11000]}'
    )
    text = _call_claude_full(
        ai_client, prompt,
        max_tokens=min(MAX_OUT_TOKENS_PER_CALL, int(max_words * 2.2) + 1200),
        job_id=job_id,
        max_continuations=1,
    ).strip()
    parsed = parse_sections(text)
    if not parsed or not any(int(s.get("level", 1) or 1) == 1 for s in parsed):
        return None
    return parsed

def _style_application_gate(sections, ai_client, book_title, style, style_desc, job_id, summary_tier="medium"):
    """Ensure selected style is visibly applied to every body chapter.

    v47 makes this fail-safe. First, it scores each chapter for required
    style-specific H2 headings. If the score is weak, it asks Claude to rewrite
    the span when possible. If Claude is unavailable, fails, or still returns a
    generic section, the app deterministically remaps the chapter prose under
    the required style headings. This is the important difference from v46: the
    selected method cannot silently collapse back into Narrative Basic.
    """
    if not STYLE_AUDIT_ENABLED:
        return sections
    key = _canonical_style_id(style)
    if key == "narrative_basic" and STYLE_AUDIT_SKIP_BASIC:
        return sections
    result = list(sections or [])
    rewrites = 0
    forced = 0
    spans = _chapter_spans_for_style(result)
    idx = 0
    while idx < len(spans):
        start, end = spans[idx]
        if start >= len(result):
            idx += 1
            continue
        if result[start].get("special"):
            idx += 1
            continue
        md = _section_span_markdown(result, start, end)
        details = _style_signal_details_for_markdown(md, key, summary_tier=summary_tier)
        score = float(details.get("score", 0.0))
        if score >= STYLE_AUDIT_MIN_SCORE:
            _audit_event(job_id, "style_gate_pass", style=key, heading=result[start].get("heading", ""), score=round(score, 3), heading_hits=details.get("heading_hits", []))
            idx += 1
            continue

        parsed = None
        if ai_client is not None and STYLE_AI_REWRITE and rewrites < STYLE_AUDIT_MAX_REWRITES:
            try:
                max_words = max(650, int(_count_words(md) * 1.12) + 120)
                parsed = _rewrite_span_in_style(ai_client, md, book_title, key, style_desc, job_id, max_words=max_words)
                if parsed:
                    for sec in parsed:
                        sec["special"] = False
                    post_md = "\n".join(_section_to_markdown(sec) for sec in parsed)
                    post_details = _style_signal_details_for_markdown(post_md, key, summary_tier=summary_tier)
                    post_score = float(post_details.get("score", 0.0))
                    if post_score >= STYLE_AUDIT_MIN_SCORE:
                        result = result[:start] + parsed + result[end:]
                        rewrites += 1
                        _audit_event(job_id, "style_rewrite_applied", style=key, heading=result[start].get("heading", ""), before_score=round(score, 3), after_score=round(post_score, 3), heading_hits=post_details.get("heading_hits", []))
                        spans = _chapter_spans_for_style(result)
                        idx += 1
                        continue
                    _audit_event(job_id, "style_rewrite_still_weak", style=key, heading=result[start].get("heading", ""), before_score=round(score, 3), after_score=round(post_score, 3), missing=post_details.get("missing_headings", []))
            except Exception as e:
                _audit_event(job_id, "style_rewrite_failed", style=key, heading=result[start].get("heading", ""), error=f"{type(e).__name__}: {e}")

        base_span = parsed if parsed else result[start:end]
        forced_span = _deterministic_apply_style_to_span(base_span, key, summary_tier=summary_tier)
        result = result[:start] + forced_span + result[end:]
        forced += 1
        after_md = _section_span_markdown(result, start, start + len(forced_span))
        after_details = _style_signal_details_for_markdown(after_md, key, summary_tier=summary_tier)
        _audit_event(job_id, "style_forced_structural_apply", style=key, heading=result[start].get("heading", ""), before_score=round(score, 3), after_score=round(float(after_details.get("score", 0.0)), 3), heading_hits=after_details.get("heading_hits", []), missing_before=details.get("missing_headings", []))
        spans = _chapter_spans_for_style(result)
        idx += 1
    if rewrites or forced:
        _audit_event(job_id, "style_application_gate_done", style=key, rewritten=rewrites, forced=forced)
    return result

def _build_faithfulness_note(book_title, document_mode="book"):
    title = str(book_title or "the uploaded source")
    if document_mode == "report":
        body = (
            "This summary was generated from the uploaded source file. It is designed to preserve the source's structure, major claims, figures, recommendations, and caveats, but it is not a substitute for the original report. It should not be treated as investment, legal, tax, medical, or professional advice.\n"
        )
    else:
        body = (
            "This summary was generated from the uploaded source file. It is designed to preserve the source's structure, major arguments, examples, and practical takeaways, but it is not a substitute for the original work.\n"
        )
    return {"level": 1, "heading": "Faithfulness Note", "body": body, "research_score": None, "research_reason": "", "special": True}

def _prepend_executive_summary(sections, ai_client, book_title, job_id, summary_tier="medium", style_desc="", instructions=""):
    if not OUTPUT_EXECUTIVE_SUMMARY:
        return sections
    if any(_norm_title_key(s.get("heading", "")) == "executivesummary" for s in sections if s.get("level") == 1):
        return sections
    sample = "\n\n".join(_section_to_markdown(s) for s in sections[:min(10, len(sections))])[:9000]
    prompt = (
        f'Write a concise executive summary for "{book_title}" based on the generated chapter summaries below.\n'
        f'Write the prose within the fixed headings below in this style — tone, voice, and emphasis must reflect it: {style_desc or "Clear, polished nonfiction summary style."}\n'
    )
    if instructions:
        prompt += f'Additional instructions: {instructions}\n'
    prompt += (
        f'Do not change the required headings (Core Thesis, Why It Matters, Main Ideas, What to Remember) and do not mention the style name.\n'
        f'Use natural paragraphs and source-specific bullets. No placeholders, no generic filler, and no clipped sentences.\n'
        f'Format exactly as:\n# Executive Summary\n'
        f'## Core Thesis\n2-3 sentences.\n'
        f'## Why It Matters\n2-3 sentences.\n'
        f'## Main Ideas\n- 4 to 6 bullets.\n'
        f'## What to Remember\n2-3 sentences.\n'
        f'Do not invent facts not supported by the summaries. Keep it compact because it is inside the page budget.\n\n'
        f'Summaries:\n{sample}'
    )
    try:
        text = _call_claude_full(ai_client, prompt, 1200, job_id, max_continuations=1).strip()
        parsed = parse_sections(text)
        if parsed and parsed[0].get("level") == 1:
            parsed[0]["special"] = True
            return parsed + sections
    except Exception:
        pass
    fallback = {
        "level": 1,
        "heading": "Executive Summary",
        "body": "This summary distills the source into its central thesis, major supporting ideas, and practical implications. The detailed chapter sections that follow preserve the source sequence and provide the supporting explanation.\n",
        "research_score": None,
        "research_reason": "",
        "special": True,
    }
    return [fallback] + sections

def _append_final_review_sheet(sections, ai_client, book_title, job_id, summary_tier="medium"):
    if not OUTPUT_FINAL_REVIEW_SHEET:
        return sections
    if any(_norm_title_key(s.get("heading", "")) == "finalreviewsheet" for s in sections if s.get("level") == 1):
        return sections
    sample = "\n\n".join(_section_to_markdown(s) for s in sections[-min(12, len(sections)):])[:9000]
    prompt = (
        f'Create a final review sheet for "{book_title}" based on the summary below.\n'
        f'Format exactly as:\n# Final Review Sheet\n'
        f'## The Whole Source in 10 Ideas\n- exactly 10 bullets.\n'
        f'## Most Actionable Lessons\n- 4 to 6 bullets.\n'
        f'## Common Traps to Avoid\n- 3 to 5 bullets.\n'
        f'## Questions to Remember\n- 3 to 5 reflective questions.\n'
        f'Be specific and source-grounded. Keep it compact.\n\nSummary:\n{sample}'
    )
    try:
        text = _call_claude_full(ai_client, prompt, 1800, job_id, max_continuations=1).strip()
        parsed = parse_sections(text)
        if parsed and parsed[0].get("level") == 1:
            parsed[0]["special"] = True
            return sections + parsed
    except Exception:
        pass
    fallback = {
        "level": 1,
        "heading": "Final Review Sheet",
        "body": "Use the chapter takeaways above as the primary review checklist. Revisit the Executive Summary for the core thesis and the Final Key Takeaways for the highest-level lessons.\n",
        "research_score": None,
        "research_reason": "",
        "special": True,
    }
    return sections + [fallback]


def _feynman_word_bounds():
    min_pages = max(1, int(FEYNMAN_MIN_PAGES or 3))
    max_pages = max(min_pages, int(FEYNMAN_MAX_PAGES or 5))
    target_pages = max(min_pages, min(max_pages, int(FEYNMAN_TARGET_PAGES or 4)))
    min_words = max(850, min_pages * max(250, FEYNMAN_WORDS_PER_PAGE))
    max_words = max(min_words + 200, max_pages * max(250, FEYNMAN_WORDS_PER_PAGE))
    target_words = max(min_words, min(max_words, target_pages * max(250, FEYNMAN_WORDS_PER_PAGE)))
    return min_words, max_words, target_words


def _should_add_feynman_storyline(requested_pages=0, detection_source="", source_format="pdf"):
    if not OUTPUT_FEYNMAN_STORYLINE:
        return False
    # The user asked for a book-learning aid. Skip GreenStreet/report-deck style
    # documents by default, but always allow EPUB because EPUBs are normally books.
    if str(source_format).lower() != "epub" and "page_title" in str(detection_source or ""):
        return False
    try:
        rp = int(requested_pages or 0)
    except Exception:
        rp = 0
    if rp and rp < max(1, FEYNMAN_MIN_SUMMARY_PAGES):
        return False
    return True


def _trim_sections_to_word_cap(sections, max_words):
    result = [dict(s) for s in sections]
    current = sum(_count_words(s.get("body", "")) for s in result)
    if current <= max_words or current <= 0:
        return result
    remaining = max(1, int(max_words))
    body_indices = [i for i, s in enumerate(result) if _count_words(s.get("body", "")) > 0]
    counts = {i: _count_words(result[i].get("body", "")) for i in body_indices}
    for pos, i in enumerate(body_indices):
        if pos == len(body_indices) - 1:
            budget = remaining
        else:
            budget = min(counts[i], int(max_words * counts[i] / current))
        result[i]["body"] = _trim_text_to_word_budget(result[i].get("body", ""), budget)
        remaining -= min(budget, counts[i])
        if remaining <= 0:
            # Drop remaining bodies while retaining headings.
            for j in body_indices[pos + 1:]:
                result[j]["body"] = ""
            break
    return result


def _append_feynman_storyline(sections, ai_client, book_title, job_id, requested_pages=0,
                              detection_source="", source_format="pdf", summary_tier="medium"):
    """Append a 3-5 page teach-back narrative using the Feynman method.

    This is intentionally a book-mode learning section, not a report appendix.
    It retells the whole source in simple language, in sequence, with bullets
    that a reader could use to explain the book to someone else.
    """
    if not _should_add_feynman_storyline(requested_pages, detection_source, source_format):
        return sections
    if any(_norm_title_key(s.get("heading", "")) in ("feynmanstorylinereview", "feynmanlearningstoryline", "feynmanteachback") for s in sections if s.get("level") == 1):
        return sections

    min_words, max_words, target_words = _feynman_word_bounds()
    real_sections = [s for s in sections if not _is_special_section(s)]
    # Use a balanced sample: beginning, middle, end, and chapter-level takeaways.
    h1s = _h1_spans(real_sections)
    selected = []
    if h1s:
        picks = sorted(set([0, len(h1s)//3, (2*len(h1s))//3, len(h1s)-1]))
        for pidx in picks:
            h1_idx, end_idx = h1s[pidx]
            selected.extend(real_sections[h1_idx:end_idx])
    sample_parts = []
    for sec in selected or real_sections[:12]:
        sample_parts.append(_section_to_markdown(sec))
    takeaways = []
    for sec in real_sections:
        if sec.get("level") == 3 and "takeaway" in str(sec.get("heading", "")).lower():
            takeaways.append(sec.get("body", ""))
    sample = ("\n\n".join(sample_parts) + "\n\nChapter takeaways:\n" + "\n".join(takeaways[:80]))[:18000]

    prompt = (
        f'Create a final learning section for "{book_title}" using the Feynman method. '\
        f'Explain the whole book as if teaching it to an intelligent friend who has not read it.\n\n'
        f'Format exactly as:\n# Feynman Storyline Review\n'
        f'## The Big Picture\nA simple-language overview.\n'
        f'## The Story of the Book\n- 12 to 18 narrative bullets that move from the beginning of the book to the end. Each bullet should explain one major idea in plain language and show how it connects to the next idea.\n'
        f'## Teach-Back Explanation\nA clear narrative explanation someone could say out loud to another person.\n'
        f'## What You Should Be Able to Explain\n- 6 to 10 bullets phrased as concepts the reader should now be able to teach.\n\n'
        f'LENGTH RULES:\n'
        f'- Write between {min_words} and {max_words} words. Target about {target_words} words.\n'
        f'- This should render as roughly {FEYNMAN_MIN_PAGES}-{FEYNMAN_MAX_PAGES} PDF pages.\n'
        f'- Use plain language, analogies, and connective explanations.\n'
        f'- Do not introduce unsupported facts. Do not quote long passages.\n'
        f'- This is a learning aid, not another chapter summary.\n\n'
        f'Source summary material:\n{sample}'
    )
    parsed = []
    try:
        text = _call_claude_full(
            ai_client, prompt,
            max_tokens=min(MAX_OUT_TOKENS_PER_CALL, int(max_words * 2.2) + 1200),
            job_id=job_id,
            max_continuations=1,
        ).strip()
        parsed = parse_sections(text)
        if not parsed or parsed[0].get("level") != 1:
            parsed = parse_sections("# Feynman Storyline Review\n\n" + text)
    except Exception:
        parsed = []

    if not parsed:
        # Last-resort deterministic shell. The AI path should normally be used;
        # this keeps the output structurally complete if a late API call fails.
        headings = [s.get("heading", "") for s in real_sections if s.get("level") == 1][:20]
        body = (
            "## The Big Picture\n"
            "This section is a teach-back review of the source. It restates the book in simple language so the reader can explain the argument to someone else.\n\n"
            "## The Story of the Book\n" + "\n".join(f"- The book develops the idea of {h}, then connects it to the next part of the argument." for h in headings) + "\n\n"
            "## Teach-Back Explanation\n"
            "A strong test of understanding is whether the reader can explain the source without hiding behind jargon. The sections above provide the detailed evidence; this review turns that evidence into a teachable storyline.\n\n"
            "## What You Should Be Able to Explain\n"
            "- The main problem the source is trying to solve.\n- The sequence of ideas the author uses to solve it.\n- The practical implications a reader should remember.\n"
        )
        parsed = [{"level": 1, "heading": "Feynman Storyline Review", "body": body, "research_score": None, "research_reason": "", "special": True}]

    for sec in parsed:
        sec["special"] = True
    current_words = sum(_count_words(s.get("body", "")) for s in parsed)
    if current_words < min_words and ai_client is not None:
        try:
            existing = "\n\n".join(_section_to_markdown(s) for s in parsed)
            extension_prompt = (
                f'The Feynman Storyline Review for "{book_title}" is too short at {current_words} words. '
                f'Add {min_words - current_words + 250} to {min_words - current_words + 650} words of new teach-back material.\n'
                f'Return ONLY additional prose and bullets to append under the same section. Use simple language and stay source-grounded.\n\nExisting section:\n{existing}\n\nSource material:\n{sample[:9000]}'
            )
            extra = _call_claude_full(ai_client, extension_prompt, 1800, job_id, max_continuations=1).strip()
            if extra:
                parsed[-1]["body"] = (parsed[-1].get("body", "").rstrip() + "\n\n" + extra + "\n")
        except Exception:
            pass
    current_words = sum(_count_words(s.get("body", "")) for s in parsed)
    if current_words > max_words:
        parsed = _trim_sections_to_word_cap(parsed, max_words)
    return sections + parsed


def _summary_of_summary_bounds(requested_pages=0):
    """Return (min_words, max_words, target_words) for the final recap."""
    try:
        rp = int(requested_pages or 0)
    except Exception:
        rp = 0
    target_pages = max(1, int(SUMMARY_OF_SUMMARY_TARGET_PAGES or 2))
    if rp and rp < max(1, SUMMARY_OF_SUMMARY_MIN_PAGES):
        target_pages = 1
    target_words = max(420, target_pages * max(250, SUMMARY_OF_SUMMARY_WORDS_PER_PAGE))
    min_words = max(330, int(target_words * 0.73))
    max_words = max(min_words + 120, int(target_words * 1.18))
    return min_words, max_words, target_words


def _should_add_summary_of_summary(requested_pages=0, detection_source="", source_format="pdf"):
    return bool(OUTPUT_SUMMARY_OF_SUMMARY)


def _summary_of_summary_source_material(sections, max_chars=18000):
    """Build a balanced source from cleaned summary sections."""
    real_sections = [s for s in (sections or []) if not _is_special_section(s)]
    h1s = _h1_spans(real_sections)
    parts = []
    h1_headings = [real_sections[i].get("heading", "") for i, _ in h1s]
    if h1_headings:
        parts.append("Source structure:\n" + "\n".join(f"- {h}" for h in h1_headings[:120]))
    if h1s:
        pick_positions = []
        for frac in (0, 0.18, 0.36, 0.54, 0.72, 0.90, 1.0):
            idx = min(len(h1s) - 1, max(0, int(round((len(h1s) - 1) * frac))))
            if idx not in pick_positions:
                pick_positions.append(idx)
        for idx in pick_positions:
            start, end = h1s[idx]
            chapter = real_sections[start:end]
            md = "\n\n".join(_section_to_markdown(x) for x in chapter)
            parts.append(md[:2600])
    else:
        parts.append("\n\n".join(_section_to_markdown(s) for s in real_sections[:12])[:max_chars])
    bullets = []
    for s in real_sections:
        if int(s.get("level", 1) or 1) == 3 and "takeaway" in str(s.get("heading", "")).lower():
            for line in str(s.get("body", "")).splitlines():
                st = line.strip()
                if st.startswith(("- ", "* ")):
                    b = re.sub(r"^[-*]\s*", "", st).strip()
                    if b and not _quality_is_placeholder(b) and not _quality_looks_incomplete(b):
                        bullets.append("- " + b)
                if len(bullets) >= 80:
                    break
        if len(bullets) >= 80:
            break
    if bullets:
        parts.append("Selected chapter takeaways:\n" + "\n".join(bullets))
    return "\n\n".join(parts)[:max_chars]


def _build_deterministic_summary_of_summary(sections, book_title, requested_pages=0):
    """Fallback final recap that never uses placeholders."""
    min_words, max_words, target_words = _summary_of_summary_bounds(requested_pages)
    real_sections = [s for s in (sections or []) if not _is_special_section(s)]
    h1s = _h1_spans(real_sections)
    headings = [real_sections[i].get("heading", "") for i, _ in h1s]
    candidates = []
    seen = set()
    for sec in real_sections:
        for sent in _quality_sentence_candidates(sec.get("body", ""), cap=8):
            key = _quality_unit_key(sent)
            if key and key not in seen:
                seen.add(key)
                candidates.append(sent)
            if len(candidates) >= 70:
                break
        if len(candidates) >= 70:
            break
    title = clean_title(book_title or "the source")
    first = candidates[0] if candidates else f"{title} develops a connected argument through its major sections and chapters."
    second = candidates[1] if len(candidates) > 1 else "The detailed summary above preserves the source sequence while condensing the main evidence and conclusions."
    arc = []
    for h in headings[:14]:
        clean_h = _normalize_source_chapter_heading(h)
        if clean_h and not _is_source_boilerplate_heading(clean_h):
            arc.append(f"- {clean_h}: this part advances the source's central storyline and supplies evidence for the larger argument.")
    if len(headings) > 14:
        arc.append("- Later sections: the remaining chapters complete the argument, test the earlier claims, and show the consequences of the source's central ideas.")
    lessons = []
    for sent in candidates[2:18]:
        short = _truncate_words_preserving_sentence(sent, 28)
        if short and not _quality_looks_incomplete(short):
            lessons.append("- " + short)
        if len(lessons) >= 8:
            break
    if len(lessons) < 4:
        lessons.extend([
            "- Focus on the causal chain: what starts the problem, what allows it to grow, and what finally exposes or resolves it.",
            "- Retain the difference between surface events and the deeper system that makes those events possible.",
            "- Use the chapter summaries above as evidence, not as isolated facts.",
            "- The source matters most when its pattern can be applied beyond the specific examples it describes.",
        ])
    body = (
        "## The Whole Summary in Plain English\n"
        f"{first} {second} The shortest useful way to remember the summary is to follow the chain of cause, mechanism, consequence, and lesson: the source introduces a central problem, shows the conditions that let it grow, traces the decisions or institutions that sustain it, and closes by revealing what the reader should now understand differently.\n\n"
        "## The Storyline to Retain\n"
        + "\n".join(arc[:18] or ["- The source moves from setup to development to consequence, using each chapter to deepen the central argument."]) + "\n\n"
        "## The Main Points to Carry Forward\n"
        + "\n".join(lessons[:8]) + "\n\n"
        "## The Final Memory Hook\n"
        f"When explaining {title} to someone else, do not list chapters mechanically. Explain the pattern: what the source says is happening, why it happens, who or what enables it, what changes as the story or argument develops, and what warning or lesson remains at the end. That pattern is the real value of the summary.\n"
    )
    current = _count_words(body)
    extra_idx = 18
    while current < min_words and extra_idx < len(candidates):
        addition = candidates[extra_idx]
        extra_idx += 1
        if addition and not _quality_looks_incomplete(addition):
            body += "\n" + addition
            current = _count_words(body)

    if current < min_words:
        # Last-resort enrichment for API-failure/offline runs. This is deliberately
        # source-structure based, not placeholder text. It explains how to use the
        # recap and why the chapter arc matters.
        body += (
            "\n\n## How the Pieces Fit Together\n"
            "The useful way to read the summary is not as a pile of separate chapter notes but as one connected argument. "
            "The opening sections establish the problem, the middle sections show the mechanism that lets the problem grow, and the closing sections reveal the consequences, costs, or corrective insight. "
            "That sequence matters because it turns isolated facts into a usable mental model. When the details start to blur, return to the chapter headings and ask what each one contributed to the overall movement of the source.\n\n"
            "The reader should also separate examples from principles. Examples make the source memorable, but the principles are what travel beyond the book: the incentives, blind spots, habits, systems, or choices that explain why the events unfolded as they did. "
            "A good retelling therefore begins with the central problem, then names the forces that amplified it, then shows the turning points where the logic became visible. "
            "This recap is meant to make that retelling easier without replacing the richer chapter summaries above.\n\n"
            "Finally, use the summary as a hierarchy. The executive summary gives the thesis; the chapter summaries provide evidence and sequence; the chapter takeaways identify local lessons; this final recap reconnects the pieces into one compact memory structure. "
            "If you can explain that structure clearly to someone else, you have retained the source's main value rather than merely remembering scattered facts.\n\n"
            "A second pass through the recap should answer four questions. First, what is the source really about beneath the surface plot or topic? Second, what recurring mechanism explains the events or arguments? Third, which characters, institutions, technologies, incentives, or assumptions keep that mechanism alive? Fourth, what changes by the end that makes the reader understand the opening problem differently? These questions turn the summary into active understanding rather than passive recall.\n\n"
            "The final test is compression without distortion. A weak retelling names too many facts and loses the point; a strong retelling keeps the spine of the argument intact. The strongest memory of the source should therefore be a clean chain: setup, pressure, escalation, turning point, consequence, and lesson. Keep that chain in mind, then return to the chapters above whenever you need the supporting evidence.\n"
        )
    if _count_words(body) > max_words:
        body = _trim_text_to_word_budget(body, max_words)
    return {"level": 1, "heading": "Summary of the Summary", "body": body, "research_score": None, "research_reason": "", "special": True}


def _append_summary_of_summary(sections, ai_client, book_title, job_id, requested_pages=0,
                               detection_source="", source_format="pdf", summary_tier="medium", style_desc=""):
    """Append one strong final recap instead of multiple weak final sections."""
    if not _should_add_summary_of_summary(requested_pages, detection_source, source_format):
        return sections
    existing_keys = {_norm_title_key(s.get("heading", "")) for s in sections if s.get("level") == 1}
    if "summaryofthesummary" in existing_keys or "summaryofsummary" in existing_keys:
        return sections
    min_words, max_words, target_words = _summary_of_summary_bounds(requested_pages)
    sample = _summary_of_summary_source_material(sections)
    prompt = (
        f'Create ONE final section for "{book_title}" called "Summary of the Summary". '
        f'This replaces all Feynman/final-review/final-takeaway appendices. It must read like a polished two-page recap of the entire generated summary, not a generic learning aid.\n'
        f'Write the prose within the fixed headings below in this style — tone, voice, and emphasis must reflect it: {style_desc or "Clear, polished nonfiction recap style."}\n'
        f'Do not change the required headings and do not mention the style name.\n\n'
        f'Format exactly as:\n# Summary of the Summary\n'
        f'## The Whole Summary in Plain English\n2-4 coherent paragraphs.\n'
        f'## The Storyline to Retain\n- 8 to 12 bullets that move through the source from beginning to end.\n'
        f'## The Main Points to Carry Forward\n- 6 to 8 specific bullets.\n'
        f'## The Final Memory Hook\n1-2 paragraphs explaining how to remember the whole source.\n\n'
        f'LENGTH RULES:\n'
        f'- Write between {min_words} and {max_words} words; target about {target_words} words.\n'
        f'- This should render as roughly {1 if target_words < 700 else 2} PDF page(s).\n'
        f'- Be source-grounded and specific. No placeholders. No generic bullets. No repeated paragraphs.\n'
        f'- Do not introduce unsupported facts, and do not quote long passages.\n'
        f'- End on a complete sentence.\n\n'
        f'Source summary material:\n{sample}'
    )
    parsed = []
    if ai_client is not None:
        try:
            text = _call_claude_full(
                ai_client, prompt,
                max_tokens=min(MAX_OUT_TOKENS_PER_CALL, int(max_words * 2.25) + 1200),
                job_id=job_id,
                max_continuations=1,
            ).strip()
            parsed = parse_sections(text)
            if not parsed or parsed[0].get("level") != 1:
                parsed = parse_sections("# Summary of the Summary\n\n" + text)
        except Exception as e:
            _audit_event(job_id, "summary_of_summary_ai_failed", error=f"{type(e).__name__}: {e}")
    if not parsed:
        fallback = _build_deterministic_summary_of_summary(sections, book_title, requested_pages)
        parsed = parse_sections(_section_to_markdown(fallback))
    for sec in parsed:
        sec["special"] = True
    first_h1 = next((i for i, s in enumerate(parsed) if int(s.get("level", 1) or 1) == 1), 0)
    parsed = parsed[first_h1:]
    if parsed:
        parsed[0]["heading"] = "Summary of the Summary"
    wc = sum(_count_words(s.get("body", "")) for s in parsed)
    if wc > max_words:
        parsed = _trim_sections_to_word_cap(parsed, max_words)
    return list(sections) + parsed


def _remove_deprecated_final_sections(sections):
    """Remove the old weak final appendices before adding the new recap."""
    deprecated = {
        "finalkeytakeaways", "booklevelkeytakeaways", "booklevelkeytakeaways",
        "overallkeytakeaways", "summarykeytakeaways", "feynmanstorylinereview",
        "feynmanlearningstoryline", "feynmanteachback", "finalreviewsheet",
        "twopagerecap",
    }
    out = []
    i = 0
    while i < len(sections or []):
        sec = sections[i]
        try:
            lvl = int(sec.get("level", 1) or 1)
        except Exception:
            lvl = 1
        key = _norm_title_key(sec.get("heading", ""))
        if lvl == 1 and key in deprecated:
            i += 1
            while i < len(sections):
                try:
                    nlvl = int(sections[i].get("level", 1) or 1)
                except Exception:
                    nlvl = 1
                if nlvl == 1:
                    break
                i += 1
            continue
        out.append(sec)
        i += 1
    return out


def _append_before_summary_of_summary(sections, new_sections):
    """Append new sections, but keep Summary of the Summary as the final H1."""
    base = list(sections or [])
    additions = list(new_sections or [])
    for i, sec in enumerate(base):
        try:
            lvl = int(sec.get("level", 1) or 1)
        except Exception:
            lvl = 1
        if lvl == 1 and _norm_title_key(sec.get("heading", "")) in ("summaryofthesummary", "summaryofsummary"):
            return base[:i] + additions + base[i:]
    return base + additions

def _insert_faithfulness_note(sections, book_title, detection_source=""):
    if not OUTPUT_FAITHFULNESS_NOTE:
        return sections
    if any(_norm_title_key(s.get("heading", "")) in ("faithfulnessnote", "sourcenote") for s in sections if s.get("level") == 1):
        return sections
    mode = "report" if "page_title" in str(detection_source or "") else "book"
    note = _build_faithfulness_note(book_title, mode)
    # Place after Executive Summary when present, otherwise at the front.
    insert_at = 1 if sections and _is_special_section(sections[0]) and _norm_title_key(sections[0].get("heading", "")) == "executivesummary" else 0
    return sections[:insert_at] + [note] + sections[insert_at:]


# ── G6: Chapter summarizer (parallel-safe) ────────────────────────────────────
def _summarize_chapter(ai_client, i, chapter, total_chapters, book_title,
                       instructions, style_desc, target_words, max_tokens, job_id,
                       summary_tier="medium", style="narrative_basic"):
    """Summarize one chapter; returns (index, summary, rs, rr, ch_title)."""
    title_label = chapter["title"]
    part_info   = (f" (Part {chapter['part']} of {chapter['n_parts']})"
                   if chapter["n_parts"] > 1 else "")
    summary_tier = str(summary_tier or "medium").lower()
    bullets_required = _tier_takeaway_count(summary_tier)

    # v51 style-fix: when a non-basic style is selected, the style's exact H2 headings are
    # the chapter structure. The legacy generic "Practical Application" /
    # "Common Mistake" appendices and the "use subsections only where they help"
    # guidance both fight the style, so they are suppressed for styled output.
    style_key = _canonical_style_id(style)
    is_styled = style_key != "narrative_basic"
    style_headings = _style_headings_for_tier(style_key, summary_tier) if is_styled else []

    practical_rule = ""
    if OUTPUT_CHAPTER_PRACTICAL and summary_tier in ("medium", "large") and not is_styled:
        practical_rule = (
            f"5. After Key Takeaways, add exactly two compact sections:\n"
            f"   ### Practical Application\n"
            f"   One short paragraph or 1-2 bullets explaining how to use this chapter.\n"
            f"   ### Common Mistake to Avoid\n"
            f"   One short paragraph or 1 bullet warning against a likely misreading.\n"
        )

    if is_styled:
        heading_text = "; ".join(f"## {h}" for h in style_headings)
        subsection_rule = (
            f"2. STRUCTURE IS FIXED BY THE STYLE. Use these EXACT H2 subsection "
            f"headings, in this order, between the # chapter heading and the "
            f"### Key Takeaways: {heading_text}. Do NOT rename, drop, merge, or "
            f"reorder them, and do NOT add generic headings such as Overview, "
            f"Summary, Main Ideas, Background, Context, or Analysis. Place the "
            f"chapter's content under whichever of these style headings fits "
            f"best, written fully in the selected style's voice. Cover the "
            f"chapter from start to finish. Use short, natural paragraphs "
            f"(2-4 sentences each); never one huge block of prose.\n"
        )
        paragraph_rule = (
            f"- Make the chapter easy to read in a PDF by separating ideas into "
            f"natural paragraphs under the fixed style headings above.\n\n"
        )
    else:
        subsection_rule = (
            f"2. Use `## [subsection name]` for major subsections, `### [detail name]` for finer "
            f"breakdowns. Cover the chapter from start to finish — opening through "
            f"closing arguments. Use short, natural paragraphs: generally 2-4 sentences per paragraph. "
            f"Never return a huge single block of prose.\n"
        )
        paragraph_rule = (
            f"- Make the chapter easy to read in a PDF: separate ideas into natural paragraphs, "
            f"and use subsection headings only where they genuinely help navigation.\n\n"
        )

    prompt = (
        f'You are summarising chapter {i+1} of {total_chapters} of "{book_title}".\n'
        f'Chapter: "{title_label}"{part_info}\n\n'
        f"STYLE: {style_desc}\n"
        f"Apply this style throughout ALL prose — tone, voice, sentence rhythm, emphasis, and "
        f"subsection heading names. The required structural elements (# chapter heading, "
        f"## subsections, ### Key Takeaways) must be present, but both the writing voice AND "
        f"the names you choose for subsections must fully reflect the selected style. "
        f"If the style contract names exact H2 headings, you MUST use those exact H2 headings; "
        f"do not substitute generic headings such as Overview, Summary, Main Ideas, or Analysis. "
        f"The reader should be able to identify the selected method without seeing the dropdown.\n\n"
    )
    if instructions:
        prompt += f"Additional instructions: {instructions}\n\n"
    prompt += (
        f"STRICT FORMAT RULES (every rule is mandatory):\n"
        f"1. First line of your response: `# {title_label}`. Use EXACTLY this "
        f"heading — do NOT append phrases like 'Comprehensive Section Summary', "
        f"'Overview', or any other wrapper text. One '#', then the title.\n"
        f"{subsection_rule}"
        f"3. The chapter MUST include this subsection near the end:\n"
        f"   ### Key Takeaways\n"
        f"   Exactly {bullets_required} bullets, each as one complete sentence.\n"
        f"4. End every section on a complete sentence — NEVER trail off mid-thought.\n"
        f"{practical_rule}"
        f"6. Final line, after everything else:\n"
        f"   RESEARCH_SCORE: X/10 | one sentence reason\n"
        f"   (high = data/citations/studies; low = anecdotes/opinions)\n\n"
        f"LENGTH (this is the most important rule):\n"
        f"- Write a MINIMUM of {int(target_words * 0.88)} words and AT MOST "
        f"{int(target_words * SUMMARY_PROMPT_MAX_RATIO)} words of chapter prose (excludes takeaway "
        f"bullets and the SCORE line).\n"
        f"- If you find yourself wrapping up before {int(target_words * 0.88)} "
        f"words, KEEP GOING: add more detail, examples, supporting evidence, "
        f"secondary arguments, or analytical commentary drawn from the source.\n"
        f"- Do NOT compress the chapter to be efficient — the user picked this "
        f"length deliberately, but also do NOT exceed the maximum above.\n"
        f"- Do NOT pad with filler phrases — every sentence must advance the "
        f"summary.\n"
        f"{paragraph_rule}"
        f"Summary tier: {summary_tier}. Small summaries should be compact; medium and large summaries should be richer while respecting the word cap.\n"
        f"Do not add emoji, decorative dividers, invented quotations, or fictional dialogue. "
        f"Do not invent facts not present in the source text.\n"
        f"\nSOURCE TEXT FROM THE CHAPTER:\n{chapter['text']}"
    )

    continuation_hint = (
        f"Continue the summary of '{title_label}'. "
        f"Pick up exactly where you left off. Do not repeat headings already written."
    )

    try:
        if job_id in jobs:
            jobs[job_id]["last_update"] = time.time()
        summary = _call_claude_full(
            ai_client, prompt, max_tokens, job_id,
            continuation_hint=continuation_hint,
        )

        research_score  = 5
        research_reason = ""
        lines       = summary.splitlines()
        clean_lines = []
        for line in lines:
            m = re.match(r"RESEARCH_SCORE:\s*(\d+)/10\s*\|\s*(.+)", line.strip())
            if m:
                research_score  = max(1, min(10, int(m.group(1))))
                research_reason = m.group(2).strip()
            else:
                clean_lines.append(line)
        summary = "\n".join(clean_lines).strip()
        summary = f"<!--RSCORE:{research_score}|{research_reason}-->\n" + summary

        ch_title = title_label
        for line in clean_lines:
            m = re.match(r"^#\s+(.*)", line)
            if m:
                ch_title = m.group(1).strip()
                break

        return (i, summary, research_score, research_reason, ch_title)

    except Exception as e:
        log_path = os.path.join(TMP_DIR, "summarize_errors.log")
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(
                    f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] "
                    f"Chapter {i+1} '{title_label}': {e}\n{traceback.format_exc()}\n"
                )
        except Exception:
            pass
        raise


def _norm_title_key(s):
    """Stable key for fuzzy chapter-title matching."""
    return re.sub(r"[^a-z0-9]", "", str(s or "").lower())


def _title_tokens(s):
    return set(re.findall(r"[a-z0-9]+", str(s or "").lower()))


def _title_matches(a, b):
    """Conservative fuzzy match for detected chapter titles vs model headings."""
    # v51: when both headings carry explicit chapter numbers, the numbers must
    # match. This prevents Chapter 6 Part One from stealing Chapter 7 Part Two
    # simply because their subtitles share many tokens.
    an = _chapter_number_from_title(a)
    bn = _chapter_number_from_title(b)
    if an is not None and bn is not None and an != bn:
        return False
    ak = _norm_title_key(a)
    bk = _norm_title_key(b)
    if not ak or not bk:
        return False
    if ak == bk or ak in bk or bk in ak:
        return True
    at = _title_tokens(a)
    bt = _title_tokens(b)
    if not at or not bt:
        return False
    # For numbered headings require stronger overlap after the number gate.
    threshold = 0.72 if (an is not None or bn is not None) else 0.60
    return len(at & bt) / max(1, len(at)) >= threshold


def _is_special_h1_heading(heading):
    h = re.sub(r"\s+", " ", str(heading or "").strip().lower())
    if not h:
        return False
    specials = {
        "key takeaways",
        "faithfulness note",
        "source note",
        "final review sheet",
        "feynman storyline review",
        "feynman learning storyline",
        "feynman teach back",
        "final key takeaways",
        "book-level key takeaways",
        "book level key takeaways",
        "overall key takeaways",
        "summary key takeaways",
        "summary of the summary",
        "summary of summary",
        "two-page recap",
        "you might also like",
        "if you enjoyed this book",
    }
    return h in specials


def _is_special_section(sec):
    """Return True only for app-generated special sections or reserved final sections.

    Some source PDFs legitimately contain a chapter/slide titled "Executive
    Summary". In v20, generated sections carry special=True so a source
    Executive Summary remains a normal covered section instead of being
    mislabeled as front matter or excluded from audits.
    """
    if not isinstance(sec, dict):
        return False
    if bool(sec.get("special")):
        return True
    return _is_special_h1_heading(sec.get("heading", ""))


def _unique_expected_titles(chapter_chunks):
    titles = []
    seen = set()
    for chunk in chapter_chunks or []:
        title = str(chunk.get("title", "")).strip()
        key = _norm_title_key(title)
        if title and key and key not in seen:
            seen.add(key)
            titles.append(title)
    return titles


def _chapter_targets_from_chunks(chapter_chunks, target_words_per_chunk):
    """Return normalized title -> target words, scaled by chunk count per title."""
    counts = Counter()
    display = {}
    source_words = Counter()
    for chunk in chapter_chunks or []:
        title = str(chunk.get("title", "")).strip()
        key = _norm_title_key(title)
        if not key:
            continue
        counts[key] += 1
        source_words[key] += _count_words(chunk.get("text", ""))
        display.setdefault(key, title)
    return {
        key: {
            "title": display[key],
            "chunks": counts[key],
            "source_words": source_words[key],
            "target": max(MIN_CHAPTER_WORDS, int(target_words_per_chunk * counts[key])),
        }
        for key in counts
    }


def _rebalance_chapter_targets(chapter_targets, total_words):
    """Budget-first allocation across canonical chapters.

    Uses source length as the main allocator while preserving a small per-chapter
    floor. This makes long chapters naturally receive larger budgets and reduces
    the need for final compression.
    """
    if not chapter_targets:
        return chapter_targets
    total_words = max(1, int(total_words or 1))
    keys = list(chapter_targets.keys())
    floors = {}
    for k in keys:
        floors[k] = min(MIN_CHAPTER_WORDS, max(120, int(total_words / max(1, len(keys)) * 0.35)))
    floor_sum = sum(floors.values())
    source_total = sum(max(1, int(chapter_targets[k].get("source_words") or 0)) for k in keys)
    remaining = max(0, total_words - floor_sum)
    out = {}
    for k in keys:
        meta = dict(chapter_targets[k])
        share = max(1, int(meta.get("source_words") or 0)) / max(1, source_total)
        meta["target"] = max(120, floors[k] + int(remaining * share))
        out[k] = meta
    # Spend rounding remainder on largest source chapters.
    used = sum(m["target"] for m in out.values())
    remainder = max(0, total_words - used)
    if remainder:
        for k in sorted(keys, key=lambda x: int(out[x].get("source_words") or 0), reverse=True):
            add = min(80, remainder)
            out[k]["target"] += add
            remainder -= add
            if remainder <= 0:
                break
    return out


def _estimate_feasibility(total_pages, chapter_count, requested_pages, ocr_used=False):
    requested_pages = int(requested_pages or 0)
    chapter_count = int(chapter_count or 0)
    if requested_pages <= 0:
        return {"level": "good", "message": "Percent-based summary length selected.", "recommended_min_pages": None}
    # Minimum is intentionally conservative: each detected chapter/section needs
    # space for at least a heading, prose, and takeaways; add front/back reserve.
    min_coverage = max(3, _reserved_pages_for_fixed(requested_pages) + math.ceil(chapter_count * 0.55))
    if chapter_count >= 20:
        min_coverage = max(min_coverage, math.ceil(chapter_count * 0.80))
    if requested_pages >= min_coverage * 1.20:
        level = "good"
    elif requested_pages >= min_coverage:
        level = "tight"
    else:
        level = "not_recommended"
    msg = {
        "good": "The requested length should be feasible for the detected structure.",
        "tight": "The requested length is tight; the app may need compact chapter prose to preserve coverage.",
        "not_recommended": "The requested length is probably too short to cover every detected section with key takeaways.",
    }[level]
    if ocr_used:
        msg += " OCR was required, so heading detection may be less reliable."
    return {
        "level": level,
        "message": msg,
        "recommended_min_pages": int(min_coverage),
        "detected_sections": chapter_count,
        "source_pages": int(total_pages or 0),
    }


def _section_to_markdown(sec):
    heading = sec.get("heading", "")
    level = max(1, min(6, int(sec.get("level", 1) or 1)))
    body = sec.get("body", "") or ""
    return ("#" * level) + " " + heading + "\n" + body


def _count_words(text):
    return len(re.findall(r"\b\w+(?:[-']\w+)*\b", str(text or "")))


def _h1_spans(sections, include_special=False):
    h1s = [i for i, s in enumerate(sections) if s.get("level") == 1]
    spans = []
    for pos, h1 in enumerate(h1s):
        heading = sections[h1].get("heading", "")
        if not include_special and _is_special_section(sections[h1]):
            continue
        end = h1s[pos + 1] if pos + 1 < len(h1s) else len(sections)
        spans.append((h1, end))
    return spans


def _find_span_for_title(sections, title):
    for h1_idx, end_idx in _h1_spans(sections):
        if _title_matches(title, sections[h1_idx].get("heading", "")):
            return h1_idx, end_idx
    return None


def _chapter_word_count(sections, h1_idx, end_idx, exclude_takeaways=True):
    total = 0
    for k in range(h1_idx, end_idx):
        s = sections[k]
        if exclude_takeaways and s.get("level") == 3 and "takeaway" in s.get("heading", "").lower():
            continue
        total += _count_words(s.get("body", ""))
    return total


def _has_takeaway_section(sections, h1_idx, end_idx, min_bullets=3):
    for k in range(h1_idx + 1, end_idx):
        s = sections[k]
        if s.get("level") == 3 and "takeaway" in s.get("heading", "").lower():
            bullets = [ln for ln in s.get("body", "").splitlines()
                       if ln.strip().startswith("-") or ln.strip().startswith("*")]
            if len(bullets) >= min_bullets:
                return True
    return False


def _has_h3_named_section(sections, h1_idx, end_idx, needle):
    needle = str(needle or "").lower()
    for k in range(h1_idx + 1, end_idx):
        s = sections[k]
        if s.get("level") == 3 and needle in str(s.get("heading", "")).lower() and str(s.get("body", "")).strip():
            return True
    return False

def _append_chapter_practical_sections(sections, h1_idx, end_idx, title):
    """Deterministic safety net for v20 chapter endings."""
    result = list(sections)
    inserts = []
    if not _has_h3_named_section(result, h1_idx, end_idx, "practical application"):
        inserts.append({
            "level": 3,
            "heading": "Practical Application",
            "body": "Use this chapter as a checklist for recognizing the pattern in concrete situations, then choose one small behavior to practice before trying to change the whole relationship or system at once.\n",
            "research_score": None,
            "research_reason": "",
        })
    if not _has_h3_named_section(result, h1_idx, end_idx, "common mistake"):
        inserts.append({
            "level": 3,
            "heading": "Common Mistake to Avoid",
            "body": "Do not reduce this chapter to a slogan; the useful insight depends on the specific evidence, limits, and examples summarized above.\n",
            "research_score": None,
            "research_reason": "",
        })
    if inserts:
        result = result[:end_idx] + inserts + result[end_idx:]
    return result


def _remove_takeaway_sections_from_span(sections, h1_idx, end_idx):
    """Remove H3 takeaway sections inside one H1 span; returns new sections."""
    out = []
    for idx, sec in enumerate(sections):
        if h1_idx < idx < end_idx and sec.get("level") == 3 and "takeaway" in sec.get("heading", "").lower():
            continue
        out.append(sec)
    return out


def _chapter_context(sections, h1_idx, end_idx, char_limit=8000):
    parts = [_section_to_markdown(sections[k]) for k in range(h1_idx, end_idx)]
    return "\n".join(parts)[:char_limit]


def _append_prose_before_takeaways(sections, h1_idx, end_idx, extra):
    """Append prose to the last non-takeaway section of a chapter."""
    if not extra or not extra.strip():
        return sections
    result = list(sections)
    insert_at = h1_idx
    for k in range(end_idx - 1, h1_idx - 1, -1):
        s = result[k]
        if s.get("level") == 3 and "takeaway" in s.get("heading", "").lower():
            continue
        insert_at = k
        break
    result[insert_at] = dict(result[insert_at])
    result[insert_at]["body"] = ((result[insert_at].get("body") or "").rstrip() + "\n\n" + extra.strip()).strip() + "\n"
    return result


# ── G2: Chapter audit (sequential, iterative) ────────────────────────────────
def _audit_sections(sections, ai_client, book_title, target_words_per_chapter,
                    job_id, instructions="", chapter_targets=None,
                    force_refresh_takeaway_keys=None, summary_tier="medium",
                    style="narrative_basic"):
    """Guarantee chapter-level sufficiency and key takeaways.

    chapter_targets is a mapping produced by _chapter_targets_from_chunks:
    normalized title -> {title, chunks, target}. When available, each chapter is
    audited against its own target, so a chapter split into three source chunks
    gets about three times the prose of a one-chunk chapter. This fixes the v9
    average-target bug that let long chapters end up under-summarized.
    """
    log_path = os.path.join(TMP_DIR, "audit.log")
    force_refresh_takeaway_keys = set(force_refresh_takeaway_keys or set())

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] {msg}\n")
        except Exception:
            pass

    def _fallback_targets(secs):
        out = {}
        for h1_idx, _end_idx in _h1_spans(secs):
            heading = secs[h1_idx].get("heading", "") or f"Chapter {len(out) + 1}"
            key = _norm_title_key(heading)
            if key:
                out[key] = {"title": heading, "chunks": 1, "target": target_words_per_chapter}
        return out

    def _extract_bullet_lines(text, max_items=TAKEAWAY_BULLETS):
        bullets = []
        for line in str(text or "").splitlines():
            st = line.strip()
            if st.startswith("- ") or st.startswith("* "):
                bullet = re.sub(r"^[\-*]\s+", "", st).strip()
                if bullet:
                    bullets.append(bullet)
            elif re.match(r"^\d+[.)]\s+", st):
                bullets.append(re.sub(r"^\d+[.)]\s+", "", st).strip())
        cleaned = []
        seen = set()
        for b in bullets:
            key = re.sub(r"[^a-z0-9]", "", b.lower())[:100]
            if key and key not in seen:
                seen.add(key)
                cleaned.append(b.rstrip(" .") + ".")
            if len(cleaned) >= max_items:
                break
        return cleaned

    result = list(sections)
    summary_tier = str(summary_tier or "medium").lower()
    bullets_required = _tier_takeaway_count(summary_tier)
    targets = dict(chapter_targets or {}) or _fallback_targets(result)
    if not targets:
        _log("audit skipped: no H1 chapters found")
        return result

    _log(f"audit start: chapters={len(targets)}, threshold={AUDIT_EXTEND_THRESHOLD:.2f}")

    for key, meta in targets.items():
        title = meta.get("title") or key
        target = max(MIN_CHAPTER_WORDS, int(meta.get("target") or target_words_per_chapter))
        floor = max(MIN_CHAPTER_WORDS, int(AUDIT_EXTEND_THRESHOLD * target))

        span = _find_span_for_title(result, title)
        if not span:
            _log(f"chapter '{title}': not present during audit; coverage step will handle")
            continue
        h1_idx, end_idx = span
        heading = result[h1_idx].get("heading", title) or title

        # (A) Takeaway guarantee. Multi-part chapters are refreshed because
        # their per-part takeaways may only describe the final source chunk.
        _check_job_control(job_id, "audit")
        refresh_takeaways = key in force_refresh_takeaway_keys or not _has_takeaway_section(
            result, h1_idx, end_idx, min_bullets=max(3, min(bullets_required, 4))
        )
        if refresh_takeaways:
            _log(f"chapter '{heading}': generating/refining key takeaways")
            ctx = _chapter_context(result, h1_idx, end_idx, char_limit=9000)
            ta_prompt = (
                f'Write a "### Key Takeaways" section for the chapter "{heading}" '
                f'from "{book_title}". Return exactly {bullets_required} bullets.\n'
                f'STRICT RULES:\n'
                f'- Start with exactly: ### Key Takeaways\n'
                f'- Each bullet starts with "- " and is one complete sentence.\n'
                f'- Each bullet must capture a distinct insight from THIS chapter.\n'
                f'- Do not use generic advice and do not mention other chapters.\n'
                f'- Return only that section.\n\n'
                f'Chapter summary to base the takeaways on:\n{ctx}'
            )
            try:
                ta_text = _call_claude_full(
                    ai_client, ta_prompt, max_tokens=900, job_id=job_id,
                    max_continuations=1,
                ).strip()
                bullets = _extract_bullet_lines(ta_text, max_items=bullets_required)
                if len(bullets) < 3:
                    _log(f"  -> takeaway response weak ({len(bullets)} bullets); keeping existing if any")
                else:
                    result = _remove_takeaway_sections_from_span(result, h1_idx, end_idx)
                    span = _find_span_for_title(result, title)
                    if not span:
                        _log("  -> span disappeared after takeaway removal; skipping insert")
                    else:
                        h1_idx, end_idx = span
                        ta_sec = {
                            "level": 3,
                            "heading": "Key Takeaways",
                            "body": "\n".join(f"- {b}" for b in bullets) + "\n",
                            "research_score": None,
                            "research_reason": "",
                        }
                        result = result[:end_idx] + [ta_sec] + result[end_idx:]
                        _log(f"  -> inserted {len(bullets)} key takeaways")
            except Exception as e:
                _log(f"  -> takeaway generation FAILED: {type(e).__name__}: {e}\n{traceback.format_exc()}")

        # (B) Word-count guarantee with iterative top-up.
        for round_n in range(AUDIT_MAX_ROUNDS):
            span = _find_span_for_title(result, title)
            if not span:
                break
            h1_idx, end_idx = span
            wc = _chapter_word_count(result, h1_idx, end_idx, exclude_takeaways=True)
            if wc >= floor:
                _log(f"chapter '{heading}': sufficient ({wc}/{target}, floor {floor})")
                break

            deficit = max(180, target - wc)
            request_words = min(max(deficit, 250), max(2500, int(target * 0.65)))
            _log(f"chapter '{heading}': short ({wc}/{target}, floor {floor}); round {round_n + 1}/{AUDIT_MAX_ROUNDS}, requesting +{request_words}")
            ctx = _chapter_context(result, h1_idx, end_idx, char_limit=10000)
            ext_prompt = (
                f'The chapter "{heading}" from "{book_title}" is under-summarized. '
                f'It currently has about {wc} prose words; the target is {target}.\n\n'
                f'Write about {request_words} ADDITIONAL words of substantive prose to append.\n'
                f'STRICT RULES:\n'
                f'- Output only new prose paragraphs. No headings, no bullets, no key takeaways.\n'
                f'- Do not repeat existing wording or recap generic points.\n'
                f'- Add concrete detail, examples, causal logic, distinctions, evidence, and implications already supported by the chapter summary.\n'
                f'- Match the existing style and end on a complete sentence.\n'
            )
            if instructions:
                ext_prompt += f'- Respect these user instructions: {instructions}\n'
            ext_prompt += f'\nExisting chapter summary:\n{ctx}'

            try:
                extra = _call_claude_full(
                    ai_client, ext_prompt,
                    max_tokens=min(MAX_OUT_TOKENS_PER_CALL, int(request_words * 2.8) + 1200),
                    job_id=job_id,
                    max_continuations=2,
                ).strip()
                extra_lines = []
                for ln in extra.splitlines():
                    stripped = ln.strip()
                    if not stripped:
                        extra_lines.append(ln)
                    elif stripped.startswith("#"):
                        continue
                    elif "key takeaway" in stripped.lower():
                        continue
                    else:
                        extra_lines.append(ln)
                extra = "\n".join(extra_lines).strip()
                added = _count_words(extra)
                if added <= 0:
                    _log(f"  -> round {round_n + 1}: no usable prose returned")
                    break
                result = _append_prose_before_takeaways(result, h1_idx, end_idx, extra)
                _log(f"  -> round {round_n + 1}: added {added} words")
                if added < 60:
                    _log(f"  -> round {round_n + 1}: yield too small; stopping chapter top-up")
                    break
            except Exception as e:
                _log(f"  -> extension FAILED: {type(e).__name__}: {e}\n{traceback.format_exc()}")
                break

    if OUTPUT_CHAPTER_PRACTICAL and summary_tier in ("medium", "large") and _canonical_style_id(style) == "narrative_basic":
        # Deterministic safety net: live model output is expected to include
        # these, but do not let a missing section survive the audit. v51 style-fix: only
        # for Narrative Basic — styled chapters carry their own fixed H2
        # structure, and these generic appendices fight the selected style.
        span_pos = 0
        while span_pos < len(_h1_spans(result)):
            spans_now = _h1_spans(result)
            h1_idx, end_idx = spans_now[span_pos]
            heading_now = result[h1_idx].get("heading", "")
            result = _append_chapter_practical_sections(result, h1_idx, end_idx, heading_now)
            span_pos += 1

    # Final pass: move chapter-ending sections to the end of their chapter spans
    # in a consistent order: Key Takeaways, Practical Application, Common Mistake.
    final = []
    last = 0
    spans = _h1_spans(result, include_special=True)
    for h1_idx, end_idx in spans:
        if last < h1_idx:
            final.extend(result[last:h1_idx])
        if _is_special_section(result[h1_idx]):
            final.extend(result[h1_idx:end_idx])
        else:
            ending_names = ("takeaway", "practical application", "common mistake")
            body_secs = []
            takes = []
            practical = []
            mistakes = []
            for k in range(h1_idx, end_idx):
                sec = result[k]
                hlow = str(sec.get("heading", "")).lower()
                if sec.get("level") == 3 and "takeaway" in hlow:
                    takes.append(sec)
                elif sec.get("level") == 3 and "practical application" in hlow:
                    practical.append(sec)
                elif sec.get("level") == 3 and "common mistake" in hlow:
                    mistakes.append(sec)
                else:
                    body_secs.append(sec)
            final.extend(body_secs)
            final.extend(takes[-1:] if takes else [])
            final.extend(practical[-1:] if practical else [])
            final.extend(mistakes[-1:] if mistakes else [])
        last = end_idx
    if last < len(result):
        final.extend(result[last:])
    return final


# ── G4c: Chapter coverage verification ────────────────────────────────────────
def _find_missing_chapter_chunks(sections, expected_chapter_titles, chapter_chunks):
    """Return all source chunks for expected chapters that have no H1 summary."""
    expected = expected_chapter_titles or _unique_expected_titles(chapter_chunks)
    if not expected:
        return []

    missing_keys = []
    for title in expected:
        if not _find_span_for_title(sections, title):
            key = _norm_title_key(title)
            if key and key not in missing_keys:
                missing_keys.append(key)

    if not missing_keys:
        return []

    out = []
    missing_set = set(missing_keys)
    for chunk in chapter_chunks or []:
        if _norm_title_key(chunk.get("title", "")) in missing_set:
            out.append(chunk)
    return out


def _verify_chapter_coverage(sections, expected_chapter_titles, ai_client,
                              chapter_chunks, book_title, instructions,
                              style_desc, target_words, max_tokens, job_id,
                              summary_tier="medium", style="narrative_basic"):
    """Re-summarize missing chapters repeatedly, then let caller fail closed if any remain."""
    log_path = os.path.join(TMP_DIR, "coverage.log")

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] {msg}\n")
        except Exception:
            pass

    expected = expected_chapter_titles or _unique_expected_titles(chapter_chunks)
    if not expected:
        return sections

    new_sections = list(sections)
    max_rounds = 4
    for round_n in range(1, max_rounds + 1):
        missing_chunks = _find_missing_chapter_chunks(new_sections, expected, chapter_chunks)
        if not missing_chunks:
            _log(f"Coverage OK after round {round_n - 1}: all {len(expected)} expected chapters present")
            return new_sections

        missing_titles = _unique_expected_titles(missing_chunks)
        _log(f"Coverage round {round_n}/{max_rounds}: missing {missing_titles}")
        added_any = False

        for title_key in [_norm_title_key(t) for t in missing_titles]:
            title_chunks = [c for c in missing_chunks if _norm_title_key(c.get("title", "")) == title_key]
            if not title_chunks:
                continue
            title = title_chunks[0].get("title", "Untitled chapter")
            _log(f"  -> Re-summarizing missing chapter: {title} ({len(title_chunks)} chunk(s))")
            chapter_summaries = []
            for chunk in title_chunks:
                try:
                    _, summary, _, _, _ = _summarize_chapter(
                        ai_client, len(chapter_summaries), chunk, len(title_chunks),
                        book_title, instructions, style_desc, target_words, max_tokens, job_id,
                        summary_tier=summary_tier, style=style
                    )
                    chapter_summaries.append(summary)
                except Exception as e:
                    _log(f"    -> Re-summarize FAILED for '{chunk.get('title', '')}': {type(e).__name__}: {e}\n{traceback.format_exc()}")

            if chapter_summaries:
                merged_text = _merge_multipart_summaries("\n\n".join(chapter_summaries))
                parsed = parse_sections(merged_text)
                if parsed and not any(s.get("level") == 1 for s in parsed):
                    parsed = parse_sections(f"# {title}\n\n{merged_text}")
                if parsed:
                    new_sections.extend(parsed)
                    added_any = True

        if not added_any:
            _log("Coverage recovery made no progress; stopping retries")
            break

    remaining = _find_missing_chapter_chunks(new_sections, expected, chapter_chunks)
    if remaining:
        _log(f"Coverage FAILED after retries: remaining {_unique_expected_titles(remaining)}")
    return new_sections


def _summary_prose_word_count(sections, chapter_targets=None):
    """Count prose words in real chapters, excluding takeaway bullets and special H1s."""
    total = 0
    if chapter_targets:
        for meta in chapter_targets.values():
            span = _find_span_for_title(sections, meta.get("title", ""))
            if span:
                total += _chapter_word_count(sections, span[0], span[1], exclude_takeaways=True)
        return total
    for h1_idx, end_idx in _h1_spans(sections):
        total += _chapter_word_count(sections, h1_idx, end_idx, exclude_takeaways=True)
    return total


def _source_excerpt_for_title(chapter_chunks, title, char_limit=12000):
    key = _norm_title_key(title)
    text = "\n\n".join(
        (chunk.get("text") or "") for chunk in (chapter_chunks or [])
        if _norm_title_key(chunk.get("title", "")) == key
    ).strip()
    if not text:
        return ""
    if len(text) <= char_limit:
        return text
    third = max(1000, char_limit // 3)
    mid = len(text) // 2
    return (
        text[:third]
        + "\n\n[... middle excerpt ...]\n\n"
        + text[max(0, mid - third // 2):min(len(text), mid + third // 2)]
        + "\n\n[... final excerpt ...]\n\n"
        + text[-third:]
    )


def _expand_summary_to_word_target(sections, ai_client, book_title, chapter_chunks,
                                   chapter_targets, target_total_words, job_id,
                                   instructions="", max_rounds=None):
    """Expand chapters until the prose word target is reached or progress stalls."""
    log_path = os.path.join(TMP_DIR, "length_enforcement.log")
    max_rounds = LENGTH_ENFORCE_MAX_ROUNDS if max_rounds is None else max_rounds

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] {msg}\n")
        except Exception:
            pass

    result = list(sections)
    target_total_words = max(0, int(target_total_words or 0))
    if target_total_words <= 0:
        return result

    if not chapter_targets:
        chapter_targets = {}
        spans = _h1_spans(result)
        per = max(MIN_CHAPTER_WORDS, target_total_words // max(1, len(spans)))
        for h1_idx, _end_idx in spans:
            heading = result[h1_idx].get("heading", "")
            key = _norm_title_key(heading)
            if key:
                chapter_targets[key] = {"title": heading, "chunks": 1, "target": per}

    # v27: the caller may ask for a higher total word target during page-floor
    # enforcement than the original per-chapter budget. Scale effective chapter
    # targets upward so long/short-output expansion can actually reach the new
    # PDF page floor instead of repeatedly adding only tiny fragments.
    chapter_targets = {k: dict(v) for k, v in (chapter_targets or {}).items()}
    target_sum = sum(max(0, int(meta.get("target") or 0)) for meta in chapter_targets.values())
    if target_sum > 0 and target_sum < target_total_words:
        scale = target_total_words / max(1, target_sum)
        for meta in chapter_targets.values():
            base = max(0, int(meta.get("target") or 0))
            meta["target"] = max(base, int(base * scale))
        _log(f"scaled expansion targets upward: target_sum={target_sum}, target_total={target_total_words}, scale={scale:.3f}")

    floor_total = int(target_total_words * LENGTH_ENFORCE_MIN_RATIO)
    for round_n in range(1, max_rounds + 1):
        current_total = _summary_prose_word_count(result, chapter_targets)
        if current_total >= floor_total:
            _log(f"word target OK after round {round_n - 1}: {current_total}/{target_total_words}")
            return result

        shortage = target_total_words - current_total
        candidates = []
        for key, meta in chapter_targets.items():
            title = meta.get("title") or key
            span = _find_span_for_title(result, title)
            if not span:
                continue
            current = _chapter_word_count(result, span[0], span[1], exclude_takeaways=True)
            desired = max(MIN_CHAPTER_WORDS, int(meta.get("target") or 0))
            ratio = current / max(1, desired)
            deficit = max(0, desired - current)
            candidates.append({
                "key": key,
                "title": title,
                "span": span,
                "current": current,
                "desired": desired,
                "ratio": ratio,
                "deficit": deficit,
            })
        if not candidates:
            _log("word target expansion stopped: no expandable chapter spans")
            return result

        under = [c for c in candidates if c["deficit"] > 80]
        if not under:
            under = sorted(candidates, key=lambda c: c["ratio"])[:max(1, min(8, len(candidates)))]
            for c in under:
                c["deficit"] = max(250, int(shortage / max(1, len(under))))

        total_deficit = sum(max(1, c["deficit"]) for c in under)
        _log(f"word expansion round {round_n}/{max_rounds}: current={current_total}, target={target_total_words}, shortage={shortage}, chapters={len(under)}")

        made_progress = False
        for c in sorted(under, key=lambda x: x["ratio"]):
            span = _find_span_for_title(result, c["title"])
            if not span:
                continue
            h1_idx, end_idx = span
            share = max(1, c["deficit"]) / max(1, total_deficit)
            request_words = int(shortage * share)
            request_words = max(250, min(request_words, 3200))
            if shortage > 12000 and len(under) <= 4:
                request_words = min(5000, max(request_words, shortage // max(1, len(under))))

            ctx = _chapter_context(result, h1_idx, end_idx, char_limit=9000)
            source_excerpt = _source_excerpt_for_title(chapter_chunks, c["title"], char_limit=9000)
            prompt = (
                f'The generated summary for "{book_title}" is shorter than the requested length. '
                f'Expand the chapter "{result[h1_idx].get("heading", c["title"])}" by about {request_words} words.\n\n'
                f'STRICT RULES:\n'
                f'- Output only new prose paragraphs to append to the chapter.\n'
                f'- Do not include headings, bullet lists, or key takeaways.\n'
                f'- Do not repeat existing sentences.\n'
                f'- Add detailed, source-grounded explanation: examples, mechanisms, qualifications, implications, and connections inside this chapter.\n'
                f'- End on a complete sentence.\n'
            )
            if instructions:
                prompt += f'- Respect these user instructions: {instructions}\n'
            prompt += f'\nExisting chapter summary:\n{ctx}\n'
            if source_excerpt:
                prompt += f'\nRelevant source excerpt from this chapter:\n{source_excerpt}\n'

            try:
                extra = _call_claude_full(
                    ai_client, prompt,
                    max_tokens=min(MAX_OUT_TOKENS_PER_CALL, int(request_words * 2.8) + 1400),
                    job_id=job_id,
                    max_continuations=2,
                ).strip()
                extra = "\n".join(
                    ln for ln in extra.splitlines()
                    if not ln.lstrip().startswith("#") and "key takeaway" not in ln.lower()
                ).strip()
                added = _count_words(extra)
                if added > 0:
                    result = _append_prose_before_takeaways(result, h1_idx, end_idx, extra)
                    made_progress = True
                    _log(f"  -> {c['title']}: requested {request_words}, added {added}")
                else:
                    _log(f"  -> {c['title']}: no usable text returned")
            except Exception as e:
                _log(f"  -> {c['title']}: expansion FAILED: {type(e).__name__}: {e}\n{traceback.format_exc()}")

        if not made_progress:
            _log("word target expansion stopped: no progress this round")
            return result

    final_total = _summary_prose_word_count(result, chapter_targets)
    _log(f"word target final after max rounds: {final_total}/{target_total_words}")
    return result



# ── Fixed-page upper-bound compression helpers ────────────────────────────────
def _strictness_settings(strictness):
    """Return (max_ratio, min_ratio, target_ratio, label) for UI strictness."""
    s = str(strictness or "standard").strip().lower()
    if s in ("quickdirty", "quick-dirty", "quick", "loose"):
        return 1.50, 0.85, 1.00, "Quick & Dirty"
    if s == "flexible":
        return 1.20, 0.94, 1.08, "Flexible"
    if s == "strict":
        return 1.05, 0.99, 1.015, "Strict"
    if s in ("exact", "exact-ish", "exactish"):
        return 1.03, 0.99, 1.00, "Exact-ish"
    return LENGTH_ENFORCE_MAX_RATIO, LENGTH_ENFORCE_MIN_RATIO, LENGTH_ENFORCE_TARGET_RATIO, "Standard"

def _reserved_pages_for_fixed(requested_pages):
    rp = max(1, int(requested_pages or 1))
    if rp <= 8:
        return 2
    if rp <= 15:
        return 3
    reserve = FIXED_RESERVED_BASE_PAGES + (FIXED_RESERVED_LONG_EXTRA_PAGES if rp >= 45 else 0)
    if OUTPUT_FEYNMAN_STORYLINE and rp >= FEYNMAN_MIN_SUMMARY_PAGES:
        reserve += max(0, min(FEYNMAN_MAX_PAGES, FEYNMAN_TARGET_PAGES))
    return min(max(3, reserve), max(1, rp // 3))

def _fixed_body_word_target(requested_pages):
    rp = max(1, int(requested_pages or 1))
    reserve = _reserved_pages_for_fixed(rp)
    body_pages = max(1, rp - reserve)
    return max(500, int(body_pages * WORDS_PER_PAGE * FIXED_PAGE_WORD_RATIO))

def _length_tier(requested_pages=0, total_words=0):
    try:
        rp = int(requested_pages or 0)
    except Exception:
        rp = 0
    if rp and rp <= 20:
        return "small"
    if rp and rp <= 60:
        return "medium"
    if rp:
        return "large"
    if int(total_words or 0) <= 5000:
        return "small"
    if int(total_words or 0) <= 18000:
        return "medium"
    return "large"

def _tier_takeaway_count(tier):
    if tier == "small":
        return max(3, min(TAKEAWAY_BULLETS, 3))
    return max(4, TAKEAWAY_BULLETS)


def _fixed_page_bounds(requested_pages, strictness=None):
    """Return (min_pages, max_pages, target_pages) for fixed-page mode.

    The maximum uses floor(requested * max_ratio), not ceil, so a 75-page
    request with a 1.10 max ratio caps at 82 pages rather than allowing 83
    pages (83 would be +10.7%).
    """
    requested_pages = max(1, int(requested_pages or 1))
    max_ratio, min_ratio, target_ratio, _label = _strictness_settings(strictness)
    min_pages = max(1, math.ceil(requested_pages * min_ratio))
    max_pages = max(min_pages, int(math.floor(requested_pages * max_ratio + 1e-9)))
    target_pages = max(
        min_pages,
        min(max_pages, int(math.floor(requested_pages * target_ratio + 1e-9))),
    )
    return min_pages, max_pages, target_pages


def _replace_section_span(sections, start_idx, end_idx, replacement):
    """Replace sections[start_idx:end_idx] with sanitized replacement sections."""
    clean = []
    for sec in replacement or []:
        if not isinstance(sec, dict):
            continue
        clean.append({
            "level": max(1, min(6, int(sec.get("level", 1) or 1))),
            "heading": str(sec.get("heading", "") or "").strip(),
            "body": str(sec.get("body", "") or ""),
            "research_score": sec.get("research_score"),
            "research_reason": str(sec.get("research_reason", "") or ""),
            "special": bool(sec.get("special")),
        })
    if not clean:
        return sections
    return list(sections[:start_idx]) + clean + list(sections[end_idx:])





# v37 final output quality gate -----------------------------------------------
_PLACEHOLDER_LINE_RE = re.compile(
    r"\b(this takeaway (?:preserves|captures)|placeholder|lorem ipsum|tk|tbd)\b",
    re.I,
)
_BAD_FRAGMENT_TAIL_RE = re.compile(
    r"(?:\b(?:of|to|by|with|from|into|about|through|and|or|but|because|in|on|at|for|as|that|which|while|although)\.|[,;:]\s*)$",
    re.I,
)


def _quality_unit_key(text):
    t = re.sub(r"<[^>]+>", " ", str(text or ""))
    t = re.sub(r"[*_`#>\-]+", " ", t)
    t = re.sub(r"[^a-z0-9]+", " ", t.lower()).strip()
    return t[:260]


def _quality_is_placeholder(text):
    return bool(_PLACEHOLDER_LINE_RE.search(str(text or "")))


def _quality_looks_incomplete(text):
    raw = str(text or "").strip()
    if not raw:
        return False
    clean = re.sub(r"^[-*]\s*", "", raw).strip()
    if _BAD_FRAGMENT_TAIL_RE.search(clean):
        return True
    # Very short clauses without punctuation usually came from interrupted model output.
    words = clean.split()
    if len(words) <= 12 and not re.search(r"[.!?]$", clean):
        return True
    low = re.sub(r"[^a-z0-9\s]", "", clean.lower()).split()
    if low:
        suspect = {"identifiable", "systemic", "social", "economic", "psychological", "neurological", "cognitive", "emotional", "structural", "institutional", "financial", "political", "personal", "individual", "collective", "specific", "central", "larger", "broader", "deeper", "major", "critical", "meaningful", "substantive", "sustained", "foundational", "transformative", "legitimate", "strategic", "extraordinary", "important"}
        if low[-1] in suspect and len(low) <= 34:
            return True
    # Common live-output fragments from partially emitted bullets.
    if re.search(r"\b(?:organized into|involving major|written|stems from twelve identifiable|social and economic|undermines our capacity|this book emerges|attention loss)\.$", clean, re.I) and len(words) <= 28:
        return True
    if re.search(r"\b(?:a|an|the)\s+(?:systemic|structural|institutional|psychological|neurological|economic|social|political|financial|central|major|critical|specific|important)\.$", clean, re.I):
        return True
    return False


def _quality_sentence_candidates(text, cap=12):
    out = []
    for part in re.split(r"(?<=[.!?])\s+|\n+", str(text or "")):
        t = re.sub(r"^[-*#\s]+", "", part).strip()
        if not t or _quality_is_placeholder(t) or _quality_looks_incomplete(t):
            continue
        if len(t.split()) >= 6:
            out.append(t)
        if len(out) >= cap:
            break
    return out


def _quality_clean_body(body, heading=""):
    """Remove known-bad artifacts before every PDF build."""
    if not OUTPUT_QUALITY_GATE:
        return str(body or "")
    text = str(body or "").replace("\r", "")
    text = re.sub(r"\n\s*---+\s*\n", "\n\n", text)
    text = re.sub(r"[ \t]+\n", "\n", text)
    paras = re.split(r"\n\s*\n", text)
    cleaned = []
    seen_recent = []
    for para in paras:
        p = para.strip()
        if not p:
            continue
        lines = []
        para_is_list = False
        for line in p.splitlines():
            ln = line.strip()
            if not ln:
                continue
            if _quality_is_placeholder(ln):
                continue
            if ln.startswith(("- ", "* ")):
                para_is_list = True
                bullet = re.sub(r"^[-*]\s*", "", ln).strip()
                if _quality_is_placeholder(bullet) or _quality_looks_incomplete(bullet):
                    continue
                if not re.search(r"[.!?]$", bullet):
                    bullet += "."
                lines.append("- " + bullet)
            else:
                lines.append(ln)
        if not lines:
            continue
        newp = "\n".join(lines) if para_is_list else " ".join(lines)
        if _quality_is_placeholder(newp):
            continue
        if _quality_looks_incomplete(newp) and len(newp.split()) <= 28:
            continue
        key = _quality_unit_key(newp)
        if key and key in seen_recent:
            continue
        cleaned.append(newp)
        if key:
            seen_recent.append(key)
            if len(seen_recent) > max(3, QUALITY_DEDUPE_WINDOW):
                seen_recent = seen_recent[-max(3, QUALITY_DEDUPE_WINDOW):]
    result = "\n\n".join(cleaned).strip()
    return (result + "\n") if result else ""


def _quality_takeaway_bullets_from_text(text, heading="", min_bullets=3, max_bullets=4):
    """Build non-placeholder fallback bullets from existing clean prose."""
    candidates = _quality_sentence_candidates(text, cap=max_bullets * 2)
    out = []
    seen = set()
    for sent in candidates:
        sent = _safe_takeaway_sentence(sent, max_words=36, parent_heading=heading)
        if not sent or _quality_is_placeholder(sent) or _quality_looks_incomplete(sent) or _looks_like_bad_fragment(sent):
            continue
        key = _quality_unit_key(sent)
        if key in seen:
            continue
        seen.add(key)
        out.append("- " + sent)
        if len(out) >= max_bullets:
            break
    fallback = [
        f"{heading or 'This section'} contributes a distinct part of the source's overall argument.",
        "The section's evidence and examples should be read as support for the surrounding chapter logic.",
        "The reader should retain how this section connects to the source's larger narrative or framework.",
    ]
    i = 0
    while len(out) < min_bullets:
        line = fallback[min(i, len(fallback) - 1)]
        out.append("- " + line)
        i += 1
    return "\n".join(out[:max_bullets]) + "\n"


def _quality_repair_takeaways(sections):
    """Ensure every real H1 chapter has a usable non-placeholder takeaway block."""
    result = [dict(s) for s in sections]
    # Because inserting while iterating can invalidate span indexes, walk with a while loop.
    span_pos = 0
    while True:
        spans = _h1_spans(result, include_special=True)
        if span_pos >= len(spans):
            break
        h1_idx, end_idx = spans[span_pos]
        h1 = result[h1_idx]
        if _is_special_section(h1):
            span_pos += 1
            continue
        heading = h1.get("heading", "Chapter")
        source_bits = []
        takeaway_indices = []
        for k in range(h1_idx, end_idx):
            sec = result[k]
            hlow = str(sec.get("heading", "")).lower()
            if sec.get("level") == 3 and "takeaway" in hlow:
                takeaway_indices.append(k)
            elif sec.get("level") <= 3:
                if not any(x in hlow for x in ("practical application", "common mistake", "takeaway")):
                    source_bits.append(sec.get("body", ""))
        source_text = "\n\n".join(source_bits)
        if takeaway_indices:
            k = takeaway_indices[-1]
            bullets = []
            for ln in str(result[k].get("body", "")).splitlines():
                st = ln.strip()
                if not st.startswith(("-", "*")):
                    continue
                bullet = re.sub(r"^[-*]\s*", "", st).strip()
                if bullet and not _quality_is_placeholder(bullet) and not _quality_looks_incomplete(bullet):
                    safe_bullet = _safe_takeaway_sentence(bullet, max_words=36, parent_heading=heading)
                    if safe_bullet and not _looks_like_bad_fragment(safe_bullet):
                        bullets.append("- " + safe_bullet)
            if len(bullets) >= 3:
                result[k]["body"] = "\n".join(bullets[:max(3, min(TAKEAWAY_BULLETS, 5))]) + "\n"
            else:
                result[k]["body"] = _quality_takeaway_bullets_from_text(source_text, heading, min_bullets=3, max_bullets=max(3, TAKEAWAY_BULLETS))
        else:
            result.insert(end_idx, {
                "level": 3,
                "heading": "Key Takeaways",
                "body": _quality_takeaway_bullets_from_text(source_text, heading, min_bullets=3, max_bullets=max(3, TAKEAWAY_BULLETS)),
                "research_score": None,
                "research_reason": "",
                "special": False,
            })
        span_pos += 1
    return result


def _compact_special_section_body(body, max_items=8, words_per_item=24):
    """Compact Final Key Takeaways / Final Review without inventing placeholders."""
    body = _quality_clean_body(body)
    bullets = []
    for line in body.splitlines():
        st = line.strip()
        if st.startswith(("- ", "* ")):
            text = re.sub(r"^[-*]\s*", "", st).strip()
            if text and not _quality_is_placeholder(text) and not _quality_looks_incomplete(text):
                bullets.append(text)
    if not bullets:
        bullets = _quality_sentence_candidates(body, cap=max_items)
    out = []
    seen = set()
    for b in bullets:
        b = _safe_takeaway_sentence(b, max_words=max(24, words_per_item), parent_heading="")
        if not b or _quality_is_placeholder(b) or _quality_looks_incomplete(b) or _looks_like_bad_fragment(b):
            continue
        key = _quality_unit_key(b)
        if key in seen:
            continue
        seen.add(key)
        out.append("- " + b)
        if len(out) >= max_items:
            break
    if not out:
        return _quality_clean_body(body)
    return "\n".join(out) + "\n"


def _normalize_sections_for_pdf(sections):
    """Return a PDF-safe and quality-gated section list.

    v37 adds a deterministic final pass for live-model artifacts: placeholder
    bullets, duplicate paragraphs, source boilerplate chapters, malformed
    headings, and incomplete takeaway fragments are removed before every PDF
    build. Because all variant builds call this function, the same quality gate
    applies to main, phone, B&W, and cyan outputs.
    """
    raw_sections = [s for s in (sections or []) if isinstance(s, dict)]

    # Drop whole H1 spans for source boilerplate. This must happen at span level
    # so child H2/H3 blocks under Praise/Copyright/Notes/Index are removed too.
    if OUTPUT_QUALITY_GATE and QUALITY_DROP_SOURCE_BOILERPLATE:
        filtered = []
        i = 0
        while i < len(raw_sections):
            sec = raw_sections[i]
            try:
                level = int(sec.get("level", 1) or 1)
            except Exception:
                level = 1
            heading = _effective_source_heading(sec)
            is_special = bool(sec.get("special"))
            if level == 1 and (not is_special) and _is_source_boilerplate_heading(heading):
                i += 1
                while i < len(raw_sections):
                    try:
                        nxt_level = int(raw_sections[i].get("level", 1) or 1)
                    except Exception:
                        nxt_level = 1
                    if nxt_level == 1:
                        break
                    i += 1
                continue
            filtered.append(sec)
            i += 1
        raw_sections = filtered

    clean = []
    have_h1 = False
    orphan_body = []

    def _append(sec):
        nonlocal have_h1
        level = sec.get("level", 1)
        try:
            level = int(level or 1)
        except Exception:
            level = 1
        level = max(1, min(3, level))
        heading = str(sec.get("heading", "") or "").strip()
        body = str(sec.get("body", "") or "")
        is_special = bool(sec.get("special"))

        if level == 1 and not is_special:
            sec = _promote_generic_section_heading({**sec, "level": level, "heading": heading, "body": body})
            heading = _normalize_source_chapter_heading(sec.get("heading", heading))
            body = str(sec.get("body", body) or "")
            if OUTPUT_QUALITY_GATE and QUALITY_DROP_SOURCE_BOILERPLATE and _is_source_boilerplate_heading(_effective_source_heading(sec)):
                return

        body = _quality_clean_body(body, heading) if OUTPUT_QUALITY_GATE else body

        if level == 1:
            have_h1 = True
            if not heading:
                heading = f"Section {1 + sum(1 for x in clean if x.get('level') == 1)}"
        elif not have_h1:
            prefix = (("#" * level) + " " + heading).strip() if heading else ""
            merged = (prefix + "\n" + body).strip()
            if merged:
                orphan_body.append(merged)
            return
        elif not heading:
            heading = "Detail" if level == 2 else "Key Takeaways" if "takeaway" in body.lower() else "Detail"

        if level > 1 and not body.strip() and not is_special:
            return

        clean.append({
            "level": level,
            "heading": heading,
            "body": body,
            "research_score": sec.get("research_score"),
            "research_reason": str(sec.get("research_reason", "") or ""),
            "special": is_special,
        })

    for sec in raw_sections:
        _append(sec)

    if orphan_body:
        synthetic_body = _quality_clean_body("\n\n".join(x for x in orphan_body if x).strip())
        if synthetic_body.strip():
            clean.insert(0, {
                "level": 1,
                "heading": "Summary",
                "body": synthetic_body,
                "research_score": None,
                "research_reason": "",
                "special": False,
            })

    if not clean:
        clean.append({
            "level": 1,
            "heading": "Summary",
            "body": "The summary content could not be structured, but the source was processed.\n",
            "research_score": None,
            "research_reason": "",
            "special": False,
        })

    if OUTPUT_QUALITY_GATE:
        clean = _quality_repair_takeaways(clean)
    return clean

def _coerce_compressed_chapter_sections(text, fallback_heading, old_sections=None):
    """Parse an AI-compressed chapter and make sure it remains one H1 chapter.

    The compressor is allowed to rewrite prose, but not to rename or split the
    chapter. If it forgets takeaways, we preserve the previous takeaway section.
    """
    parsed = parse_sections((text or "").strip())
    if not parsed:
        parsed = parse_sections(f"# {fallback_heading}\n\n{text or ''}")

    out = []
    seen_h1 = False
    for sec in parsed:
        sec = dict(sec)
        level = int(sec.get("level", 1) or 1)
        if level == 1:
            if not seen_h1:
                sec["heading"] = fallback_heading
                seen_h1 = True
            else:
                # Stray H1s inside a compressed chapter become H2s.
                sec["level"] = 2
        out.append(sec)

    if not seen_h1:
        out.insert(0, {
            "level": 1,
            "heading": fallback_heading,
            "body": "",
            "research_score": None,
            "research_reason": "",
        })

    if not _has_takeaway_section(out, 0, len(out), min_bullets=3):
        old_takeaways = [
            dict(sec) for sec in (old_sections or [])
            if sec.get("level") == 3 and "takeaway" in sec.get("heading", "").lower()
        ]
        if old_takeaways:
            out.extend(old_takeaways[-1:])
        else:
            out.append({
                "level": 3,
                "heading": "Key Takeaways",
                "body": "- This chapter's main ideas remain represented in the compressed summary.\n- The compression preserves the chapter's coverage while reducing detail.\n- The reader should use the surrounding chapter prose for context and nuance.\n",
                "research_score": None,
                "research_reason": "",
            })
    return out


def _split_text_units(text):
    """Split body text into sentence/list units that can be trimmed safely."""
    units = []
    for block in re.split(r"\n\s*\n", str(text or "").strip()):
        block = block.strip()
        if not block:
            continue
        lines = [ln.strip() for ln in block.splitlines() if ln.strip()]
        if lines and all(ln.startswith(("- ", "* ")) or re.match(r"^\d+\.\s", ln) for ln in lines):
            units.extend(lines)
            continue
        paragraph = " ".join(lines)
        parts = re.split(r"(?<=[.!?])\s+", paragraph)
        for part in parts:
            part = part.strip()
            if part:
                units.append(part)
    return units


def _trim_unit_to_budget(unit, budget):
    words = re.findall(r"\S+", str(unit or ""))
    if len(words) <= budget:
        return str(unit or "").strip()
    if budget <= 0:
        return ""
    trimmed = " ".join(words[:budget]).strip()
    trimmed = re.sub(r"[,;:\-–—]+$", "", trimmed).strip()
    if trimmed and trimmed[-1] not in ".!?":
        trimmed += "."
    return trimmed


def _trim_text_to_word_budget(text, budget):
    """Trim body text to a word budget while ending on a complete unit."""
    budget = max(0, int(budget or 0))
    if budget <= 0:
        return ""
    text = str(text or "").strip()
    if _count_words(text) <= budget:
        return text + ("\n" if text else "")

    kept = []
    used = 0
    for unit in _split_text_units(text):
        wc = _count_words(unit)
        if wc <= 0:
            continue
        if used + wc <= budget:
            kept.append(unit)
            used += wc
            continue
        remaining = budget - used
        # Add a partial final unit only when enough words remain to make it useful.
        if remaining >= 18 or not kept:
            partial = _trim_unit_to_budget(unit, remaining)
            if partial:
                kept.append(partial)
        break

    if not kept:
        kept.append(_trim_unit_to_budget(text, budget))
    return "\n\n".join(k for k in kept if k).strip() + "\n"


def _chapter_shrink_budgets(result, target_total_words):
    """Return h1_idx -> target prose budget for deterministic compression."""
    spans = _h1_spans(result)
    if not spans:
        return {}
    current_by_h1 = {
        h1_idx: _chapter_word_count(result, h1_idx, end_idx, exclude_takeaways=True)
        for h1_idx, end_idx in spans
    }
    current_total = sum(current_by_h1.values())
    if current_total <= 0:
        return {}

    target_total_words = max(1, int(target_total_words or 1))
    ratio = min(1.0, target_total_words / max(1, current_total))
    # Keep a floor for sufficiency, but lower it automatically for very short
    # requested outputs or books with many small chapters.
    per_chapter_soft_floor = min(
        MIN_CHAPTER_WORDS,
        max(140, int(target_total_words / max(1, len(spans)) * 0.45)),
    )

    floors = {h1: min(current, per_chapter_soft_floor) for h1, current in current_by_h1.items()}
    floor_sum = sum(floors.values())
    budgets = {}

    if floor_sum < target_total_words:
        extra_budget = target_total_words - floor_sum
        extra_pool = sum(max(0, current_by_h1[h1] - floors[h1]) for h1 in current_by_h1)
        for h1, current in current_by_h1.items():
            if extra_pool > 0:
                share = max(0, current - floors[h1]) / extra_pool
                budgets[h1] = min(current, floors[h1] + int(extra_budget * share))
            else:
                budgets[h1] = min(current, floors[h1])
    else:
        # When the user asks for an extremely compact report with many detected
        # sections, the normal 40-word prose floor alone can exceed the page
        # budget. In that case keep the H1 and Key Takeaways, but allow the
        # prose body to shrink to a micro-summary.
        hard_floor = 10 if len(spans) >= 15 and target_total_words < 1200 else 40
        for h1, current in current_by_h1.items():
            budgets[h1] = max(hard_floor, min(current, int(current * ratio)))

    # Spend any rounding remainder on the longest chapters without exceeding current.
    used = sum(budgets.values())
    remainder = max(0, target_total_words - used)
    for h1, _current in sorted(current_by_h1.items(), key=lambda kv: kv[1], reverse=True):
        if remainder <= 0:
            break
        room = max(0, current_by_h1[h1] - budgets[h1])
        add = min(room, remainder)
        budgets[h1] += add
        remainder -= add
    return budgets




# ── v37 final output quality gate ─────────────────────────────────────────────
_PLACEHOLDER_PATTERNS = [
    re.compile(r"this takeaway preserves one essential point from the section", re.I),
    re.compile(r"this takeaway captures point \d+ from the section", re.I),
    re.compile(r"use the chapter takeaways above as the primary review checklist", re.I),
]
_BAD_FRAGMENT_ENDINGS = {"of", "by", "and", "or", "to", "the", "a", "an", "in", "on", "at", "for", "as", "with", "from", "into", "through", "across", "because", "which", "that", "while", "although", "including", "involving", "organized", "written", "identifiable", "systemic", "social", "economic", "psychological", "neurological", "cognitive", "emotional", "structural", "institutional", "financial", "political", "personal", "individual", "collective", "public", "private", "modern", "digital", "specific", "central", "core", "broader", "larger", "deeper", "major", "critical", "meaningful", "substantive", "sustained", "foundational", "transformative", "legitimate", "strategic", "extraordinary", "important"}
_BAD_FRAGMENT_ENDINGS.update({
    "selfreflection", "reflection", "measurable", "markers", "marker", "pattern", "patterns",
    "capacity", "capacities", "relationship", "relationships", "connection", "connections",
    "maturity", "immaturity", "validation", "reciprocity", "support", "systems", "structures",
    "institutions", "development", "framework", "approach", "evidence", "mechanism", "argument",
    "behaviour", "behavior", "behaviours", "behaviors", "parents", "children", "needs",
    "availability", "unavailability", "limits", "boundaries", "awareness", "insight", "wealth", "fund", "funds", "capital", "network", "networks", "system"
})


def _is_placeholder_text(text):
    s = re.sub(r"\s+", " ", str(text or "")).strip()
    return any(p.search(s) for p in _PLACEHOLDER_PATTERNS)


def _looks_like_bad_fragment(text):
    s = re.sub(r"\s+", " ", str(text or "")).strip()
    if not s or _is_placeholder_text(s):
        return True
    if re.search(r"[,;:]\s*$", s) or re.search(r"\b[A-Za-z]+,\.$", s):
        return True
    low = re.sub(r"[^a-z0-9\s]", "", s.lower()).split()
    if not low:
        return True
    last = low[-1]
    # Short bullets ending in adjective/preposition-like fragments are almost
    # always live-model truncations, e.g. "twelve identifiable." or
    # "social and economic.". Longer prose can still legitimately end with
    # some of these words, so use a length guard.
    if last in _BAD_FRAGMENT_ENDINGS and len(low) <= 34:
        return True
    # Truncated subordinate clauses: "signals that attention loss."
    if re.search(r"\b(?:that|how|why|where|when|whether|because|as|which|who|what)\s+[^.!?]{1,90}\b(?:emerges|reveals|shows|signals|requires|creates|undermines|depends|reflects|represents|describes|establishes|illustrates|stems|operates|contributes|points|means)\.$", s, re.I):
        return True
    # Common live-output fragments observed in generated summaries.
    if re.search(r"\b(?:organized into|involving major|written|before|stems from twelve identifiable|specific social and economic|undermines our capacity|this book emerges|attention loss|sovereign wealth|transitioned from print-based epistemology|displayed these markers)\.?$", s, re.I) and len(low) <= 34:
        return True
    if re.search(r"\b(?:transitioned|moves|shifts|shifted)\s+from\s+[^.!?]{3,100}\.$", s, re.I) and not re.search(r"\bto\b", s, re.I):
        return True
    # A determiner + adjective before the full stop often means the noun was cut.
    if re.search(r"\b(?:a|an|the)\s+(?:systemic|structural|institutional|psychological|neurological|economic|social|political|financial|central|major|critical|specific|important)\.$", s, re.I):
        return True
    return False


def _repair_sentence_fragment(text):
    s = re.sub(r"\s+", " ", str(text or "")).strip()
    s = re.sub(r"\s+([,.;:!?])", r"\1", s)
    s = re.sub(r",\s*\.", ".", s).strip()
    if _looks_like_bad_fragment(s):
        return ""
    if s and s[-1] not in ".!?":
        s += "."
    return s


def _strip_parent_heading_prefix(text, parent_heading=""):
    """Remove duplicated chapter-title prefixes from fallback takeaway sentences."""
    s = re.sub(r"\s+", " ", str(text or "")).strip()
    h = re.sub(r"^\s*chapter\s+\d+\s*[:.\-–—]?\s*", "", str(parent_heading or ""), flags=re.I).strip()
    if not s or not h:
        return s
    def toks(x):
        return re.findall(r"[a-z0-9]+", x.lower().replace("’", "'"))
    s_tokens = toks(s)
    h_tokens = toks(h)
    if not s_tokens or not h_tokens:
        return s
    variants = [h_tokens]
    m = re.match(r"^\s*(chapter\s+\d+)\s*[:.\-–—]?\s*", str(parent_heading or ""), flags=re.I)
    if m:
        variants.append(toks(m.group(1)) + h_tokens)
    token_spans = list(re.finditer(r"[A-Za-z0-9]+", s.replace("’", "'")))
    for vt in variants:
        if len(s_tokens) > len(vt) + 3 and s_tokens[:len(vt)] == vt and len(token_spans) >= len(vt):
            # Remove through the character end of the matched title tokens.
            # This avoids over-removing the first real sentence word when
            # punctuation such as children's creates extra tokens.
            cut_at = token_spans[len(vt) - 1].end()
            return s[cut_at:].strip(" :.-–—")
    return s


def _safe_takeaway_sentence(text, max_words=34, min_words=6, parent_heading=""):
    """Return a complete, non-fragment takeaway sentence without mid-clause clipping.

    Earlier versions shortened bullets by cutting after N words and appending a
    period. That produced polished-looking but unfinished lines such as
    "avoid self-reflection." or "displayed these markers:." v50 keeps whole
    sentences whenever possible and only shortens at real clause boundaries.
    """
    s = re.sub(r"^[-*•]\s*", "", str(text or "")).strip()
    s = re.sub(r"[*_`]+", "", s)
    s = re.sub(r"\s+", " ", s)
    s = _strip_parent_heading_prefix(s, parent_heading)
    s = re.sub(r"\s+([,.;:!?])", r"\1", s)
    s = re.sub(r"[:;,]\s*\.$", ".", s).strip()
    if not s or _is_placeholder_text(s):
        return ""
    # Prefer the first complete sentence if the input contains several.
    first = re.match(r"^(.+?[.!?])(?:\s|$)", s)
    if first and len(first.group(1).split()) >= min_words:
        s = first.group(1).strip()
    else:
        s = _repair_sentence_fragment(s)
    if not s or _looks_like_bad_fragment(s):
        return ""
    words = s.split()
    if len(words) < min_words and not re.match(r"^(Stop|Use|Set|Ask|Notice|Name|Accept|Recognize|Recognise|Identify|Choose|Track|Build|Keep|Treat|Remember|Practice|Apply|Review|Compare|Return)\b", s):
        return ""
    if len(words) <= max_words:
        return s
    # Try to shorten at a true clause boundary before the word budget.
    char_limit = len(" ".join(words[:max_words]))
    prefix = s[:char_limit]
    cut_positions = []
    for token in [";", ":", " - ", " – ", " — "]:
        pos = prefix.rfind(token)
        if pos > 0:
            cut_positions.append(pos)
    for pat in [r",\s+(?:and|but|while|because|which|that|so|though)\b", r",\s+"]:
        matches = list(re.finditer(pat, prefix, flags=re.I))
        if matches:
            cut_positions.append(matches[-1].start())
    for pos in sorted(set(cut_positions), reverse=True):
        cand = prefix[:pos].strip(" ,;:-–—")
        if len(cand.split()) >= min_words:
            cand = _repair_sentence_fragment(cand)
            if cand and not _looks_like_bad_fragment(cand):
                return cand
    # Better a slightly longer complete bullet than a clipped one. If still
    # reasonably sized, keep the whole sentence. Otherwise let caller pick a
    # different source sentence or use a fallback.
    if len(words) <= max_words + 18:
        return s
    return ""


def _repair_complete_sentence_text(text):
    """Global final-stage sentence check.

    It removes obvious truncated sentence tails and ensures every bullet or
    paragraph that remains ends on a sentence boundary. This is intentionally
    deterministic: the final PDF should never contain half-sentences just
    because a model call ended badly.
    """
    raw = str(text or "").replace("\r", "")
    paras = re.split(r"\n\s*\n", raw)
    fixed = []
    repairs = 0
    for para in paras:
        p = para.strip()
        if not p:
            continue
        if p.startswith(("## ", "### ")):
            fixed.append(p)
            continue
        # Bullet block: validate every bullet individually.
        if any(ln.strip().startswith(("- ", "* ")) for ln in p.splitlines()):
            good_lines = []
            for ln in p.splitlines():
                st = ln.strip()
                if not st:
                    continue
                if st.startswith(("- ", "* ")):
                    repaired = _repair_sentence_fragment(re.sub(r"^[-*]\s*", "", st).strip())
                    if repaired:
                        good_lines.append("- " + repaired)
                    else:
                        repairs += 1
                else:
                    repaired = _repair_sentence_fragment(st)
                    if repaired:
                        good_lines.append(repaired)
                    else:
                        repairs += 1
            if good_lines:
                fixed.append("\n".join(good_lines))
            continue
        flat = re.sub(r"\s+", " ", p).strip()
        # Split into complete sentence-like units. If the last unit is a bad
        # fragment, drop it; otherwise add final punctuation.
        units = re.findall(r"[^.!?]+[.!?]", flat)
        tail = re.sub(r".*[.!?]", "", flat).strip() if re.search(r"[.!?]", flat) else flat
        if units:
            cleaned_units = []
            for u in units:
                u = u.strip()
                if _looks_like_bad_fragment(u) and len(u.split()) <= 34:
                    repairs += 1
                    continue
                cleaned_units.append(u)
            if tail:
                repaired_tail = _repair_sentence_fragment(tail)
                if repaired_tail:
                    cleaned_units.append(repaired_tail)
                else:
                    repairs += 1
            if cleaned_units:
                fixed.append(" ".join(cleaned_units))
        else:
            repaired = _repair_sentence_fragment(flat)
            if repaired:
                fixed.append(repaired)
            else:
                repairs += 1
    return ("\n\n".join(fixed).strip() + ("\n" if fixed else "")), repairs


def _dedupe_body_text(body):
    raw = str(body or "").replace("\x00", "")
    raw = "\n".join(ln.rstrip() for ln in raw.splitlines())
    dedup_lines = []
    prev_key = ""
    for ln in raw.splitlines():
        key = re.sub(r"\s+", " ", ln.strip().lower())
        if key and key == prev_key:
            continue
        dedup_lines.append(ln)
        if key:
            prev_key = key
    raw = "\n".join(dedup_lines)
    paras = re.split(r"\n\s*\n", raw)
    out = []
    seen = set()
    for p in paras:
        p = p.strip()
        if not p or _is_placeholder_text(p):
            continue
        flat = re.sub(r"\s+", " ", p).strip()
        key = re.sub(r"[^a-z0-9]", "", flat.lower())
        if key and key in seen:
            continue
        if key and out:
            prev_key = re.sub(r"[^a-z0-9]", "", re.sub(r"\s+", " ", out[-1]).lower())
            if len(key) > 40 and (key in prev_key or prev_key in key):
                if len(key) > len(prev_key):
                    out[-1] = flat
                    seen.discard(prev_key)
                    seen.add(key)
                continue
        if key:
            seen.add(key)
        out.append(flat if not p.startswith(("- ", "* ", "##", "###")) else p)
    return "\n\n".join(out).strip() + ("\n" if out else "")


def _clean_bullets_and_fragments(body, parent_heading=""):
    cleaned = []
    for ln in str(body or "").splitlines():
        st = ln.strip()
        if _is_placeholder_text(st):
            continue
        if st.startswith(("- ", "* ")):
            bullet = _repair_sentence_fragment(re.sub(r"^[-*]\s*", "", st).strip())
            if bullet:
                cleaned.append("- " + bullet)
        else:
            if len(st.split()) <= 34 and _looks_like_bad_fragment(st):
                continue
            cleaned.append(ln)
    repaired, _repairs = _repair_complete_sentence_text("\n".join(cleaned))
    return repaired



def _split_embedded_markdown_subsections(sections):
    """Turn stray markdown headings inside section bodies into real sections.

    This prevents rendered output such as literal "## The Storyline" from
    appearing when a fallback or model response embeds subsections inside the
    body of an H1 instead of returning parseable markdown sections.
    """
    result = []
    for sec in sections or []:
        sec = dict(sec)
        body = str(sec.get("body", "") or "")
        if not re.search(r"(?m)^\s*#{2,3}\s+\S", body):
            result.append(sec)
            continue
        try:
            level = int(sec.get("level", 1) or 1)
        except Exception:
            level = 1
        heading = str(sec.get("heading", "") or "").strip()
        prefix = ("#" * max(1, min(level, 3))) + " " + heading + "\n" if heading else ""
        parsed = parse_sections(prefix + body)
        if not parsed:
            result.append(sec)
            continue
        # Preserve metadata from the parent on the reconstructed H1 and mark
        # all child sections as special if the parent was generated special
        # matter. Do not leak the parent's body into child sections.
        for idx, child in enumerate(parsed):
            child = dict(child)
            if idx == 0:
                for k in ("research_score", "research_reason", "special"):
                    if k in sec:
                        child[k] = sec[k]
                if heading:
                    child["heading"] = heading
            elif sec.get("special"):
                child["special"] = True
            result.append(child)
    return result

def _split_embedded_feynman_sections(sections):
    result = []
    for sec in sections or []:
        if int(sec.get("level") or 1) == 1 and _norm_title_key(sec.get("heading", "")) in {"finalkeytakeaways", "finalreviewsheet"}:
            body = str(sec.get("body", "") or "")
            m = re.search(r"(?im)^\s*(?:##\s*)?(The Big Picture|The Story of the Book|Teach-Back Explanation)\s*$", body)
            if m:
                before = body[:m.start()].strip()
                after = body[m.start():].strip()
                kept = dict(sec); kept["body"] = before + ("\n" if before else "")
                result.append(kept)
                result.append({"level": 1, "heading": "Feynman Storyline Review", "body": after + "\n", "research_score": None, "research_reason": "", "special": True})
                continue
        result.append(sec)
    return result


def _reorder_special_sections(sections):
    """Move generated special H1 spans without detaching their children."""
    order = {
        "executivesummary": 0,
        "faithfulnessnote": 1,
        "sourcenote": 1,
        "extendedlearningnotes": 88,
        "finalkeytakeaways": 90,
        "feynmanstorylinereview": 91,
        "finalreviewsheet": 92,
        "summaryofthesummary": 93,
        "summaryofsummary": 93,
        "ifyouenjoyedthisbook": 99,
        "youmightalsolike": 99,
    }
    secs = list(sections or [])
    front, middle, back = [], [], []
    i = 0
    seq = 0
    while i < len(secs):
        sec = secs[i]
        try:
            level = int(sec.get("level", 1) or 1)
        except Exception:
            level = 1
        if level != 1:
            middle.append((seq, [sec]))
            seq += 1
            i += 1
            continue
        j = i + 1
        while j < len(secs):
            try:
                nxt_level = int(secs[j].get("level", 1) or 1)
            except Exception:
                nxt_level = 1
            if nxt_level == 1:
                break
            j += 1
        span = secs[i:j]
        if _is_special_section(sec):
            key = _norm_title_key(sec.get("heading", ""))
            ordv = order.get(key, 50)
            if ordv <= 10:
                front.append((ordv, seq, span))
            else:
                back.append((ordv, seq, span))
        else:
            middle.append((seq, span))
        seq += 1
        i = j
    front.sort(key=lambda x: (x[0], x[1]))
    back.sort(key=lambda x: (x[0], x[1]))
    out = []
    for _ord, _seq, span in front:
        out.extend(span)
    for _seq, span in middle:
        out.extend(span)
    for _ord, _seq, span in back:
        out.extend(span)
    return out


def _make_takeaway_fallback(parent_heading, parent_body, needed=3):
    flat = re.sub(r"\s+", " ", str(parent_body or "")).strip()
    sentences = [s.strip() for s in re.split(r"(?<=[.!?])\s+", flat) if len(s.split()) >= 8]
    out = []
    seen = set()
    for s in sentences:
        s = re.sub(r"^[-*]\s*", "", s).strip()
        s = _safe_takeaway_sentence(s, max_words=36, parent_heading=parent_heading)
        if not s:
            continue
        key = _quality_unit_key(s)
        if key in seen:
            continue
        seen.add(key)
        out.append("- " + s)
        if len(out) >= needed:
            break
    while len(out) < needed:
        h = re.sub(r"\s+", " ", str(parent_heading or "this section")).strip() or "this section"
        fallbacks = [
            f"{h} advances one part of the source's larger argument.",
            f"{h} should be read in connection with the surrounding chapters, not as an isolated note.",
            "Return to the original source for exact wording, supporting evidence, and nuance.",
            "Use this chapter as a checkpoint for understanding how the source's argument develops.",
        ]
        out.append("- " + fallbacks[len(out) % len(fallbacks)])
    return "\n".join(out[:needed]) + "\n"


def _final_output_quality_gate(sections, job_id=None, book_title=""):
    if not OUTPUT_QUALITY_GATE:
        return _normalize_sections_for_pdf(sections)
    changed = {"dropped_boilerplate": 0, "placeholder_removed": 0, "duplicates_cleaned": 0, "headings_fixed": 0, "takeaways_repaired": 0, "sentence_repairs": 0}
    src = _split_embedded_markdown_subsections(_split_embedded_feynman_sections([dict(s) for s in sections or []]))
    out = []
    i = 0
    while i < len(src):
        sec = dict(src[i])
        level = int(sec.get("level") or 1)
        heading = str(sec.get("heading", "") or "")
        if QUALITY_DROP_SOURCE_BOILERPLATE and level == 1 and not _is_special_section(sec) and _is_source_boilerplate_heading(heading):
            changed["dropped_boilerplate"] += 1
            i += 1
            while i < len(src) and int(src[i].get("level") or 1) != 1:
                i += 1
            continue
        new_heading = _normalize_source_chapter_heading(heading)
        if new_heading and new_heading != heading:
            sec["heading"] = new_heading; changed["headings_fixed"] += 1
        if level == 1 and re.match(r"^section\s+\d+$", str(sec.get("heading", "")), re.I):
            lines = str(sec.get("body", "") or "").splitlines()
            for idx2, line in enumerate(lines[:4]):
                cand = _normalize_source_chapter_heading(line)
                if _chapter_number_from_title(cand) is not None and cand:
                    sec["heading"] = cand
                    sec["body"] = "\n".join(lines[idx2 + 1:]).strip() + "\n"
                    changed["headings_fixed"] += 1
                    break
        before_body = str(sec.get("body", "") or "")
        sec["body"] = _dedupe_body_text(_clean_bullets_and_fragments(before_body, sec.get("heading", "")))
        if before_body != sec["body"]:
            if any(p.search(before_body) for p in _PLACEHOLDER_PATTERNS):
                changed["placeholder_removed"] += 1
            else:
                changed["duplicates_cleaned"] += 1
        out.append(sec)
        i += 1
    spans = _h1_spans(out)
    for h1_idx, end_idx in spans:
        parent_heading = out[h1_idx].get("heading", "Section")
        parent_body = "\n".join(out[k].get("body", "") for k in range(h1_idx, end_idx))
        for k in range(h1_idx + 1, end_idx):
            sec = out[k]
            if int(sec.get("level") or 1) == 3 and "takeaway" in str(sec.get("heading", "")).lower():
                bullets = []
                for ln in str(sec.get("body", "") or "").splitlines():
                    st = ln.strip()
                    if not st.startswith(("- ", "* ")) or _is_placeholder_text(st):
                        continue
                    safe_bullet = _safe_takeaway_sentence(re.sub(r"^[-*]\s*", "", st), max_words=38, parent_heading=parent_heading)
                    if safe_bullet and not _looks_like_bad_fragment(safe_bullet):
                        bullets.append("- " + safe_bullet)
                if len(bullets) < 3:
                    sec["body"] = _make_takeaway_fallback(parent_heading, parent_body, needed=3)
                    changed["takeaways_repaired"] += 1
                else:
                    sec["body"] = "\n".join(bullets[:max(3, min(len(bullets), TAKEAWAY_BULLETS))]) + "\n"
    real_h1_headings = [s.get("heading", "") for s in out if int(s.get("level") or 1) == 1 and not _is_special_section(s) and not _is_source_boilerplate_heading(s.get("heading", ""))][:12]
    for sec in out:
        if int(sec.get("level") or 1) != 1 or not _is_special_section(sec):
            continue
        key = _norm_title_key(sec.get("heading", ""))
        body_words = _count_words(sec.get("body", ""))
        if key == "finalkeytakeaways" and body_words < 12:
            bullets = [f"- {h} is one of the core source sections to revisit when checking the summary's argument." for h in real_h1_headings[:8]]
            fallback_bullets = ["- Revisit the Executive Summary for the source's central argument.", "- Use the chapter takeaways to check the source's supporting logic.", "- Treat this summary as a structured guide to the original source."]
            for fb in fallback_bullets:
                if len(bullets) >= 3:
                    break
                if fb not in bullets:
                    bullets.append(fb)
            sec["body"] = "\n".join(bullets[:8]) + "\n"
            changed["takeaways_repaired"] += 1
        elif key == "finalreviewsheet" and body_words < 12:
            ideas = real_h1_headings[:10] or ["the source's central argument", "the main evidence", "the practical implications"]
            sec["body"] = "## The Whole Source in 10 Ideas\n" + "\n".join(f"- Review {h} as part of the source's overall storyline." for h in ideas[:10]) + "\n\n## Most Actionable Lessons\n- Compare the details against the source's central thesis.\n- Use the chapter takeaways as a review checklist.\n- Return to the original source for exact wording, evidence, and nuance.\n"
            changed["takeaways_repaired"] += 1
    out = _reorder_special_sections(_normalize_sections_for_pdf(out))
    for sec in out:
        before = str(sec.get("body", "") or "")
        repaired, n_repairs = _repair_complete_sentence_text(before)
        if repaired != before:
            sec["body"] = repaired
            changed["sentence_repairs"] += int(n_repairs or 1)
    # A second takeaway pass catches any bullets removed by the complete-sentence
    # gate and ensures every real chapter still has usable takeaways. Run one
    # more sentence pass afterwards because takeaway rebuilding itself can add
    # new bullet text.
    out = _quality_repair_takeaways(out)
    for sec in out:
        before = str(sec.get("body", "") or "")
        repaired, n_repairs = _repair_complete_sentence_text(before)
        if repaired != before:
            sec["body"] = repaired
            changed["sentence_repairs"] += int(n_repairs or 1)
    if job_id:
        _audit_event(job_id, "final_quality_gate", **changed)
    return out

def _truncate_words_preserving_sentence(text, max_words):
    """Return text capped to roughly max_words without raising on odd input."""
    words = re.findall(r"\S+", str(text or ""))
    if len(words) <= max_words:
        return str(text or "").strip()
    cut = " ".join(words[:max(1, int(max_words))]).strip()
    # Prefer ending at a sentence boundary if one is close to the cap.
    boundary = max(cut.rfind(". "), cut.rfind("! "), cut.rfind("? "))
    if boundary > len(cut) * 0.65:
        cut = cut[:boundary + 1]
    if cut and cut[-1] not in ".!?":
        cut += "."
    return cut


def _compact_takeaway_body(body, max_bullets=3, words_per_bullet=16):
    """Compact bullets without leaking generic placeholders.

    v35 filled missing bullets with placeholder text. v37 reuses existing
    bullets, headings, and sentences before falling back to non-placeholder
    review prompts.
    """
    raw = str(body or "")
    lines = [ln.strip() for ln in raw.splitlines()]
    candidates = []
    for ln in lines:
        if not ln or _is_placeholder_text(ln):
            continue
        if ln.startswith(("- ", "* ")):
            candidates.append(re.sub(r"^[-*]\s*", "", ln).strip())
        elif re.match(r"^[A-Z][A-Za-z0-9 ,:'’\-]{3,90}$", ln) and len(ln.split()) <= 12:
            candidates.append(ln.rstrip(".") + ".")
    sentence_text = re.sub(r"\s+", " ", re.sub(r"^#+\s*", "", raw, flags=re.MULTILINE)).strip()
    for s in re.split(r"(?<=[.!?])\s+", sentence_text):
        s = s.strip()
        if len(s.split()) >= 5 and not _is_placeholder_text(s):
            candidates.append(s)
    cleaned = []
    seen = set()
    for cand in candidates:
        cand = _repair_sentence_fragment(cand)
        if not cand or _looks_like_bad_fragment(cand):
            continue
        key = re.sub(r"[^a-z0-9]", "", cand.lower())[:100]
        if key and key not in seen:
            seen.add(key)
            safe_cand = _safe_takeaway_sentence(cand, max_words=max(24, words_per_bullet), parent_heading="")
            if safe_cand:
                cleaned.append("- " + safe_cand)
        if len(cleaned) >= max(3, max_bullets):
            break
    fallback = [
        "Review the source's central argument before relying on the details.",
        "Connect each chapter's takeaways back to the overall thesis.",
        "Use the summary as a structured guide to the original source.",
    ]
    while len(cleaned) < 3:
        cleaned.append("- " + fallback[len(cleaned) % len(fallback)])
    return "\n".join(cleaned) + "\n"


def _compact_sections_for_page_cap(sections, requested_pages=0, job_id=None, aggressive=False):
    """Compact non-essential generated material under fixed-page pressure.

    The page cap should preserve source coverage and chapter-level Key Takeaways.
    Under tight requests, however, the richer v20/v21 add-ons (Practical
    Application, Common Mistake, long Feynman section, verbose review sheets)
    can dominate page count and make a bounded output impossible. This pass
    removes/trims those extras before semantic or deterministic compression.
    """
    try:
        rp = int(requested_pages or 0)
    except Exception:
        rp = 0
    result = []
    dropped = 0
    trimmed = 0
    tight = aggressive or (rp and rp <= 30)
    very_tight = aggressive or (rp and rp <= 15)
    drop_headings = {
        "practical application",
        "common mistake to avoid",
        "common mistake / misreading",
        "common mistake",
    }
    for sec in sections or []:
        new_sec = dict(sec)
        heading_key = re.sub(r"\s+", " ", str(new_sec.get("heading", "")).strip().lower())
        level = int(new_sec.get("level") or 1)
        if tight and level >= 3 and heading_key in drop_headings:
            dropped += 1
            continue
        if level == 3 and "takeaway" in heading_key:
            before = _count_words(new_sec.get("body", ""))
            new_sec["body"] = _compact_takeaway_body(
                new_sec.get("body", ""),
                max_bullets=3 if tight else 4,
                words_per_bullet=7 if very_tight else 18,
            )
            after = _count_words(new_sec.get("body", ""))
            if after < before:
                trimmed += before - after
        elif _is_special_section(new_sec):
            # Keep concise front/back matter, but drop the long Feynman review when
            # a compact fixed output is already over cap. It is valuable in 50+ page
            # books, not in a mechanically tight 10-30 page output.
            if "feynman" in heading_key and tight:
                dropped += 1
                continue
            if heading_key == "executive summary":
                before = _count_words(new_sec.get("body", ""))
                new_sec["body"] = _truncate_words_preserving_sentence(new_sec.get("body", ""), 110 if tight else 180) + "\n"
                after = _count_words(new_sec.get("body", ""))
                if after < before:
                    trimmed += before - after
            elif "summary of the summary" in heading_key or "summaryofsummary" in re.sub(r"[^a-z0-9]", "", heading_key):
                before = _count_words(new_sec.get("body", ""))
                cap = 520 if tight else 950
                new_sec["body"] = _trim_text_to_word_budget(new_sec.get("body", ""), cap) + "\n"
                after = _count_words(new_sec.get("body", ""))
                if after < before:
                    trimmed += before - after
            elif "final review" in heading_key or "final key" in heading_key:
                before = _count_words(new_sec.get("body", ""))
                new_sec["body"] = _compact_takeaway_body(new_sec.get("body", ""), max_bullets=5 if tight else 8, words_per_bullet=16)
                after = _count_words(new_sec.get("body", ""))
                if after < before:
                    trimmed += before - after
        result.append(new_sec)
    if job_id:
        try:
            with open(os.path.join(TMP_DIR, "length_enforcement.log"), "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] compact page-cap pass: requested={requested_pages}, aggressive={aggressive}, dropped_sections={dropped}, trimmed_words={trimmed}\n")
        except Exception:
            pass
    return _normalize_sections_for_pdf(result)



def _append_length_expansion_notes(sections, ai_client, book_title, chapter_chunks,
                                   missing_pages, job_id, instructions=""):
    """Append a source-grounded expansion section when fixed-page output is under target.

    This is a final lower-bound safety net for cases like asking a 2-page brief
    to become a 25-page learning summary. It is used only after normal chapter
    expansion has failed to reach the requested page floor.
    """
    try:
        mp = max(1, int(math.ceil(float(missing_pages))))
    except Exception:
        mp = 1
    target_words = max(750, min(6000, int(mp * WORDS_PER_PAGE * 1.45)))
    excerpts = []
    for chunk in (chapter_chunks or [])[:30]:
        title = chunk.get("title", "Section")
        txt = re.sub(r"\s+", " ", str(chunk.get("text", "") or "")).strip()
        if txt:
            excerpts.append(f"[{title}] {txt[:700]}")
        if len("\n".join(excerpts)) > 11000:
            break
    sample = "\n\n".join(excerpts)[:12000]
    prompt = (
        f'The fixed-page summary for "{book_title}" is shorter than requested. '
        f'Create an additional source-grounded learning section of about {target_words} words.\n\n'
        f'Format exactly as:\n# Extended Learning Notes\n'
        f'## The Source in Plain English\n[clear narrative explanation]\n'
        f'## Main Points Revisited\n- bullet points that deepen the most important ideas\n'
        f'## Connections and Implications\n[paragraphs connecting the ideas]\n\n'
        f'STRICT RULES:\n'
        f'- Stay within the uploaded source; do not invent facts.\n'
        f'- Do not copy long passages from the source. Paraphrase.\n'
        f'- Use this to add useful depth, not filler.\n'
        f'- End on a complete sentence.\n'
    )
    if instructions:
        prompt += f'- Respect these user instructions where possible: {instructions}\n'
    prompt += f"\nSource excerpts for grounding:\n{sample}\n"
    try:
        text = _call_claude_full(
            ai_client, prompt,
            max_tokens=min(MAX_OUT_TOKENS_PER_CALL, int(target_words * 2.3) + 1200),
            job_id=job_id,
            max_continuations=1,
        ).strip()
        parsed = parse_sections(text)
        if parsed and parsed[0].get("level") == 1:
            parsed[0]["special"] = True
            _audit_event(job_id, "length_expansion_notes_added", target_words=target_words, sections=len(parsed))
            return _append_before_summary_of_summary(sections, parsed)
    except Exception as e:
        _audit_event(job_id, "length_expansion_notes_failed", error=f"{type(e).__name__}: {e}")

    body = []
    for h1_idx, end_idx in _h1_spans(sections):
        heading = sections[h1_idx].get("heading", "Section")
        snippet = _trim_text_to_word_budget(sections[h1_idx].get("body", ""), 75)
        if snippet:
            body.append(f"- {heading}: {snippet}")
        if len(body) >= 24:
            break
    fallback = {
        "level": 1,
        "heading": "Extended Learning Notes",
        "body": "These notes revisit the strongest ideas from the generated summary to support review and retention.\n\n" + "\n".join(body),
        "research_score": None,
        "research_reason": "",
        "special": True,
    }
    _audit_event(job_id, "length_expansion_notes_fallback", bullets=len(body))
    return _append_before_summary_of_summary(sections, [fallback])

def _deterministic_shrink_to_word_target(sections, target_total_words, job_id=None):
    """Hard deterministic shrink used as the final page-cap safety net.

    It never removes H1 chapter sections and leaves Key Takeaways in place. It
    trims only prose bodies, distributing the budget across chapters and then
    across subsections proportionally.
    """
    result = [dict(sec) for sec in sections]
    target_total_words = max(1, int(target_total_words or 1))
    current_total = _summary_prose_word_count(result)
    if current_total <= target_total_words:
        return result

    budgets_by_h1 = _chapter_shrink_budgets(result, target_total_words)
    if not budgets_by_h1:
        return result

    log_path = os.path.join(TMP_DIR, "length_enforcement.log")
    def _log(msg):
        if not job_id:
            return
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] {msg}\n")
        except Exception:
            pass

    spans = _h1_spans(result, include_special=True)
    for h1_idx, end_idx in spans:
        if h1_idx not in budgets_by_h1:
            continue
        chapter_budget = budgets_by_h1[h1_idx]
        prose_indices = [
            k for k in range(h1_idx, end_idx)
            if not (result[k].get("level") == 3 and "takeaway" in result[k].get("heading", "").lower())
        ]
        counts = {k: _count_words(result[k].get("body", "")) for k in prose_indices}
        current = sum(counts.values())
        if current <= chapter_budget:
            continue

        section_budgets = {}
        remaining = chapter_budget
        nonempty = [k for k in prose_indices if counts.get(k, 0) > 0]
        for pos, k in enumerate(nonempty):
            if pos == len(nonempty) - 1:
                b = max(0, remaining)
            else:
                b = int(chapter_budget * counts[k] / max(1, current))
                b = min(b, counts[k], remaining)
            section_budgets[k] = b
            remaining -= b

        for k, budget in section_budgets.items():
            result[k] = dict(result[k])
            result[k]["body"] = _trim_text_to_word_budget(result[k].get("body", ""), budget)
        _log(f"deterministic shrink: '{result[h1_idx].get('heading', '')}' {current}->{chapter_budget} words")

    final_total = _summary_prose_word_count(result)
    _log(f"deterministic shrink total: {current_total}->{final_total}, target={target_total_words}")
    return result


def _compress_summary_to_word_target(sections, ai_client, book_title, chapter_chunks,
                                     chapter_targets, target_total_words, job_id,
                                     instructions="", max_rounds=None):
    """Compress summary prose toward a target while preserving chapters/takeaways.

    Uses Claude for semantic compression when available, then applies a
    deterministic trim as a hard safety net so page caps are enforceable.
    """
    log_path = os.path.join(TMP_DIR, "length_enforcement.log")
    max_rounds = LENGTH_COMPRESS_MAX_ROUNDS if max_rounds is None else max_rounds

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] {msg}\n")
        except Exception:
            pass

    result = [dict(sec) for sec in sections]
    target_total_words = max(1, int(target_total_words or 1))
    current_total = _summary_prose_word_count(result, chapter_targets)
    if current_total <= int(target_total_words * 1.02):
        _log(f"compression not needed: {current_total}/{target_total_words}")
        return result

    if not (LENGTH_COMPRESS_AI and ai_client is not None):
        _log(f"AI compression disabled/unavailable; deterministic target={target_total_words}")
        return _deterministic_shrink_to_word_target(result, target_total_words, job_id=job_id)

    for round_n in range(1, max(1, max_rounds) + 1):
        current_total = _summary_prose_word_count(result, chapter_targets)
        if current_total <= int(target_total_words * 1.02):
            _log(f"AI compression OK after round {round_n - 1}: {current_total}/{target_total_words}")
            return result

        ratio = target_total_words / max(1, current_total)
        _log(f"AI compression round {round_n}/{max_rounds}: current={current_total}, target={target_total_words}, ratio={ratio:.3f}")
        made_progress = False
        spans = _h1_spans(result)
        candidates = []
        for h1_idx, end_idx in spans:
            current = _chapter_word_count(result, h1_idx, end_idx, exclude_takeaways=True)
            if current <= MIN_CHAPTER_WORDS:
                continue
            desired = max(
                min(current, MIN_CHAPTER_WORDS),
                int(current * ratio * 0.98),
            )
            if current - desired >= 120:
                candidates.append((current - desired, current, desired, h1_idx, end_idx))
        candidates.sort(reverse=True)
        if not candidates:
            _log("AI compression found no useful candidates; switching to deterministic trim")
            break

        overage_ratio = current_total / max(1, target_total_words)
        max_candidates = len(candidates) if overage_ratio > 1.15 else min(8, len(candidates))

        # Replacing a chapter span can change the length of `result`. Process
        # selected spans from the back of the document toward the front so the
        # remaining stored indices stay valid. v18 processed by deficit order,
        # which could corrupt later spans and surface as a ReportLab/PdfReader
        # "list index out of range" during the post-compression rebuild.
        selected_candidates = list(candidates[:max_candidates])
        selected_candidates.sort(key=lambda item: item[3], reverse=True)

        for _deficit, current, desired, h1_idx, end_idx in selected_candidates:
            if h1_idx >= len(result):
                _log(f"  -> skipped stale compression span h1_idx={h1_idx}, len={len(result)}")
                continue
            end_idx = min(end_idx, len(result))
            heading = result[h1_idx].get("heading", "Chapter") or "Chapter"
            old_span_sections = [dict(sec) for sec in result[h1_idx:end_idx]]
            ctx = _chapter_context(result, h1_idx, end_idx, char_limit=14000)
            prompt = (
                f'The PDF summary for "{book_title}" is over the user requested page limit. '
                f'Rewrite this chapter summary to about {desired} prose words while preserving coverage.\n\n'
                f'STRICT FORMAT RULES:\n'
                f'- First line must be exactly: # {heading}\n'
                f'- Preserve the chapter meaning, sequence, and key details, but remove repetition and secondary elaboration.\n'
                f'- Keep only the strongest details needed for a reader to understand the chapter.\n'
                f'- Include a final "### Key Takeaways" section with exactly {TAKEAWAY_BULLETS} concise bullets.\n'
                f'- Do not add unsupported facts. Do not include a research score.\n'
                f'- Return only the rewritten chapter.\n'
            )
            if instructions:
                prompt += f'- Respect these user instructions where possible: {instructions}\n'
            prompt += f'\nExisting chapter summary to compress:\n{ctx}'
            try:
                rewritten = _call_claude_full(
                    ai_client, prompt,
                    max_tokens=min(MAX_OUT_TOKENS_PER_CALL, int(desired * 2.3) + 1200),
                    job_id=job_id,
                    max_continuations=1,
                ).strip()
                parsed = _coerce_compressed_chapter_sections(rewritten, heading, old_sections=old_span_sections)
                before = _chapter_word_count(result, h1_idx, end_idx, exclude_takeaways=True)
                result = _replace_section_span(result, h1_idx, end_idx, parsed)
                result = _normalize_sections_for_pdf(result)
                span = _find_span_for_title(result, heading)
                after = _chapter_word_count(result, span[0], span[1], exclude_takeaways=True) if span else before
                if after < before:
                    made_progress = True
                _log(f"  -> compressed '{heading}': {before}->{after}, desired={desired}")
            except Exception as e:
                _log(f"  -> compression FAILED for '{heading}': {type(e).__name__}: {e}\n{traceback.format_exc()}")

        if not made_progress:
            _log("AI compression made no progress; switching to deterministic trim")
            break

    current_total = _summary_prose_word_count(result, chapter_targets)
    if current_total > int(target_total_words * 1.02):
        _log(f"AI compression still above target ({current_total}/{target_total_words}); applying deterministic safety trim")
        result = _deterministic_shrink_to_word_target(result, target_total_words, job_id=job_id)
    return _normalize_sections_for_pdf(result)

def _fixed_page_pdf_options(requested_pages):
    """Return include_toc/include_back flags for fixed-page outputs.

    Very small fixed-page requests cannot physically fit cover + TOC + back
    matter plus enough chapter prose inside a strict +10% window. Keep the
    branded cover, but omit optional front/back matter for compact outputs.
    """
    try:
        rp = int(requested_pages or 0)
    except Exception:
        rp = 0
    if rp and rp <= 8:
        return False, False
    if rp and rp <= 12:
        return True, False
    return True, True


def _build_pdf_and_count(out_path, sections, book_title, total_pages, cover_path,
                         author_info, similar_md, diff_label, diff_explain,
                         include_cover=True, include_toc=True, include_back=True,
                         bw=False, phone=False, cyan=False, summary_pages_override=None):
    """Build a PDF atomically and return its rendered page count.

    The fixed-page compressor may rebuild the same output path several times.
    Build into a temporary file first so a failed/corrupt rebuild never destroys
    the last valid PDF. If ReportLab or PdfReader hits a TOC edge case, retry
    with optional TOC/back matter disabled before failing the job.
    """
    sections = _normalize_sections_for_pdf(sections)
    attempts = [(include_toc, include_back, "requested")]
    if include_toc:
        attempts.append((False, include_back, "without_toc"))
    if include_back:
        attempts.append((False, False, "without_toc_or_back"))

    last_exc = None
    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    log_path = os.path.join(TMP_DIR, "pdf_error.log")

    for attempt_toc, attempt_back, attempt_name in attempts:
        tmp_path = None
        try:
            fd, tmp_path = tempfile.mkstemp(prefix="pdfbuild_", suffix=".pdf", dir=TMP_DIR)
            os.close(fd)
            build_pdf(
                out_path=tmp_path,
                sections=sections,
                book_title=book_title,
                total_pages=total_pages,
                cover_path=cover_path,
                author_info=author_info,
                similar_md=similar_md,
                diff_label=diff_label,
                diff_explain=diff_explain,
                include_cover=include_cover,
                include_toc=attempt_toc,
                include_back=attempt_back,
                bw=bw,
                phone=phone,
                cyan=cyan,
                summary_pages_override=summary_pages_override,
            )
            rendered = len(PdfReader(tmp_path).pages)
            if rendered <= 0:
                raise RuntimeError("PDF rendered with zero pages")
            os.replace(tmp_path, out_path)
            return rendered
        except Exception as exc:
            last_exc = exc
            try:
                with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                    f.write(
                        f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] "
                        f"PDF build/count attempt {attempt_name} failed: {type(exc).__name__}: {exc}\n"
                    )
            except Exception:
                pass
        finally:
            if tmp_path and os.path.exists(tmp_path):
                try:
                    os.remove(tmp_path)
                except Exception:
                    pass

    if last_exc:
        raise last_exc
    raise RuntimeError("PDF build failed for unknown reason")


def _refresh_cover_with_actual_page_count(out_path, sections, book_title, total_pages,
                                          cover_path, author_info, similar_md,
                                          diff_label, diff_explain, rendered_pages,
                                          include_toc=True, include_back=True):
    """Rebuild once so the cover's "This Summary" page count equals the actual PDF page count."""
    try:
        new_count = _build_pdf_and_count(
            out_path, sections, book_title, total_pages, cover_path, author_info,
            similar_md, diff_label, diff_explain, include_cover=True,
            include_toc=include_toc, include_back=include_back, summary_pages_override=rendered_pages,
        )
        if new_count != rendered_pages:
            new_count = _build_pdf_and_count(
                out_path, sections, book_title, total_pages, cover_path, author_info,
                similar_md, diff_label, diff_explain, include_cover=True,
                include_toc=include_toc, include_back=include_back, summary_pages_override=new_count,
            )
        return new_count
    except Exception:
        return rendered_pages


def _variant_max_pages(requested_pages, ratio=None):
    """Maximum pages allowed for downloadable variants.

    Main PDFs can be stricter (+10% in Standard mode). Variants use a universal
    +20% ceiling so phone/B&W/cyan never surprise the user with a much longer
    file than the requested summary.
    """
    try:
        rp = int(requested_pages or 0)
    except Exception:
        rp = 0
    if rp <= 0:
        return 0
    ratio = VARIANT_LENGTH_MAX_RATIO if ratio is None else float(ratio)
    return max(1, int(math.floor(rp * ratio + 1e-9)))




def _variant_page_cap(requested_pages, ratio=None):
    """Backward-compatible alias used by tests and diagnostics."""
    return _variant_max_pages(requested_pages, ratio=ratio)


def _build_variant_pdf_with_page_cap(out_path, sections, book_title, total_pages,
                                     cover_path, author_info, similar_md,
                                     diff_label, diff_explain, requested_pages=0,
                                     variant_name="variant", include_cover=True,
                                     include_toc=True, include_back=True,
                                     bw=False, phone=False, cyan=False):
    """Build a downloadable PDF variant and cap it to +20% when fixed pages are requested.

    This is deliberately deterministic: no Claude calls at download time. It
    first removes optional front/back matter, then trims prose while preserving
    H1 chapter coverage and Key Takeaways.
    """
    result = _final_output_quality_gate(_normalize_sections_for_pdf([dict(sec) for sec in sections]), job_id=None, book_title=book_title)
    requested_pages = int(requested_pages or 0)
    max_pages = _variant_max_pages(requested_pages)
    log_path = os.path.join(TMP_DIR, "variant_page_count.log")

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{variant_name}] {msg}\n")
        except Exception:
            pass

    pages = _build_pdf_and_count(
        out_path, result, book_title, total_pages, cover_path, author_info,
        similar_md, diff_label, diff_explain, include_cover=include_cover,
        include_toc=include_toc, include_back=include_back, bw=bw, phone=phone, cyan=cyan,
    )
    _log(f"initial pages={pages}, requested={requested_pages}, max={max_pages}, phone={phone}, bw={bw}, cyan={cyan}")

    if requested_pages <= 0 or pages <= max_pages:
        return result, pages

    # First, remove optional TOC/back matter. This preserves the actual summary.
    cur_toc, cur_back = include_toc, include_back
    if cur_toc or cur_back:
        cur_toc = False
        cur_back = False
        pages = _build_pdf_and_count(
            out_path, result, book_title, total_pages, cover_path, author_info,
            similar_md, diff_label, diff_explain, include_cover=include_cover,
            include_toc=cur_toc, include_back=cur_back, bw=bw, phone=phone, cyan=cyan,
        )
        _log(f"after optional-matter removal pages={pages}, max={max_pages}")
        if pages <= max_pages:
            return result, pages

    # Then apply deterministic shrink. This preserves chapter headings and takeaways.
    current_words = max(1, _summary_prose_word_count(result))
    for factor in (0.86, 0.72, 0.58, 0.44, 0.32, 0.22):
        try:
            target_words = max(1, int(current_words * factor))
            candidate = _compact_sections_for_page_cap(result, requested_pages=requested_pages, job_id=None, aggressive=True)
            candidate = _deterministic_shrink_to_word_target(candidate, target_words, job_id=None)
            pages = _build_pdf_and_count(
                out_path, candidate, book_title, total_pages, cover_path, author_info,
                similar_md, diff_label, diff_explain, include_cover=include_cover,
                include_toc=cur_toc, include_back=cur_back, bw=bw, phone=phone, cyan=cyan,
            )
            _log(f"shrink factor={factor}, target_words={target_words}, pages={pages}, max={max_pages}")
            result = candidate
            if pages <= max_pages:
                return result, pages
        except Exception as e:
            _log(f"shrink factor failed {factor}: {type(e).__name__}: {e}")

    # Fail closed for variants too: better to show a clear error than return a huge file.
    raise RuntimeError(
        f"{variant_name} PDF exceeded the +{int((VARIANT_LENGTH_MAX_RATIO - 1) * 100)}% cap: "
        f"requested {requested_pages}, maximum {max_pages}, rendered {pages}."
    )


def _build_pdf_with_page_enforcement(out_path, sections, book_title, total_pages,
                                     cover_path, author_info, similar_md,
                                     diff_label, diff_explain, ai_client,
                                     chapter_chunks, chapter_targets, job_id,
                                     instructions, requested_pages=None, strictness="standard"):
    """Build PDF and enforce fixed-page lower and upper bounds.

    v16 only enforced a lower bound, so a 75-page request could render as 110
    pages. v17 enforces a bounded window. By default, fixed-page summaries must
    be at least 98.5% of the request and no more than +10% of the request.
    """
    log_path = os.path.join(TMP_DIR, "page_count.log")

    def _log(msg):
        try:
            with open(log_path, "a", encoding="utf-8", errors="replace") as f:
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] {msg}\n")
        except Exception:
            pass

    result = _final_output_quality_gate(_normalize_sections_for_pdf([dict(sec) for sec in sections]), job_id=job_id, book_title=book_title)
    requested_pages = int(requested_pages or 0)
    include_toc, include_back = _fixed_page_pdf_options(requested_pages)
    rendered_pages = _build_pdf_and_count(
        out_path, result, book_title, total_pages, cover_path, author_info,
        similar_md, diff_label, diff_explain, include_cover=True,
        include_toc=include_toc, include_back=include_back,
    )
    _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note="initial build")

    if requested_pages <= 0:
        rendered_pages = _refresh_cover_with_actual_page_count(
            out_path, result, book_title, total_pages, cover_path, author_info,
            similar_md, diff_label, diff_explain, rendered_pages,
            include_toc=include_toc, include_back=include_back,
        )
        return result, rendered_pages

    min_pages, max_pages, target_pages = _fixed_page_bounds(requested_pages, strictness=strictness)
    max_ratio, _min_ratio, _target_ratio, _strictness_label = _strictness_settings(strictness)
    _log(
        f"page enforcement start: requested={requested_pages}, strictness={strictness}, min={min_pages}, "
        f"max={max_pages}, target={target_pages}, rendered={rendered_pages}, "
        f"include_toc={include_toc}, include_back={include_back}"
    )

    expand_rounds = 0
    compress_rounds = 0
    cap_compacted = False
    toc_compacted = False
    max_total_rounds = max(3, LENGTH_ENFORCE_MAX_ROUNDS + LENGTH_COMPRESS_MAX_ROUNDS + 6)

    for loop_n in range(1, max_total_rounds + 1):
        if min_pages <= rendered_pages <= max_pages:
            refreshed = _refresh_cover_with_actual_page_count(
                out_path, result, book_title, total_pages, cover_path, author_info,
                similar_md, diff_label, diff_explain, rendered_pages,
                include_toc=include_toc, include_back=include_back,
            )
            _log(f"page enforcement cover refresh: {rendered_pages}->{refreshed}")
            rendered_pages = refreshed
            if min_pages <= rendered_pages <= max_pages:
                _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note="within requested bounds")
                _log(f"page enforcement OK: requested={requested_pages}, rendered={rendered_pages}, bounds={min_pages}-{max_pages}")
                return result, rendered_pages

        if rendered_pages < min_pages:
            if expand_rounds >= LENGTH_ENFORCE_MAX_ROUNDS:
                _log(f"page enforcement cannot expand further: rendered={rendered_pages}, min={min_pages}")
                break
            expand_rounds += 1
            missing_pages = max(1, min_pages - rendered_pages)
            current_words = _summary_prose_word_count(result, chapter_targets)
            if rendered_pages > 0:
                page_ratio = min_pages / max(1, rendered_pages)
                extra_words = int(current_words * max(0.04, page_ratio - 1.0) * 1.06)
            else:
                extra_words = int(missing_pages * WORDS_PER_PAGE * FIXED_PAGE_WORD_RATIO)
            extra_words = max(250, min(extra_words, max(600, int(missing_pages * WORDS_PER_PAGE * FIXED_PAGE_WORD_RATIO * 2))))
            target_words = current_words + extra_words
            _log(
                f"expand round {expand_rounds}: rendered={rendered_pages}, "
                f"missing_pages={missing_pages}, current_words={current_words}, target_words={target_words}"
            )

            if job_id in jobs:
                jobs[job_id].update({
                    "progress": min(95, jobs[job_id].get("progress", 88) + 1),
                    "message": f"Expanding summary to reach requested {requested_pages} pages (currently {rendered_pages})...",
                    "last_update": time.time(),
                })

            result = _expand_summary_to_word_target(
                result, ai_client, book_title, chapter_chunks, chapter_targets,
                target_words, job_id, instructions, max_rounds=1,
            )
            rendered_pages = _build_pdf_and_count(
                out_path, result, book_title, total_pages, cover_path, author_info,
                similar_md, diff_label, diff_explain, include_cover=True,
                include_toc=include_toc, include_back=include_back,
            )
            _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note=f"expanded round {expand_rounds}")
            _log(f"expand round {expand_rounds} rebuilt: rendered={rendered_pages}")
            continue

        if rendered_pages > max_pages:
            if not cap_compacted:
                # v27: First remove optional verbosity that does not affect the
                # core guarantees (source coverage + Key Takeaways). This is much
                # cheaper and safer than asking the model to rewrite repeatedly.
                h1_count = len(_h1_spans(result))
                aggressive_compact = requested_pages <= 30 or rendered_pages > max_pages * 1.35 or h1_count >= max(10, requested_pages)
                result = _compact_sections_for_page_cap(result, requested_pages=requested_pages, job_id=job_id, aggressive=aggressive_compact)
                if aggressive_compact and (requested_pages <= 30 or h1_count > 18):
                    include_toc = False
                    include_back = False
                    toc_compacted = True
                rendered_pages = _build_pdf_and_count(
                    out_path, result, book_title, total_pages, cover_path, author_info,
                    similar_md, diff_label, diff_explain, include_cover=True,
                    include_toc=include_toc, include_back=include_back,
                )
                _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note="compact page-cap pass")
                _log(f"compact page-cap rebuilt: rendered={rendered_pages}, include_toc={include_toc}, include_back={include_back}, toc_compacted={toc_compacted}")
                cap_compacted = True
                continue

            if compress_rounds >= LENGTH_COMPRESS_MAX_ROUNDS:
                current_words = _summary_prose_word_count(result, chapter_targets)
                emergency_words = max(
                    1,
                    int(current_words * (max_pages / max(1, rendered_pages)) * 0.82),
                )
                _log(
                    f"emergency deterministic compression: rendered={rendered_pages}, "
                    f"max={max_pages}, current_words={current_words}, target_words={emergency_words}"
                )
                result = _compact_sections_for_page_cap(result, requested_pages=requested_pages, job_id=job_id, aggressive=True)
                result = _deterministic_shrink_to_word_target(result, emergency_words, job_id=job_id)
                rendered_pages = _build_pdf_and_count(
                    out_path, result, book_title, total_pages, cover_path, author_info,
                    similar_md, diff_label, diff_explain, include_cover=True,
                    include_toc=include_toc, include_back=include_back,
                )
                _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note="emergency deterministic compression")
                _log(f"emergency compression rebuilt: rendered={rendered_pages}")
                break

            compress_rounds += 1
            _start_stage(job_id, "compress", message=f"Compressing summary to stay within page cap ({rendered_pages} pages -> max {max_pages})...", progress=min(96, jobs.get(job_id, {}).get("progress", 88) + 1))
            current_words = _summary_prose_word_count(result, chapter_targets)
            target_words = max(
                1,
                int(current_words * (target_pages / max(1, rendered_pages)) * LENGTH_COMPRESS_SAFETY),
            )
            _log(
                f"compress round {compress_rounds}: rendered={rendered_pages}, max={max_pages}, "
                f"target_pages={target_pages}, current_words={current_words}, target_words={target_words}"
            )

            if job_id in jobs:
                _job_update(
                    job_id,
                    progress=min(96, jobs[job_id].get("progress", 88) + 1),
                    message=f"Compressing summary to stay within page cap ({rendered_pages} pages -> max {max_pages})...",
                    stage="compress",
                )

            pre_compress_result = [dict(sec) for sec in result]
            result = _compress_summary_to_word_target(
                result, ai_client, book_title, chapter_chunks, chapter_targets,
                target_words, job_id, instructions, max_rounds=1,
            )
            result = _normalize_sections_for_pdf(result)
            try:
                rendered_pages = _build_pdf_and_count(
                    out_path, result, book_title, total_pages, cover_path, author_info,
                    similar_md, diff_label, diff_explain, include_cover=True,
                    include_toc=include_toc, include_back=include_back,
                )
            except Exception as e:
                _log(
                    f"compress round {compress_rounds} rebuild failed after AI compression: "
                    f"{type(e).__name__}: {e}. Retrying deterministic shrink from last good sections."
                )
                fallback_words = max(1, int(target_words * 0.86))
                result = _deterministic_shrink_to_word_target(pre_compress_result, fallback_words, job_id=job_id)
                result = _normalize_sections_for_pdf(result)
                rendered_pages = _build_pdf_and_count(
                    out_path, result, book_title, total_pages, cover_path, author_info,
                    similar_md, diff_label, diff_explain, include_cover=True,
                    include_toc=include_toc, include_back=include_back,
                )
            _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note=f"compressed round {compress_rounds}")
            _log(f"compress round {compress_rounds} rebuilt: rendered={rendered_pages}")
            continue

    rendered_pages = _refresh_cover_with_actual_page_count(
        out_path, result, book_title, total_pages, cover_path, author_info,
        similar_md, diff_label, diff_explain, rendered_pages,
        include_toc=include_toc, include_back=include_back,
    )
    if rendered_pages > max_pages:
        _log(f"page enforcement still above cap after compression loops: requested={requested_pages}, max={max_pages}, rendered={rendered_pages}. Starting final progressive trim.")
        current_words = max(1, _summary_prose_word_count(result, chapter_targets))
        for factor in (0.78, 0.64, 0.50, 0.38, 0.28):
            try:
                candidate_words = max(1, int(current_words * factor))
                candidate = _compact_sections_for_page_cap(result, requested_pages=requested_pages, job_id=job_id, aggressive=True)
                candidate = _deterministic_shrink_to_word_target(candidate, candidate_words, job_id=job_id)
                cand_pages = _build_pdf_and_count(
                    out_path, candidate, book_title, total_pages, cover_path, author_info,
                    similar_md, diff_label, diff_explain, include_cover=True,
                    include_toc=False if requested_pages <= 35 else include_toc,
                    include_back=False if requested_pages <= 35 else include_back,
                )
                _record_last_valid_pdf(job_id, out_path, cand_pages, sections=candidate, note=f"progressive final trim factor {factor}")
                _log(f"progressive final trim factor={factor}: rendered={cand_pages}, target_words={candidate_words}")
                if min_pages <= cand_pages <= max_pages:
                    result, rendered_pages = candidate, cand_pages
                    break
                if cand_pages < min_pages:
                    # Use the closest compact undershoot as a base for the under-floor branch.
                    result, rendered_pages = candidate, cand_pages
                    break
                result, rendered_pages = candidate, cand_pages
            except Exception as e:
                _log(f"progressive final trim failed at factor={factor}: {type(e).__name__}: {e}")
        if rendered_pages > max_pages:
            _log(f"page enforcement FAILED: still above cap after progressive trim: requested={requested_pages}, max={max_pages}, rendered={rendered_pages}")
            if LENGTH_FAIL_ON_OVERSHOOT:
                raise RuntimeError(
                    f"Could not fit the summary within the +{int((max_ratio - 1) * 100)}% page cap: "
                    f"requested {requested_pages}, maximum {max_pages}, rendered {rendered_pages}. "
                    f"Try a larger requested page count or lower BBC_MIN_CHAPTER_WORDS."
                )
    elif rendered_pages < min_pages:
        _log(
            f"page enforcement below floor after normal expansion: requested={requested_pages}, "
            f"min={min_pages}, rendered={rendered_pages}. Starting final aggressive expansion."
        )
        missing_pages = max(1, min_pages - rendered_pages)
        current_words = _summary_prose_word_count(result, chapter_targets)
        target_words = current_words + max(900, int(missing_pages * WORDS_PER_PAGE * 1.25))
        result = _expand_summary_to_word_target(
            result, ai_client, book_title, chapter_chunks, chapter_targets,
            target_words, job_id, instructions, max_rounds=max(1, LENGTH_ENFORCE_MAX_ROUNDS)
        )
        rendered_pages = _build_pdf_and_count(
            out_path, result, book_title, total_pages, cover_path, author_info,
            similar_md, diff_label, diff_explain, include_cover=True,
            include_toc=include_toc, include_back=include_back,
        )
        _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note="final aggressive expansion")
        rendered_pages = _refresh_cover_with_actual_page_count(
            out_path, result, book_title, total_pages, cover_path, author_info,
            similar_md, diff_label, diff_explain, rendered_pages,
            include_toc=include_toc, include_back=include_back,
        )
        if min_pages <= rendered_pages <= max_pages:
            _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note="within requested bounds after final expansion")
            _log(f"page enforcement OK after final aggressive expansion: requested={requested_pages}, rendered={rendered_pages}, bounds={min_pages}-{max_pages}")
            return result, rendered_pages
        if rendered_pages > max_pages:
            _log(f"final expansion overshot cap: requested={requested_pages}, max={max_pages}, rendered={rendered_pages}. Trimming back toward window.")
            current_words = max(1, _summary_prose_word_count(result, chapter_targets))
            for factor in (max_pages / max(1, rendered_pages) * 0.92, max_pages / max(1, rendered_pages) * 0.78, 0.55, 0.40):
                candidate = _compact_sections_for_page_cap(result, requested_pages=requested_pages, job_id=job_id, aggressive=True)
                candidate = _deterministic_shrink_to_word_target(candidate, max(1, int(current_words * max(0.15, factor))), job_id=job_id)
                cand_pages = _build_pdf_and_count(
                    out_path, candidate, book_title, total_pages, cover_path, author_info,
                    similar_md, diff_label, diff_explain, include_cover=True,
                    include_toc=False if requested_pages <= 35 else include_toc,
                    include_back=False if requested_pages <= 35 else include_back,
                )
                _log(f"post-expansion trim factor={factor:.3f}: rendered={cand_pages}")
                if min_pages <= cand_pages <= max_pages:
                    _record_last_valid_pdf(job_id, out_path, cand_pages, sections=candidate, note="post-expansion trim within bounds")
                    return candidate, cand_pages
            raise RuntimeError(
                f"Could not fit the summary within the fixed-page window after final expansion: "
                f"requested {requested_pages}, allowed {min_pages}-{max_pages}, rendered {rendered_pages}."
            )
        # Last under-length rescue: add source-grounded learning notes until the
        # PDF reaches the lower bound or until it becomes clear that the request
        # cannot be satisfied inside the cap.
        for fill_round in range(1, 4):
            if rendered_pages >= min_pages:
                break
            missing_pages = max(1, min_pages - rendered_pages)
            _log(f"length expansion notes round {fill_round}: missing_pages={missing_pages}, rendered={rendered_pages}, min={min_pages}")
            result = _append_length_expansion_notes(result, ai_client, book_title, chapter_chunks, missing_pages, job_id, instructions)
            rendered_pages = _build_pdf_and_count(
                out_path, result, book_title, total_pages, cover_path, author_info,
                similar_md, diff_label, diff_explain, include_cover=True,
                include_toc=include_toc, include_back=include_back,
            )
            _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note=f"length expansion notes round {fill_round}")
            rendered_pages = _refresh_cover_with_actual_page_count(
                out_path, result, book_title, total_pages, cover_path, author_info,
                similar_md, diff_label, diff_explain, rendered_pages,
                include_toc=include_toc, include_back=include_back,
            )
            if rendered_pages > max_pages:
                _log(f"length expansion notes overshot cap: rendered={rendered_pages}, max={max_pages}")
                current_words = max(1, _summary_prose_word_count(result, chapter_targets))
                result = _deterministic_shrink_to_word_target(result, int(current_words * max_pages / max(1, rendered_pages) * 0.92), job_id=job_id)
                rendered_pages = _build_pdf_and_count(
                    out_path, result, book_title, total_pages, cover_path, author_info,
                    similar_md, diff_label, diff_explain, include_cover=True,
                    include_toc=include_toc, include_back=include_back,
                )
        if min_pages <= rendered_pages <= max_pages:
            _record_last_valid_pdf(job_id, out_path, rendered_pages, sections=result, note="within bounds after length expansion notes")
            _log(f"page enforcement OK after length expansion notes: requested={requested_pages}, rendered={rendered_pages}, bounds={min_pages}-{max_pages}")
            return result, rendered_pages
        _log(f"page enforcement FAILED: still below floor after final expansion: requested={requested_pages}, min={min_pages}, rendered={rendered_pages}")
        raise RuntimeError(
            f"Could not reach the requested fixed-page minimum: requested {requested_pages}, "
            f"minimum {min_pages}, rendered {rendered_pages}. Try a smaller strictness setting or a lower requested page count."
        )
    else:
        _log(f"page enforcement OK after final refresh: requested={requested_pages}, rendered={rendered_pages}, bounds={min_pages}-{max_pages}")
    return result, rendered_pages


# ── Background Job ─────────────────────────────────────────────────────────────
def run_job(job_id, source_bytes, api_key, title, instructions, style, length_mode, length_value, author="", strictness="standard", source_format="pdf", original_filename=""):
    try:
        _run_job(job_id, source_bytes, api_key, title, instructions, style, length_mode, length_value, author, strictness=strictness, source_format=source_format, original_filename=original_filename)
    except JobCancelled as e:
        if job_id in jobs:
            jobs[job_id].update({"status": "cancelled", "message": str(e), "error": "", "last_update": time.time()})
    except JobBudgetExceeded as e:
        if job_id in jobs:
            out_path = os.path.join(TMP_DIR, f"{job_id}_summary.pdf")
            restored = _restore_last_valid_pdf(job_id, out_path, int(length_value) if length_mode == "fixed" else 0)
            if restored:
                jobs[job_id].update({
                    "status": "done",
                    "progress": 100,
                    "message": f"Returned the last valid PDF after a time-budget stop ({restored} pages).",
                    "output_path": out_path,
                    "rendered_pages": restored,
                    "last_update": time.time(),
                })
            else:
                fail(job_id, str(e))
    except Exception as e:
        tb = traceback.format_exc()
        log_path = os.path.join(TMP_DIR, "pdf_error.log")
        with open(log_path, "a", encoding="utf-8", errors="replace") as f:
            f.write(f"\n--- JOB {job_id} ---\n{tb}\n")
        # v20 fallback: if a late PDF/compression stage fails after producing a
        # readable in-bounds PDF, return that instead of throwing away the job.
        out_path = os.path.join(TMP_DIR, f"{job_id}_summary.pdf")
        restored = _restore_last_valid_pdf(job_id, out_path, int(length_value) if length_mode == "fixed" else 0)
        if restored and job_id in jobs:
            jobs[job_id].update({
                "status": "done",
                "progress": 100,
                "message": f"Returned the last valid PDF after a late-stage recovery ({restored} pages).",
                "output_path": out_path,
                "rendered_pages": restored,
                "last_update": time.time(),
            })
        else:
            fail(job_id, str(e))

def _run_job(job_id, source_bytes, api_key, title, instructions, style, length_mode, length_value, author="", strictness="standard", source_format="pdf", original_filename=""):
    job = jobs[job_id]

    # Step 1 — Extract text (cached)
    job.update({"progress": 2, "message": f"Extracting text from {str(source_format).upper()}..."})
    try:
        pdf_data = _get_document_data(source_bytes, source_format=source_format, allow_ocr=True, job_id=job_id)
    except Exception as e:
        fail(job_id, f"Failed to open source file: {e}")
        return

    total_pages = pdf_data["pages"]
    full_text   = pdf_data["full_text"]
    page_texts  = pdf_data["page_texts"]
    if str(source_format).lower() == "epub":
        meta_title = pdf_data.get("metadata_title") or ""
        filename_base = clean_title(os.path.splitext(os.path.basename(str(original_filename or "")))[0])
        if meta_title and (not title or title == "Untitled Book" or _norm_title_key(title) == _norm_title_key(filename_base)):
            title = clean_title(meta_title) or str(meta_title)[:80]
            jobs[job_id]["title"] = title
        if not author and pdf_data.get("metadata_author"):
            author = pdf_data.get("metadata_author", "")
    else:
        filename_base = clean_title(os.path.splitext(os.path.basename(str(original_filename or "")))[0])
        if title and ("_" in str(title) or "--" in str(original_filename or "") or "Anna" in str(original_filename or "")):
            cleaned_pdf_title = clean_title(title) or filename_base
            if cleaned_pdf_title and cleaned_pdf_title != title:
                title = cleaned_pdf_title
                jobs[job_id]["title"] = title

    if len(full_text.strip()) < OCR_MIN_TEXT_CHARS:
        status = pdf_data.get("ocr_status", "text_layer")
        if str(source_format).lower() == "epub":
            fail(job_id, "Could not extract enough text to summarize from this EPUB. It may be DRM-protected or image-based.")
        else:
            fail(job_id, f"Could not extract enough text to summarize. OCR status: {status}. If this is a scanned/image PDF, install PyMuPDF, Pillow, pytesseract, and Tesseract OCR, or set BBC_OCR_ENABLED=1.")
        return

    jobs[job_id]["ocr_used"] = bool(pdf_data.get("ocr_used"))
    jobs[job_id]["ocr_status"] = pdf_data.get("ocr_status", "text_layer")
    jobs[job_id]["source_format"] = str(source_format).lower()

    # Step 2 — Target word count + style
    requested_pages = int(length_value) if length_mode == "fixed" else 0
    strictness = str(strictness or "standard").strip().lower()
    max_ratio, min_ratio, target_ratio, strictness_label = _strictness_settings(strictness)

    if length_mode == "percent":
        pct         = max(5, min(50, int(length_value))) / 100
        total_words = int(len(full_text.split()) * pct)
    else:
        total_words = _fixed_body_word_target(requested_pages)

    summary_tier = _length_tier(requested_pages, total_words)
    jobs[job_id].update({
        "requested_pages": requested_pages,
        "length_strictness": strictness_label,
        "summary_tier": summary_tier,
    })

    style_descriptions = {
        # ── NARRATIVE BASIC ──────────────────────────────────────────────────────
        "narrative_basic": (
            "Write in a warm, polished narrative voice — like a skilled nonfiction author who respects the reader's "
            "intelligence and time. Each paragraph flows naturally into the next; use transitional phrases that show "
            "how ideas connect and build. The tone should feel like a thoughtful, well-read friend explaining the "
            "chapter to you: direct, clear, and engaged. "
            "Do NOT write in academic register, do not hedge every sentence, and do not use bullet-point logic in "
            "the prose. State what the chapter argues confidently, show how the pieces fit together, and keep the "
            "reader moving. Subsection headings should be readable and descriptive, not generic ('Overview', 'Introduction')."
        ),
        # ── STORY-ARC NARRATIVE ──────────────────────────────────────────────────
        "story_arc": (
            "Frame every chapter as a story with a beginning, a middle, and an end — not a catalogue of topics. "
            "Open each section by establishing the context: what situation or question opens this chapter, what is "
            "at stake. Identify where the tension lives — what is contested, unsettled, or being worked out. "
            "Track the argument's movement: what the author discovers, tests, overturns, or resolves. "
            "Mark the turning point clearly — the key insight, reversal, or conclusion that shifts the frame. "
            "Close with the consequence: what the reader is left holding after this chapter. "
            "IMPORTANT: name your subsections to reflect this arc. Use headings like 'The Setup', 'The Problem', "
            "'The Discovery', 'The Turn', 'The Consequence' — not generic topic labels. "
            "Even in analytical nonfiction there is always a narrative spine. Find it and write along it. "
            "Do not write a list of claims — write a progression."
        ),
        # ── FEYNMAN STORYTELLER ───────────────────────────────────────────────────
        "feynman_storyteller": (
            "Write in Richard Feynman's teaching voice. You are a brilliant, enthusiastic teacher explaining this book "
            "to a smart friend who has never read it. Start every concept from first principles — state the problem "
            "before giving the solution. Translate every abstract idea into a concrete everyday analogy or real-world "
            "scenario that makes it click instantly. Strip all jargon; when a technical term is unavoidable, immediately "
            "explain it in plain conversational English. Use short, punchy sentences. Address the reader directly with "
            "'you'. Ask rhetorical questions and answer them. Highlight what is surprising, counterintuitive, or "
            "commonly misunderstood. Build each idea from the previous one so the reader can feel the logic click into "
            "place step by step. The tone must be warm, curious, and conversational throughout — never academic, "
            "formal, or detached. Avoid long winding paragraphs; land one clear idea per paragraph. The writing "
            "should feel like an excited, knowledgeable friend talking to you, not a textbook."
        ),
        # ── INVESTIGATIVE NARRATIVE ───────────────────────────────────────────────
        "investigative_narrative": (
            "Write like an investigative journalist following a trail of cause and effect. "
            "For every idea or claim in the chapter, ask: Who decided this? What was at stake? What evidence existed "
            "and what was overlooked or contested? What were the motives and incentives? What changed as a result, "
            "and who bore the cost? Trace the intellectual genealogy of each argument: where did it come from, who "
            "challenged it, what happened when it was tested in the real world. "
            "Write in vivid, concrete detail — use names, numbers, and specific consequences, not abstractions. "
            "Structure subsections like a chain of events: 'The Problem', 'The Evidence', 'The Resistance', "
            "'The Consequences' — not generic topic headings. "
            "Key Takeaways should read like investigation conclusions — specific findings, not general observations. "
            "Tone: serious, purposeful, and factual. Vivid but never sensationalised."
        ),
        # ── STRATEGIC BRIEFING ────────────────────────────────────────────────────
        "strategic_briefing": (
            "Write like a senior analyst briefing a busy executive who has ten minutes and needs to act on this. "
            "Lead every section with the verdict, not the setup: 'The core claim here is X. The implication is Y. "
            "The risk of ignoring it is Z.' Use short, crisp, declarative sentences. "
            "Prioritise in this order: what the chapter claims, what evidence supports it, what changed or is changing, "
            "what the decision-maker should do differently, what risks or second-order effects to watch. "
            "Do NOT use narrative storytelling, literary flourishes, or slow build-ups to the point. "
            "Get to the verdict in the FIRST sentence of every paragraph. "
            "Name subsections with executive language: 'Core Thesis', 'Supporting Evidence', 'Decision Implications', "
            "'Risk Factors', 'Watch Items'. "
            "Key Takeaways MUST be action items — 'Do X', 'Stop Y', 'Monitor Z' — not descriptions of what the author said."
        ),
        # ── DEEP READING ──────────────────────────────────────────────────────────
        "deep_reading": (
            "Write as a patient, thorough intellectual companion who reads BETWEEN the lines — not just what the "
            "author argues, but HOW and WHY they argue it. For every major idea, ask: what rhetorical or logical "
            "purpose does this section serve in the larger argument? What implicit assumption is the author relying on? "
            "What counterargument are they pre-empting without naming it? What is deliberately left unresolved? "
            "When the author gives an example, interrogate it: what does this example actually prove? Does it fully "
            "support the claim, or only partially? What would a sceptical reader say? "
            "Preserve secondary arguments, tensions between ideas, and the author's own qualifications — do not "
            "flatten them into the main headline. "
            "The output should feel like an annotated reading, not a summary. It should feel fundamentally different "
            "from simply reporting what the chapter says: it should feel like thinking aloud at the margins of the book. "
            "Write in the voice of a careful, curious reader who is genuinely working through the argument — not "
            "reporting it from above. Never rush to the conclusion; sit with the complexity."
        ),
        # ── PRACTICAL PLAYBOOK ────────────────────────────────────────────────────
        "practical_playbook": (
            "Write like you are distilling this chapter into a field manual for someone who wants to apply it tomorrow. "
            "Every major concept MUST become either: a principle ('Always X when Y'), a specific behaviour "
            "('When you notice X, do Y'), a warning ('Avoid Z because it leads to W'), or a concrete example "
            "that proves the rule. Use imperative, direct language: 'Stop doing X' not 'the author suggests avoiding X'. "
            "Keep enough narrative context to explain WHY each principle matters, but always return to the actionable lesson. "
            "Name subsections with action-oriented labels: 'The Core Rule', 'How to Apply It', 'The Trap to Avoid', "
            "'In Practice'. "
            "Key Takeaways MUST be rules someone can follow immediately — not observations about what the book said. "
            "If the chapter contains a framework, list, or checklist, preserve it explicitly and label it as such. "
            "Avoid passive or hedged language. Every sentence should either state a principle or support one."
        ),
        # ── LITERARY ESSAY ────────────────────────────────────────────────────────
        "literary_essay": (
            "Write like a literary critic reviewing this chapter for The Atlantic or The New York Review of Books. "
            "Do not merely summarise — interpret. What is the author really doing in this chapter? What intellectual "
            "tradition or argument are they drawing on? What makes the argument elegant or persuasive, and where "
            "does it strain or leave important questions unaddressed? "
            "Be willing to evaluate as well as describe: 'this argument is particularly persuasive because...', "
            "'the chapter is less convincing when...', 'what the author is really after here is...'. "
            "Use precise, elegant prose with varied sentence rhythms. Prioritise insight over comprehensive coverage. "
            "Subsection headings should be thematic and evocative — not generic topic labels. "
            "The voice should be confident, cultured, and slightly interpretive: you have an informed view of the work "
            "and you share it. Do not be neutral or merely descriptive."
        ),
        # ── ACADEMIC ──────────────────────────────────────────────────────────────
        "academic": (
            "Write with the precision and rigour of a scholarly paper aimed at an intelligent non-specialist. "
            "Define key terms explicitly before using them. State claims carefully and qualify them where appropriate: "
            "'the evidence suggests...', 'under the assumption that...', 'this holds when...'. "
            "Separate what the author claims from the evidence they provide for it. Identify the logical structure "
            "of the argument explicitly where helpful: 'the argument proceeds as follows...', "
            "'this conclusion depends on the premise that...'. "
            "Where the author addresses counterarguments, represent both sides before stating which is better supported. "
            "Do NOT make strong claims the text does not support. Do NOT omit the qualifications the author makes. "
            "Use precise, hedged analytical language throughout — rigorous but still readable, not sterile jargon. "
            "Key Takeaways should be carefully qualified propositions, not slogans or imperatives."
        ),
        # ── BACKWARD-COMPATIBLE ALIASES ───────────────────────────────────────────
        "narrative": (
            "Write in a warm, polished narrative voice — like a skilled nonfiction author who respects the reader's "
            "intelligence and time. Each paragraph flows naturally into the next with clear transitions. "
            "The tone should feel like a thoughtful, well-read friend explaining the chapter: direct, clear, engaged. "
            "Do not write in academic register or hedge every sentence. State what the chapter argues confidently "
            "and keep the reader moving."
        ),
        "concise": (
            "Write in a warm, polished narrative voice — like a skilled nonfiction author who respects the reader's "
            "intelligence and time. Each paragraph flows naturally into the next with clear transitions. "
            "The tone should feel like a thoughtful, well-read friend explaining the chapter: direct, clear, engaged. "
            "Do not write in academic register or hedge every sentence. State what the chapter argues confidently "
            "and keep the reader moving."
        ),
        "bullet": (
            "Write in Richard Feynman's teaching voice. You are a brilliant, enthusiastic teacher explaining this "
            "to a smart friend who has never read it. Use plain language, concrete everyday analogies, short punchy "
            "sentences, direct 'you' address, and rhetorical questions answered immediately. "
            "Ask: why is this surprising? What's the simplest way to say this? What would happen if the opposite were true? "
            "Use bullets only where they genuinely improve clarity over prose. The default should still be flowing, "
            "conversational paragraphs — not a bullet dump."
        ),
        "narrative_explainer": (
            "Write in Richard Feynman's teaching voice. You are a brilliant, enthusiastic teacher explaining this book "
            "to a smart friend who has never read it. Start every concept from first principles — state the problem "
            "before giving the solution. Translate every abstract idea into a concrete everyday analogy. "
            "Strip all jargon; explain any unavoidable technical term in plain English immediately. "
            "Use short sentences, direct 'you' address, and rhetorical questions. Highlight what is surprising or "
            "counterintuitive. The tone must be warm, curious, and conversational — never academic or formal. "
            "Land one clear idea per paragraph. Do not write like a textbook."
        ),
        "narrative_editorial": (
            "Frame every chapter as a story with a beginning, middle, and end. Open by establishing context and stakes. "
            "Track the argument's movement through tension, discovery, and resolution. Mark the key turning point. "
            "Close with consequence. Name subsections to reflect the arc — 'The Setup', 'The Turn', 'The Consequence'. "
            "Write with polished editorial transitions and a coherent beginning-to-end throughline. "
            "Do not write a list of claims — write a progression."
        ),
        "narrative_deep": (
            "Write as a patient, thorough intellectual companion. Not just what the author argues but how: the structure "
            "of the reasoning, where tensions live, what examples reveal, what is assumed. Go below the surface: "
            "what is the deeper claim? What does it rest on? Preserve nuance, secondary arguments, and logical "
            "connections. Write reflectively and richly. Feel like thinking alongside the book, not summarising it."
        ),
    }
    style_desc = style_descriptions.get(style, style_descriptions["narrative_basic"])
    # v46: override the legacy soft description with a hard style contract so
    # live Claude output visibly changes across styles rather than collapsing
    # into the same generic summary voice.
    style = _canonical_style_id(style)
    style_desc = _style_contract(style)
    jobs[job_id]["style"] = style

    ai_client = _make_ai_client(api_key, timeout_seconds=180.0)

    # Step 3 — Chapter-aware chunking (G4a/G4b)
    job.update({"progress": 4, "message": "Detecting chapters..."})
    if str(source_format).lower() == "epub" and pdf_data.get("chapter_list"):
        chapter_list = pdf_data.get("chapter_list") or []
        detection_source = "epub_spine_locked"
    else:
        chapter_list, detection_source = _resolve_chapter_list(
            source_bytes, page_texts, ai_client, job_id
        )

    # Build enough chunks that each model call has a realistic output target.
    # v9 could get stuck in an infinite loop at the 10k char floor and, even
    # when it did not hang, too few huge chunks caused long fixed-page summaries
    # to top out around 30-40 pages. Here the desired chunk count scales with
    # requested output length and the guard always makes forward progress.
    target_chunk_count = max(
        1,
        min(MAX_SUMMARY_CHUNKS, math.ceil(max(1, total_words) / max(1, HAIKU_RELIABLE_WORDS))),
    )
    max_chars_guard = CHARS_PER_CHUNK
    while True:
        chapter_chunks = _build_chapter_chunks(full_text, page_texts, chapter_list, max_chars_guard)
        n_chunks = len(chapter_chunks)
        if n_chunks == 0:
            fail(job_id, "Could not split extracted text into summarizable chunks.")
            return
        if n_chunks >= target_chunk_count or max_chars_guard <= MIN_CHARS_PER_CHUNK:
            break
        next_chars = max(max_chars_guard // 2, MIN_CHARS_PER_CHUNK)
        if next_chars == max_chars_guard:
            break
        max_chars_guard = next_chars

    target_words_per_chunk = max(300, math.ceil(total_words / max(1, n_chunks)))
    chapter_manifest = _build_chapter_manifest(
        chapter_chunks, chapter_list=chapter_list, page_texts=page_texts,
        source_format=source_format, detection_source=detection_source
    )
    if chapter_manifest:
        jobs[job_id]["chapter_manifest"] = chapter_manifest
        jobs[job_id]["chapter_manifest_count"] = len(chapter_manifest)
        _audit_event(job_id, "chapter_manifest_built", detection_source=detection_source, count=len(chapter_manifest), titles=_manifest_expected_titles(chapter_manifest)[:40])

    chapter_targets = _rebalance_chapter_targets(
        _chapter_targets_from_chunks(chapter_chunks, target_words_per_chunk), total_words
    )
    if chapter_manifest:
        chapter_targets = _apply_manifest_targets(chapter_targets, chapter_manifest, total_words)
    if chapter_targets:
        target_words_per_chunk = max(300, math.ceil(sum(m.get("target", 0) for m in chapter_targets.values()) / max(1, n_chunks)))
    _write_chapter_manifest_artifacts(job_id, chapter_manifest, {"stage": "built"}, chapter_targets)

    feasibility = _estimate_feasibility(
        total_pages, len(chapter_targets), requested_pages, ocr_used=bool(pdf_data.get("ocr_used"))
    )
    jobs[job_id]["feasibility"] = feasibility
    if requested_pages and feasibility.get("level") == "not_recommended":
        jobs[job_id]["warning"] = feasibility.get("message")

    force_refresh_takeaway_keys = {
        key for key, meta in chapter_targets.items() if int(meta.get("chunks", 1)) > 1
    }
    # max_tokens needs HEADROOM so Haiku doesn't hit the wall mid-sentence.
    # v7 used `* 1.6` which was barely above the word target, causing the
    # mid-sentence breaks on pages 14/20/31 of the broken output.  At
    # 2.5× + 1000-token base, even when Haiku overshoots the word target
    # by 50% it still has runway to finish cleanly.
    max_tokens_per_chunk   = min(
        MAX_OUT_TOKENS_PER_CALL,
        max(4000, int(target_words_per_chunk * 2.5) + 1000),
    )

    # Step 4 — Summarize chapters in parallel (G6)
    _start_stage(job_id, "summarize", progress=5, message=f"Summarizing {n_chunks} chapters...")

    summaries_map = {}
    completed     = [0]
    state_lock    = threading.Lock()

    with ThreadPoolExecutor(max_workers=max(1, SUMMARY_MAX_WORKERS)) as ex:
        future_map = {
            ex.submit(
                _summarize_chapter, ai_client, i, chunk, n_chunks, title,
                instructions, style_desc, target_words_per_chunk,
                max_tokens_per_chunk, job_id, summary_tier=summary_tier, style=style
            ): i
            for i, chunk in enumerate(chapter_chunks)
        }
        for future in as_completed(future_map):
            idx, summary, rs, rr, ct = future.result()   # propagates exception to caller
            # v51: bind the model response to the source manifest chunk title before
            # merging/parsing so Claude cannot rename or split H1 chapters.
            try:
                expected_chunk_title = chapter_chunks[idx].get("title", "")
                summary = _force_summary_to_chunk_heading(summary, expected_chunk_title)
                ct = _normalize_source_chapter_heading(expected_chunk_title) or ct
            except Exception:
                pass
            _check_job_control(job_id, "summarize")
            with state_lock:
                completed[0] += 1
                pct_done = 5 + int(60 * completed[0] / n_chunks)
                ch_list  = job.get("chapters", [])
                ch_list.append({"index": idx, "title": ct,
                                "research_score": rs, "research_reason": rr})
                _job_update(job_id, progress=pct_done, message=f"Summarized chapter {completed[0]} of {n_chunks}...", stage="summarize", chapters=ch_list)
            summaries_map[idx] = summary

    summaries = [summaries_map[i] for i in range(n_chunks)]

    # Step 5 — Merge multi-part chapter summaries (G4d)
    job.update({"progress": 66, "message": "Merging chapter parts..."})
    full_summary = _merge_multipart_summaries("\n\n".join(summaries))

    # Step 6 - Parse chapter summaries. v38 removes the old book-level
    # "Final Key Takeaways" section because live runs showed it could become
    # generic and underwhelming. Chapter-level takeaways remain mandatory.
    job.update({"progress": 68, "message": "Structuring chapter summaries..."})

    sections = parse_sections(full_summary)
    # v51: put model-created H1s back into canonical source order before any
    # audits or coverage recovery. This prevents early drift from becoming a
    # page-budgeting or coverage problem.
    sections, manifest_report = _lock_sections_to_manifest(sections, chapter_manifest, job_id=job_id)
    _write_chapter_manifest_artifacts(job_id, chapter_manifest, manifest_report, chapter_targets)
    sections = _prepend_executive_summary(sections, ai_client, title, job_id, summary_tier=summary_tier, style_desc=style_desc, instructions=instructions)
    sections = _insert_faithfulness_note(sections, title, detection_source=detection_source)

    # Step 7 — Audit chapter completeness (G2)
    _start_stage(job_id, "audit", progress=70, message="Auditing chapters...")
    target_words_per_chapter = max(
        MIN_CHAPTER_WORDS,
        math.ceil(total_words / max(1, len(chapter_targets))),
    )
    _audit_log = os.path.join(TMP_DIR, "audit.log")
    try:
        with open(_audit_log, "a", encoding="utf-8", errors="replace") as f:
            f.write(
                f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] "
                f"audit start: detection={detection_source}, n_chunks={n_chunks}, "
                f"target_chunk_count={target_chunk_count}, max_chars={max_chars_guard}, "
                f"per_chunk_target={target_words_per_chunk}, "
                f"chapter_targets={len(chapter_targets)}, total_target={total_words}\n"
            )
    except Exception:
        pass
    sections = _audit_sections(
        sections, ai_client, title, target_words_per_chapter, job_id, instructions,
        chapter_targets=chapter_targets,
        force_refresh_takeaway_keys=force_refresh_takeaway_keys,
        summary_tier=summary_tier, style=style,
    )

    # Step 8 — Verify chapter coverage (G4c) — fail-closed
    job.update({"progress": 76, "message": "Verifying chapter coverage..."})
    expected_titles = _manifest_expected_titles(chapter_manifest) or _unique_expected_titles(chapter_chunks)
    sections = _verify_chapter_coverage(
        sections, expected_titles, ai_client, chapter_chunks,
        title, instructions, style_desc, target_words_per_chunk,
        max_tokens_per_chunk, job_id, summary_tier=summary_tier, style=style
    )
    still_missing = _find_missing_chapter_chunks(sections, expected_titles, chapter_chunks)
    if still_missing:
        missing_names = _unique_expected_titles(still_missing)
        fail(job_id, f"Summary incomplete - chapters still missing after retries: {missing_names}")
        return

    # Coverage recovery can append new H1 sections after the first audit. Run a
    # second targeted audit so recovered chapters also receive sufficient prose
    # and their own Key Takeaways section.
    _start_stage(job_id, "audit", progress=78, message="Final chapter audit...")
    sections = _audit_sections(
        sections, ai_client, title, target_words_per_chapter, job_id, instructions,
        chapter_targets=chapter_targets,
        force_refresh_takeaway_keys=set(),
        summary_tier=summary_tier, style=style,
    )

    requested_pages = int(length_value) if length_mode == "fixed" else 0
    if requested_pages > 0:
        _job_update(job_id, progress=79, message="Checking requested summary length...", stage="audit")
        sections = _expand_summary_to_word_target(
            sections, ai_client, title, chapter_chunks, chapter_targets,
            total_words, job_id, instructions, max_rounds=2,
        )

    # v46: if a non-basic style was selected, verify the style is actually
    # visible in headings/prose and rewrite weak chapters before final recap.
    _job_update(job_id, progress=79, message="Checking selected writing style...", stage="audit")
    sections = _style_application_gate(
        sections, ai_client, title, style, style_desc, job_id, summary_tier=summary_tier
    )

    # v38: replace the old Feynman Storyline / Final Review Sheet / Final Key
    # Takeaways appendices with one polished final recap. This happens after
    # any length top-up so the recap remains the final reader-facing section.
    sections = _remove_deprecated_final_sections(sections)
    sections = _append_summary_of_summary(
        sections, ai_client, title, job_id, requested_pages=requested_pages,
        detection_source=detection_source, source_format=source_format, summary_tier=summary_tier, style_desc=style_desc,
    )
    sections = _remove_deprecated_final_sections(sections)
    sections = _final_output_quality_gate(sections, job_id=job_id, book_title=title)
    sections, manifest_report = _lock_sections_to_manifest(sections, chapter_manifest, job_id=job_id)
    _write_chapter_manifest_artifacts(job_id, chapter_manifest, manifest_report, chapter_targets)
    if chapter_manifest and (manifest_report.get("missing") or manifest_report.get("out_of_order")):
        missing_titles = manifest_report.get("missing") or []
        # v52: only hard-fail when the gap is large or chapters are out of order.
        # A small number of missing chapters (typically from the model renaming a
        # quirky title) is tolerated so the PDF still builds with whatever
        # chapters were produced.
        if manifest_report.get("out_of_order") or len(missing_titles) > CHAPTER_MANIFEST_MAX_MISSING:
            fail(job_id, f"Chapter manifest validation failed before PDF build: {manifest_report}")
            return
        _audit_event(job_id, "chapter_manifest_missing_tolerated",
                     missing=missing_titles, missing_count=len(missing_titles),
                     max_allowed=CHAPTER_MANIFEST_MAX_MISSING,
                     expected=manifest_report.get("expected_count"),
                     matched=manifest_report.get("matched_count"))
        job_warn = f"Note: {len(missing_titles)} chapter(s) could not be matched and were skipped: {', '.join(t for t in missing_titles if t)}."
        try:
            jobs[job_id]["warning"] = job_warn
        except Exception:
            pass

    # Step 9 — Fetch metadata in parallel
    job.update({"progress": 80, "message": "Fetching book metadata..."})

    cover_path   = None
    author_info  = {"author": "", "bio": ""}
    similar_md   = ""
    diff_label   = "Moderate"
    diff_explain = ""

    def fetch_cover_task():
        nonlocal cover_path, author_info
        cover_url, info = fetch_book_cover(title, author=author)
        if cover_url and info:
            author_info = info
            path        = os.path.join(TMP_DIR, f"{job_id}_cover.jpg")
            cover_path  = download_cover(cover_url, path)

    def fetch_similar_task():
        nonlocal similar_md
        try:
            prompt = f'Suggest 5 similar books to "{title}". Format each as: **Title** by Author — reason'
            resp   = ai_client.messages.create(
                model=MODEL_CHUNK,
                max_tokens=400,
                messages=[{"role": "user", "content": prompt}]
            )
            similar_md = _anthropic_text(resp)
        except Exception:
            similar_md = ""

    def fetch_difficulty_task():
        nonlocal diff_label, diff_explain
        try:
            prompt = (
                f'Rate the reading difficulty of "{title}". '
                f'Reply as: SCORE|LABEL|explanation (score 1-5, label like Beginner/Moderate/Advanced)'
            )
            resp  = ai_client.messages.create(
                model=MODEL_CHUNK,
                max_tokens=200,
                messages=[{"role": "user", "content": prompt}]
            )
            parts = _anthropic_text(resp).strip().split("|", 2)
            if len(parts) == 3:
                diff_label   = parts[1].strip()
                diff_explain = parts[2].strip()
        except Exception:
            pass

    with ThreadPoolExecutor(max_workers=max(1, min(4, SUMMARY_MAX_WORKERS))) as ex:
        futures = [
            ex.submit(fetch_cover_task),
            ex.submit(fetch_similar_task),
            ex.submit(fetch_difficulty_task),
        ]
        for f in futures:
            try:
                f.result()
            except Exception:
                pass

    # Step 10 — Build PDF. For fixed-page requests, build once, verify the
    # rendered page count, then expand/rebuild until it reaches the requested
    # length or the configured retry limit.
    _job_update(job_id, progress=88, message="Building PDF...", stage="pdf")
    out_path = os.path.join(TMP_DIR, f"{job_id}_summary.pdf")

    try:
        sections, rendered_pages = _build_pdf_with_page_enforcement(
            out_path=out_path,
            sections=sections,
            book_title=title,
            total_pages=total_pages,
            cover_path=cover_path,
            author_info=author_info,
            similar_md=similar_md,
            diff_label=diff_label,
            diff_explain=diff_explain,
            ai_client=ai_client,
            chapter_chunks=chapter_chunks,
            chapter_targets=chapter_targets,
            job_id=job_id,
            instructions=instructions,
            requested_pages=requested_pages,
            strictness=strictness,
        )
        page_log = os.path.join(TMP_DIR, "page_count.log")
        with open(page_log, "a", encoding="utf-8", errors="replace") as f:
            req_pages = requested_pages if requested_pages else "N/A"
            f.write(
                f"[{time.strftime('%Y-%m-%d %H:%M:%S')}][{job_id}] "
                f"title={title!r} requested_pages={req_pages} "
                f"target_words={total_words} rendered_pages={rendered_pages} "
                f"ocr_used={bool(pdf_data.get('ocr_used'))} "
                f"ocr_status={pdf_data.get('ocr_status', 'text_layer')}\n"
            )
        jobs[job_id]["rendered_pages"] = rendered_pages
        jobs[job_id]["requested_pages"] = requested_pages
    except Exception as e:
        tb = traceback.format_exc()
        log_path = os.path.join(TMP_DIR, "pdf_error.log")
        with open(log_path, "a", encoding="utf-8", errors="replace") as f:
            f.write(f"\n--- PDF BUILD {job_id} ---\n{tb}\n")
        fail(job_id, f"PDF build failed: {e}")
        return

    jobs[job_id]["build_meta"] = {
        "sections":    sections,
        "total_pages": total_pages,
        "cover_path":  cover_path,
        "author_info": author_info,
        "similar_md":  similar_md,
        "diff_label":  diff_label,
        "diff_explain":diff_explain,
    }

    # Step 11 — Build phone PDF. v34 caps phone output to +20% of the fixed-page request.
    phone_path = os.path.join(TMP_DIR, f"{job_id}_phone.pdf")
    try:
        _phone_sections, phone_pages = _build_variant_pdf_with_page_cap(
            out_path=phone_path,
            sections=sections,
            book_title=title,
            total_pages=total_pages,
            cover_path=cover_path,
            author_info=author_info,
            similar_md=similar_md,
            diff_label=diff_label,
            diff_explain=diff_explain,
            requested_pages=requested_pages,
            variant_name=f"{job_id}:phone",
            include_cover=True,
            include_toc=True,
            include_back=True,
            phone=True,
        )
        jobs[job_id]["phone_rendered_pages"] = phone_pages
        jobs[job_id]["phone_max_pages"] = _variant_max_pages(requested_pages)
        _audit_event(job_id, "variant_built", variant="phone", rendered_pages=phone_pages, max_pages=_variant_max_pages(requested_pages))
    except Exception as e:
        phone_path = None
        jobs[job_id]["phone_error"] = str(e)
        _audit_event(job_id, "variant_failed", variant="phone", error=str(e))

    jobs[job_id]["phone_path"] = phone_path

    # Step 12 — Build PDF splits when the original is a PDF + save to both clouds
    st     = _safe_title(title)
    if str(source_format).lower() == "pdf":
        splits = smart_split_pdf(source_bytes, st, page_texts=page_texts)
    else:
        splits = []

    original_ext = _source_extension(source_format)
    original_path = os.path.join(TMP_DIR, f"{job_id}_original{original_ext}")
    with open(original_path, "wb") as f:
        f.write(source_bytes)

    part_paths = []
    for i, (filename, part_bytes) in enumerate(splits):
        pp = os.path.join(TMP_DIR, f"{job_id}_part{i+1}.pdf")
        with open(pp, "wb") as f:
            f.write(part_bytes)
        part_paths.append((filename, pp))
    if phone_path and os.path.exists(phone_path):
        part_paths.append((f"{st} — PHONE.pdf", phone_path))

    jobs[job_id]["original_path"] = original_path
    jobs[job_id]["original_ext"]  = original_ext
    jobs[job_id]["part_paths"]    = part_paths

    gdrive_root   = find_gdrive_root()
    onedrive_root = find_onedrive_root()

    gdrive_folder   = save_bundle_to_root(gdrive_root,   source_bytes, out_path, title, splits=splits, phone_path=phone_path, source_format=source_format)
    onedrive_folder = save_bundle_to_root(onedrive_root, source_bytes, out_path, title, splits=splits, phone_path=phone_path, source_format=source_format)

    # Step 13 — Share token + done
    share_token = uuid.uuid4().hex
    shares[share_token] = {
        "title": title, "sections": sections, "book_pages": total_pages,
        "created_at": time.time(),
    }

    saved_to = []
    if gdrive_folder:   saved_to.append("Google Drive")
    if onedrive_folder: saved_to.append("OneDrive")
    if saved_to:
        done_msg = f"Complete! Also saved to {' & '.join(saved_to)}."
    else:
        done_msg = "Complete! (Cloud sync not detected — see cloud_save.log for details.)"

    if jobs[job_id].get("status") != "error":
        jobs[job_id].update({
            "status":      "done",
            "progress":    100,
            "message":     done_msg,
            "output_path": out_path,
            "share_token": share_token,
        })
        _history_add({
            "id":         job_id,
            "type":       "book",
            "title":      title,
            "created_at": time.time(),
            "pdf_path":   out_path,
        })

# ── PDF Builder ────────────────────────────────────────────────────────────────

# ── v40 reader-friendly output layout helpers ─────────────────────────────────
def _is_bare_chapter_heading(title):
    t = re.sub(r"\s+", " ", str(title or "")).strip()
    if not t:
        return False
    if re.match(r"^chapter\s+(\d{1,3}|[ivxlcdm]{1,8})\s*$", t, re.I):
        return True
    if re.match(r"^chapter\s+(\d{1,3}|[ivxlcdm]{1,8})\s*[:.\-]\s*$", t, re.I):
        return True
    return False


def _looks_like_real_chapter_subtitle(text):
    t = re.sub(r"\s+", " ", str(text or "")).strip(" .:-–—")
    if not t:
        return False
    key = _norm_title_key(t)
    bad = {
        "overview", "summary", "chapteroverview", "sectionoverview", "thechapter", "keytakeaways",
        "practicalapplication", "commonmistaketoavoid", "background", "context", "introduction",
        "opening", "conclusion", "finalthoughts", "mainideas", "centralargument", "coreargument",
    }
    if key in bad or "takeaway" in key:
        return False
    words = t.split()
    if len(words) > 16:
        return False
    # Must look like a title rather than a sentence fragment/prose line.
    if re.search(r"[.!?]$", t):
        return False
    alpha = [w for w in words if re.search(r"[A-Za-z]", w)]
    if not alpha:
        return False
    titleish = sum(1 for w in alpha if w[:1].isupper() or w.lower() in {"of", "the", "and", "or", "in", "to", "a", "an", "with", "for", "on", "by", "from"})
    return titleish / max(1, len(alpha)) >= 0.55


def _extract_chapter_subtitle_from_body(body):
    lines = [ln.strip() for ln in str(body or "").splitlines() if ln.strip()]
    if not lines:
        return "", body
    first = re.sub(r"^#+\s*", "", lines[0]).strip()
    if _looks_like_real_chapter_subtitle(first):
        # Remove only the first occurrence; leave the rest unchanged.
        remainder = "\n".join(lines[1:]).strip()
        return first, (remainder + "\n" if remainder else "")
    return "", body


def _promote_bare_chapter_titles(sections):
    """Make output headings read as 'Chapter N: Title' when the model/source
    produced a bare 'Chapter N' H1 and placed the real title in the first H2 or
    first body line. This is cosmetic and preserves the underlying content.
    """
    if not PDF_CHAPTER_TITLE_PROMOTION:
        return list(sections or [])
    src = [dict(s) for s in sections or []]
    out = []
    i = 0
    while i < len(src):
        sec = dict(src[i])
        try:
            level = int(sec.get("level", 1) or 1)
        except Exception:
            level = 1
        if level != 1 or _is_special_section(sec) or not _is_bare_chapter_heading(sec.get("heading", "")):
            out.append(sec)
            i += 1
            continue

        n = _chapter_number_from_title(sec.get("heading", ""))
        subtitle = ""
        moved_body = ""
        skip_next = False

        # Case 1: first body line is the real title.
        body_subtitle, new_body = _extract_chapter_subtitle_from_body(sec.get("body", ""))
        if body_subtitle:
            subtitle = body_subtitle
            sec["body"] = new_body

        # Case 2: first child H2 is the real title. Move its body into the H1
        # to avoid a duplicated H1/H2 title on the page.
        if not subtitle and i + 1 < len(src):
            nxt = src[i + 1]
            try:
                nxt_level = int(nxt.get("level", 1) or 1)
            except Exception:
                nxt_level = 1
            nxt_heading = str(nxt.get("heading", "") or "").strip()
            if nxt_level == 2 and _looks_like_real_chapter_subtitle(nxt_heading):
                subtitle = nxt_heading
                moved_body = str(nxt.get("body", "") or "").strip()
                skip_next = True

        if subtitle and n:
            sec["heading"] = f"Chapter {n}: {subtitle}"[:180]
            if moved_body:
                base = str(sec.get("body", "") or "").strip()
                sec["body"] = ((base + "\n\n") if base else "") + moved_body + "\n"
        out.append(sec)
        i += 2 if skip_next else 1
    return out


def _reader_sentence_split(text):
    raw = re.sub(r"\s+", " ", str(text or "")).strip()
    if not raw:
        return []
    # Protect a small set of common abbreviations from false sentence splits.
    protected = {
        "Mr.": "Mr§", "Mrs.": "Mrs§", "Ms.": "Ms§", "Dr.": "Dr§", "Prof.": "Prof§",
        "U.S.": "U§S§", "U.K.": "U§K§", "e.g.": "e§g§", "i.e.": "i§e§", "vs.": "vs§",
    }
    for k, v in protected.items():
        raw = raw.replace(k, v)
    parts = [p.strip() for p in re.split(r"(?<=[.!?])\s+(?=[A-Z0-9'\"“‘])", raw) if p.strip()]
    out = []
    for p in parts:
        for k, v in protected.items():
            p = p.replace(v, k)
        out.append(p)
    return out or [str(text or "").strip()]


def _reader_paragraph_chunks(text, max_words=None, max_sentences=None):
    """Split large prose blocks into natural reader paragraphs.

    The app now keeps the summary format the user liked, but avoids pages that
    feel like a single wall of text. Bullets and explicit blank-line paragraphs
    are left alone by the renderer; this helper only breaks oversized prose.
    """
    text = re.sub(r"\s+", " ", str(text or "")).strip()
    if not text:
        return []
    if not PDF_AUTO_PARAGRAPHIZE:
        return [text]
    max_words = max(35, int(max_words or PDF_MAX_PARAGRAPH_WORDS))
    max_sentences = max(2, int(max_sentences or PDF_MAX_PARAGRAPH_SENTENCES))
    if len(text.split()) <= max_words:
        return [text]
    sentences = _reader_sentence_split(text)
    if len(sentences) <= 1:
        words = text.split()
        return [" ".join(words[i:i + max_words]).strip() + ("." if words[i:i + max_words] and words[i + max_words - 1 if i + max_words - 1 < len(words) else -1][-1:] not in [".", "!", "?"] else "") for i in range(0, len(words), max_words)]
    chunks, buf, wc = [], [], 0
    for sent in sentences:
        sw = len(sent.split())
        # Start a new paragraph when adding this sentence would make a wall of
        # text, but avoid orphaning tiny single-sentence paragraphs.
        if buf and (wc + sw > max_words or len(buf) >= max_sentences):
            chunks.append(" ".join(buf).strip())
            buf, wc = [], 0
        buf.append(sent)
        wc += sw
    if buf:
        chunks.append(" ".join(buf).strip())
    return [c for c in chunks if c]

def build_pdf(out_path, sections, book_title, total_pages, cover_path,
              author_info, similar_md, diff_label, diff_explain,
              include_cover=True, include_toc=True, include_back=True, bw=False, phone=False, cyan=False,
              summary_pages_override=None):

    # v40: promote bare chapter headings before and after the quality gate so
    # output pages/TOC read as "Chapter N: Title" rather than just "Chapter N".
    normalized_sections = _promote_bare_chapter_titles(_normalize_sections_for_pdf(sections))
    gated_sections = _promote_bare_chapter_titles(
        _final_output_quality_gate(normalized_sections, job_id=None, book_title=book_title)
    )
    sections = [
        {
            "level":           s.get("level", 1),
            "heading":         scrub(s.get("heading", "")),
            "body":            scrub(s.get("body", "")),
            "research_score":  s.get("research_score"),
            "research_reason": scrub(s.get("research_reason", "") or ""),
            "special":         bool(s.get("special")),
        }
        for s in gated_sections
    ]
    diff_label   = scrub(diff_label)
    diff_explain = scrub(diff_explain)
    similar_md   = scrub(similar_md)
    book_title   = scrub(book_title)
    author_info  = {
        "author": scrub(author_info.get("author", "") or ""),
        "bio":    scrub(author_info.get("bio", "") or ""),
    }

    # Local color palette — B&W / Cyan overrides for print-friendly output
    if cyan:
        _BG     = colors.white
        _ACCENT = colors.HexColor("#006064")
        _GOLD   = colors.HexColor("#00838f")
        _TEXT   = colors.HexColor("#006064")
        _WHITE  = colors.HexColor("#006064")
        _MUTED  = colors.HexColor("#00acc1")
        _CARD   = colors.HexColor("#e0f7fa")
        _BORDER = colors.HexColor("#b2ebf2")
        _GREEN  = colors.HexColor("#00838f")
    elif bw:
        _BG     = colors.white
        _ACCENT = colors.HexColor("#333333")
        _GOLD   = colors.black
        _TEXT   = colors.black
        _WHITE  = colors.black
        _MUTED  = colors.HexColor("#555555")
        _CARD   = colors.white
        _BORDER = colors.HexColor("#bbbbbb")
        _GREEN  = colors.HexColor("#333333")
    else:
        _BG     = C_BG
        _ACCENT = C_ACCENT
        _GOLD   = C_GOLD
        _TEXT   = C_TEXT
        _WHITE  = C_WHITE
        _MUTED  = C_MUTED
        _CARD   = C_CARD
        _BORDER = C_BORDER
        _GREEN  = C_GREEN

    # Page geometry — phone uses 9:16 portrait; B&W uses tighter margins to save paper
    if phone:
        W, H        = 360, 640      # ~127mm x 226mm
        # v34: phone output used to paginate almost twice as long as the A4
        # summary. Tight margins + smaller type keep it useful on mobile while
        # allowing the same +20% length cap as the other downloadable variants.
        _lm = _rm   = 0.42 * cm
        _tm = _bm   = 0.62 * cm
        _hdr_txt_y  = H - 0.42*cm
        _hdr_rule_y = H - 0.55*cm
        _ftr_rule_y = 0.46*cm
        _ftr_txt_y  = 0.17*cm
    else:
        W, H        = A4
        _lm = _rm   = 1.5*cm if bw else 2.0*cm
        _tm = _bm   = 2.0*cm if bw else 2.5*cm
        _hdr_txt_y  = H - 1.5*cm
        _hdr_rule_y = H - 1.8*cm
        _ftr_rule_y = 1.8*cm
        _ftr_txt_y  = 1.2*cm

    # Font sizes - phone uses a denser mobile layout so its page count stays
    # within the same +20% cap as the main/print versions.
    _fs_cover_title  = 15 if phone else 28
    _fs_cover_lead   = 18 if phone else 34
    _fs_toc_title    = 12 if phone else 22
    _fs_ch_title     = 12 if phone else 20
    _fs_ch_lead      = 14 if phone else 26
    _fs_h2           = 8 if phone else 14
    _fs_h3           = 7.6 if phone else 11
    _fs_body         = 7.2 if phone else 10
    _fs_body_leading = 8.7 if phone else 16
    _fs_bullet       = 7.0 if phone else 10
    _fs_bullet_lead  = 8.3 if phone else 15
    _fs_pull         = 8.2 if phone else 12
    _fs_pull_lead    = 10 if phone else 18
    _fs_similar_head = 10 if phone else 18
    _fs_back_title   = 16 if phone else 36
    _fs_back_tag     = 8 if phone else 14

    doc = BookDocTemplate(
        out_path, pagesize=(W, H),
        leftMargin=_lm, rightMargin=_rm,
        topMargin=_tm, bottomMargin=_bm,
    )

    cover_frame = Frame(0, 0, W, H, leftPadding=15, rightPadding=15, topPadding=15, bottomPadding=15)
    body_frame  = Frame(_lm, _bm, W - _lm - _rm, H - _tm - _bm)

    def cover_canvas(canvas, doc):
        canvas.saveState()
        canvas.setFillColor(_BG)
        canvas.rect(0, 0, W, H, fill=1, stroke=0)
        canvas.restoreState()

    def _draw_chrome(canvas):
        """Shared header/footer chrome without the page number."""
        canvas.setFillColor(_BG)
        canvas.rect(0, 0, W, H, fill=1, stroke=0)

        canvas.setFillColor(_MUTED)
        canvas.setFont("Helvetica", 7)
        trunc = book_title[:50] + ("..." if len(book_title) > 50 else "")
        canvas.drawString(_lm, _hdr_txt_y, trunc.upper())
        canvas.drawRightString(W - _rm, _hdr_txt_y, "BRIANIS BOOK CLUB")

        canvas.setStrokeColor(_BORDER)
        canvas.setLineWidth(0.5)
        canvas.line(_lm, _hdr_rule_y, W - _rm, _hdr_rule_y)
        canvas.line(_lm, _ftr_rule_y, W - _rm, _ftr_rule_y)

        canvas.setFillColor(_MUTED)
        canvas.setFont("Helvetica", 7)
        canvas.drawString(_lm, _ftr_txt_y, "Brianis Book Club")
        canvas.drawRightString(W - _rm, _ftr_txt_y, "Not for redistribution, only for recreation")

    def front_matter_canvas(canvas, doc):
        """TOC pages — chrome present but no page number."""
        canvas.saveState()
        _draw_chrome(canvas)
        canvas.restoreState()

    def normal_canvas(canvas, doc):
        """Body pages — full chrome including continuous page number."""
        canvas.saveState()
        _draw_chrome(canvas)
        canvas.setFillColor(_MUTED)
        canvas.setFont("Helvetica", 7)
        canvas.drawCentredString(W / 2, _ftr_txt_y, str(canvas.getPageNumber()))
        canvas.restoreState()

    doc.addPageTemplates([
        PageTemplate(id="Cover",       frames=[cover_frame], onPage=cover_canvas),
        PageTemplate(id="FrontMatter", frames=[body_frame],  onPage=front_matter_canvas),
        PageTemplate(id="Normal",      frames=[body_frame],  onPage=normal_canvas),
    ])

    def ps(name, **kwargs):
        return ParagraphStyle(name, **kwargs)

    S = {
        "cover_label":  ps("cover_label",  fontSize=9,  textColor=_GOLD,   fontName="Helvetica-Bold",        spaceAfter=6,  alignment=TA_CENTER),
        "cover_title":  ps("cover_title",  fontSize=_fs_cover_title, textColor=_WHITE,  fontName="Helvetica-Bold",  spaceAfter=12, alignment=TA_CENTER, leading=_fs_cover_lead),
        "cover_author": ps("cover_author", fontSize=14, textColor=_MUTED,  fontName="Helvetica",             spaceAfter=16, alignment=TA_CENTER),
        "cover_stats":  ps("cover_stats",  fontSize=10, textColor=_TEXT,   fontName="Helvetica",             spaceAfter=20, alignment=TA_CENTER),
        "cover_badge":  ps("cover_badge",  fontSize=9,  textColor=_GOLD,   fontName="Helvetica-Bold",        spaceAfter=24, alignment=TA_CENTER),
        "cover_bio":    ps("cover_bio",    fontSize=9,  textColor=_TEXT,   fontName="Helvetica",             spaceAfter=4,  leftIndent=12, rightIndent=12),
        "toc_title":    ps("toc_title",    fontSize=_fs_toc_title, textColor=_WHITE,  fontName="Helvetica-Bold", spaceAfter=24),
        "toc1":         ps("toc1",         fontSize=8.5 if phone else 11, textColor=_TEXT,   fontName="Helvetica-Bold", spaceAfter=2 if phone else 4),
        "toc2":         ps("toc2",         fontSize=7.5 if phone else 10, textColor=_MUTED,  fontName="Helvetica", spaceAfter=1 if phone else 2, leftIndent=8 if phone else 16),
        "ch_label":     ps("ch_label",     fontSize=6.5 if phone else 8,  textColor=_ACCENT, fontName="Helvetica-Bold", spaceBefore=10 if phone else 24, spaceAfter=2 if phone else 4),
        "ch_title":     ps("ch_title",     fontSize=_fs_ch_title, textColor=_WHITE,  fontName="Helvetica-Bold", spaceBefore=2 if phone else 4, spaceAfter=5 if phone else 12, leading=_fs_ch_lead),
        "h2":           ps("h2",           fontSize=_fs_h2,       textColor=_ACCENT, fontName="Helvetica-Bold", spaceBefore=7 if phone else 16, spaceAfter=3 if phone else 8),
        "h3_takeaway":  ps("h3_takeaway",  fontSize=_fs_h3, textColor=_GOLD,   fontName="Helvetica-Bold", spaceBefore=5 if phone else 10, spaceAfter=2 if phone else 4),
        "body":         ps("body",         fontSize=_fs_body, textColor=_TEXT,   fontName="Helvetica", spaceBefore=1 if phone else 4, spaceAfter=2 if phone else 6, leading=_fs_body_leading, alignment=TA_JUSTIFY),
        "bullet":       ps("bullet",       fontSize=_fs_bullet, textColor=_TEXT,   fontName="Helvetica", spaceBefore=1 if phone else 2, spaceAfter=1 if phone else 2, leading=_fs_bullet_lead, leftIndent=10 if phone else 20),
        "pull_quote":   ps("pull_quote",   fontSize=_fs_pull, textColor=_ACCENT, fontName="Helvetica-BoldOblique", spaceBefore=5 if phone else 12, spaceAfter=5 if phone else 12, leading=_fs_pull_lead, leftIndent=10 if phone else 24, rightIndent=10 if phone else 24, alignment=TA_CENTER),
        "similar_label":ps("similar_label",fontSize=8,  textColor=_GOLD,   fontName="Helvetica-Bold",        spaceAfter=4,  alignment=TA_CENTER),
        "similar_head": ps("similar_head", fontSize=_fs_similar_head, textColor=_WHITE,  fontName="Helvetica-Bold", spaceAfter=12, alignment=TA_CENTER),
        "sim_title":    ps("sim_title",    fontSize=11, textColor=_WHITE,  fontName="Helvetica-Bold",        spaceAfter=2),
        "sim_reason":   ps("sim_reason",   fontSize=9,  textColor=_MUTED,  fontName="Helvetica",             spaceAfter=8),
        "back_title":   ps("back_title",   fontSize=_fs_back_title, textColor=_WHITE,  fontName="Helvetica-Bold",        alignment=TA_CENTER, spaceAfter=12, leading=int(_fs_back_title * 1.18)),
        "back_tag":     ps("back_tag",     fontSize=_fs_back_tag,   textColor=_MUTED,  fontName="Helvetica-BoldOblique", alignment=TA_CENTER, spaceAfter=20, leading=int(_fs_back_tag * 1.35)),
        "back_fine":    ps("back_fine",    fontSize=9,  textColor=_MUTED,  fontName="Helvetica",             alignment=TA_CENTER),
    }

    toc                = TableOfContents()
    toc.levelStyles    = [S["toc1"], S["toc2"]]
    toc.dotsMinLevel   = 0

    chapter_num = [0]
    toc_seen = set()

    def toc_heading(text, level, key):
        sty = S["ch_title"] if level == 1 else S["h2"]
        p   = Paragraph(f'<a name="{key}"/>{safe(text)}', sty)
        tkey = (level, re.sub(r"[^a-z0-9]", "", str(text or "").lower()))
        if level <= max(1, TOC_MAX_LEVEL) and tkey[1] and tkey not in toc_seen:
            p.toc_entry = (level - 1, safe(text), key)
            toc_seen.add(tkey)
        return p

    def display_chapter_label(heading, fallback_num):
        h = str(heading or "").strip()
        low = h.lower()
        if low.startswith("introduction"):
            return "INTRODUCTION"
        if low.startswith("preface"):
            return "PREFACE"
        if low.startswith("foreword"):
            return "FOREWORD"
        if low.startswith("prologue"):
            return "PROLOGUE"
        if low.startswith("epilogue"):
            return "EPILOGUE"
        if low.startswith("authors' note") or low.startswith("author's note") or low.startswith("authors note"):
            return "AUTHORS' NOTE"
        if low.startswith("cast of characters"):
            return "CAST OF CHARACTERS"
        m = re.match(r"^(chapter\s+[ivxlcdm\d]+)", h, flags=re.I)
        if m:
            return m.group(1).upper()
        m = re.match(r"^((?:part|unit|unidad|examen)\s+[ivxlcdm\d]+)", h, flags=re.I)
        if m:
            return m.group(1).upper()
        return ""

    def make_key(heading, num):
        slug = re.sub(r"[^a-zA-Z0-9]", "_", heading[:20])
        return f"h1_{num}_{slug}"

    def render_body(body_text):
        flowables  = []
        paragraphs = []
        lines      = body_text.strip().splitlines()
        buf        = []

        def flush():
            if buf:
                joined = " ".join(buf).strip()
                if joined:
                    max_words = 85 if phone else PDF_MAX_PARAGRAPH_WORDS
                    max_sents = 3 if phone else PDF_MAX_PARAGRAPH_SENTENCES
                    for chunk in _reader_paragraph_chunks(joined, max_words=max_words, max_sentences=max_sents):
                        paragraphs.append(("text", chunk))
                buf.clear()

        for line in lines:
            s = line.strip()
            if not s:
                flush()
            elif s.startswith("- ") or s.startswith("* "):
                flush()
                paragraphs.append(("bullet", s[2:].strip()))
            elif re.match(r"^\d+\.\s", s):
                flush()
                paragraphs.append(("bullet", re.sub(r"^\d+\.\s", "", s)))
            elif s.startswith("> "):
                flush()
                paragraphs.append(("blockquote", s[2:].strip()))
            else:
                buf.append(s)
        flush()

        pull_interval = 7
        for i, item in enumerate(paragraphs):
            kind, text = item
            if kind == "bullet":
                flowables.append(Paragraph(f"&bull; {safe(text)}", S["bullet"]))
            elif kind == "blockquote":
                if not bw:
                    flowables.append(HRFlowable(color=_ACCENT, thickness=1))
                flowables.append(Paragraph(safe(text), S["pull_quote"]))
                if not bw:
                    flowables.append(HRFlowable(color=_ACCENT, thickness=1))
            else:
                if PDF_PULL_QUOTES and i > 0 and i % pull_interval == 0:
                    sentences = re.split(r"(?<=[.!?])\s+", text)
                    long_s    = [s for s in sentences if len(s) > 60]
                    if long_s:
                        if not bw:
                            flowables.append(HRFlowable(color=_ACCENT, thickness=0.5, spaceAfter=4))
                        flowables.append(Paragraph(safe(long_s[0]), S["pull_quote"]))
                        if not bw:
                            flowables.append(HRFlowable(color=_ACCENT, thickness=0.5, spaceBefore=4))
                flowables.append(Paragraph(safe(text), S["body"]))

        return flowables

    story = []

    if not include_cover:
        story.append(NextPageTemplate("Normal"))

    if include_cover:
        story.append(Spacer(1, 3*cm))

        if cover_path and os.path.exists(cover_path):
            try:
                img       = Image(cover_path, width=6*cm, height=8*cm, kind="proportional")
                img.hAlign = "CENTER"
                story.append(img)
                story.append(Spacer(1, 0.5*cm))
            except Exception:
                pass

        story.append(Paragraph("BOOK SUMMARY", S["cover_label"]))
        story.append(Paragraph(safe(book_title), S["cover_title"]))

        if author_info.get("author"):
            story.append(Paragraph(f"by {safe(author_info['author'])}", S["cover_author"]))

        summary_word_count = sum(len(s.get("body", "").split()) for s in sections)
        if summary_pages_override:
            try:
                summary_pages = max(1, int(summary_pages_override))
            except Exception:
                summary_pages = max(1, math.ceil(summary_word_count / max(1, WORDS_PER_PAGE)))
        else:
            summary_pages = max(1, math.ceil(summary_word_count / max(1, WORDS_PER_PAGE)))
        summary_min        = max(1, math.ceil(summary_word_count / 200))

        orig_words = total_pages * WORDS_PER_PAGE
        orig_min   = max(1, math.ceil(orig_words / 200))
        saved_min  = max(0, orig_min - summary_min)

        def fmt_time(mins):
            h, m = divmod(mins, 60)
            return f"{h}h {m}m" if h else f"{m}m"

        story.append(Spacer(1, 0.4*cm))

        col_w      = (W - _lm - _rm) / 3
        stats_data = [
            [
                Paragraph("ORIGINAL LENGTH",  S["cover_label"]),
                Paragraph("SUMMARY LENGTH",   S["cover_label"]),
                Paragraph("ESTIMATED TIME SAVED", S["cover_label"]),
            ],
            [
                Paragraph(f"<b>{total_pages}</b> pages<br/>{fmt_time(orig_min)} to read",     S["cover_stats"]),
                Paragraph(f"<b>{summary_pages}</b> pages<br/>{fmt_time(summary_min)} to read", S["cover_stats"]),
                Paragraph(f"<b>{fmt_time(saved_min)}</b><br/>saved reading time",               S["cover_stats"]),
            ],
        ]
        tbl = Table(stats_data, colWidths=[col_w, col_w, col_w])
        tbl.setStyle(TableStyle([
            ("BACKGROUND",    (0, 0), (-1, 0), _CARD),
            ("BACKGROUND",    (0, 1), (-1, 1), colors.white if bw else colors.HexColor("#0d0d20")),
            ("BOX",           (0, 0), (-1, -1), 0.5, _BORDER),
            ("INNERGRID",     (0, 0), (-1, -1), 0.5, _BORDER),
            ("TOPPADDING",    (0, 0), (-1, -1), 8),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 8),
            ("LEFTPADDING",   (0, 0), (-1, -1), 10),
            ("RIGHTPADDING",  (0, 0), (-1, -1), 10),
            ("ALIGN",         (0, 0), (-1, -1), "CENTER"),
            ("VALIGN",        (0, 0), (-1, -1), "MIDDLE"),
        ]))
        story.append(tbl)
        story.append(Spacer(1, 0.4*cm))
        story.append(Paragraph("Brianis Book Club &middot; Powered by Claude AI", S["cover_badge"]))

        if author_info.get("bio"):
            story.append(Spacer(1, 0.3*cm))
            story.append(Paragraph("<b>About the Author</b>", S["cover_bio"]))
            story.append(Paragraph(safe(author_info["bio"][:400]), S["cover_bio"]))

        story.append(NextPageTemplate("FrontMatter"))
        story.append(PageBreak())

    if include_toc:
        story.append(Paragraph("Contents", S["toc_title"]))
        story.append(toc)
        story.append(NextPageTemplate("Normal"))
        story.append(PageBreak())

    for sec in sections:
        level   = sec["level"]
        heading = sec["heading"]
        body    = sec["body"]

        if level == 1:
            is_special = _is_special_section(sec)
            if is_special:
                if _norm_title_key(heading) in ("summaryofthesummary", "summaryofsummary") and story:
                    story.append(PageBreak())
                key = make_key(heading, f"special_{chapter_num[0] + 1}")
                story.append(toc_heading(heading, 1, key))
                if body.strip():
                    story.extend(render_body(body))
                continue

            chapter_num[0] += 1
            key = make_key(heading, chapter_num[0])
            label = display_chapter_label(heading, chapter_num[0])
            if label:
                story.append(Paragraph(label, S["ch_label"]))
            story.append(toc_heading(heading, 1, key))
            if body.strip():
                story.extend(render_body(body))

        elif level == 2:
            slug = re.sub(r"[^a-zA-Z0-9]", "_", heading[:20])
            key  = f"h2_{chapter_num[0]}_{slug}"
            story.append(toc_heading(heading, 2, key))
            if body.strip():
                story.extend(render_body(body))

        elif level == 3:
            is_takeaway = "takeaway" in heading.lower()
            sty = S["h3_takeaway"] if is_takeaway else S["h2"]
            story.append(Paragraph(safe(heading), sty))
            if body.strip():
                story.extend(render_body(body))

    if similar_md.strip():
        story.append(PageBreak())
        story.append(Paragraph("IF YOU ENJOYED THIS BOOK", S["similar_label"]))
        story.append(Paragraph("You Might Also Like", S["similar_head"]))
        story.append(Spacer(1, 0.3*cm))
        for m in re.finditer(
            r"\*\*(.+?)\*\*\s+by\s+([^—\n]+)[—-]+\s*(.+?)(?=\n|$)",
            similar_md
        ):
            story.append(Paragraph(f"{safe(m.group(1))} by {safe(m.group(2))}", S["sim_title"]))
            story.append(Paragraph(safe(m.group(3)), S["sim_reason"]))
            story.append(HRFlowable(color=_BORDER, thickness=0.5))

    if include_back:
        story.append(PageBreak())
        story.append(Spacer(1, 6*cm))
        story.append(Paragraph("Brianis Book Club", S["back_title"]))
        story.append(Paragraph("Read more. Know more. Be more.", S["back_tag"]))
        story.append(Paragraph("Not for redistribution, only for recreation.", S["back_fine"]))

    doc.multiBuild(story, maxPasses=12)

# ── HTML Page ──────────────────────────────────────────────────────────────────
HTML_PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Brianis Book Club</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@400;700;900&family=Inter:wght@300;400;500;600&display=swap" rel="stylesheet">
<script src="https://cdn.jsdelivr.net/npm/canvas-confetti@1.9.2/dist/confetti.browser.min.js"></script>
<style>
:root {
  --bg: #07070f; --surface: #10101e; --card: #13132a; --border: #1f1f3a;
  --accent: #7c3aed; --gold: #f59e0b; --green: #10b981; --text: #e8e8f0; --muted: #5b5b7b;
}
*, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
body { background: var(--bg); color: var(--text); font-family: 'Inter', sans-serif; min-height: 100vh; }

nav {
  display: flex; align-items: center; gap: 14px;
  padding: 18px 32px; border-bottom: 1px solid var(--border); background: var(--surface);
}
.logo {
  width: 40px; height: 40px; border-radius: 10px;
  background: linear-gradient(135deg, #7c3aed, #4f46e5);
  display: flex; align-items: center; justify-content: center; font-size: 20px;
}
.nav-title {
  font-family: 'Playfair Display', serif; font-size: 1.5rem; font-weight: 700;
  background: linear-gradient(135deg, #7c3aed, #a78bfa);
  -webkit-background-clip: text; -webkit-text-fill-color: transparent; background-clip: text;
}
.nav-badge {
  background: var(--card); border: 1px solid var(--border); padding: 3px 10px;
  border-radius: 20px; font-size: 0.72rem; color: var(--muted); margin-left: 6px;
}

.app-layout { display: flex; align-items: flex-start; gap: 24px; max-width: 1100px; margin: 0 auto; padding: 40px 20px 80px; }

/* ── History Sidebar ── */
.history-sidebar {
  width: 260px; min-width: 220px; flex-shrink: 0;
  position: sticky; top: 24px;
}
.history-sidebar h3 {
  font-family: 'Playfair Display', serif; font-size: 1rem; font-weight: 700;
  color: var(--text); margin-bottom: 14px; letter-spacing: 0.04em;
  display: flex; align-items: center; gap: 8px;
}
.history-sidebar h3 span { opacity: 0.5; font-size: 0.78rem; font-weight: 400; }
#historyList { display: flex; flex-direction: column; gap: 8px; }
.hist-item {
  background: var(--card); border: 1px solid var(--border); border-radius: 12px;
  padding: 11px 13px; cursor: pointer; transition: border-color 0.15s, background 0.15s;
  position: relative;
}
.hist-item:hover { border-color: var(--accent); background: rgba(124,58,237,0.06); }
.hist-item.active { border-color: var(--accent); background: rgba(124,58,237,0.1); }
.hist-icon { font-size: 1rem; margin-right: 6px; }
.hist-title {
  font-size: 0.82rem; font-weight: 600; color: var(--text);
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 170px;
}
.hist-date { font-size: 0.72rem; color: var(--muted); margin-top: 3px; }
.hist-type {
  font-size: 0.65rem; font-weight: 700; letter-spacing: 0.06em;
  padding: 1px 6px; border-radius: 10px; display: inline-block; margin-top: 4px;
}
.hist-type.book { background: rgba(124,58,237,0.2); color: #a78bfa; }
.hist-type.news { background: rgba(245,158,11,0.2); color: #fbbf24; }
.hist-del {
  position: absolute; top: 8px; right: 9px;
  background: none; border: none; color: var(--muted); font-size: 1rem;
  cursor: pointer; line-height: 1; padding: 2px 4px; border-radius: 4px;
  transition: color 0.15s, background 0.15s;
}
.hist-del:hover { color: #f87171; background: rgba(248,113,113,0.1); }
.hist-empty { font-size: 0.82rem; color: var(--muted); text-align: center; padding: 20px 0; }

/* History download panel */
#histDetail {
  margin-top: 14px; background: var(--card); border: 1px solid var(--border);
  border-radius: 12px; padding: 14px; display: none;
}
#histDetail .hist-detail-title {
  font-size: 0.8rem; font-weight: 600; color: var(--text); margin-bottom: 10px;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
}
#histDetail .hist-dl-btn {
  display: block; width: 100%; text-align: center;
  background: var(--surface); border: 1px solid var(--border); border-radius: 8px;
  color: var(--text); font-size: 0.8rem; font-weight: 600;
  padding: 8px 0; margin-bottom: 6px; cursor: pointer; text-decoration: none;
  transition: border-color 0.15s, background 0.15s;
}
#histDetail .hist-dl-btn:hover { border-color: var(--accent); background: rgba(124,58,237,0.08); }
#histDetail .hist-dl-btn:last-child { margin-bottom: 0; }

main { flex: 1; min-width: 0; }
h2.section-title { font-family: 'Playfair Display', serif; font-size: 1.6rem; font-weight: 700; color: var(--text); margin-bottom: 28px; }

.card { background: var(--card); border: 1px solid var(--border); border-radius: 16px; padding: 28px; margin-bottom: 20px; }

.drop-zone {
  border: 2px dashed var(--border); border-radius: 12px;
  padding: 40px 20px; text-align: center; cursor: pointer;
  transition: border-color 0.2s, background 0.2s; position: relative;
}
.drop-zone:hover, .drop-zone.drag-over { border-color: var(--accent); background: rgba(124,58,237,0.05); }
.drop-zone input[type=file] { position: absolute; inset: 0; opacity: 0; cursor: pointer; width: 100%; height: 100%; }
.drop-icon { font-size: 2.5rem; margin-bottom: 8px; }
.drop-label { font-size: 0.95rem; color: var(--muted); }
.drop-sub { font-size: 0.8rem; color: var(--muted); margin-top: 4px; }
.file-badge {
  display: inline-flex; align-items: center; gap: 8px;
  background: rgba(124,58,237,0.15); border: 1px solid var(--accent);
  border-radius: 8px; padding: 8px 14px; margin-top: 10px; font-size: 0.88rem;
}
.page-badge { background: var(--accent); color: white; border-radius: 20px; padding: 2px 8px; font-size: 0.75rem; font-weight: 600; }

label { display: block; font-size: 0.82rem; color: var(--muted); font-weight: 500; margin-bottom: 6px; letter-spacing: 0.04em; }
input[type=text], input[type=password], input[type=number], textarea, select {
  width: 100%; background: var(--surface); border: 1px solid var(--border);
  border-radius: 8px; color: var(--text); font-size: 0.93rem; font-family: 'Inter', sans-serif;
  padding: 10px 14px; outline: none; transition: border-color 0.2s;
}
input:focus, textarea:focus, select:focus { border-color: var(--accent); }
textarea { resize: vertical; min-height: 70px; }
.form-row { display: grid; grid-template-columns: 1fr 1fr; gap: 16px; margin-bottom: 16px; }
.form-group { margin-bottom: 16px; }

.length-toggle { display: flex; gap: 0; border: 1px solid var(--border); border-radius: 8px; overflow: hidden; margin-bottom: 10px; }
.length-toggle button { flex: 1; background: none; border: none; color: var(--muted); padding: 8px; cursor: pointer; font-size: 0.85rem; transition: all 0.2s; }
.length-toggle button.active { background: var(--accent); color: white; }

.slider-row { display: flex; align-items: center; gap: 12px; }
input[type=range] { flex: 1; accent-color: var(--accent); }
.slider-val { color: var(--accent); font-weight: 600; font-size: 0.9rem; min-width: 40px; }

.cost-badge {
  display: inline-flex; align-items: center; gap: 8px;
  background: rgba(245,158,11,0.1); border: 1px solid rgba(245,158,11,0.3);
  border-radius: 8px; padding: 8px 14px; font-size: 0.85rem; color: var(--gold); margin-top: 8px;
}

#suggestions-section { display: none; margin-top: 16px; }
#suggestions-section label { margin-bottom: 10px; display: block; }
.suggestion-cards { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); gap: 10px; }
.suggestion-card {
  background: var(--surface); border: 1px solid var(--border); border-radius: 10px;
  padding: 14px; cursor: pointer; transition: border-color 0.2s, background 0.2s;
  position: relative;
}
.suggestion-card:hover { border-color: var(--accent); background: rgba(124,58,237,0.06); }
.suggestion-card.selected { border-color: var(--accent); background: rgba(124,58,237,0.12); }
.suggestion-card .s-label { font-size: 0.7rem; font-weight: 700; letter-spacing: 0.08em; color: var(--gold); margin-bottom: 4px; }
.suggestion-card .s-pages { font-size: 1.1rem; font-weight: 700; color: var(--text); margin-bottom: 6px; }
.suggestion-card .s-reason { font-size: 0.78rem; color: var(--muted); line-height: 1.5; }
.tailored-panel { margin-top: 10px; padding: 12px; border: 1px solid var(--border); border-radius: 14px; background: rgba(124,58,237,0.06); font-size: 0.82rem; color: var(--text); }
.tailored-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(120px, 1fr)); gap: 8px; margin-top: 10px; }
.tailored-option { border: 1px solid var(--border); border-radius: 12px; padding: 9px; cursor: pointer; background: rgba(255,255,255,0.03); }
.tailored-option:hover { border-color: var(--accent); background: rgba(124,58,237,0.12); }
.tailored-metric { color: var(--muted); margin-top: 3px; }
.suggestion-card .s-check { position: absolute; top: 10px; right: 10px; color: var(--accent); display: none; font-size: 1rem; }
.suggestion-card.selected .s-check { display: block; }
.suggestion-loading { font-size: 0.82rem; color: var(--muted); font-style: italic; }

.btn-submit {
  width: 100%; padding: 14px; border: none; border-radius: 10px; cursor: pointer;
  font-size: 1rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: linear-gradient(135deg, #7c3aed, #4f46e5); color: white; transition: opacity 0.2s; margin-top: 4px;
}
.btn-submit:hover { opacity: 0.9; }
.btn-submit:disabled { opacity: 0.5; cursor: not-allowed; }

.split-toggle-row { display:flex; align-items:center; gap:10px; padding:14px 0 6px; }
.split-toggle-row span { font-size:0.9rem; color:var(--text); }
.toggle-switch { position:relative; display:inline-block; width:44px; height:24px; cursor:pointer; flex-shrink:0; }
.toggle-switch input { opacity:0; width:0; height:0; }
.toggle-slider { position:absolute; top:0; left:0; right:0; bottom:0; background:var(--border); border-radius:24px; transition:.2s; }
.toggle-slider:before { position:absolute; content:""; height:18px; width:18px; left:3px; bottom:3px; background:#fff; border-radius:50%; transition:.2s; }
input:checked + .toggle-slider { background:var(--accent); }
input:checked + .toggle-slider:before { transform:translateX(20px); }
.split-half { padding-bottom:4px; }
.split-half-label { font-weight:600; font-size:0.82rem; color:var(--accent); letter-spacing:.04em; margin-bottom:6px; }
.split-result-card { background:var(--surface); border:1px solid var(--border); border-radius:10px; padding:16px; margin-bottom:12px; }
.split-result-title { font-weight:600; margin-bottom:12px; color:var(--text); }
.style-hint-card {
  margin-top: 8px; padding: 10px 12px; border: 1px solid rgba(124,58,237,0.35);
  background: rgba(124,58,237,0.10); border-radius: 10px; color: var(--muted);
  font-size: 0.82rem; line-height: 1.45; min-height: 38px;
}
.style-hint-card strong { color: var(--text); font-weight: 600; }

#progress-section { display: none; }
.progress-bar-wrap { background: var(--surface); border-radius: 99px; height: 10px; margin: 14px 0 6px; overflow: hidden; }
.progress-bar { height: 100%; background: linear-gradient(90deg, #7c3aed, #a78bfa); border-radius: 99px; transition: width 0.4s; width: 0%; }
.progress-msg { font-size: 0.88rem; color: var(--muted); }

.chapter-feed { margin-top: 16px; display: flex; flex-direction: column; gap: 8px; }
.chapter-card {
  background: var(--surface); border: 1px solid var(--border); border-radius: 8px;
  padding: 10px 14px; font-size: 0.85rem; color: var(--text);
  display: flex; align-items: center; gap: 8px;
  animation: fadeIn 0.4s ease;
}
@keyframes fadeIn { from { opacity:0; transform:translateY(4px); } to { opacity:1; transform:translateY(0); } }
.chapter-dot { width: 8px; height: 8px; border-radius: 50%; background: var(--accent); flex-shrink: 0; }

#result-section { display: none; }
.btn-download {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 24px; border: none; border-radius: 10px; cursor: pointer;
  font-size: 0.95rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: var(--green); color: white; transition: opacity 0.2s; margin-right: 10px;
}
.btn-download:hover { opacity: 0.88; }
.btn-share {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 24px; border: 1px solid var(--accent); border-radius: 10px; cursor: pointer;
  font-size: 0.95rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: none; color: var(--accent); transition: background 0.2s;
}
.btn-share:hover { background: rgba(124,58,237,0.1); }
.btn-bw {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 24px; border: 1px solid var(--border); border-radius: 10px; cursor: pointer;
  font-size: 0.95rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: #f5f5f5; color: #222; transition: opacity 0.2s; margin-right: 10px;
}
.btn-bw:hover { opacity: 0.85; }
.btn-cyan {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 24px; border: 1px solid #00838f; border-radius: 10px; cursor: pointer;
  font-size: 0.95rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: #e0f7fa; color: #006064; transition: opacity 0.2s; margin-right: 10px;
}
.btn-cyan:hover { opacity: 0.85; }
.btn-phone {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 24px; border: 1px solid var(--accent); border-radius: 10px; cursor: pointer;
  font-size: 0.95rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: rgba(124,58,237,0.12); color: var(--accent); transition: opacity 0.2s; margin-right: 10px;
}
.btn-phone:hover { opacity: 0.85; }

.error-box {
  background: rgba(239,68,68,0.1); border: 1px solid rgba(239,68,68,0.4);
  border-radius: 8px; padding: 12px 16px; color: #f87171; font-size: 0.9rem; margin-top: 12px; display: none;
}

.toast {
  position: fixed; bottom: 30px; left: 50%; transform: translateX(-50%);
  background: var(--card); border: 1px solid var(--accent); border-radius: 10px;
  padding: 12px 24px; font-size: 0.92rem; color: var(--text); z-index: 999;
  display: none; animation: slideUp 0.3s ease;
}
@keyframes slideUp { from { opacity:0; transform:translateX(-50%) translateY(10px); } to { opacity:1; transform:translateX(-50%) translateY(0); } }

.mode-switcher {
  display: flex; gap: 0; border: 2px solid var(--accent); border-radius: 12px;
  overflow: hidden; margin-bottom: 24px;
}
.mode-btn {
  flex: 1; background: none; border: none; color: var(--muted);
  padding: 14px 20px; cursor: pointer; font-size: 1rem; font-weight: 600;
  font-family: 'Inter', sans-serif; transition: all 0.2s; letter-spacing: 0.01em;
}
.mode-btn.active { background: var(--accent); color: white; }
.mode-btn:not(.active):hover { background: rgba(124,58,237,0.08); color: var(--text); }
.news-drop-zone {
  border: 2px dashed rgba(245,158,11,0.5); border-radius: 12px;
  padding: 30px 20px; text-align: center; cursor: pointer;
  transition: border-color 0.2s, background 0.2s; position: relative; margin-bottom: 10px;
}
.news-drop-zone:hover, .news-drop-zone.drag-over { border-color: var(--gold); background: rgba(245,158,11,0.06); }
.news-drop-zone input[type=file] { position: absolute; inset: 0; opacity: 0; cursor: pointer; width: 100%; height: 100%; }
.news-file-list { margin-top: 8px; display: flex; flex-direction: column; gap: 6px; }
.news-file-item {
  display: flex; align-items: center; gap: 8px;
  background: rgba(245,158,11,0.08); border: 1px solid rgba(245,158,11,0.3);
  border-radius: 8px; padding: 7px 12px; font-size: 0.85rem; color: var(--text);
}
.news-file-num { background: var(--gold); color: #07070f; border-radius: 50%; width: 20px; height: 20px; display: flex; align-items: center; justify-content: center; font-size: 0.72rem; font-weight: 700; flex-shrink: 0; }
.btn-news-dark {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 24px; border: none; border-radius: 10px; cursor: pointer;
  font-size: 0.95rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: #1a1a2e; color: #a78bfa; transition: opacity 0.2s; margin-right: 10px;
}
.btn-news-dark:hover { opacity: 0.85; }
.btn-news-light {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 24px; border: 1px solid #d1d5db; border-radius: 10px; cursor: pointer;
  font-size: 0.95rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: #f3f4f6; color: #374151; transition: opacity 0.2s; margin-right: 10px;
}
.btn-news-light:hover { opacity: 0.85; }
.btn-news-print {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 24px; border: 1px solid #374151; border-radius: 10px; cursor: pointer;
  font-size: 0.95rem; font-weight: 600; font-family: 'Inter', sans-serif;
  background: #e5e7eb; color: #111316; transition: opacity 0.2s; margin-right: 10px;
}
.btn-news-print:hover { opacity: 0.85; }
</style>
</head>
<body>

<nav>
  <div class="logo">&#128218;</div>
  <div>
    <div class="nav-title">Brianis Book Club</div>
  </div>
  <span class="nav-badge">AI-Powered Reading Companion</span>
</nav>

<div class="app-layout">

<!-- ── History Sidebar ── -->
<aside class="history-sidebar">
  <h3>&#128197; History <span id="histCount"></span></h3>
  <div id="historyList"><div class="hist-empty">No history yet</div></div>
  <div id="histDetail">
    <div class="hist-detail-title" id="histDetailTitle"></div>
    <div id="histDetailLinks"></div>
  </div>
</aside>

<main>
  <h2 class="section-title" style="margin-top:32px;">Summarize a Book</h2>

  <div class="card">
    <div class="mode-switcher">
      <button id="btnBookMode" class="mode-btn active" onclick="setMode('book')">&#128218; Book Summary</button>
      <button id="btnNewsMode" class="mode-btn" onclick="setMode('news')">&#128240; News Digest</button>
    </div>

    <div class="form-group">
      <label>BOOK FILE</label>
      <div class="drop-zone" id="dropZone">
        <input type="file" id="pdfFile" accept=".pdf,.epub,application/pdf,application/epub+zip">
        <div id="dropContent">
          <div class="drop-icon">&#128196;</div>
          <div class="drop-label">Drag &amp; drop your PDF or EPUB here, or click to browse</div>
          <div class="drop-sub">Supports text PDFs, scanned PDFs with OCR, and EPUBs &middot; max 100 MB</div>
        </div>
      </div>
      <div id="costBadge" style="display:none" class="cost-badge">
        <span>&#128202;</span> <span id="costText">Calculating...</span>
      </div>
    </div>

    <div id="suggestions-section">
      <label>AI LENGTH SUGGESTIONS</label>
      <div id="suggestionsContent" class="suggestion-loading">Analysing book...</div>
    </div>

    <div class="form-row" id="bookTitleAuthorRow">
      <div class="form-group" style="margin-bottom:0">
        <label>BOOK TITLE</label>
        <input type="text" id="bookTitle" placeholder="Auto-filled from filename">
      </div>
      <div class="form-group" style="margin-bottom:0">
        <label>AUTHOR <span style="color:var(--muted);font-weight:400">(optional — improves cover lookup)</span></label>
        <input type="text" id="bookAuthor" placeholder="e.g. James Clear">
      </div>
    </div>

    <div class="form-group">
      <label>ANTHROPIC API KEY</label>
      <input type="password" id="apiKey" placeholder="sk-ant-...">
    </div>

    <div class="form-row" id="styleLengthRow">
      <div class="form-group" style="margin-bottom:0">
        <label>SUMMARY STYLE</label>
        <select id="summaryStyle">
          <option value="narrative_basic" selected>Narrative — Basic</option>
          <option value="story_arc">Story-Arc Narrative</option>
          <option value="feynman_storyteller">Feynman Storyteller</option>
          <option value="investigative_narrative">Investigative Narrative</option>
          <option value="strategic_briefing">Strategic Briefing</option>
          <option value="deep_reading">Deep Reading Companion</option>
          <option value="practical_playbook">Practical Playbook</option>
          <option value="literary_essay">Literary Essay</option>
          <option value="academic">Academic</option>
        </select>
        <div id="styleHint" class="style-hint-card"></div>
      </div>
      <div class="form-group" style="margin-bottom:0">
        <label>SUMMARY LENGTH</label>
        <div class="length-toggle">
          <button id="btnPercent" class="active" onclick="setLengthMode('percent')">% of book</button>
          <button id="btnFixed" onclick="setLengthMode('fixed')">Fixed pages</button>
        </div>
        <div id="pctRow" class="slider-row">
          <input type="range" id="pctSlider" min="5" max="50" value="15"
            oninput="document.getElementById('pctVal').textContent=this.value+'%'">
          <span class="slider-val" id="pctVal">15%</span>
        </div>
        <div id="fixedRow" style="display:none">
          <input type="number" id="fixedPages" value="20" min="5" step="1" style="width:100px">
          <span style="color:var(--muted);font-size:0.85rem;margin-left:8px;">pages</span>
        </div>
      </div>
    </div>

    <div class="form-group" id="strictnessGroup" style="margin-top:16px;">
      <label>PAGE TARGET STRICTNESS</label>
      <select id="pageStrictness">
        <option value="quickdirty">Quick &amp; Dirty - up to +50%, fastest</option>
        <option value="flexible">Flexible - up to +20%, fast</option>
        <option value="standard" selected>Standard - up to +10%</option>
        <option value="strict">Strict - up to +5%, slower</option>
        <option value="exactish">Exact-ish - up to +3%, slowest</option>
      </select>
      <div class="feasibility-note" id="strictnessNote">Standard mode returns the safest bounded output for most jobs.</div>
    </div>

    <div class="form-group" id="instructionsGroup" style="margin-top:16px;">
      <label>CUSTOM INSTRUCTIONS <span style="color:var(--muted);font-weight:400">(optional)</span></label>
      <textarea id="instructions" placeholder="e.g. focus on practical takeaways, ignore the introduction..."></textarea>
    </div>

    <div class="split-toggle-row" id="splitToggleRow">
      <label class="toggle-switch">
        <input type="checkbox" id="splitMode" onchange="onSplitToggle()">
        <span class="toggle-slider"></span>
      </label>
      <span>&#9993; Split into 2 halves &mdash; generate separate summaries for each half</span>
    </div>

    <div id="newsArea" style="display:none; margin-top:12px;">

      <label>PDF ARTICLES (up to 10 &middot; add in multiple batches)</label>
      <div class="news-drop-zone" id="newsDropZone">
        <input type="file" id="newsFiles" accept=".pdf,application/pdf" multiple>
        <div class="drop-icon">&#128240;</div>
        <div class="drop-label">Drag &amp; drop PDFs or click to browse &mdash; you can add more after</div>
        <div class="drop-sub">Financial Times &middot; The Economist &middot; any news article PDF</div>
      </div>
      <div class="news-file-list" id="newsFileList"></div>

      <label style="margin-top:16px;display:block;">YOUTUBE VIDEOS (paste one URL per line)</label>
      <div style="position:relative;">
        <textarea id="ytUrlInput" rows="3" placeholder="https://www.youtube.com/watch?v=...&#10;https://youtu.be/..."
          style="width:100%;box-sizing:border-box;background:#1e293b;color:#e2e8f0;border:1.5px dashed #334155;
                 border-radius:8px;padding:10px 12px;font-size:0.88rem;resize:vertical;font-family:inherit;
                 outline:none;line-height:1.5;"></textarea>
        <button onclick="addYoutubeUrls()" style="margin-top:6px;padding:5px 16px;background:#1e40af;
          color:#fff;border:none;border-radius:6px;cursor:pointer;font-size:0.82rem;font-weight:600;">
          + Add URLs
        </button>
      </div>
      <div class="news-file-list" id="ytUrlList"></div>

    </div>

    <button class="btn-submit" id="submitBtn" onclick="startJob()">Generate Summary PDF</button>
    <div class="error-box" id="errorBox"></div>
  </div>

  <div class="card" id="progress-section">
    <div style="font-weight:600;margin-bottom:4px;">Processing...</div>
    <div class="progress-bar-wrap"><div class="progress-bar" id="progressBar"></div></div>
    <div class="progress-msg" id="progressMsg">Starting...</div>
    <button class="btn-cancel" id="cancelBtn" onclick="cancelJob()">Cancel job</button>
    <div class="chapter-feed" id="chapterFeed"></div>
  </div>

  <div class="card" id="result-section">
    <div style="font-size:1.1rem;font-weight:600;margin-bottom:16px;color:var(--green);" id="resultHeading">&#10003; Summary Ready!</div>
    <button class="btn-download" id="downloadBtn">&#11015; Download Summary PDF</button>
    <button class="btn-download" id="bundleBtn" style="background: var(--gold); margin-left: 10px;">&#128230; Download Full Bundle (ZIP)</button>
    <button class="btn-phone" id="phoneBtn">&#128241; Phone Version</button>
    <button class="btn-bw" id="bwBtn">&#128438; Print-Friendly (B&amp;W)</button>
    <button class="btn-cyan" id="cyanBtn">&#128438; Print-Friendly (Cyan)</button>
    <button class="btn-download" id="auditBtn" style="background:#334155;margin-left:10px;">&#128221; Audit Trail</button>
    <button class="btn-share" id="shareBtn">&#128279; Copy Share Link</button>
    <button class="btn-news-dark" id="newsDarkBtn" style="display:none">&#127769; Dark Mode</button>
    <button class="btn-news-light" id="newsLightBtn" style="display:none">&#9728; Light Mode</button>
    <button class="btn-phone" id="newsPhoneBtn" style="display:none">&#128241; Phone Dark</button>
    <button class="btn-news-print" id="newsPrintBtn" style="display:none">&#128424;&#65039; Print (B&amp;W)</button>
  </div>

  <!-- ── Split mode panels ───────────────────────────────────────────────── -->
  <div class="card" id="split-progress-section" style="display:none">
    <div style="font-weight:600;margin-bottom:16px;">&#9993; Processing — Split Mode</div>
    <div class="split-half">
      <div class="split-half-label" id="splitHalf1Label">PART 1 — FIRST HALF</div>
      <div class="progress-bar-wrap"><div class="progress-bar" id="splitBar1"></div></div>
      <div class="progress-msg" id="splitMsg1">Starting...</div>
    </div>
    <div class="split-half" style="margin-top:18px">
      <div class="split-half-label" id="splitHalf2Label">PART 2 — SECOND HALF</div>
      <div class="progress-bar-wrap"><div class="progress-bar" id="splitBar2"></div></div>
      <div class="progress-msg" id="splitMsg2">Waiting...</div>
    </div>
  </div>

  <div class="card" id="split-result-section" style="display:none">
    <div style="font-size:1.1rem;font-weight:600;margin-bottom:16px;color:var(--green);">&#10003; Both summaries ready!</div>
    <div id="splitResults"></div>
  </div>
</main>
</div><!-- /.app-layout -->

<div class="toast" id="toast"></div>

<script>
let currentJobId = null;
let pollInterval = null;
let lengthMode = 'percent';
let shareToken = null;
let knownChapters = new Set();

// Split mode state
let splitJobIds       = [];
let splitPollInterval = null;
let splitDone         = [false, false];
let splitShareTokens  = [null, null];

function escapeHtml(value) {
  return String(value).replace(/[&<>"']/g, ch => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
  }[ch]));
}

const STYLE_HINTS = {
  narrative_basic: ['Narrative — Basic', 'Default. Smooth chapter-by-chapter prose for most nonfiction and general reading.'],
  story_arc: ['Story-Arc Narrative', 'Best for story-driven books. Turns arguments/events into a clear beginning-to-end narrative.'],
  feynman_storyteller: ['Feynman Storyteller', 'Best for learning. Explains ideas simply, like teaching a smart friend from scratch.'],
  investigative_narrative: ['Investigative Narrative', 'Best for scandals, history, biographies. Follows motives, evidence, consequences, and turning points.'],
  strategic_briefing: ['Strategic Briefing', 'Best for business/investing reports. Focuses on thesis, implications, risks, decisions, and what changed.'],
  deep_reading: ['Deep Reading Companion', 'Best for dense books. Preserves nuance, examples, tensions, and author logic.'],
  practical_playbook: ['Practical Playbook', 'Best for self-help/business. Turns ideas into usable actions, warnings, principles, and checklists.'],
  literary_essay: ['Literary Essay', 'Best for philosophy/culture. Elegant thematic interpretation with context, ideas, and reflective synthesis.'],
  academic: ['Academic', 'Best for serious/technical sources. Precise, analytical, careful with definitions, evidence, and caveats.']
};

function updateStyleHint() {
  const el = document.getElementById('summaryStyle');
  const box = document.getElementById('styleHint');
  if (!el || !box) return;
  const info = STYLE_HINTS[el.value];
  if (!info) { box.style.display = 'none'; return; }
  box.style.display = 'block';
  box.innerHTML = `<strong>${escapeHtml(info[0])}</strong> — ${escapeHtml(info[1])}`;
}

window.addEventListener('DOMContentLoaded', () => {
  const saved = localStorage.getItem('bbc_api_key');
  if (saved) document.getElementById('apiKey').value = saved;
  updateStyleHint();
});

document.getElementById('summaryStyle').addEventListener('change', updateStyleHint);
document.getElementById('apiKey').addEventListener('change', e => {
  localStorage.setItem('bbc_api_key', e.target.value);
  const file = fileInput.files[0];
  if (file) handleFile(file);
});

const dropZone = document.getElementById('dropZone');
const fileInput = document.getElementById('pdfFile');
function isSupportedFile(file) {
  if (!file || !file.name) return false;
  const lower = file.name.toLowerCase();
  return lower.endsWith('.pdf') || lower.endsWith('.epub') || file.type === 'application/pdf' || file.type === 'application/epub+zip';
}

dropZone.addEventListener('dragover', e => { e.preventDefault(); dropZone.classList.add('drag-over'); });
dropZone.addEventListener('dragleave', () => dropZone.classList.remove('drag-over'));
dropZone.addEventListener('drop', e => {
  e.preventDefault();
  dropZone.classList.remove('drag-over');
  const file = e.dataTransfer.files[0];
  if (file && isSupportedFile(file)) handleFile(file);
});
fileInput.addEventListener('change', e => { const f = e.target.files[0]; if (f && isSupportedFile(f)) handleFile(f); else if (f) showError('Please upload a PDF or EPUB file.'); });

function handleFile(file) {
  const base = file.name.replace(/\.(pdf|epub)$/i, '');
  document.getElementById('bookTitle').value = base;

  document.getElementById('dropContent').innerHTML =
    `<div class="file-badge">&#128196; <span>${escapeHtml(file.name)}</span> <span class="page-badge" id="pageBadge">counting...</span></div>`;

  const fd = new FormData();
  fd.append('pdf', file);
  fetch('/pagecount', { method: 'POST', body: fd })
    .then(r => r.json())
    .then(d => {
      if (d.pages) {
        document.getElementById('pageBadge').textContent = d.pages + (d.estimated_pages ? ' est. pages' : ' pages');
        document.getElementById('costBadge').style.display = 'inline-flex';
        document.getElementById('costText').textContent = `${d.cost} · ${d.time}`;
      }
      if (d.error) showError(d.error);
    }).catch(() => {});

  const apiKey = document.getElementById('apiKey').value.trim();
  const cleanKey = apiKey.split('').filter(c => c.charCodeAt(0) < 128).join('');
  const sugSection = document.getElementById('suggestions-section');
  sugSection.style.display = 'block';
  document.getElementById('suggestionsContent').className = 'suggestion-loading';
  document.getElementById('suggestionsContent').textContent = 'Analysing book...';

  const fd2 = new FormData();
  fd2.append('pdf', file);
  fd2.append('api_key', cleanKey);
  fd2.append('title', base);
  fetch('/suggest', { method: 'POST', body: fd2 })
    .then(r => r.json())
    .then(data => {
      if (data.suggestions) renderSuggestions(data.suggestions);
    }).catch(() => {
      document.getElementById('suggestionsContent').textContent = 'Could not generate suggestions.';
    });
}

function renderSuggestions(suggestions) {
  const labels = ['QUICK', 'BALANCED', 'DEEP DIVE'];
  const html = `<div class="suggestion-cards">${suggestions.map((s, i) => {
    const pages = Math.max(1, parseInt(s.pages || 20, 10));
    return `
    <div class="suggestion-card" onclick="selectSuggestion(this, ${pages})" data-pages="${pages}">
      <div class="s-check">&#10003;</div>
      <div class="s-label">${escapeHtml(labels[i] || 'OPTION ' + (i+1))}</div>
      <div class="s-pages">${pages} pages</div>
      <div class="s-reason">${escapeHtml(s.reason || '')}</div>
    </div>`;
  }).join('')}
    <div class="suggestion-card" onclick="calculateTailoredPlan()" data-pages="tailored">
      <div class="s-label">TAILORED</div>
      <div class="s-pages">10%-50% plan</div>
      <div class="s-reason">Calculates source words, chapter count, average chapter size, and fixed-page requests for 10%, 20%, 30%, 40%, and 50% summaries.</div>
    </div>
  </div><div id="tailoredDetails"></div>`;
  const el = document.getElementById('suggestionsContent');
  el.className = '';
  el.innerHTML = html;
}

function formatInt(n) {
  return (parseInt(n || 0, 10)).toLocaleString();
}

function calculateTailoredPlan() {
  const file = fileInput.files[0];
  if (!file) { showError('Please upload a PDF or EPUB first.'); return; }
  const details = document.getElementById('tailoredDetails');
  details.innerHTML = '<div class="tailored-panel">Calculating tailored plan from the full source text...</div>';
  const fd = new FormData();
  fd.append('pdf', file);
  fetch('/tailored', { method: 'POST', body: fd })
    .then(r => r.json())
    .then(data => {
      if (data.error) {
        details.innerHTML = '<div class="tailored-panel">' + escapeHtml(data.error) + '</div>';
        return;
      }
      const opts = (data.options || []).map(o => `
        <div class="tailored-option" onclick="selectTailoredPages(${parseInt(o.pages || 1, 10)})">
          <strong>${parseInt(o.percent || 0, 10)}%</strong> of source words<br>
          <span>${formatInt(o.target_words)} words</span><br>
          <span class="tailored-metric">Use ~${parseInt(o.pages || 1, 10)} pages (${parseInt(o.allowed_min || 1, 10)}-${parseInt(o.allowed_max || 1, 10)} allowed)</span>
        </div>`).join('');
      details.innerHTML = `
        <div class="tailored-panel">
          <strong>Tailored length planner</strong><br>
          Source words: <strong>${formatInt(data.word_count)}</strong> &nbsp; | &nbsp;
          Chapters/sections: <strong>${formatInt(data.chapter_count)}</strong> &nbsp; | &nbsp;
          Avg. words/chapter: <strong>${formatInt(data.avg_words_per_chapter)}</strong>
          <div class="tailored-grid">${opts}</div>
          <div class="tailored-metric" style="margin-top:10px;">These are fixed-page requests estimated from the app's current page-density settings. The final PDF still uses the selected strictness cap.</div>
        </div>`;
    }).catch(() => {
      details.innerHTML = '<div class="tailored-panel">Could not calculate tailored plan.</div>';
    });
}

function selectTailoredPages(pages) {
  setLengthMode('fixed');
  document.getElementById('fixedPages').value = Math.max(1, parseInt(pages || 1, 10));
  showToast('Tailored page length selected.');
}

function selectSuggestion(card, pages) {
  document.querySelectorAll('.suggestion-card').forEach(c => c.classList.remove('selected'));
  card.classList.add('selected');
  setLengthMode('fixed');
  document.getElementById('fixedPages').value = pages;
}

function setLengthMode(mode) {
  lengthMode = mode;
  document.getElementById('btnPercent').classList.toggle('active', mode === 'percent');
  document.getElementById('btnFixed').classList.toggle('active', mode === 'fixed');
  document.getElementById('pctRow').style.display   = mode === 'percent' ? 'flex' : 'none';
  document.getElementById('fixedRow').style.display = mode === 'fixed'   ? 'block' : 'none';
}

function onSplitToggle() {
  if (newsMode) { document.getElementById('splitMode').checked = false; return; }
  const on = document.getElementById('splitMode').checked;
  document.getElementById('submitBtn').textContent = on
    ? 'Split & Summarize Both Halves'
    : 'Generate Summary PDF';
}

async function startJob() {
  if (newsMode) { await startNewsJob(); return; }
  const file = fileInput.files[0];
  if (!file) { showError('Please upload a PDF or EPUB.'); return; }

  const rawKey   = document.getElementById('apiKey').value.trim();
  const cleanKey = rawKey.split('').filter(c => c.charCodeAt(0) < 128).join('');
  if (!cleanKey.startsWith('sk-ant-')) { showError('API key must start with sk-ant-'); return; }

  const title        = document.getElementById('bookTitle').value.trim() || file.name.replace(/\.(pdf|epub)$/i, '');
  const author       = document.getElementById('bookAuthor').value.trim();
  const style        = document.getElementById('summaryStyle').value;
  const instructions = document.getElementById('instructions').value;
  const pageStrictness = document.getElementById('pageStrictness').value;
  const lengthValue  = lengthMode === 'percent'
    ? document.getElementById('pctSlider').value
    : document.getElementById('fixedPages').value;

  const fd = new FormData();
  fd.append('pdf', file);
  fd.append('api_key', cleanKey);
  fd.append('title', title);
  fd.append('author', author);
  fd.append('style', style);
  fd.append('instructions', instructions);
  fd.append('length_mode', lengthMode);
  fd.append('length_value', lengthValue);
  fd.append('page_strictness', pageStrictness);

  showError('');
  document.getElementById('submitBtn').disabled = true;
  knownChapters = new Set();

  const isSplit = document.getElementById('splitMode').checked;
  if (isSplit && file.name.toLowerCase().endsWith('.epub')) { showError('Split mode is only available for PDF files.'); document.getElementById('submitBtn').disabled = false; return; }

  // Reset all panels
  ['progress-section','result-section','split-progress-section','split-result-section'].forEach(id => {
    document.getElementById(id).style.display = 'none';
  });

  if (isSplit) {
    document.getElementById('split-progress-section').style.display = 'block';
    document.getElementById('splitBar1').style.width = '0%';
    document.getElementById('splitBar2').style.width = '0%';
    document.getElementById('splitMsg1').textContent = 'Starting...';
    document.getElementById('splitMsg2').textContent = 'Waiting for Part 1 to start...';
    document.getElementById('splitHalf1Label').textContent = 'PART 1 — FIRST HALF';
    document.getElementById('splitHalf2Label').textContent = 'PART 2 — SECOND HALF';
    fd.append('split_mode', 'true');
    try {
      const res  = await fetch('/start', { method: 'POST', body: fd });
      const data = await res.json();
      if (data.error) { showError(data.error); resetForm(); return; }
      splitJobIds      = data.job_ids;
      splitDone        = [false, false];
      splitShareTokens = [null, null];
      const sp = data.split_page || '?';
      const st = data.split_title || 'Second Half';
      document.getElementById('splitHalf1Label').textContent = `PART 1 — Pages 1–${sp}`;
      document.getElementById('splitHalf2Label').textContent = `PART 2 — From “${st}”`;
      splitPollInterval = setInterval(pollSplitStatus, 2000);
    } catch (e) {
      showError('Network error: ' + e.message);
      resetForm();
    }
  } else {
    document.getElementById('progress-section').style.display = 'block';
    document.getElementById('chapterFeed').innerHTML = '';
    try {
      const res  = await fetch('/start', { method: 'POST', body: fd });
      const data = await res.json();
      if (data.error) { showError(data.error); resetForm(); return; }
      currentJobId = data.job_id;
      pollInterval = setInterval(pollStatus, 2000);
    } catch (e) {
      showError('Network error: ' + e.message);
      resetForm();
    }
  }
}

async function pollStatus() {
  if (!currentJobId) return;
  try {
    const res  = await fetch('/status/' + currentJobId);
    const data = await res.json();

    document.getElementById('progressBar').style.width = data.progress + '%';
    document.getElementById('progressMsg').textContent = data.message || '';

    if (data.chapters) {
      for (const ch of data.chapters) {
        if (!knownChapters.has(ch.index)) {
          knownChapters.add(ch.index);
          const card = document.createElement('div');
          card.className = 'chapter-card';
          card.innerHTML = `<div class="chapter-dot"></div><span>${escapeHtml(ch.title || '')}</span>`;
          document.getElementById('chapterFeed').appendChild(card);
        }
      }
    }

    if (data.status === 'done') {
      clearInterval(pollInterval);
      shareToken = data.share_token;
      showResult();
    } else if (data.status === 'cancelled') {
      clearInterval(pollInterval);
      showError('Job cancelled.');
      resetForm();
    } else if (data.status === 'error') {
      clearInterval(pollInterval);
      showError(data.error || 'An error occurred.');
      resetForm();
    }
  } catch (e) { /* ignore transient */ }
}

async function cancelJob() {
  if (!currentJobId) return;
  try {
    await fetch('/cancel/' + currentJobId, { method: 'POST' });
    document.getElementById('progressMsg').textContent = 'Cancelling after the current safe checkpoint...';
  } catch (e) { /* ignore */ }
}

function showResult() {
  document.getElementById('result-section').style.display = 'block';
  if (newsMode) {
    // Show news-specific buttons, hide all book buttons
    ['downloadBtn','bundleBtn','phoneBtn','bwBtn','cyanBtn','auditBtn','shareBtn'].forEach(id => {
      document.getElementById(id).style.display = 'none';
    });
    ['newsDarkBtn','newsLightBtn','newsPhoneBtn','newsPrintBtn'].forEach(id => {
      document.getElementById(id).style.display = '';
    });
    document.getElementById('resultHeading').textContent = '✓ News Digest Ready!';
    document.getElementById('newsDarkBtn').onclick  = () => { window.location.href = '/download_news_dark/'  + currentJobId; };
    document.getElementById('newsLightBtn').onclick = () => { window.location.href = '/download_news_light/' + currentJobId; };
    document.getElementById('newsPhoneBtn').onclick = () => { window.location.href = '/download_news_phone/' + currentJobId; };
    document.getElementById('newsPrintBtn').onclick = () => { window.location.href = '/download_news_print/' + currentJobId; };
  } else {
    ['newsDarkBtn','newsLightBtn','newsPhoneBtn','newsPrintBtn'].forEach(id => {
      document.getElementById(id).style.display = 'none';
    });
    ['downloadBtn','bundleBtn','phoneBtn','bwBtn','cyanBtn','auditBtn','shareBtn'].forEach(id => {
      document.getElementById(id).style.display = '';
    });
    document.getElementById('resultHeading').textContent = '✓ Summary Ready!';
    document.getElementById('downloadBtn').onclick = () => { window.location.href = '/download/'        + currentJobId; };
    document.getElementById('bundleBtn').onclick   = () => { window.location.href = '/download_bundle/' + currentJobId; };
    document.getElementById('phoneBtn').onclick    = () => { window.location.href = '/download_phone/'  + currentJobId; };
    document.getElementById('bwBtn').onclick       = () => { window.location.href = '/download_bw/'     + currentJobId; };
    document.getElementById('cyanBtn').onclick     = () => { window.location.href = '/download_cyan/'   + currentJobId; };
    document.getElementById('auditBtn').onclick    = () => { window.location.href = '/download_audit/'  + currentJobId; };
    document.getElementById('shareBtn').onclick    = () => {
      const url = window.location.origin + '/view/' + shareToken;
      navigator.clipboard.writeText(url).then(() => showToast("You're getting wiser! 📚"));
    };
  }
  confetti({ particleCount: 120, spread: 80, origin: { y: 0.5 } });
  showToast(newsMode ? 'News digest ready! 📰' : "You're getting wiser! 📚");
  setTimeout(_histLoad, 1500);
}

function resetForm() {
  document.getElementById('submitBtn').disabled = false;
  if (splitPollInterval) { clearInterval(splitPollInterval); splitPollInterval = null; }
}

// ── Split mode polling ────────────────────────────────────────────────────────
async function pollSplitStatus() {
  for (let i = 0; i < 2; i++) {
    if (splitDone[i]) continue;
    try {
      const res  = await fetch('/status/' + splitJobIds[i]);
      const data = await res.json();
      document.getElementById('splitBar' + (i+1)).style.width = data.progress + '%';
      document.getElementById('splitMsg' + (i+1)).textContent  = data.message || '';
      if (data.status === 'done') {
        splitDone[i]        = true;
        splitShareTokens[i] = data.share_token;
        document.getElementById('splitMsg' + (i+1)).textContent += ' ✓';
      } else if (data.status === 'error') {
        splitDone[i] = true;
        document.getElementById('splitMsg' + (i+1)).textContent = '⚠ Error: ' + (data.error || 'Unknown');
      }
    } catch (e) { /* ignore transient */ }
  }
  if (splitDone[0] && splitDone[1]) {
    clearInterval(splitPollInterval);
    splitPollInterval = null;
    showSplitResult();
  }
}

function showSplitResult() {
  const container = document.getElementById('splitResults');
  container.innerHTML = '';
  [['Part 1 of 2', 0], ['Part 2 of 2', 1]].forEach(([label, i]) => {
    const card = document.createElement('div');
    card.className = 'split-result-card';
    const err = document.getElementById('splitMsg' + (i+1)).textContent.startsWith('⚠');
    if (err) {
      card.innerHTML = `<div class="split-result-title">&#128218; ${label}</div>
        <span style="color:#f87171">This half failed — see message above.</span>`;
    } else {
      card.innerHTML = `<div class="split-result-title">&#128218; ${label}</div>
        <button class="btn-download" onclick="window.location.href='/download/${splitJobIds[i]}'">&#11015; Download PDF</button>
        <button class="btn-download" onclick="window.location.href='/download_bundle/${splitJobIds[i]}'" style="background:var(--gold);margin-left:10px;">&#128230; Full Bundle</button>
        <button class="btn-phone" onclick="window.location.href='/download_phone/${splitJobIds[i]}'" style="margin-left:10px;">&#128241; Phone</button>`;
    }
    container.appendChild(card);
  });
  document.getElementById('split-result-section').style.display = 'block';
  const anyOk = !splitDone.every((_, i) =>
    document.getElementById('splitMsg' + (i+1)).textContent.startsWith('⚠'));
  if (anyOk) {
    confetti({ particleCount: 150, spread: 90, origin: { y: 0.5 } });
    showToast('Both halves summarized! 📚📚');
  }
}

function showError(msg) {
  const box = document.getElementById('errorBox');
  if (msg) { box.textContent = msg; box.style.display = 'block'; }
  else { box.style.display = 'none'; }
}

function showToast(msg) {
  const t = document.getElementById('toast');
  t.textContent = msg;
  t.style.display = 'block';
  setTimeout(() => { t.style.display = 'none'; }, 3500);
}

// ── News Mode ──────────────────────────────────────────────────────────────────
let newsMode = false;
const NEWS_HIDE_IDS = ['dropZone','costBadge','suggestions-section','bookTitleAuthorRow','styleLengthRow','strictnessGroup','instructionsGroup','splitToggleRow'];

function setMode(mode) {
  newsMode = mode === 'news';
  document.getElementById('btnBookMode').classList.toggle('active', !newsMode);
  document.getElementById('btnNewsMode').classList.toggle('active', newsMode);
  NEWS_HIDE_IDS.forEach(id => {
    const el = document.getElementById(id);
    if (el) el.style.display = newsMode ? 'none' : '';
  });
  document.getElementById('newsArea').style.display = newsMode ? 'block' : 'none';
  document.getElementById('submitBtn').textContent = newsMode ? 'Generate News Digest' : 'Generate Summary PDF';
  if (newsMode) document.getElementById('splitMode').checked = false;
  showError('');
}

// ── News: cumulative PDF staging + YouTube URL list ───────────────────────────
let stagedNewsFiles = [];   // File objects accumulated across multiple browse/drops
let stagedYtUrls    = [];   // YouTube URLs accumulated

const newsDropZone   = document.getElementById('newsDropZone');
const newsFilesInput = document.getElementById('newsFiles');
newsDropZone.addEventListener('dragover', e => { e.preventDefault(); newsDropZone.classList.add('drag-over'); });
newsDropZone.addEventListener('dragleave', () => newsDropZone.classList.remove('drag-over'));
newsDropZone.addEventListener('drop', e => {
  e.preventDefault();
  newsDropZone.classList.remove('drag-over');
  addNewsFiles(e.dataTransfer.files);
});
newsFilesInput.addEventListener('change', e => { addNewsFiles(e.target.files); e.target.value = ''; });

function addNewsFiles(fileList) {
  const incoming = Array.from(fileList).filter(f => f.name.toLowerCase().endsWith('.pdf'));
  if (!incoming.length) { showError('Please add PDF files.'); return; }
  const existing = new Set(stagedNewsFiles.map(f => f.name));
  incoming.forEach(f => { if (!existing.has(f.name)) stagedNewsFiles.push(f); });
  if (stagedNewsFiles.length > 10) {
    stagedNewsFiles = stagedNewsFiles.slice(0, 10);
    showError('Maximum 10 PDFs — list capped at 10.');
  } else { showError(''); }
  renderNewsList();
}

function removeNewsFile(idx) {
  stagedNewsFiles.splice(idx, 1);
  renderNewsList();
}

function renderNewsList() {
  const list = document.getElementById('newsFileList');
  if (!stagedNewsFiles.length) { list.innerHTML = ''; return; }
  list.innerHTML = stagedNewsFiles.map((f, i) =>
    `<div class="news-file-item">
       <div class="news-file-num">${i+1}</div>
       <span style="flex:1;">${escapeHtml(f.name)}</span>
       <button onclick="removeNewsFile(${i})" style="background:none;border:none;color:#f87171;
         cursor:pointer;font-size:1rem;padding:0 4px;line-height:1;" title="Remove">&times;</button>
     </div>`
  ).join('');
}

function addYoutubeUrls() {
  const ta   = document.getElementById('ytUrlInput');
  const lines = ta.value.split('\n').map(l => l.trim()).filter(l =>
    l && (l.includes('youtube.com') || l.includes('youtu.be'))
  );
  if (!lines.length) { showError('Paste at least one YouTube URL.'); return; }
  const existing = new Set(stagedYtUrls);
  lines.forEach(u => { if (!existing.has(u)) { stagedYtUrls.push(u); existing.add(u); } });
  if (stagedYtUrls.length > 10) { stagedYtUrls = stagedYtUrls.slice(0, 10); showError('Maximum 10 videos.'); }
  else { showError(''); }
  ta.value = '';
  renderYtList();
}

function removeYtUrl(idx) {
  stagedYtUrls.splice(idx, 1);
  renderYtList();
}

function renderYtList() {
  const list = document.getElementById('ytUrlList');
  if (!stagedYtUrls.length) { list.innerHTML = ''; return; }
  list.innerHTML = stagedYtUrls.map((u, i) =>
    `<div class="news-file-item">
       <div class="news-file-num" style="background:#1e40af;">&#9654;</div>
       <span style="flex:1;font-size:0.78rem;word-break:break-all;">${escapeHtml(u)}</span>
       <button onclick="removeYtUrl(${i})" style="background:none;border:none;color:#f87171;
         cursor:pointer;font-size:1rem;padding:0 4px;line-height:1;" title="Remove">&times;</button>
     </div>`
  ).join('');
}

async function startNewsJob() {
  // Auto-grab any URLs still sitting in the textarea before validating
  const ta = document.getElementById('ytUrlInput');
  if (ta && ta.value.trim()) addYoutubeUrls();

  if (!stagedNewsFiles.length && !stagedYtUrls.length) {
    showError('Add at least one PDF or YouTube URL before generating.');
    return;
  }

  const rawKey   = document.getElementById('apiKey').value.trim();
  const cleanKey = rawKey.split('').filter(c => c.charCodeAt(0) < 128).join('');
  if (!cleanKey.startsWith('sk-ant-')) { showError('API key must start with sk-ant-'); return; }

  showError('');
  document.getElementById('submitBtn').disabled = true;
  knownChapters = new Set();
  ['progress-section','result-section','split-progress-section','split-result-section'].forEach(id => {
    document.getElementById(id).style.display = 'none';
  });
  document.getElementById('progress-section').style.display = 'block';
  document.getElementById('chapterFeed').innerHTML = '';
  document.getElementById('progressMsg').textContent = 'Starting news digest...';
  document.getElementById('progressBar').style.width = '0%';

  const fd = new FormData();
  stagedNewsFiles.forEach(f => fd.append('pdfs', f));
  fd.append('youtube_urls', stagedYtUrls.join('\n'));
  fd.append('api_key', cleanKey);

  try {
    const res  = await fetch('/start_news', { method: 'POST', body: fd });
    const data = await res.json();
    if (data.error) { showError(data.error); resetForm(); return; }
    currentJobId = data.job_id;
    pollInterval = setInterval(pollStatus, 2000);
  } catch (e) {
    showError('Network error: ' + e.message);
    resetForm();
  }
}

// ── History Sidebar ────────────────────────────────────────────────────────────
let _histActiveId = null;

function _histFmtDate(ts) {
  const d = new Date(ts * 1000);
  return d.toLocaleDateString('en-GB', { day:'numeric', month:'short', year:'numeric' });
}

function _histRender(entries) {
  const list = document.getElementById('historyList');
  const count = document.getElementById('histCount');
  count.textContent = entries.length ? `(${entries.length})` : '';
  if (!entries.length) {
    list.innerHTML = '<div class="hist-empty">No history yet</div>';
    document.getElementById('histDetail').style.display = 'none';
    return;
  }
  list.innerHTML = entries.map(e => {
    const icon = e.type === 'news' ? '&#128240;' : '&#128218;';
    const typeLabel = e.type === 'news' ? 'NEWS' : 'BOOK';
    const active = e.id === _histActiveId ? ' active' : '';
    return `<div class="hist-item${active}" id="hitem-${e.id}" onclick="_histSelect('${e.id}')">
      <button class="hist-del" onclick="event.stopPropagation();_histDelete('${e.id}')" title="Delete">&times;</button>
      <div><span class="hist-icon">${icon}</span><span class="hist-title">${e.title}</span></div>
      <div class="hist-date">${_histFmtDate(e.created_at)}</div>
      <span class="hist-type ${e.type}">${typeLabel}</span>
    </div>`;
  }).join('');
}

function _histSelect(id) {
  _histActiveId = id;
  const entries = _histCurrentEntries || [];
  const e = entries.find(x => x.id === id);
  document.querySelectorAll('.hist-item').forEach(el => el.classList.remove('active'));
  const el = document.getElementById('hitem-' + id);
  if (el) el.classList.add('active');
  const detail = document.getElementById('histDetail');
  const title  = document.getElementById('histDetailTitle');
  const links  = document.getElementById('histDetailLinks');
  if (!e) { detail.style.display = 'none'; return; }
  detail.style.display = 'block';
  title.textContent = e.title;
  if (e.type === 'book') {
    links.innerHTML = `<a class="hist-dl-btn" href="/download_history/${e.id}/pdf" download>&#128196; Download PDF</a>`;
  } else {
    links.innerHTML = `
      <a class="hist-dl-btn" href="/download_history/${e.id}/dark" download>&#127761; Dark Mode</a>
      <a class="hist-dl-btn" href="/download_history/${e.id}/light" download>&#9728;&#65039; Light Mode</a>
      <a class="hist-dl-btn" href="/download_history/${e.id}/phone" download>&#128241; Phone Dark</a>
      <a class="hist-dl-btn" href="/download_history/${e.id}/print" download>&#128424;&#65039; Print (B&amp;W)</a>`;
  }
}

let _histCurrentEntries = [];

async function _histLoad() {
  try {
    const r = await fetch('/history');
    _histCurrentEntries = await r.json();
    _histRender(_histCurrentEntries);
    if (_histActiveId) _histSelect(_histActiveId);
  } catch (e) {}
}

async function _histDelete(id) {
  if (!confirm('Remove this entry from history?')) return;
  await fetch('/history/' + id, { method: 'DELETE' });
  if (_histActiveId === id) {
    _histActiveId = null;
    document.getElementById('histDetail').style.display = 'none';
  }
  await _histLoad();
}

_histLoad();
</script>
</body>
</html>"""

# ── News Mode ─────────────────────────────────────────────────────────────────
def _clean_news_article_text(raw_text, max_chars=None):
    """Remove browser/PDF chrome from Economist/FT-style article exports.

    The news summarizer should budget and summarize the article body, not nav
    menus, page headers, newsletter promos, recirculation links, or legal footer
    text. This cleaner is intentionally conservative: it drops known boilerplate
    lines/blocks, repairs common PDF drop-cap splits, and preserves the title,
    subtitle, date, and article prose.
    """
    max_chars = NEWS_ARTICLE_MAX_CHARS if max_chars is None else int(max_chars or NEWS_ARTICLE_MAX_CHARS)
    text = str(raw_text or "")
    text = (
        text.replace("\x00", " ")
            .replace("\r", "\n")
            .replace("\u00ad", "")
            .replace("￾", "")
            .replace("ﬁ", "fi")
            .replace("ﬂ", "fl")
            .replace("￾", "")
            .replace("", " ")
            .replace("", " ")
    )
    text = re.sub(r"https?://\S+", " ", text)
    text = re.sub(r"(?im)^\s*\d{1,2}/\d{1,2}/\d{2,4},.*$", " ", text)
    text = re.sub(r"(?im)^\s*page\s+\d+\s+of\s+\d+\s*$", " ", text)

    lines = []
    skip_related = 0
    stop = False
    hard_stop_patterns = [
        r"^Subscribers to The Economist can sign up",
        r"^Explore more$",
        r"^This article appeared in ",
        r"^From the May \d",
        r"^Discover stories from this section",
        r"^More from ",
        r"^Get The Economist app",
        r"^To enhance your experience",
        r"^Terms of use",
        r"^Registered in ",
        r"^©\s*The Economist",
        r"^the economist$",
        r"^THE ECONOMIST$",
        r"^About$",
        r"^Reuse our content$",
        r"^Subscribe$",
        r"^Gift subscriptions$",
        r"^SecureDrop$",
        r"^Help and support$",
        r"^Advertise$",
        r"^Press centre$",
        r"^Affiliate programme$",
        r"^Working here$",
        r"^Executive Jobs$",
    ]
    boilerplate_patterns = [
        r"^\s*[]+\s*$",
        r"^Weekly edition\b",
        r"^World in brief\b",
        r"^United States\b.*Finance",
        r"^Europe?$",
        r"^Leaders\s+Follow",
        r"^Opinion\s+Follow",
        r"^Economics\s+Follow",
        r"^Defence\s+Follow",
        r"^Medicine\s+Follow",
        r"^Africa\s+Follow",
        r"^Elon Musk\s+Follow",
        r"^Space\s+Follow",
        r"^Keir Starmer\s+Follow",
        r"^Britain\s+Follow",
        r"^Save\s+Share",
        r"^Reuse this content$",
        r"^subscriber only",
        r"^Sign up to our",
        r"^Editorials, columns",
        r"^Sign up$",
        r"^Listen to this story$",
        r"^ADVERTISEMENT$",
        r"^advertisement$",
        r"^0:00\s*/\s*0:00$",
        r"^●\s*Insider",
        r"^Insider\s+For you",
        r"^For you$",
        r"^Menu$",
        r"^Your Privacy Choices",
        r"^Cookie Policy$",
        r"^Modern Slavery Statement$",
        r"^Sitemap$",
        r"^Manage cookies$",
        r"^The Economist Pro$",
        r"^The Economist Group$",
        r"^Economist Enterprise",
        r"^contact$",
        r"^careers$",
        r"^Photograph:",
        r"^PHOTOGRAPH:",
        r"^Illustration:",
        r"^ILLUSTRATION:",
        r"^May \d{1,2}(?:st|nd|rd|th) \d{4}\s*\|",
        r"^\d+\s*min read$",
        r"^→\s*See the latest",
        r"^⇒?Explore the edition$",
    ]
    related_starts = (
        "Dig deeper",
        "Read the rest of our cover package",
    )
    related_resume_prefixes = (
        "America was", "On May", "Another lesson", "Success will",
        "Mr Rutte", "Even with", "In Mr", "One lesson", "Whoever next",
        "Last,", "Britain needs", "Politically,", "Be patient",
    )

    for raw_line in text.splitlines():
        line = re.sub(r"\s+", " ", raw_line or "").strip()
        line = re.sub(r"●\s*Insider\s+For\s+you", " ", line, flags=re.IGNORECASE)
        line = re.sub(r"\bInsider\s+For\s+you\b", " ", line, flags=re.IGNORECASE)
        line = re.sub(r"\bj\s+y,\s*p\s+y\b", " ", line, flags=re.IGNORECASE)
        line = re.sub(r"0:00\s*/?\s*0:00(?:\s*/?\s*0:00)?", " ", line, flags=re.IGNORECASE)
        line = re.sub(r"\s+", " ", line).strip()
        if not line:
            continue
        if any(re.search(pat, line, flags=re.IGNORECASE) for pat in hard_stop_patterns):
            stop = True
            break
        if skip_related > 0:
            # Drop short related-story link lines after boxes like "Dig deeper".
            # Real article paragraphs resume with recognizable prose starts or
            # longer lines.
            if any(line.startswith(prefix) for prefix in related_resume_prefixes):
                skip_related = 0
            elif _count_words(line) <= 12 or line.startswith(("•", "-", "→")):
                skip_related -= 1
                continue
            else:
                skip_related = 0
        if any(line.lower().startswith(x.lower()) for x in related_starts):
            skip_related = 4
            continue
        if any(re.search(pat, line, flags=re.IGNORECASE) for pat in boilerplate_patterns):
            continue
        if re.match(r"^\d+/\d+$", line):
            continue
        if line in {"/", "//"}:
            continue
        if re.match(r"^https?://", line, flags=re.I):
            continue
        if re.match(r"^The Economist$", line):
            continue
        lines.append(line)

    cleaned = "\n".join(lines)
    # Repair common drop-cap splits produced by PDF text extraction.
    dropcap_repairs = {
        r"\bY\s+et\b": "Yet",
        r"\bE\s+bola\b": "Ebola",
        r"\bI\s+f\b": "If",
        r"\bT\s+o\b": "To",
        r"\bT\s+he\b": "The",
    }
    for pat, repl in dropcap_repairs.items():
        cleaned = re.sub(pat, repl, cleaned)
    cleaned = re.sub(r"\n{3,}", "\n\n", cleaned)
    cleaned = re.sub(r"[ \t]{2,}", " ", cleaned).strip()
    if max_chars and len(cleaned) > max_chars:
        cleaned = cleaned[:max_chars].rsplit(" ", 1)[0].strip()
    return cleaned


def _extract_article_text(pdf_bytes, max_chars=None):
    """Extract and clean text from a single article PDF for news summarization."""
    max_chars = NEWS_ARTICLE_MAX_CHARS if max_chars is None else int(max_chars or NEWS_ARTICLE_MAX_CHARS)
    raw = ""
    try:
        reader = PdfReader(BytesIO(pdf_bytes))
        texts = [page.extract_text() or "" for page in reader.pages]
        raw = "\n\n".join(texts).strip()
    except Exception:
        raw = ""
    if len(raw.strip()) < 500:
        try:
            with pdfplumber.open(BytesIO(pdf_bytes)) as pdf:
                texts = [page.extract_text() or "" for page in pdf.pages]
                raw = "\n\n".join(texts).strip()
        except Exception:
            raw = raw or ""
    return _clean_news_article_text(raw, max_chars=max_chars)


def _build_news_pdf(out_path, title, sections, mode="dark"):
    """Build a polished news digest PDF. mode: 'dark' | 'light' | 'phone_dark'."""
    is_dark  = mode in ("dark", "phone_dark")
    is_phone = mode == "phone_dark"
    is_print = mode == "print"

    # ── Palette ────────────────────────────────────────────────────────────────
    if is_dark:
        PAGE_BG   = colors.HexColor("#07070f")
        TEXT      = colors.HexColor("#e8e8f0")
        ACCENT    = colors.HexColor("#a78bfa"); AHX = "#a78bfa"
        GOLD      = colors.HexColor("#f59e0b"); GHX = "#f59e0b"
        MUTED     = colors.HexColor("#5b5b7b")
        RULE      = colors.HexColor("#1f1f3a")
        SW_BG     = colors.HexColor("#1c1400")
        DA_LINE   = colors.HexColor("#4b5563")
        BADGE_BG  = colors.HexColor("#a78bfa")
        BADGE_FG  = colors.HexColor("#07070f")
    elif is_print:
        # Consultancy black-&-white print mode. Designed grayscale-first so it
        # reads as a professional report on a mono laser printer rather than a
        # colour design flattened into muddy greys.
        PAGE_BG   = colors.white
        TEXT      = colors.HexColor("#16181d")
        ACCENT    = colors.HexColor("#000000"); AHX = "#000000"
        GOLD      = colors.HexColor("#2b2b2b"); GHX = "#2b2b2b"
        MUTED     = colors.HexColor("#5c6066")
        RULE      = colors.HexColor("#c7ccd1")
        SW_BG     = colors.HexColor("#f1f2f4")
        DA_LINE   = colors.HexColor("#7a7f87")
        BADGE_BG  = colors.HexColor("#111316")
        BADGE_FG  = colors.white
    else:
        PAGE_BG   = colors.white
        TEXT      = colors.HexColor("#1a1a2e")
        ACCENT    = colors.HexColor("#7c3aed"); AHX = "#7c3aed"
        GOLD      = colors.HexColor("#b45309"); GHX = "#b45309"
        MUTED     = colors.HexColor("#6b7280")
        RULE      = colors.HexColor("#e5e7eb")
        SW_BG     = colors.HexColor("#fffbeb")
        DA_LINE   = colors.HexColor("#9ca3af")
        BADGE_BG  = colors.HexColor("#7c3aed")
        BADGE_FG  = colors.white

    # YouTube section rule is red in colour modes, but a red hairline prints as a
    # weak grey — use the body ink colour so it stays crisp in B&W.
    YT_RULE = TEXT if is_print else colors.HexColor("#ff0000")

    # ── Geometry ───────────────────────────────────────────────────────────────
    if is_phone:
        PAGE = (90*mm, 190*mm); LR, TB = 1.2*cm, 1.4*cm; FS = 10.5
    else:
        PAGE = A4;              LR, TB = 2.2*cm, 2.2*cm; FS = 9.5
    W, H = PAGE

    # ── Styles ─────────────────────────────────────────────────────────────────
    def _ps(name, **kw):
        return ParagraphStyle(name, **kw)

    st_cov_main  = _ps("NC0", fontName="Helvetica-Bold",    fontSize=FS*3.8,
                        textColor=TEXT,   alignment=TA_CENTER, leading=FS*4.2, spaceAfter=0)
    st_cov_date  = _ps("NC1", fontName="Helvetica",         fontSize=FS*1.35,
                        textColor=GOLD,   alignment=TA_CENTER, spaceAfter=4)
    st_cov_sub   = _ps("NC2", fontName="Helvetica",         fontSize=FS*1.05,
                        textColor=MUTED,  alignment=TA_CENTER, spaceAfter=0)
    st_section   = _ps("NS0", fontName="Helvetica-Bold",    fontSize=FS*1.7,
                        textColor=ACCENT, spaceAfter=4, spaceBefore=0)
    st_label     = _ps("NL0", fontName="Helvetica-Bold",    fontSize=FS*0.78,
                        textColor=ACCENT, spaceAfter=2, spaceBefore=9, leading=FS)
    st_gold_lbl  = _ps("NL1", fontName="Helvetica-Bold",    fontSize=FS*0.78,
                        textColor=GOLD,   spaceAfter=2, spaceBefore=6, leading=FS)
    st_art_title = _ps("NAT", fontName="Helvetica-Bold",    fontSize=FS*1.25,
                        textColor=TEXT,   spaceAfter=0, spaceBefore=0, leading=FS*1.65)
    st_headline  = _ps("NHL", fontName="Helvetica-Oblique", fontSize=FS*1.08,
                        textColor=TEXT,   spaceAfter=4, leading=FS*1.65,
                        alignment=TA_JUSTIFY)
    st_body      = _ps("NBO", fontName="Helvetica",         fontSize=FS,
                        textColor=TEXT,   spaceAfter=3, leading=FS*1.6,
                        alignment=TA_JUSTIFY)
    st_bullet    = _ps("NBL", fontName="Helvetica",         fontSize=FS,
                        textColor=TEXT,   spaceAfter=2, leading=FS*1.5, leftIndent=10)
    st_badge     = _ps("NBG", fontName="Helvetica-Bold",    fontSize=FS*1.1,
                        textColor=BADGE_FG, alignment=TA_CENTER, leading=FS*1.5)

    # ── Field parser ───────────────────────────────────────────────────────────
    def _parse(text):
        # Use findall with lookahead so **bold** inside bullet content doesn't break field boundaries
        text = text or ""
        matches = re.findall(
            r'\*\*([^*\n]+?)\*\*\s*:?\s*(.*?)(?=\n\s*\*\*[^*\n]+?\*\*|\Z)',
            text, re.DOTALL
        )
        d = {k.strip().upper(): v.strip() for k, v in matches}
        return d or {"BODY": text.strip()}

    def _get(d, key):
        ku = key.upper()
        for k, v in d.items():
            if ku in k:
                return v
        return None

    # ── Line renderer ──────────────────────────────────────────────────────────
    def _lines(text, sty=None):
        sty = sty or st_body
        out = []
        for line in (text or "").strip().splitlines():
            line = line.strip()
            if not line:
                continue
            safe = html.escape(line)
            safe = re.sub(r"\*\*(.*?)\*\*", r"<b>\1</b>", safe)
            m = re.match(r'^[•\-\*]\s*(.*)', safe, re.DOTALL)
            if m:
                content = m.group(1).strip()
                if content:
                    out.append(Paragraph(
                        f'<font color="{AHX}">&#8226;</font> {content}', st_bullet))
            else:
                out.append(Paragraph(safe, sty))
        return out

    # ── Component builders ─────────────────────────────────────────────────────
    def _so_what(text, cw):
        rows = [[Paragraph("SO WHAT", st_gold_lbl)]] + [[p] for p in _lines(text)]
        t = Table(rows, colWidths=[cw])
        t.setStyle(TableStyle([
            ("BACKGROUND",    (0,0), (-1,-1), SW_BG),
            ("LINEBEFORE",    (0,0), (-1,-1), 3,   GOLD),
            ("TOPPADDING",    (0,0), (-1,-1), 8),
            ("BOTTOMPADDING", (0,0), (-1,-1), 8),
            ("LEFTPADDING",   (0,0), (-1,-1), 12),
            ("RIGHTPADDING",  (0,0), (-1,-1), 10),
        ]))
        return t

    def _da_box(text, cw):
        rows = [[Paragraph("DEVIL'S ADVOCATE", st_label)]] + [[p] for p in _lines(text)]
        t = Table(rows, colWidths=[cw])
        t.setStyle(TableStyle([
            ("LINEBEFORE",    (0,0), (-1,-1), 2.5, DA_LINE),
            ("TOPPADDING",    (0,0), (-1,-1), 4),
            ("BOTTOMPADDING", (0,0), (-1,-1), 4),
            ("LEFTPADDING",   (0,0), (-1,-1), 12),
            ("RIGHTPADDING",  (0,0), (-1,-1), 6),
        ]))
        return t

    def _art_header(num, art_title, cw):
        bw = 0.75*cm
        badge = Paragraph(f"<b>{num:02d}</b>", st_badge)
        titl  = Paragraph(html.escape(art_title), st_art_title)
        t = Table([[badge, titl]], colWidths=[bw, cw - bw - 0.15*cm])
        t.setStyle(TableStyle([
            ("BACKGROUND",    (0,0), (0,0), BADGE_BG),
            ("VALIGN",        (0,0), (-1,-1), "MIDDLE"),
            ("TOPPADDING",    (0,0), (-1,-1), 7),
            ("BOTTOMPADDING", (0,0), (-1,-1), 7),
            ("LEFTPADDING",   (0,0), (0, 0), 4),
            ("RIGHTPADDING",  (0,0), (0, 0), 4),
            ("LEFTPADDING",   (1,0), (1, 0), 10),
            ("RIGHTPADDING",  (1,0), (1, 0), 4),
        ]))
        return t

    # ── Page callbacks ─────────────────────────────────────────────────────────
    short_title = title if len(title) <= 48 else title[:45] + "..."

    def _cover_page(canvas, doc):
        canvas.saveState()
        if is_dark:
            canvas.setFillColor(PAGE_BG)
            canvas.rect(0, 0, W, H, fill=1, stroke=0)
        canvas.setFillColor(ACCENT)
        canvas.rect(0, H - 2.2*cm, W, 2.2*cm, fill=1, stroke=0)
        canvas.setFillColor(GOLD)
        canvas.rect(0, 0.9*cm, W, 1.5, fill=1, stroke=0)
        canvas.setFont("Helvetica-Oblique", 6.5)
        canvas.setFillColor(MUTED)
        canvas.drawCentredString(W / 2, 0.32*cm, "Brianis Book Club — AI News Digest")
        canvas.restoreState()

    def _main_page(canvas, doc):
        canvas.saveState()
        if is_dark:
            canvas.setFillColor(PAGE_BG)
            canvas.rect(0, 0, W, H, fill=1, stroke=0)
        canvas.setFillColor(ACCENT)
        canvas.rect(0, H - 2, W, 2, fill=1, stroke=0)
        canvas.setFont("Helvetica", 6.5)
        canvas.setFillColor(MUTED)
        canvas.drawString(LR, 0.35*cm, short_title)
        canvas.drawRightString(W - LR, 0.35*cm, str(doc.page))
        canvas.restoreState()

    # ── Document setup ─────────────────────────────────────────────────────────
    doc = BaseDocTemplate(out_path, pagesize=PAGE,
                          leftMargin=LR, rightMargin=LR,
                          topMargin=TB, bottomMargin=TB + 0.9*cm)
    cw = doc.width
    cover_frame = Frame(LR, 1.2*cm, W - 2*LR, H - 3.8*cm, id="cover")
    main_frame  = Frame(doc.leftMargin, doc.bottomMargin,
                        doc.width, doc.height, id="main")
    doc.addPageTemplates([
        PageTemplate(id="Cover", frames=[cover_frame], onPage=_cover_page),
        PageTemplate(id="Main",  frames=[main_frame],  onPage=_main_page),
    ])

    # ── Count articles and parse date ──────────────────────────────────────────
    n_articles = sum(1 for s in sections if s.get("level") == 2)
    date_part  = title.split("—")[-1].strip() if "—" in title else title

    # ── Cover page story ───────────────────────────────────────────────────────
    story = []
    story.append(Spacer(1, 1.6*cm))
    story.append(Paragraph("NEWS", st_cov_main))
    story.append(Paragraph("DIGEST", st_cov_main))
    story.append(Spacer(1, 0.9*cm))
    story.append(HRFlowable(color=GOLD, thickness=1.5, width="30%", hAlign="CENTER"))
    story.append(Spacer(1, 0.9*cm))
    story.append(Paragraph(date_part, st_cov_date))
    story.append(Spacer(1, 0.3*cm))
    story.append(Paragraph(
        f"{n_articles} article{'s' if n_articles != 1 else ''}", st_cov_sub))
    story.append(Spacer(1, 0.5*cm))
    import datetime as _dt
    _stamp = _dt.datetime.now().strftime("%Y-%m-%d %H:%M")
    story.append(Paragraph(
        f"{BUILD_TAG} \u00b7 ANALYSIS BUILD \u00b7 generated {_stamp}", st_cov_sub))
    story.append(NextPageTemplate("Main"))
    story.append(PageBreak())

    # ── Body ───────────────────────────────────────────────────────────────────
    article_num = 0

    for sec in sections:
        level   = sec.get("level", 1)
        heading = sec.get("heading", "")
        body    = sec.get("body",    "")

        # ── Synthesis ──────────────────────────────────────────────────────────
        if level == 1 and heading == "Synthesis":
            story.append(Paragraph("SYNTHESIS", st_section))
            story.append(HRFlowable(color=ACCENT, thickness=1.5, width="100%", spaceAfter=10))
            f = _parse(body)
            big    = _get(f, "THE BIG PICTURE")
            themes = _get(f, "KEY THEMES")
            watch  = _get(f, "WHAT TO WATCH")
            if big:
                story.append(Paragraph("THE BIG PICTURE", st_label))
                story.extend(_lines(big)); story.append(Spacer(1, 8))
            if themes:
                story.append(Paragraph("KEY THEMES & WHY THEY MATTER", st_label))
                story.extend(_lines(themes)); story.append(Spacer(1, 8))
            if watch:
                story.append(Paragraph("WHAT TO WATCH", st_label))
                story.extend(_lines(watch))
            if not (big or themes or watch):
                story.extend(_lines(body))
            story.append(Spacer(1, 16))
            story.append(HRFlowable(color=RULE, thickness=0.5, width="100%"))
            story.append(Spacer(1, 16))

        # ── Articles header ────────────────────────────────────────────────────
        elif level == 1 and heading == "Individual Article Summaries":
            story.append(Paragraph("ARTICLE SUMMARIES", st_section))
            story.append(HRFlowable(color=ACCENT, thickness=1.5, width="100%", spaceAfter=14))

        # ── YouTube section header ─────────────────────────────────────────────
        elif level == 1 and heading == "YouTube Video Summaries":
            story.append(PageBreak())
            story.append(Spacer(1, 0.5*cm))
            story.append(Paragraph("YOUTUBE VIDEO SUMMARIES", st_section))
            story.append(HRFlowable(color=YT_RULE, thickness=1.5, width="100%", spaceAfter=14))

        # ── Skipped videos note ────────────────────────────────────────────────
        elif level == 1 and heading == "Skipped Videos":
            story.append(Spacer(1, 0.5*cm))
            story.append(Paragraph("SKIPPED VIDEOS", st_section))
            story.append(HRFlowable(color=RULE, thickness=0.5, width="100%", spaceAfter=8))
            story.extend(_lines(body))
            story.append(Spacer(1, 12))

        # ── Wife section ───────────────────────────────────────────────────────
        elif level == 1 and "learnt today" in heading.lower():
            story.append(PageBreak())
            story.append(Spacer(1, 0.5*cm))
            story.append(Paragraph("WHAT I LEARNT TODAY", st_section))
            story.append(Paragraph("4 My Wife", st_cov_date))
            story.append(HRFlowable(color=GOLD, thickness=1.5, width="100%", spaceAfter=18))

            # Custom renderer: split body into per-article blocks (blank line delimited)
            st_wife_intro  = _ps("WFI", fontName="Helvetica-Oblique", fontSize=FS*1.04,
                                  textColor=TEXT, spaceAfter=5, leading=FS*1.65,
                                  alignment=TA_JUSTIFY)
            st_wife_bullet = _ps("WFB", fontName="Helvetica", fontSize=FS,
                                  textColor=TEXT, spaceAfter=4, leading=FS*1.55, leftIndent=16)

            raw_blocks = re.split(r'\n\s*\n', (body or "").strip())
            for bi, block in enumerate(raw_blocks):
                if not block.strip():
                    continue
                elems = []
                for line in [l.strip() for l in block.splitlines() if l.strip()]:
                    safe = html.escape(line)
                    safe = re.sub(r"\*\*(.*?)\*\*", r"<b>\1</b>", safe)
                    if re.match(r'^[•\-\*]', safe):
                        content = re.sub(r'^[•\-\*]\s*', '', safe)
                        elems.append(Paragraph(
                            f'<font color="{AHX}">&#8226;</font>&nbsp;&nbsp;{content}',
                            st_wife_bullet))
                    else:
                        elems.append(Paragraph(safe, st_wife_intro))
                if elems:
                    story.append(KeepTogether(elems))
                if bi < len(raw_blocks) - 1:
                    story.append(HRFlowable(color=RULE, thickness=0.4, width="92%",
                                            spaceBefore=10, spaceAfter=10,
                                            hAlign="CENTER"))
            story.append(Spacer(1, 16))

        # ── Individual article ─────────────────────────────────────────────────
        elif level == 2:
            article_num += 1
            f  = _parse(body)
            hl = _get(f, "HEADLINE")
            wh = _get(f, "WHAT HAPPENED — ANALYSIS") or _get(f, "WHAT HAPPENED")
            wm = _get(f, "WHY IT MATTERS")
            da = _get(f, "DEVIL")
            kn = _get(f, "KEY NUMBERS")
            sw = _get(f, "SO WHAT")

            # Header (badge + title) kept with headline
            hdr  = _art_header(article_num, heading, cw)
            intro = [hdr]
            if hl:
                intro += [Spacer(1, 5)] + _lines(hl, st_headline)
                intro.append(HRFlowable(color=RULE, thickness=0.3,
                                        width="100%", spaceAfter=2))
            story.append(KeepTogether(intro))

            if wh:
                story.append(Paragraph("WHAT HAPPENED — ANALYSIS", st_label))
                story.extend(_lines(wh))
            if wm:
                story.append(Paragraph("WHY IT MATTERS", st_label))
                story.extend(_lines(wm))
            if da:
                story.append(Spacer(1, 5))
                story.append(_da_box(da, cw))
                story.append(Spacer(1, 4))
            if kn:
                story.append(Paragraph("KEY NUMBERS", st_label))
                story.extend(_lines(kn))
            if sw:
                story.append(Spacer(1, 7))
                story.append(_so_what(sw, cw))

            story.append(Spacer(1, 18))
            story.append(HRFlowable(color=RULE, thickness=0.5, width="100%"))
            story.append(Spacer(1, 12))

    doc.build(story)


def _news_text_fingerprint(text):
    """Normalised first 800 chars for duplicate detection."""
    return re.sub(r"[^a-z0-9]", "", text.lower())[:800]


def _parse_news_field(summary_text, field_label):
    """Extract the value of a **FIELD:** line from Claude's structured output."""
    pattern = rf"\*\*{re.escape(field_label)}[:\*]*\*?\*?\s*(.*?)(?=\n\*\*|\Z)"
    m = re.search(pattern, summary_text, re.DOTALL | re.IGNORECASE)
    if m:
        return m.group(1).strip().splitlines()[0].strip()
    return ""


def _trim_to_words(text, max_words):
    """Trim text to at most max_words, backing off to the last sentence end."""
    max_words = max(0, int(max_words or 0))
    if max_words <= 0:
        return ""
    words = re.findall(r"\S+", str(text or ""))
    if len(words) <= max_words:
        return str(text or "").strip()
    truncated = " ".join(words[:max_words])
    # Prefer to end on a complete sentence within the cap.
    cut = max(truncated.rfind(". "), truncated.rfind("! "), truncated.rfind("? "))
    if cut > len(truncated) * 0.5:
        return truncated[:cut + 1].strip()
    # No good sentence boundary: hard cut but finish cleanly.
    return truncated.rstrip(" ,;:—-.") + "."


def _news_wh_budget(article_word_count):
    """Return (floor, target, cap) for WHAT HAPPENED - ANALYSIS.

    Cap policy: no more than min(350 words, 50% of the cleaned article body).
    Floor/target are soft generation targets so the section uses the available
    room instead of collapsing into a 60-word blurb.
    """
    source_words = max(0, int(article_word_count or 0))
    if source_words <= 0:
        cap = max(1, NEWS_WH_ABSOLUTE_MAX)
    else:
        source_cap = max(1, int(math.floor(source_words * NEWS_WH_SOURCE_MAX_RATIO)))
        cap = max(1, min(int(NEWS_WH_ABSOLUTE_MAX), source_cap))
    target = max(1, min(cap, int(math.ceil(cap * NEWS_WH_TARGET_RATIO))))
    if cap < 80:
        floor = max(1, int(math.floor(cap * 0.65)))
    else:
        floor = max(50, int(math.floor(cap * NEWS_WH_MIN_RATIO)))
        floor = min(floor, cap)
    return floor, target, cap


def _news_wh_pattern():
    return re.compile(
        r"(\*\*\s*WHAT\s+HAPPENED(?:\s*[—–-]\s*ANALYSIS)?\s*:?\s*\*\*\s*:?\s*)(.*?)(?=\n\s*\*\*[^*\n]+?\*\*|\Z)",
        re.DOTALL | re.IGNORECASE,
    )


def _news_wh_content(summary_body):
    m = _news_wh_pattern().search(str(summary_body or ""))
    return m.group(2).strip() if m else ""


def _news_wh_word_count(summary_body):
    return _count_words(_news_wh_content(summary_body))


def _replace_wh_content(summary_body, replacement):
    text = str(summary_body or "")
    m = _news_wh_pattern().search(text)
    replacement = str(replacement or "").strip()
    if not m:
        return (text.rstrip() + f"\n\n**WHAT HAPPENED — ANALYSIS:** {replacement}\n").strip()
    label = m.group(1)
    return text[:m.start()] + label + replacement + text[m.end():]


def _enforce_wh_cap(summary_body, wh_max):
    """Hard-cap the WHAT HAPPENED — ANALYSIS section to wh_max words.

    The prompt asks the model to stay within the ceiling, but models cannot
    count words reliably, so this enforces it deterministically after the fact.
    """
    wh_max = max(0, int(wh_max or 0))
    if not summary_body or wh_max <= 0:
        return summary_body
    m = _news_wh_pattern().search(str(summary_body or ""))
    if not m:
        return summary_body
    content = m.group(2).strip()
    if _count_words(content) <= wh_max:
        return summary_body
    trimmed = _trim_to_words(content, wh_max)
    return _replace_wh_content(summary_body, trimmed)


def _ensure_wh_length(summary_body, wh_min, wh_max, client=None, source_text="", fname="", job_id=None):
    """Keep WHAT HAPPENED within cap and optionally retry if it is too short."""
    body = _enforce_wh_cap(summary_body, wh_max)
    current = _news_wh_word_count(body)
    wh_min = max(0, int(wh_min or 0))
    wh_max = max(1, int(wh_max or 1))
    if current >= wh_min or not NEWS_WH_RETRY_EXPAND or client is None or not str(source_text or "").strip():
        return body

    prompt = (
        "Rewrite ONLY the WHAT HAPPENED — ANALYSIS section for this article.\n"
        f"Filename hint: {fname}\n"
        f"Current section is too short at about {current} words. Write between {wh_min} and {wh_max} words. "
        f"Do not exceed {wh_max} words. Use flowing analytical paragraphs, not bullets. "
        "Cover what happened, why it happened, the causal logic, relevant context, and what the developments mean. "
        "Every sentence must be complete. Return only the section body text - no heading and no other fields.\n\n"
        f"Existing structured summary:\n{body[:7000]}\n\n"
        f"Cleaned article text:\n{str(source_text)[:16000]}"
    )
    try:
        resp = client.messages.create(
            model=MODEL_CHUNK,
            max_tokens=min(MAX_OUT_TOKENS_PER_CALL, max(900, int(wh_max * 5.2) + 800)),
            messages=[{"role": "user", "content": prompt}],
        )
        candidate = _anthropic_text(resp).strip()
        candidate = _normalize_news_field_labels(candidate)
        # Tolerate a model that returns the label despite being asked not to.
        labelled = _news_wh_content(candidate)
        if labelled:
            candidate = labelled
        candidate = _trim_to_words(candidate, wh_max)
        if _count_words(candidate) > current:
            body = _replace_wh_content(body, candidate)
            body = _enforce_wh_cap(body, wh_max)
            _audit_event(job_id, "news_wh_expanded", article=fname, before_words=current, after_words=_news_wh_word_count(body), min_words=wh_min, max_words=wh_max)
    except Exception as e:
        _audit_event(job_id, "news_wh_expand_failed", article=fname, error=f"{type(e).__name__}: {e}")
    return body


# Canonical labels keyed by a regex that matches the variants a model might emit.
_NEWS_LABEL_CANON = [
    (r"WHAT\s+HAPPENED(?:\s*[—–-]\s*ANALYSIS)?", "WHAT HAPPENED — ANALYSIS"),
    (r"DEVIL'?S\s+ADVOCATE",                      "DEVIL'S ADVOCATE"),
    (r"WHY\s+IT\s+MATTERS",                       "WHY IT MATTERS"),
    (r"KEY\s+NUMBERS",                            "KEY NUMBERS"),
    (r"SO\s+WHAT",                                "SO WHAT"),
    (r"HEADLINE",                                 "HEADLINE"),
    (r"ARTICLE\s+TITLE",                          "ARTICLE TITLE"),
]


def _normalize_news_field_labels(text):
    """Canonicalize **BOLD LABEL:** tokens so the renderer reliably finds every
    section regardless of dash style or minor model variation. For example
    '**WHAT HAPPENED:**' or '**WHAT HAPPENED - ANALYSIS**:' both become
    '**WHAT HAPPENED — ANALYSIS:**'. Bold spans in body text (e.g. '**MAGA tax**')
    are left untouched because they match none of the label patterns.
    """
    t = str(text or "").replace("\r", "")

    def _repl(m):
        inner = m.group(1).strip().strip(":").strip()
        for pat, canon in _NEWS_LABEL_CANON:
            if re.fullmatch(pat, inner, flags=re.IGNORECASE):
                return f"**{canon}:**"
        return m.group(0)

    return re.sub(r"\*\*\s*([^*\n]+?)\s*\*\*", _repl, t)


def _postprocess_article_summary(summary, fname, wh_max):
    """Shared post-processing for one article summary, used by both the live job
    and the backtest suite: canonicalize labels, lift out the article title, then
    hard-cap the WHAT HAPPENED — ANALYSIS section. Returns (title, body)."""
    summary = _normalize_news_field_labels(summary)
    title = _parse_news_field(summary, "ARTICLE TITLE")
    if not title or len(title) < 4:
        title = re.sub(r"\.pdf$", "", fname, flags=re.IGNORECASE)
    body = re.sub(
        r"\*\*\s*ARTICLE TITLE\s*:?\s*\*\*\s*.*?(?=\n\*\*|\Z)", "",
        summary, count=1, flags=re.DOTALL,
    ).strip()
    body = _enforce_wh_cap(body, wh_max)
    return title, body


_YOUTUBE_MIN_WORDS    = 350
_YOUTUBE_MIN_COVERAGE = 0.50   # 50 % of video duration must have captions
_YOUTUBE_MAX_WORDS    = 8_000  # upper cap to stay inside token budget

def _extract_youtube_transcript(url):
    """Return (title, text) from a YouTube URL, or raise RuntimeError with a user-friendly message."""
    try:
        from youtube_transcript_api import YouTubeTranscriptApi
    except ImportError:
        raise RuntimeError("youtube-transcript-api is not installed. Run: pip install youtube-transcript-api")

    # ── Extract video ID (handles watch, youtu.be, /live/, /shorts/, /embed/) ──
    import urllib.parse as _up
    parsed    = _up.urlparse(url)
    hostname  = (parsed.hostname or "").lower()
    path_parts = [p for p in parsed.path.split("/") if p]

    if hostname in ("youtu.be",):
        vid = path_parts[0] if path_parts else None
    elif path_parts and path_parts[0] in ("live", "shorts", "embed", "v", "e"):
        vid = path_parts[1] if len(path_parts) > 1 else None
    else:
        vid = _up.parse_qs(parsed.query).get("v", [None])[0]

    if not vid:
        raise RuntimeError(f"Could not parse video ID from URL: {url}")

    # ── Fetch transcript (v1.x instance API) ──────────────────────────────────
    api = YouTubeTranscriptApi()
    fetched      = None
    chosen_lang  = "en"

    # Pass 1: try English variants directly (fast path)
    try:
        fetched = api.fetch(vid, languages=["en", "en-GB", "en-US"])
    except Exception:
        # Pass 2: enumerate available transcripts and pick the best one
        try:
            available = list(api.list(vid))
        except Exception as e_list:
            raise RuntimeError(f"Transcript fetch failed: {e_list}")
        if not available:
            raise RuntimeError("No transcripts available for this video.")
        # Prefer manually created over auto-generated; otherwise just take the first
        manual  = [t for t in available if not t.is_generated]
        chosen  = (manual or available)[0]
        chosen_lang = chosen.language_code
        try:
            fetched = chosen.fetch()
        except Exception as e_fetch:
            raise RuntimeError(f"Transcript fetch failed ({chosen_lang}): {e_fetch}")

    # Normalise entries — v1.x returns objects with .text/.start/.duration attrs
    def _get(entry, key, default=0):
        if isinstance(entry, dict):
            return entry.get(key, default)
        return getattr(entry, key, default)

    entries = list(fetched)
    if not entries:
        raise RuntimeError("Transcript returned empty.")

    # Quality gate: coverage
    last            = entries[-1]
    total_duration  = _get(last, "start") + _get(last, "duration")
    captured        = sum(_get(e, "duration") for e in entries)
    coverage        = (captured / total_duration) if total_duration > 0 else 0

    raw_words  = " ".join(_get(e, "text") for e in entries)
    word_count = len(raw_words.split())

    if word_count < _YOUTUBE_MIN_WORDS and coverage < _YOUTUBE_MIN_COVERAGE:
        raise RuntimeError(
            f"Transcript too sparse ({word_count} words, {coverage*100:.0f}% coverage) — "
            f"need ≥{_YOUTUBE_MIN_WORDS} words OR ≥{int(_YOUTUBE_MIN_COVERAGE*100)}% coverage."
        )

    # Cap at max words
    words = raw_words.split()
    if len(words) > _YOUTUBE_MAX_WORDS:
        raw_words = " ".join(words[:_YOUTUBE_MAX_WORDS])

    lang_tag = "" if chosen_lang.startswith("en") else f" [{chosen_lang}]"
    title    = f"YouTube video ({vid}){lang_tag}"
    return title, raw_words


def _generate_wife_summary_section(client, individual_summaries, job_id=None):
    if not individual_summaries:
        return ""
    articles_text = "\n\n".join(
        f"Article {i+1}: {s['title']}\n{s['summary'][:1800]}"
        for i, s in enumerate(individual_summaries)
    )
    n = len(individual_summaries)
    prompt = (
        "You are telling your spouse about today's news over dinner. "
        "They are smart but not a specialist in finance or politics. "
        f"There are exactly {n} articles below. Cover ALL {n} of them.\n\n"
        "OUTPUT FORMAT — follow this exactly, no exceptions:\n"
        "For each article output THREE lines then a blank line:\n"
        "Line 1: One plain-English sentence introducing the topic (no bullet, no label, no number).\n"
        "Line 2: • First bullet — one sentence, simple and engaging.\n"
        "Line 3: • Second bullet — one sentence, simple and engaging.\n"
        "(blank line between articles)\n\n"
        "RULES:\n"
        "- Do NOT add any title, header, greeting, intro, or outro — start immediately with article 1.\n"
        "- Do NOT number the articles or add labels.\n"
        "- Do NOT merge bullets into the opening sentence.\n"
        "- Plain English only. Warm, conversational tone.\n\n"
        f"Article summaries:\n{articles_text[:16000]}"
    )
    try:
        resp = client.messages.create(
            model=MODEL_CHUNK, max_tokens=min(2000, n * 120 + 200),
            messages=[{"role": "user", "content": prompt}],
        )
        text = _anthropic_text(resp).strip()
        # Strip any markdown headers the model sneaks in (# Tonight's News etc.)
        lines = [l for l in text.splitlines() if not l.lstrip().startswith("#")]
        text = "\n".join(lines).strip()
        _audit_event(job_id, "wife_section_generated", words=_count_words(text))
        return text
    except Exception as e:
        _audit_event(job_id, "wife_section_failed", error=f"{type(e).__name__}: {e}")
        parts = []
        for s in individual_summaries:
            headline = _parse_news_field(s.get("summary", ""), "HEADLINE")
            if headline:
                parts.append(
                    f"{s.get('title', 'Article')}.\n"
                    f"• {headline}\n"
                    f"• This story is worth following in the coming days."
                )
        return "\n\n".join(parts) if parts else ""


def _run_news_job(job_id, pdf_list_bytes, filenames, api_key, youtube_urls=None):
    """Background job: deduplicate, summarize each article, then synthesize a digest."""
    import datetime
    from difflib import SequenceMatcher
    job    = jobs[job_id]
    client = _make_ai_client(api_key, timeout_seconds=120.0)
    youtube_urls = youtube_urls or []

    # ── Step 1: extract text + deduplicate ────────────────────────────────────
    job.update({"progress": 3, "message": "Checking for duplicate articles...", "last_update": time.time()})
    articles = []   # [{pdf_bytes, fname, text}]
    seen_fps = []
    seen_titles_norm = []

    for pdf_bytes, fname in zip(pdf_list_bytes, filenames):
        text = _extract_article_text(pdf_bytes)
        fp   = _news_text_fingerprint(text)
        fname_norm = re.sub(r"[^a-z0-9]", "", fname.lower())

        is_dup = False
        # Content fingerprint similarity
        for seen_fp in seen_fps:
            if seen_fp and fp and SequenceMatcher(None, fp, seen_fp).ratio() > 0.82:
                is_dup = True
                break
        # Filename similarity fallback (catches same file uploaded under different name)
        if not is_dup:
            for seen_fn in seen_titles_norm:
                if seen_fn and fname_norm and SequenceMatcher(None, fname_norm, seen_fn).ratio() > 0.90:
                    is_dup = True
                    break

        if is_dup:
            _audit_event(job_id, "news_duplicate_skipped", filename=fname)
            continue

        seen_fps.append(fp)
        seen_titles_norm.append(fname_norm)
        articles.append({"pdf_bytes": pdf_bytes, "fname": fname, "text": text})

    n = len(articles)
    if n == 0:
        fail(job_id, "All uploaded files appear to be duplicates — nothing to summarize.")
        return

    # ── Step 2: summarize each article ───────────────────────────────────────
    individual_summaries = []
    for i, art in enumerate(articles):
        fname = art["fname"]
        text  = art["text"]
        pct   = 5 + int(55 * i / n)
        job.update({"progress": pct,
                    "message": f"Summarizing article {i+1}/{n}...",
                    "last_update": time.time()})
        _audit_event(job_id, "news_article_start", article=fname, index=i + 1, total=n)

        if not text.strip():
            individual_summaries.append({"title": re.sub(r"\.pdf$", "", fname, flags=re.IGNORECASE),
                                          "summary": "(Could not extract text from this PDF.)"})
            continue

        article_word_count = _count_words(text)
        wh_min, wh_target, wh_max = _news_wh_budget(article_word_count)
        _audit_event(
            job_id, "news_article_budget", article=fname,
            source_words=article_word_count, wh_min=wh_min,
            wh_target=wh_target, wh_max=wh_max,
        )

        prompt = (
            "You are summarizing a Financial Times or Economist article for a senior professional.\n\n"
            f"Filename hint: {fname}\n"
            f"Cleaned article word count: {article_word_count}.\n"
            f"WHAT HAPPENED policy: write between {wh_min} and {wh_max} words, targeting about {wh_target}; "
            f"the hard cap is the smaller of {NEWS_WH_ABSOLUTE_MAX} words and {int(NEWS_WH_SOURCE_MAX_RATIO * 100)}% of the cleaned article.\n\n"
            f"Full cleaned article text:\n{text[:NEWS_ARTICLE_MAX_CHARS]}\n\n"
            "Write a structured summary with EXACTLY these seven labelled sections in this order:\n\n"
            "**ARTICLE TITLE:** The actual title of this article as it appears in the text "
            "(not the filename). Keep it concise — max 12 words.\n\n"
            "**HEADLINE:** One sentence capturing the core news.\n\n"
            f"**WHAT HAPPENED — ANALYSIS:** A thorough analytical account of what happened, why, "
            f"and what the key developments mean. Write {wh_min}-{wh_max} words, target about {wh_target}. "
            f"NO MORE THAN {wh_max} words — this is a hard maximum. "
            "Use the available space; do not collapse this to a short blurb. "
            "Cover the major facts, arguments, causal logic, and context, but prioritise the most important "
            "points if space is tight. "
            "Every sentence must be complete. Do not truncate mid-thought. "
            "Write in flowing paragraphs — not bullets. Be analytical, not just descriptive.\n\n"
            "**WHY IT MATTERS:** 2-3 sentences on broader significance and implications.\n\n"
            "**DEVIL'S ADVOCATE:** 1-2 sentences — what is this article missing, overstating, "
            "or what is the strongest counterargument to its thesis?\n\n"
            "**KEY NUMBERS:** A bullet list of 3-5 important statistics or data points (• prefix).\n\n"
            "**SO WHAT:** One sentence — the single most actionable implication for a decision-maker.\n\n"
            "Be direct and precise. No filler. No hedging. "
            "The WHAT HAPPENED — ANALYSIS section is the centrepiece, but keep it within its word ceiling."
        )
        try:
            resp = client.messages.create(
                model=MODEL_CHUNK,
                max_tokens=min(MAX_OUT_TOKENS_PER_CALL, max(2600, int(wh_max * 5.5) + 1100)),
                messages=[{"role": "user", "content": prompt}],
            )
            summary = _anthropic_text(resp).strip()
            extracted_title, summary_body = _postprocess_article_summary(summary, fname, wh_max)
            summary_body = _ensure_wh_length(
                summary_body, wh_min, wh_max, client=client, source_text=text,
                fname=fname, job_id=job_id,
            )
            _audit_event(
                job_id, "news_article_done", article=fname, title=extracted_title,
                what_happened_words=_news_wh_word_count(summary_body), wh_min=wh_min, wh_max=wh_max,
            )
        except Exception as e:
            extracted_title = re.sub(r"\.pdf$", "", fname, flags=re.IGNORECASE)
            summary_body = f"(Summarization error: {e})"

        individual_summaries.append({"title": extracted_title, "summary": summary_body})
        if job.get("chapters") is None:
            job["chapters"] = []
        job["chapters"].append({"index": i, "title": extracted_title})

    # ── Step 2b: YouTube videos ───────────────────────────────────────────────
    youtube_summaries = []
    youtube_skipped   = []
    if youtube_urls:
        ny = len(youtube_urls)
        for yi, url in enumerate(youtube_urls):
            pct_y = 60 + int(8 * yi / ny)
            job.update({"progress": pct_y,
                        "message": f"Fetching YouTube transcript {yi+1}/{ny}...",
                        "last_update": time.time()})
            _audit_event(job_id, "youtube_start", url=url, index=yi + 1, total=ny)
            try:
                yt_title, yt_text = _extract_youtube_transcript(url)
            except RuntimeError as e:
                youtube_skipped.append({"url": url, "reason": str(e)})
                _audit_event(job_id, "youtube_skipped", url=url, reason=str(e))
                continue

            # Summarize the transcript using the same pipeline as PDFs
            yt_word_count = _count_words(yt_text)
            wh_min, wh_target, wh_max = _news_wh_budget(yt_word_count)
            prompt = (
                "You are summarizing a YouTube video transcript for a senior professional.\n\n"
                f"Video URL: {url}\n"
                f"Transcript word count: {yt_word_count}.\n"
                f"WHAT HAPPENED policy: write between {wh_min} and {wh_max} words, targeting about {wh_target}.\n\n"
                f"Full transcript:\n{yt_text[:NEWS_ARTICLE_MAX_CHARS]}\n\n"
                "Write a structured summary with EXACTLY these seven labelled sections in this order:\n\n"
                "**ARTICLE TITLE:** A short descriptive title for this video (max 12 words).\n\n"
                "**HEADLINE:** One sentence capturing the core message.\n\n"
                f"**WHAT HAPPENED — ANALYSIS:** A thorough analytical account of what was said, why it matters, "
                f"and what the key developments mean. Write {wh_min}-{wh_max} words, target about {wh_target}. "
                "Write in flowing paragraphs — not bullets. Be analytical, not just descriptive.\n\n"
                "**WHY IT MATTERS:** 2-3 sentences on broader significance and implications.\n\n"
                "**DEVIL'S ADVOCATE:** 1-2 sentences — what is this video missing, overstating, "
                "or what is the strongest counterargument?\n\n"
                "**KEY NUMBERS:** A bullet list of 3-5 important statistics or data points (• prefix). "
                "If none exist, write '• No specific data points cited.'\n\n"
                "**SO WHAT:** One sentence — the single most actionable implication for a decision-maker.\n\n"
                "Be direct and precise. No filler."
            )
            try:
                resp = client.messages.create(
                    model=MODEL_CHUNK,
                    max_tokens=min(MAX_OUT_TOKENS_PER_CALL, max(2600, int(wh_max * 5.5) + 1100)),
                    messages=[{"role": "user", "content": prompt}],
                )
                yt_summary = _anthropic_text(resp).strip()
                extracted_title, summary_body = _postprocess_article_summary(yt_summary, yt_title, wh_max)
                summary_body = _ensure_wh_length(
                    summary_body, wh_min, wh_max, client=client, source_text=yt_text,
                    fname=url, job_id=job_id,
                )
                _audit_event(job_id, "youtube_done", url=url, title=extracted_title)
            except Exception as e:
                extracted_title = yt_title
                summary_body = f"(Summarization error: {e})"
                _audit_event(job_id, "youtube_error", url=url, error=str(e))

            youtube_summaries.append({"title": extracted_title, "url": url, "summary": summary_body})
            if job.get("chapters") is None:
                job["chapters"] = []
            job["chapters"].append({"index": n + yi, "title": f"[Video] {extracted_title}"})

    # ── Step 3: synthesis ────────────────────────────────────────────────────
    job.update({"progress": 65, "message": "Synthesizing cross-article digest...", "last_update": time.time()})
    all_summaries_for_synthesis = individual_summaries + youtube_summaries
    combined_text = "\n\n---\n\n".join(
        f"Article: {s['title']}\n{s['summary']}" for s in all_summaries_for_synthesis
    )
    total_sources = len(all_summaries_for_synthesis)
    synthesis_prompt = (
        f"You have read summaries of {total_sources} financial/news source(s) "
        f"(articles and/or video transcripts).\n\n"
        f"Individual summaries:\n\n{combined_text[:50000]}\n\n"
        "Write a synthesized NEWS DIGEST with EXACTLY these three labelled sections:\n\n"
        "**THE BIG PICTURE:** 5-6 sentences. What is the overarching narrative today? "
        "What forces, tensions, or developments connect these articles? Write with the authority of a seasoned editor.\n\n"
        "**KEY THEMES & WHY THEY MATTER:** A bullet list of 4-6 themes. "
        "For each theme write: '• [Theme name] — [one sentence on why this theme matters right now]'. "
        "Do not just name the theme — explain its significance.\n\n"
        "**WHAT TO WATCH:** A bullet list of 3-5 specific, forward-looking things to monitor "
        "in the coming days or weeks (• prefix). Be concrete — name actors, data releases, or events.\n\n"
        "Write with authority and concision. No filler. This is a briefing for a senior decision-maker."
    )
    try:
        resp = client.messages.create(
            model=MODEL_CHUNK, max_tokens=1800,
            messages=[{"role": "user", "content": synthesis_prompt}],
        )
        synthesis = _anthropic_text(resp).strip()
        synthesis = _normalize_news_field_labels(synthesis)
    except Exception as e:
        synthesis = f"(Synthesis error: {e})"

    # ── Step 4: build PDF ────────────────────────────────────────────────────
    job.update({"progress": 85, "message": "Building digest PDF...", "last_update": time.time()})

    today        = datetime.date.today()
    date_label   = f"{today.strftime('%B')} {today.day}, {today.year}"
    digest_title = f"News Digest — {date_label}"

    sections = [{"level": 1, "heading": "Synthesis", "body": synthesis}]

    if individual_summaries:
        sections.append({"level": 1, "heading": "Individual Article Summaries", "body": ""})
        for s in individual_summaries:
            sections.append({"level": 2, "heading": s["title"], "body": s["summary"]})

    if youtube_summaries:
        sections.append({"level": 1, "heading": "YouTube Video Summaries", "body": ""})
        for s in youtube_summaries:
            sections.append({"level": 2, "heading": s["title"], "body": s["summary"],
                             "source_url": s.get("url", "")})

    if youtube_skipped:
        skip_note = "\n".join(f"• {r['url']} — {r['reason']}" for r in youtube_skipped)
        sections.append({"level": 1, "heading": "Skipped Videos", "body": skip_note})

    wife_body = _generate_wife_summary_section(
        client, individual_summaries + youtube_summaries, job_id=job_id
    )
    if wife_body:
        sections.append({"level": 1, "heading": "What I Learnt Today: 4 My Wife", "body": wife_body})

    job["news_meta"] = {"sections": sections, "title": digest_title}

    out_path = os.path.join(TMP_DIR, f"{job_id}_summary.pdf")
    try:
        _build_news_pdf(out_path, digest_title, sections, mode="dark")
        job.update({
            "status": "done", "progress": 100,
            "message": (
                f"News digest ready — {n} article{'s' if n != 1 else ''}"
                + (f", {len(youtube_summaries)} video{'s' if len(youtube_summaries) != 1 else ''}" if youtube_summaries else "")
                + (f" ({len(youtube_skipped)} video{'s' if len(youtube_skipped) != 1 else ''} skipped)" if youtube_skipped else "")
                + "."
            ),
            "output_path": out_path,
            "title": digest_title,
            "last_update": time.time(),
        })
        meta_path = os.path.join(TMP_DIR, f"{job_id}_news_meta.json")
        with open(meta_path, "w", encoding="utf-8") as _mf:
            json.dump({"sections": sections, "title": digest_title}, _mf, ensure_ascii=False)
        _history_add({
            "id":         job_id,
            "type":       "news",
            "title":      digest_title,
            "created_at": time.time(),
            "meta_path":  meta_path,
        })
    except Exception as e:
        fail(job_id, f"Failed to build news digest PDF: {e}")


# ── Flask Routes ───────────────────────────────────────────────────────────────
@app.route("/start_news", methods=["POST"])
def start_news():
    pdf_files    = request.files.getlist("pdfs")
    youtube_raw  = request.form.get("youtube_urls", "").strip()
    youtube_urls = [u.strip() for u in youtube_raw.splitlines() if u.strip()
                    and ("youtube.com" in u or "youtu.be" in u)]

    if not pdf_files and not youtube_urls:
        return jsonify({"error": "Please upload at least one PDF or add a YouTube URL."}), 400
    if len(pdf_files) > 10:
        pdf_files = pdf_files[:10]
    if len(youtube_urls) > 10:
        youtube_urls = youtube_urls[:10]

    api_key = request.form.get("api_key", "").strip()
    api_key = "".join(c for c in api_key if ord(c) < 128)
    if not api_key.startswith("sk-ant-"):
        return jsonify({"error": "Invalid API key (must start with sk-ant-)"}), 400

    pdf_list_bytes = [f.read() for f in pdf_files]
    filenames      = [getattr(f, "filename", f"article_{i+1}.pdf") or f"article_{i+1}.pdf"
                      for i, f in enumerate(pdf_files)]

    now    = time.time()
    job_id = uuid.uuid4().hex
    jobs[job_id] = {
        "status": "running", "progress": 0, "message": "Starting...",
        "chapters": [], "output_path": None, "share_token": None,
        "last_update": now, "title": "News Digest", "created_at": now,
        "cancel_requested": False,
    }
    threading.Thread(
        target=_run_news_job,
        args=(job_id, pdf_list_bytes, filenames, api_key),
        kwargs={"youtube_urls": youtube_urls},
        daemon=True,
    ).start()
    return jsonify({"job_id": job_id})


def _serve_news_variant(job_id, mode):
    job = jobs.get(job_id)
    if not job or job.get("status") != "done":
        return jsonify({"error": "Not ready"}), 404
    meta = job.get("news_meta")
    if not meta:
        return jsonify({"error": "News metadata missing"}), 404
    label  = {"dark": "Dark", "light": "Light", "phone_dark": "Phone Dark", "print": "Consultancy Print"}[mode]
    suffix = {"dark": "dark", "light": "light", "phone_dark": "phone-dark", "print": "print"}[mode]
    title  = meta["title"]
    safe   = re.sub(r"[^\w\s\-—]", "", title).strip()[:60] or "News Digest"
    tmp    = os.path.join(TMP_DIR, f"{job_id}_news_{suffix}.pdf")
    try:
        _build_news_pdf(tmp, title, meta["sections"], mode=mode)
        with open(tmp, "rb") as f:
            pdf_bytes = f.read()
    except Exception as e:
        return jsonify({"error": f"Build failed: {e}"}), 500
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)
    return send_file(BytesIO(pdf_bytes), as_attachment=True,
                     download_name=f"{safe} — {label}.pdf",
                     mimetype="application/pdf")


@app.route("/download_news_dark/<job_id>")
def download_news_dark(job_id):
    return _serve_news_variant(job_id, "dark")


@app.route("/download_news_light/<job_id>")
def download_news_light(job_id):
    return _serve_news_variant(job_id, "light")


@app.route("/download_news_phone/<job_id>")
def download_news_phone(job_id):
    return _serve_news_variant(job_id, "phone_dark")


@app.route("/download_news_print/<job_id>")
def download_news_print(job_id):
    return _serve_news_variant(job_id, "print")


@app.route("/history")
def get_history():
    return jsonify(_history_load())


@app.route("/history/<entry_id>", methods=["DELETE"])
def delete_history(entry_id):
    _history_remove(entry_id)
    return jsonify({"ok": True})


@app.route("/download_history/<entry_id>/<variant>")
def download_history_entry(entry_id, variant):
    entries = _history_load()
    entry = next((e for e in entries if e["id"] == entry_id), None)
    if not entry:
        return jsonify({"error": "Not found"}), 404

    if entry["type"] == "book":
        pdf_path = entry.get("pdf_path", "")
        if not pdf_path or not os.path.exists(pdf_path):
            return jsonify({"error": "PDF file no longer exists"}), 404
        safe = re.sub(r"[^\w\s\-—]", "", entry["title"]).strip()[:60] or "Summary"
        return send_file(pdf_path, as_attachment=True,
                         download_name=f"{safe}.pdf", mimetype="application/pdf")

    if entry["type"] == "news":
        meta_path = entry.get("meta_path", "")
        if not meta_path or not os.path.exists(meta_path):
            return jsonify({"error": "News metadata no longer exists"}), 404
        with open(meta_path, "r", encoding="utf-8") as f:
            meta = json.load(f)
        mode_map = {"dark": "dark", "light": "light", "phone": "phone_dark", "print": "print"}
        mode = mode_map.get(variant, "dark")
        label_map = {"dark": "Dark", "light": "Light", "phone": "Phone Dark", "print": "Consultancy Print"}
        label = label_map.get(variant, "Dark")
        title = meta["title"]
        safe = re.sub(r"[^\w\s\-—]", "", title).strip()[:60] or "News Digest"
        tmp = os.path.join(TMP_DIR, f"{entry_id}_hist_{variant}.pdf")
        try:
            _build_news_pdf(tmp, title, meta["sections"], mode=mode)
            with open(tmp, "rb") as f:
                pdf_bytes = f.read()
        except Exception as e:
            return jsonify({"error": f"Build failed: {e}"}), 500
        finally:
            if os.path.exists(tmp):
                os.remove(tmp)
        return send_file(BytesIO(pdf_bytes), as_attachment=True,
                         download_name=f"{safe} — {label}.pdf",
                         mimetype="application/pdf")

    return jsonify({"error": "Unknown type"}), 400


@app.route("/health")
def health():
    return jsonify({
        "ok": True,
        "model": MODEL_CHUNK,
        "anthropic_sdk_available": anthropic is not None,
        "anthropic_http_fallback_available": True,
        "ocr_enabled": OCR_ENABLED,
        "ocr_stack_available": _ocr_stack_available(),
        "ocr_langs": OCR_LANGS,
        "ocr_dpi": OCR_DPI,
        "ocr_psm": OCR_PSM,
        "ocr_auto_psm": OCR_AUTO_PSM,
        "fixed_page_min_ratio": LENGTH_ENFORCE_MIN_RATIO,
        "fixed_page_max_ratio": LENGTH_ENFORCE_MAX_RATIO,
        "fixed_page_target_ratio": LENGTH_ENFORCE_TARGET_RATIO,
        "fixed_page_word_ratio": FIXED_PAGE_WORD_RATIO,
        "summary_prompt_max_ratio": SUMMARY_PROMPT_MAX_RATIO,
        "fixed_page_fail_on_overshoot": LENGTH_FAIL_ON_OVERSHOOT,
        "epub_supported": True,
        "feynman_storyline_enabled": OUTPUT_FEYNMAN_STORYLINE,
        "feynman_page_range": [FEYNMAN_MIN_PAGES, FEYNMAN_MAX_PAGES],
        "tailored_planner_enabled": True,
        "tailored_length_pcts": TAILORED_LENGTH_PCTS,
        "global_complete_sentence_gate": OUTPUT_QUALITY_GATE,
        "max_upload_mb": app.config.get("MAX_CONTENT_LENGTH", 0) // (1024 * 1024),
    })

@app.route("/")
def index():
    return HTML_PAGE

@app.route("/pagecount", methods=["POST"])
def pagecount():
    f = request.files.get("pdf")
    if not f:
        return jsonify({"error": "No file"}), 400
    data = f.read()
    try:
        source_format = _detect_source_format(getattr(f, "filename", ""), data)
        pdf_data = _fast_document_preflight(data, source_format=source_format)
        pages    = pdf_data["pages"]
    except Exception as e:
        return jsonify({"error": str(e)}), 400

    # Fast estimate only. Full extraction/OCR now happens only after Generate.
    chars    = pages * 2000
    n_chunks = max(1, -(-chars // CHARS_PER_CHUNK))   # ceiling division
    in_tok   = n_chunks * (CHARS_PER_CHUNK // 4)       # ~20,000 per chunk
    out_tok  = n_chunks * 1600                         # rough for 15% length
    cost     = (in_tok * HAIKU_IN + out_tok * HAIKU_OUT) / 1_000_000
    ai_mins  = max(1, n_chunks * 45 // 60)
    ocr_required = source_format == "pdf" and len(pdf_data.get("full_text", "").strip()) < OCR_MIN_TEXT_CHARS
    if ocr_required:
        ocr_mins = max(1, pages * OCR_SECONDS_PER_PAGE_EST // 60)
        time_msg = f"~{ocr_mins + ai_mins} min (OCR + AI estimate)"
    else:
        time_msg = f"~{ai_mins} min (estimate)"
    return jsonify({
        "pages": pages,
        "cost": f"~${cost:.2f}",
        "time": time_msg,
        "ocr_required": ocr_required,
        "source_format": source_format,
        "estimated_pages": bool(source_format == "epub"),
        "fast_preflight": True,
    })

@app.route("/feasibility", methods=["POST"])
def feasibility():
    f = request.files.get("pdf")
    if not f:
        return jsonify({"error": "No file"}), 400
    try:
        requested_pages = int(request.form.get("pages", "0") or 0)
    except Exception:
        requested_pages = 0
    try:
        data = f.read()
        source_format = _detect_source_format(getattr(f, "filename", ""), data)
        pdf_data = _get_document_data(data, source_format=source_format, allow_ocr=False)
        total_pages = pdf_data["pages"]
        page_texts = pdf_data["page_texts"]
        if source_format == "epub" and pdf_data.get("chapter_list"):
            chapters = pdf_data.get("chapter_list") or []
        else:
            candidates = []
            candidates.extend(_detect_chapters_from_toc_text(page_texts, len(page_texts)))
            candidates.extend(detect_chapter_starts(page_texts))
            if not candidates:
                candidates.extend(_detect_page_title_sections(page_texts))
            chapters = _canonicalize_chapter_list(candidates, len(page_texts))
        ocr_required = source_format == "pdf" and len(pdf_data.get("full_text", "").strip()) < OCR_MIN_TEXT_CHARS
        info = _estimate_feasibility(total_pages, len(chapters), requested_pages, ocr_used=ocr_required)
        info.update({"ocr_required": ocr_required, "source_format": source_format, "detected_titles": [c.get("title") for c in chapters[:40]]})
        return jsonify(info)
    except Exception as e:
        return jsonify({"error": str(e)}), 400

@app.route("/tailored", methods=["POST"])
def tailored():
    pdf_file = request.files.get("pdf")
    if not pdf_file:
        return jsonify({"error": "No PDF or EPUB uploaded"}), 400
    try:
        data = pdf_file.read()
        plan = _tailored_length_plan(data, filename=getattr(pdf_file, "filename", ""))
        return jsonify(plan)
    except Exception as e:
        return jsonify({"error": str(e)}), 400


@app.route("/suggest", methods=["POST"])
def suggest():
    pdf_file = request.files.get("pdf")
    api_key  = request.form.get("api_key", "").strip()
    title    = request.form.get("title", "this book")
    api_key  = "".join(c for c in api_key if ord(c) < 128)
    if not pdf_file:
        return jsonify({"suggestions": []}), 400

    try:
        data     = pdf_file.read()
        source_format = _detect_source_format(getattr(pdf_file, "filename", ""), data)
        pdf_data = _fast_document_preflight(data, source_format=source_format)
        total_pages = pdf_data["pages"]
        sample = pdf_data.get("full_text", "")[:5000]
        ocr_required = source_format == "pdf" and len(sample.strip()) < OCR_MIN_TEXT_CHARS
    except Exception:
        return jsonify({"suggestions": []}), 400

    # Default: instant deterministic suggestions. This keeps upload/preflight fast.
    if not AI_SUGGESTIONS_ENABLED or not api_key.startswith("sk-ant-"):
        return jsonify({
            "suggestions": _deterministic_summary_suggestions(total_pages, source_format, ocr_required),
            "source": "deterministic_fast",
        })

    # Optional legacy AI suggestions. Enable with BBC_AI_SUGGESTIONS=1.
    if source_format == "pdf" and len(sample.strip()) < 500 and OCR_ENABLED:
        try:
            pdf_data = _get_document_data(data, source_format=source_format, allow_ocr=True, ocr_max_pages=OCR_SUGGEST_PAGES)
            sample = ""
            for t in pdf_data["page_texts"][:OCR_SUGGEST_PAGES]:
                if t:
                    sample += t + "\n"
                if len(sample) > 5000:
                    break
            sample = sample[:5000]
        except Exception:
            sample = sample[:5000]

    prompt = (
        f'You are helping a reader decide how long their summary of "{title}" ({total_pages} pages) should be.\n\n'
        f"Based on the opening content below, suggest exactly 3 summary lengths.\n"
        f"For each, give: a page count (integer) and a reason of EXACTLY 25 words explaining "
        f"what depth and insight the reader will get at that length.\n\n"
        f"Reply in this exact JSON format (no markdown, no extra text):\n"
        '[{"pages": 15, "reason": "25 word reason here."}, '
        '{"pages": 30, "reason": "25 word reason here."}, '
        '{"pages": 60, "reason": "25 word reason here."}]\n\n'
        f"The 3 options should be short/medium/long — scaled sensibly to the book length.\n\n"
        f"Book sample:\n{sample[:5000]}"
    )

    try:
        client = _make_ai_client(api_key, timeout_seconds=30.0)
        resp = client.messages.create(
            model=MODEL_CHUNK,
            max_tokens=300,
            messages=[{"role": "user", "content": prompt}]
        )
        text = _anthropic_text(resp)
        m    = re.search(r"\[.*\]", text, re.DOTALL)
        if m:
            suggestions = json.loads(m.group())
            suggestions = suggestions[:3]
            for sg in suggestions:
                words      = str(sg.get("reason", "")).split()[:35]
                sg["reason"] = " ".join(words)
                sg["pages"]  = max(5, int(sg.get("pages", 20)))
            return jsonify({"suggestions": suggestions, "source": "ai"})
    except Exception:
        pass
    return jsonify({
        "suggestions": _deterministic_summary_suggestions(total_pages, source_format, ocr_required),
        "source": "deterministic_fallback",
    })

def _split_pdf_at_midpoint(source_bytes, page_texts):
    """Split PDF into two halves at the chapter boundary closest to the midpoint.
    Returns (split_page, split_title, half1_bytes, half2_bytes).
    """
    reader      = PdfReader(BytesIO(source_bytes))
    total_pages = len(reader.pages)
    mid         = max(1, total_pages // 2)

    chapter_starts = detect_chapter_starts(page_texts)
    candidates     = [cs for cs in chapter_starts if 0 < cs["page"] < total_pages - 1]

    if candidates:
        best        = min(candidates, key=lambda c: abs(c["page"] - mid))
        split_page  = best["page"]
        split_title = best["title"]
    else:
        split_page  = mid
        split_title = f"Page {mid + 1}"

    def _half(start, end):
        w = PdfWriter()
        for i in range(start, end):
            w.add_page(reader.pages[i])
        buf = BytesIO()
        w.write(buf)
        return buf.getvalue()

    return split_page, split_title, _half(0, split_page), _half(split_page, total_pages)


@app.route("/start", methods=["POST"])
def start():
    pdf_file = request.files.get("pdf")
    if not pdf_file:
        return jsonify({"error": "No PDF or EPUB uploaded"}), 400

    api_key = request.form.get("api_key", "").strip()
    api_key = "".join(c for c in api_key if ord(c) < 128)
    if not api_key.startswith("sk-ant-"):
        return jsonify({"error": "Invalid API key (must start with sk-ant-)"}), 400

    source_bytes = pdf_file.read()
    source_format = _detect_source_format(getattr(pdf_file, "filename", ""), source_bytes)
    title        = clean_title(request.form.get("title", "Untitled Book")) or clean_title(getattr(pdf_file, "filename", "Untitled Book")) or "Untitled Book"
    author       = request.form.get("author", "").strip()
    instructions = request.form.get("instructions", "")
    style        = request.form.get("style", "narrative_basic")
    allowed_styles = {
        "narrative_basic", "story_arc", "feynman_storyteller", "investigative_narrative",
        "strategic_briefing", "deep_reading", "practical_playbook", "literary_essay", "academic",
        # Backward-compatible aliases from earlier versions / cached browser forms.
        "narrative_explainer", "narrative_editorial", "narrative_deep", "narrative", "concise", "bullet",
    }
    if style not in allowed_styles:
        style = "narrative_basic"
    length_mode  = request.form.get("length_mode", "percent")
    if length_mode not in ("percent", "fixed"):
        length_mode = "percent"
    try:
        length_value = int(request.form.get("length_value", "15"))
    except (TypeError, ValueError):
        return jsonify({"error": "Summary length must be a whole number."}), 400
    if length_mode == "fixed" and length_value < 1:
        return jsonify({"error": "Fixed summary length must be at least 1 page."}), 400
    if length_mode == "percent" and length_value < 1:
        return jsonify({"error": "Percent summary length must be at least 1%."}), 400
    split_mode   = request.form.get("split_mode") == "true"
    page_strictness = request.form.get("page_strictness", "standard").strip().lower()
    if page_strictness not in ("quickdirty", "quick-dirty", "quick", "loose", "flexible", "standard", "strict", "exactish", "exact-ish", "exact"):
        page_strictness = "standard"

    if split_mode:
        if source_format != "pdf":
            return jsonify({"error": "Split mode is only available for PDF files."}), 400
        try:
            pdf_data   = _get_document_data(source_bytes, source_format=source_format, allow_ocr=False)
            page_texts = pdf_data["page_texts"]
            if len(pdf_data["page_texts"]) < 4:
                return jsonify({"error": "PDF too short to split (need ≥ 4 pages)"}), 400
            split_page, split_title, half1, half2 = _split_pdf_at_midpoint(source_bytes, page_texts)
        except Exception as e:
            return jsonify({"error": f"Failed to split PDF: {e}"}), 500

        now     = time.time()
        job_ids = []
        for idx, (half_bytes, half_label) in enumerate([
            (half1, f"{title} — Part 1 of 2"),
            (half2, f"{title} — Part 2 of 2"),
        ]):
            jid = uuid.uuid4().hex
            jobs[jid] = {
                "status": "running", "progress": 0, "message": "Starting...",
                "chapters": [], "output_path": None, "share_token": None,
                "last_update": now, "title": half_label, "created_at": now, "cancel_requested": False,
            }
            threading.Thread(
                target=run_job,
                args=(jid, half_bytes, api_key, half_label, instructions,
                      style, length_mode, length_value, author, page_strictness),
                daemon=True,
            ).start()
            job_ids.append(jid)

        return jsonify({"job_ids": job_ids, "split_page": split_page, "split_title": split_title})

    now    = time.time()
    job_id = uuid.uuid4().hex
    jobs[job_id] = {
        "status":      "running",
        "progress":    0,
        "message":     "Starting...",
        "chapters":    [],
        "output_path": None,
        "share_token": None,
        "last_update": now,
        "title":       title,
        "created_at":  now,
        "cancel_requested": False,
    }

    threading.Thread(
        target=run_job,
        args=(job_id, source_bytes, api_key, title, instructions, style, length_mode, length_value, author, page_strictness, source_format, getattr(pdf_file, "filename", "")),
        daemon=True,
    ).start()

    return jsonify({"job_id": job_id})

@app.route("/status/<job_id>")
def status(job_id):
    job = jobs.get(job_id)
    if not job:
        return jsonify({"error": "Job not found"}), 404
    return jsonify({
        "status":         job.get("status"),
        "progress":       job.get("progress", 0),
        "message":        job.get("message", ""),
        "chapters":       job.get("chapters", []),
        "output_path":    job.get("output_path"),
        "share_token":    job.get("share_token"),
        "rendered_pages": job.get("rendered_pages"),
        "requested_pages":job.get("requested_pages"),
        "phone_rendered_pages": job.get("phone_rendered_pages"),
        "phone_max_pages": job.get("phone_max_pages"),
        "variant_max_pages": _variant_max_pages(job.get("requested_pages") or 0),
        "phone_error": job.get("phone_error"),
        "bw_rendered_pages": job.get("bw_rendered_pages"),
        "cyan_rendered_pages": job.get("cyan_rendered_pages"),
        "ocr_used":       job.get("ocr_used"),
        "ocr_status":     job.get("ocr_status"),
        "error":          job.get("error"),
        "warning":        job.get("warning"),
        "feasibility":    job.get("feasibility"),
        "length_strictness": job.get("length_strictness"),
        "summary_tier":   job.get("summary_tier"),
        "source_format":  job.get("source_format"),
        "audit_events_count": len(job.get("audit_events") or []),
        "audit_url":      f"/audit/{job_id}",
        "audit_download_url": f"/download_audit/{job_id}",
    })

@app.route("/cancel/<job_id>", methods=["POST"])
def cancel(job_id):
    job = jobs.get(job_id)
    if not job:
        return jsonify({"error": "Job not found"}), 404
    if job.get("status") == "running":
        job.update({"cancel_requested": True, "message": "Cancellation requested; stopping at the next safe checkpoint.", "last_update": time.time()})
    return jsonify({"ok": True, "status": job.get("status")})

@app.route("/download/<job_id>")
def download(job_id):
    job = jobs.get(job_id)
    if not job or job.get("status") != "done":
        return jsonify({"error": "Not ready"}), 404
    path = job.get("output_path")
    if not path or not os.path.exists(path):
        return jsonify({"error": "File not found"}), 404
    job_title     = re.sub(r"[^\w\s-]", "", job.get("title", "Book Summary"))
    job_title     = re.sub(r"\s+", " ", job_title.strip())[:60]
    download_name = f"{job_title}.pdf"
    return send_file(path, as_attachment=True, download_name=download_name)

@app.route("/download_bundle/<job_id>")
def download_bundle(job_id):
    job = jobs.get(job_id)
    if not job or job.get("status") != "done":
        return jsonify({"error": "Not ready"}), 404

    title         = job.get("title", "Book Summary")
    safe_name     = re.sub(r"[^\w\s-]", "", title).strip()
    safe_name     = re.sub(r"\s+", " ", safe_name)[:60] or "Book Summary"

    summary_path  = job.get("output_path")
    original_path = job.get("original_path")
    part_paths    = job.get("part_paths", [])

    if not summary_path or not os.path.exists(summary_path):
        return jsonify({"error": "Summary missing"}), 404
    if not original_path or not os.path.exists(original_path):
        return jsonify({"error": "Original missing"}), 404

    buf = BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        original_ext = job.get("original_ext") or _source_extension(job.get("source_format", "pdf"))
        zf.write(original_path, f"{safe_name} — ORIGINAL{original_ext}")
        zf.write(summary_path,  f"{safe_name} — SUMMARY.pdf")
        for filename, path in part_paths:
            if os.path.exists(path):
                zf.write(path, filename)
    buf.seek(0)
    return send_file(
        buf,
        as_attachment=True,
        download_name=f"{safe_name} — Bundle.zip",
        mimetype="application/zip",
    )

@app.route("/audit/<job_id>")
def audit(job_id):
    job = jobs.get(job_id)
    if not job:
        return jsonify({"error": "Job not found"}), 404
    events = list(job.get("audit_events") or [])
    audit_path = os.path.join(TMP_DIR, f"{job_id}_audit.jsonl")
    if not events and os.path.exists(audit_path):
        try:
            with open(audit_path, "r", encoding="utf-8", errors="replace") as f:
                events = [json.loads(line) for line in f if line.strip()][-AUDIT_TRAIL_MAX_EVENTS:]
        except Exception:
            events = []
    return jsonify({
        "job_id": job_id,
        "status": job.get("status"),
        "progress": job.get("progress", 0),
        "message": job.get("message", ""),
        "title": job.get("title"),
        "source_format": job.get("source_format"),
        "requested_pages": job.get("requested_pages"),
        "rendered_pages": job.get("rendered_pages"),
        "length_strictness": job.get("length_strictness"),
        "summary_tier": job.get("summary_tier"),
        "ocr_used": job.get("ocr_used"),
        "ocr_status": job.get("ocr_status"),
        "feasibility": job.get("feasibility"),
        "warning": job.get("warning"),
        "last_valid_pages": job.get("last_valid_pages"),
        "last_valid_note": job.get("last_valid_note"),
        "error": job.get("error"),
        "events": events,
        "audit_download_url": f"/download_audit/{job_id}",
    })

@app.route("/download_audit/<job_id>")
def download_audit(job_id):
    job = jobs.get(job_id)
    if not job:
        return jsonify({"error": "Job not found"}), 404
    path = os.path.join(TMP_DIR, f"{job_id}_audit.jsonl")
    if not os.path.exists(path):
        events = job.get("audit_events") or []
        if events:
            with open(path, "w", encoding="utf-8", errors="replace") as f:
                for row in events:
                    f.write(json.dumps(row, ensure_ascii=False) + "\n")
    if not os.path.exists(path):
        return jsonify({"error": "Audit trail not available"}), 404
    title = re.sub(r"[^\w\s-]", "", job.get("title", "job")).strip()[:60] or "job"
    return send_file(path, as_attachment=True, download_name=f"{title} - audit.jsonl", mimetype="application/x-ndjson")


@app.route("/manifest/<job_id>")
def get_manifest(job_id):
    job = jobs.get(job_id)
    if not job:
        return jsonify({"error": "Job not found"}), 404
    return jsonify({
        "manifest": job.get("chapter_manifest", []),
        "report": job.get("chapter_manifest_report", {}),
        "path": job.get("manifest_path", ""),
    })


@app.route("/download_manifest/<job_id>")
def download_manifest(job_id):
    job = jobs.get(job_id) or {}
    path = job.get("manifest_path") or os.path.join(TMP_DIR, f"{job_id}_manifest.json")
    if not os.path.exists(path):
        return jsonify({"error": "Chapter manifest not found"}), 404
    title = re.sub(r"[^\w\s-]", "", job.get("title", "job")).strip()[:60] or "job"
    return send_file(path, as_attachment=True, download_name=f"{title} - chapter-manifest.json", mimetype="application/json")

@app.route("/download_phone/<job_id>")
def download_phone(job_id):
    job = jobs.get(job_id)
    if not job or job.get("status") != "done":
        return jsonify({"error": "Not ready"}), 404

    phone_path = job.get("phone_path")
    if not phone_path or not os.path.exists(phone_path):
        return jsonify({"error": "Phone version not available"}), 404

    title     = job.get("title", "Book Summary")
    safe_name = re.sub(r"[^\w\s-]", "", title).strip()
    safe_name = re.sub(r"\s+", " ", safe_name)[:60] or "Book Summary"

    return send_file(phone_path, as_attachment=True,
                     download_name=f"PHONE — {safe_name}.pdf",
                     mimetype="application/pdf")

@app.route("/download_bw/<job_id>")
def download_bw(job_id):
    job = jobs.get(job_id)
    if not job or job.get("status") != "done":
        return jsonify({"error": "Not ready"}), 404

    meta = job.get("build_meta")
    if not meta:
        return jsonify({"error": "Build metadata missing"}), 404

    title     = job.get("title", "Book Summary")
    safe_name = re.sub(r"[^\w\s-]", "", title).strip()
    safe_name = re.sub(r"\s+", " ", safe_name)[:60] or "Book Summary"

    tmp_path = os.path.join(TMP_DIR, f"{job_id}_bw.pdf")
    try:
        _bw_sections, bw_pages = _build_variant_pdf_with_page_cap(
            out_path=tmp_path,
            sections=meta["sections"],
            book_title=title,
            total_pages=meta["total_pages"],
            cover_path=meta["cover_path"],
            author_info=meta["author_info"],
            similar_md=meta["similar_md"],
            diff_label=meta["diff_label"],
            diff_explain=meta["diff_explain"],
            requested_pages=job.get("requested_pages") or 0,
            variant_name=f"{job_id}:bw",
            include_cover=False,
            include_toc=True,
            include_back=False,
            bw=True,
        )
        job["bw_rendered_pages"] = bw_pages
        _audit_event(job_id, "variant_built", variant="bw", rendered_pages=bw_pages, max_pages=_variant_max_pages(job.get("requested_pages") or 0))
        with open(tmp_path, "rb") as f:
            pdf_bytes = f.read()
    except Exception as e:
        return jsonify({"error": f"B&W build failed: {e}"}), 500
    finally:
        if os.path.exists(tmp_path):
            os.remove(tmp_path)

    return send_file(
        BytesIO(pdf_bytes),
        as_attachment=True,
        download_name=f"{safe_name} — Print.pdf",
        mimetype="application/pdf",
    )

@app.route("/download_cyan/<job_id>")
def download_cyan(job_id):
    job = jobs.get(job_id)
    if not job or job.get("status") != "done":
        return jsonify({"error": "Not ready"}), 404

    meta = job.get("build_meta")
    if not meta:
        return jsonify({"error": "Build metadata missing"}), 404

    title     = job.get("title", "Book Summary")
    safe_name = re.sub(r"[^\w\s-]", "", title).strip()
    safe_name = re.sub(r"\s+", " ", safe_name)[:60] or "Book Summary"

    tmp_path = os.path.join(TMP_DIR, f"{job_id}_cyan.pdf")
    try:
        _cyan_sections, cyan_pages = _build_variant_pdf_with_page_cap(
            out_path=tmp_path,
            sections=meta["sections"],
            book_title=title,
            total_pages=meta["total_pages"],
            cover_path=meta["cover_path"],
            author_info=meta["author_info"],
            similar_md=meta["similar_md"],
            diff_label=meta["diff_label"],
            diff_explain=meta["diff_explain"],
            requested_pages=job.get("requested_pages") or 0,
            variant_name=f"{job_id}:cyan",
            include_cover=False,
            include_toc=True,
            include_back=False,
            cyan=True,
        )
        job["cyan_rendered_pages"] = cyan_pages
        _audit_event(job_id, "variant_built", variant="cyan", rendered_pages=cyan_pages, max_pages=_variant_max_pages(job.get("requested_pages") or 0))
        with open(tmp_path, "rb") as f:
            pdf_bytes = f.read()
    except Exception as e:
        return jsonify({"error": f"Cyan build failed: {e}"}), 500
    finally:
        if os.path.exists(tmp_path):
            os.remove(tmp_path)

    return send_file(
        BytesIO(pdf_bytes),
        as_attachment=True,
        download_name=f"{safe_name} — Print Cyan.pdf",
        mimetype="application/pdf",
    )

@app.route("/version")
def version():
    """Browser-checkable build identity. Visit http://localhost:5001/version
    to confirm exactly which build is running, independent of any file."""
    return jsonify({
        "build": BUILD_TAG,
        "label": BUILD_LABEL,
        "style_application_gate": STYLE_AUDIT_ENABLED,
        "style_ai_rewrite": STYLE_AI_REWRITE,
        "app": "Brianis Book Club — AI News Digest",
        "what_happened_header": "WHAT HAPPENED — ANALYSIS",
        "what_happened_cap_policy": f"min({NEWS_WH_ABSOLUTE_MAX} words, {int(NEWS_WH_SOURCE_MAX_RATIO * 100)}% of cleaned article)",
        "news_article_cleaning": True,
        "news_wh_retry_expand": NEWS_WH_RETRY_EXPAND,
    })

@app.route("/view/<token>")
def view(token):
    share = shares.get(token)
    if not share:
        return "Share not found", 404
    title = share["title"]
    title_html = html.escape(title)
    sections = share["sections"]
    parts = []
    for sec in sections:
        level = sec.get("level", 1)
        heading = html.escape(sec.get("heading", ""))
        body = sec.get("body", "")
        tag = {1: "h2", 2: "h3", 3: "h4"}.get(level, "h4")
        if heading:
            parts.append(f"<{tag}>{heading}</{tag}>")
        for line in body.strip().splitlines():
            stripped = line.strip()
            if stripped:
                parts.append(f"<p>{html.escape(stripped)}</p>")
    body_html = "\n".join(parts)
    return Response(f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>{title_html} - Brianis Book Club</title>
<style>
  body {{ background:#07070f; color:#e8e8f0; font-family:Georgia,serif; max-width:800px; margin:0 auto; padding:40px 20px; }}
  h1   {{ color:#7c3aed; font-size:2em; margin-bottom:8px; }}
  h2   {{ color:#fff; border-bottom:1px solid #1f1f3a; padding-bottom:8px; margin:32px 0 12px; }}
  h3   {{ color:#7c3aed; margin:24px 0 8px; }}
  h4   {{ color:#f59e0b; margin:16px 0 6px; }}
  p    {{ line-height:1.7; margin-bottom:10px; }}
  .brand {{ color:#5b5b7b; font-size:0.8em; text-align:center; margin-top:60px; }}
</style>
</head>
<body>
<h1>{title_html}</h1>
<p class="brand">Brianis Book Club - AI-Powered Reading Companion</p>
{body_html}
<p class="brand">Brianis Book Club - Not for redistribution, only for recreation</p>
</body>
</html>""", mimetype="text/html")


# ── Entry Point ────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    print("\n  ===================================================")
    print(f"  Book Summarizer {BUILD_TAG}  —  {BUILD_LABEL}")
    print("  running at http://localhost:5001")
    print(f"  verify build at http://localhost:5001/version")
    print("  ===================================================\n")
    app.run(debug=False, port=5001)
