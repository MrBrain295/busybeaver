#!/usr/bin/env python3
"""Generate Lean BB5 hardcoded table entries from the Coq parameter files."""

from __future__ import annotations

import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
COQ_DIR = ROOT / "Coq-BB5" / "CoqBB5" / "BB5"
PARAM_DIR = COQ_DIR / "BB5_Deciders_Hardcoded_Parameters"
OUT = ROOT / "Busybeaver" / "Deciders" / "BB5TableEntries.lean"

TOKEN = r"[A-Z][LR][01]"
TM_RE = rf"((?:{TOKEN}\s+){{9}}{TOKEN})"
ROW_RE = re.compile(rf"\(makeTM\s+{TM_RE},\s*([A-Za-z_][A-Za-z0-9_]*)(?:\s+([^)]*?))?\)::", re.S)
SPORADIC_RE = re.compile(rf"Definition\s+\w+\s*:=\s*makeTM\s+{TM_RE}\.", re.S)
DNV_RE = re.compile(rf"\(makeTM\s+{TM_RE},\s*DNV\s+(\d+)\s+\(DFA_from_list\s+\((.*?)\)\)\)::", re.S)
WA_RE = re.compile(
    rf"\(makeTM\s+{TM_RE},\s*WA\s+(-?\d+)\s+"
    rf"(\d+)\s+\(WDFA_from_list\s+\((.*?)\)\)\s+"
    rf"(\d+)\s+\(WDFA_from_list\s+\((.*?)\)\)\)::",
    re.S,
)


def token_to_code(token: str) -> str:
    state, direction, symbol = token
    if state == "H":
        return "---"
    return f"{symbol}{direction}{state}"


def tm_to_code(raw: str) -> str:
    tokens = raw.split()
    if len(tokens) != 10:
        raise ValueError(f"expected 10 transitions, got {len(tokens)} in {raw!r}")
    cells = [token_to_code(token) for token in tokens]
    return "_".join(cells[i] + cells[i + 1] for i in range(0, 10, 2))


def parse_rows(path: Path) -> list[tuple[str, str, str]]:
    text = path.read_text()
    return [(tm_to_code(tm), kind, (args or "").strip()) for tm, kind, args in ROW_RE.findall(text)]


def parse_sporadic(path: Path) -> list[str]:
    text = path.read_text()
    return [tm_to_code(tm) for tm in SPORADIC_RE.findall(text)]


def parse_dnv(path: Path) -> list[tuple[str, int, list[tuple[int, int]]]]:
    text = path.read_text()
    rows = []
    for tm, states, pairs in DNV_RE.findall(text):
        dfa = [(int(a), int(b)) for a, b in re.findall(r"\((\d+),(\d+)\)", pairs)]
        rows.append((tm_to_code(tm), int(states), dfa))
    return rows


def parse_wdfa(raw: str) -> list[tuple[tuple[int, int], tuple[int, int]]]:
    return [
        ((int(a0), int(a1)), (int(b0), int(b1)))
        for a0, a1, b0, b1 in re.findall(r"\((\d+),(-?\d+);(\d+),(-?\d+)\)", raw)
    ]


def parse_wa(
    path: Path,
) -> list[tuple[str, int, int, list[tuple[tuple[int, int], tuple[int, int]]], int, list[tuple[tuple[int, int], tuple[int, int]]]]]:
    text = path.read_text()
    rows = []
    for tm, max_d, left_states, left_raw, right_states, right_raw in WA_RE.findall(text):
        max_d_int = int(max_d)
        if max_d_int < 0:
            raise ValueError(f"negative WA max_d is not supported: {max_d}")
        rows.append((
            tm_to_code(tm),
            max_d_int,
            int(left_states),
            parse_wdfa(left_raw),
            int(right_states),
            parse_wdfa(right_raw),
        ))
    return rows


def lean_entry(code: str, decider: str) -> str:
    return f'  ("{code}", {decider})'


def chunked(items: list[str], size: int = 500) -> list[list[str]]:
    return [items[i : i + size] for i in range(0, len(items), size)]


def emit_chunked_def(name: str, rows: list[str], out: list[str]) -> None:
    chunks = chunked(rows)
    if not chunks:
        out.append(f"def {name} : List Entry := []")
        out.append("")
        return
    chunk_names = []
    for idx, chunk in enumerate(chunks):
        chunk_name = f"{name}Chunk{idx}"
        chunk_names.append(chunk_name)
        out.append(f"private def {chunk_name} : List Entry := [")
        out.append(",\n".join(chunk))
        out.append("]")
        out.append("")
    out.append(f"def {name} : List Entry :=")
    out.append(f"  List.flatten [{', '.join(chunk_names)}]")
    out.append("")


def parse_nat_args(args: str, expected: int, kind: str) -> list[int]:
    parts = args.split()
    if len(parts) != expected or not all(part.isdigit() for part in parts):
        raise ValueError(f"bad {kind} args: {args!r}")
    return [int(part) for part in parts]


def main() -> None:
    halt_rows = [
        lean_entry(code, ".halt 47176870")
        for code, kind, _ in parse_rows(PARAM_DIR / "Decider_Halt_Hardcoded_Parameters.v")
        if kind == "Ha"
    ]

    loop1_rows = [
        lean_entry(code, ".loop1 1050000")
        for code, kind, _ in parse_rows(PARAM_DIR / "Decider_Loop_Hardcoded_Parameters.v")
        if kind == "Lp1"
    ]

    ngram_rows: list[str] = []
    for code, kind, args in parse_rows(PARAM_DIR / "Decider_NGramCPS_Hardcoded_Parameters.v"):
        if kind == "NG":
            history, length = parse_nat_args(args, 2, kind)
            ngram_rows.append(lean_entry(code, f".nGram {history} {length} 5000001"))
        elif kind == "NG_LRU":
            (length,) = parse_nat_args(args, 1, kind)
            ngram_rows.append(lean_entry(code, f".nGramLRU {length} 5000001"))

    repwl_rows: list[str] = []
    for code, kind, args in parse_rows(PARAM_DIR / "Decider_RepWL_Hardcoded_Parameters.v"):
        if kind == "RWL":
            length, threshold = parse_nat_args(args, 2, kind)
            repwl_rows.append(lean_entry(code, f".repWL {length} {threshold} 320 150001"))

    sporadic_rows = [
        lean_entry(code, ".sporadic")
        for code in parse_sporadic(COQ_DIR / "BB5_Sporadic_Machines.v")
    ]

    far_rows = []
    for code, states, dfa in parse_dnv(PARAM_DIR / "Verifier_FAR_Hardcoded_Certificates.v"):
        lean_dfa = "[" + ", ".join(f"({a}, {b})" for a, b in dfa) + "]"
        far_rows.append(lean_entry(code, f".far {states} {lean_dfa}"))
    wfar_rows = []
    for code, max_d, left_states, left, right_states, right in parse_wa(
        PARAM_DIR / "Verifier_WFAR_Hardcoded_Certificates.v"
    ):
        lean_left = "[" + ", ".join(f"(({a0}, {a1}), ({b0}, {b1}))" for (a0, a1), (b0, b1) in left) + "]"
        lean_right = "[" + ", ".join(f"(({a0}, {a1}), ({b0}, {b1}))" for (a0, a1), (b0, b1) in right) + "]"
        wfar_rows.append(
            lean_entry(code, f".wfar {max_d} {left_states} {lean_left} {right_states} {lean_right} 10000000")
        )

    all_codes = [
        row.split('"', 2)[1]
        for group in [halt_rows, loop1_rows, ngram_rows, repwl_rows, sporadic_rows, far_rows, wfar_rows]
        for row in group
    ]
    duplicates = sum(count - 1 for count in Counter(all_codes).values() if count > 1)

    out: list[str] = [
        "import Busybeaver.Deciders.BB5Table",
        "",
        "/-!",
        "Generated BB5 hardcoded table entries from the Coq parameter files.",
        "",
        "Regenerate with `python3 scripts/generate_bb5_table.py`.",
        "-/",
        "",
        "namespace Deciders.BB5Table.Generated",
        "",
        f"-- Rows: halt={len(halt_rows)}, loop1={len(loop1_rows)}, ngram={len(ngram_rows)}, "
        f"repWL={len(repwl_rows)}, sporadic={len(sporadic_rows)}, FAR={len(far_rows)}, WFAR={len(wfar_rows)}.",
        f"-- Duplicate machine keys across generated groups: {duplicates}.",
        "",
    ]

    emit_chunked_def("haltEntries", halt_rows, out)
    emit_chunked_def("loop1Entries", loop1_rows, out)
    emit_chunked_def("nGramEntries", ngram_rows, out)
    emit_chunked_def("repWLEntries", repwl_rows, out)
    emit_chunked_def("sporadicEntries", sporadic_rows, out)
    emit_chunked_def("farEntries", far_rows, out)
    emit_chunked_def("wfarEntries", wfar_rows, out)

    out.extend(
        [
            "def executableEntries : List Entry :=",
            "  haltEntries ++ loop1Entries ++ nGramEntries ++ repWLEntries ++ sporadicEntries ++ farEntries ++ wfarEntries",
            "",
            "def pendingEntries : List Entry :=",
            "  []",
            "",
            "def allEntries : List Entry :=",
            "  executableEntries ++ pendingEntries",
            "",
            "def executableTable : Table :=",
            "  tableOfEntries executableEntries",
            "",
            "def allTable : Table :=",
            "  tableOfEntries allEntries",
            "",
            "end Deciders.BB5Table.Generated",
            "",
        ]
    )

    OUT.write_text("\n".join(out))


if __name__ == "__main__":
    main()
