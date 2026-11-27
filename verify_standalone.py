#!/usr/bin/env python3
"""
Standalone Zero-Dependency Referee Verification Script (verify_standalone.py)
=============================================================================
Requires ONLY the Python 3 Standard Library (zero third-party packages).
Designed for independent mathematical referees to verify from scratch:

  1. [witness_k43_e2_catalog.txt]
     - Parses all 4 canonical E_{K5}=2 witnesses on K_43 (highlighting the 2
       unoriented representatives G*_1 and G*_2).
     - Verifies simple undirected graph validity (irreflexive, symmetric, < 2^43).
     - Counts monochromatic K_5 subgraphs via pure 2D boolean 5-nested loops
       (zero bitwise popcount tricks), proving E_{K5} == 2 on every witness.
     - Verifies the monochromatic bi-pyramid (K_6 - e) topology: same-color
       cliques C_0, C_1 sharing a 4-vertex spine W (|C_0 cap C_1| == 4) with
       an opposite-colored pole pair {a, b}.
     - Constructs and checks the explicit non-trivial reflection involution
       automorphism pi in Aut(G) (pi != id, pi^2 = id, 1 fixed point + 21
       transpositions, swapping poles a <-> b), proving |Aut(G*_i)| >= 2.

  2. [k42_pool_656.txt]
     - Parses all 656 non-isomorphic oriented (5, 5; 42) mother graphs.
     - Verifies simple undirected validity and E_{K5}(G_42) == 0 on ALL 656
       graphs via pure 2D boolean nested loops.
     - Computes multi-round Weisfeiler-Leman structural invariants (with exact
       backtracking fallback if any hash bucket ever collides) to verify that
       all 656 graphs are pairwise non-isomorphic, and checks that every
       recorded opt_mask42 achieves its claimed E_{K5}^* >= 2.

  3. [certificate_m55_43.lean]
     - Parses the hardcoded hexadecimal row constants of M_42_A, M_42_B,
       G_star_1, and G_star_2 directly from the Lean 4 source file.
     - Performs bit-for-bit comparison against witness_k43_e2_catalog.txt and
       k42_pool_656.txt, and checks that zero `sorry`, `admit`, or
       `native_decide` tokens appear in active Lean code.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple


# ---------------------------------------------------------------------------
# 1. File Resolution & Hex Matrix Parsing
# ---------------------------------------------------------------------------

def resolve_artifact_paths(base_dir: Path) -> Tuple[Path, Path, Path]:
    """Locate catalog, 656-pool, and Lean certificate in workspace or release_bundle."""
    candidates_cat = [
        base_dir / "witness_k43_e2_catalog.txt",
        base_dir / "data" / "witness_k43_e2_catalog.txt",
    ]
    candidates_pool = [
        base_dir / "k42_pool_656.txt",
        base_dir / "data" / "k42_pool_656.txt",
    ]
    candidates_lean = [
        base_dir / "certificate_m55_43.lean",
        base_dir / "formal" / "certificate_m55_43.lean",
    ]

    def pick(paths: Sequence[Path], label: str) -> Path:
        for p in paths:
            if p.is_file():
                return p
        raise FileNotFoundError(f"Could not locate {label}; searched: {[str(x) for x in paths]}")

    return (
        pick(candidates_cat, "witness_k43_e2_catalog.txt"),
        pick(candidates_pool, "k42_pool_656.txt"),
        pick(candidates_lean, "certificate_m55_43.lean"),
    )


def masks_to_bool_matrix(n: int, masks: Sequence[int]) -> List[List[bool]]:
    """Convert n integer bitmasks into a plain n x n 2D boolean adjacency table."""
    if len(masks) != n:
        raise ValueError(f"Expected {n} row masks, got {len(masks)}")
    limit = 1 << n
    mat: List[List[bool]] = []
    for u, m in enumerate(masks):
        if m < 0 or m >= limit:
            raise ValueError(f"Row {u} mask 0x{m:x} exceeds {n}-bit bound")
        row = [False] * n
        val = m
        for v in range(n):
            row[v] = (val % 2) == 1
            val //= 2
        if row[u]:
            raise ValueError(f"Self-loop detected at vertex {u}")
        mat.append(row)
    for u in range(n):
        for v in range(u + 1, n):
            if mat[u][v] != mat[v][u]:
                raise ValueError(f"Asymmetry detected between ({u}, {v})")
    return mat


# ---------------------------------------------------------------------------
# 2. Pure Combinatorial K_5 Enumeration & Automorphism Discovery
# ---------------------------------------------------------------------------

def enumerate_monochromatic_k5_plain(
    n: int, mat: Sequence[Sequence[bool]]
) -> List[Tuple[str, Tuple[int, int, int, int, int]]]:
    """
    Pure 2D boolean 5-nested-loop enumeration over 0 <= a < b < c < d < e < n.
    Zero bitwise operations are used.
    """
    cliques: List[Tuple[str, Tuple[int, int, int, int, int]]] = []
    for a in range(n - 4):
        row_a = mat[a]
        for b in range(a + 1, n - 3):
            col = row_a[b]
            row_b = mat[b]
            for c in range(b + 1, n - 2):
                if row_a[c] != col or row_b[c] != col:
                    continue
                row_c = mat[c]
                for d in range(c + 1, n - 1):
                    if row_a[d] != col or row_b[d] != col or row_c[d] != col:
                        continue
                    row_d = mat[d]
                    for e in range(d + 1, n):
                        if (
                            row_a[e] == col
                            and row_b[e] == col
                            and row_c[e] == col
                            and row_d[e] == col
                        ):
                            cliques.append(("RED" if col else "BLUE", (a, b, c, d, e)))
    return cliques


def has_zero_monochromatic_k5_plain(n: int, mat: Sequence[Sequence[bool]]) -> bool:
    """Pure 2D boolean 5-nested-loop check returning True iff E_{K5}(G) == 0."""
    for a in range(n - 4):
        row_a = mat[a]
        for b in range(a + 1, n - 3):
            col = row_a[b]
            row_b = mat[b]
            for c in range(b + 1, n - 2):
                if row_a[c] != col or row_b[c] != col:
                    continue
                row_c = mat[c]
                for d in range(c + 1, n - 1):
                    if row_a[d] != col or row_b[d] != col or row_c[d] != col:
                        continue
                    row_d = mat[d]
                    for e in range(d + 1, n):
                        if (
                            row_a[e] == col
                            and row_b[e] == col
                            and row_c[e] == col
                            and row_d[e] == col
                        ):
                            return False
    return True


def compute_wl_signature(
    n: int, mat: Sequence[Sequence[bool]], rounds: int = 3
) -> Tuple[str, List[int]]:
    """Compute a deterministic Weisfeiler-Leman structural invariant signature."""
    labels: List[int] = []
    for u in range(n):
        row_u = mat[u]
        deg_r = sum(1 for v in range(n) if v != u and row_u[v])
        tri_r = 0
        tri_b = 0
        for v in range(n):
            if v == u:
                continue
            uv = row_u[v]
            row_v = mat[v]
            for w in range(v + 1, n):
                if w != u and row_u[w] == uv and row_v[w] == uv:
                    if uv:
                        tri_r += 1
                    else:
                        tri_b += 1
        labels.append(hash((deg_r, tri_r, tri_b)))

    for _ in range(rounds):
        next_labels: List[int] = []
        for u in range(n):
            row_u = mat[u]
            r_mult = sorted(labels[v] for v in range(n) if v != u and row_u[v])
            b_mult = sorted(labels[v] for v in range(n) if v != u and not row_u[v])
            next_labels.append(hash((labels[u], tuple(r_mult), tuple(b_mult))))
        labels = next_labels

    canon = ",".join(f"{x & ((1 << 64) - 1):016x}" for x in sorted(labels))
    return canon, labels


def find_all_automorphisms(n: int, mat: Sequence[Sequence[bool]]) -> List[List[int]]:
    """Exact S_n backtracking enumeration of all color-preserving automorphisms."""
    _, v_labels = compute_wl_signature(n, mat, rounds=3)
    cands = [[v for v in range(n) if v_labels[v] == v_labels[u]] for u in range(n)]
    order = sorted(range(n), key=lambda u: (len(cands[u]), u))

    pi = [-1] * n
    used = [False] * n
    auts: List[List[int]] = []

    def dfs(depth: int) -> None:
        if depth == n:
            auts.append(pi[:])
            return
        u = order[depth]
        row_u = mat[u]
        for v in cands[u]:
            if used[v]:
                continue
            row_v = mat[v]
            ok = True
            for prev_d in range(depth):
                u_prev = order[prev_d]
                if row_u[u_prev] != row_v[pi[u_prev]]:
                    ok = False
                    break
            if not ok:
                continue
            pi[u] = v
            used[v] = True
            dfs(depth + 1)
            used[v] = False
            pi[u] = -1

    dfs(0)
    return auts


def are_isomorphic_exact(
    n: int,
    mat1: Sequence[Sequence[bool]],
    lab1: Sequence[int],
    mat2: Sequence[Sequence[bool]],
    lab2: Sequence[int],
) -> bool:
    """Exact S_n isomorphism test for rare hash-bucket collisions."""
    if sorted(lab1) != sorted(lab2):
        return False
    cands = [[v for v in range(n) if lab2[v] == lab1[u]] for u in range(n)]
    if any(not c for c in cands):
        return False
    order = sorted(range(n), key=lambda u: (len(cands[u]), u))
    pi = [-1] * n
    used = [False] * n

    def dfs(depth: int) -> bool:
        if depth == n:
            return True
        u = order[depth]
        row_u = mat1[u]
        for v in cands[u]:
            if used[v]:
                continue
            row_v = mat2[v]
            if all(row_u[order[k]] == row_v[pi[order[k]]] for k in range(depth)):
                pi[u] = v
                used[v] = True
                if dfs(depth + 1):
                    return True
                used[v] = False
                pi[u] = -1
        return False

    return dfs(0)


# ---------------------------------------------------------------------------
# 3. Dataset & Lean 4 Certificate Parsers
# ---------------------------------------------------------------------------

def parse_witness_catalog(path: Path) -> List[Tuple[str, List[int]]]:
    witnesses: List[Tuple[str, List[int]]] = []
    cur_header: Optional[str] = None
    cur_masks: List[int] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("WITNESS "):
            cur_header = line
            cur_masks = []
        elif cur_header is not None and line.lower().startswith("0x"):
            cur_masks.append(int(line, 16))
            if len(cur_masks) == 43:
                witnesses.append((cur_header, cur_masks))
                cur_header = None
    return witnesses


def parse_pool_656(path: Path) -> List[Tuple[int, int, int, List[int]]]:
    """Return list of (graph_id, exact_e_star, opt_mask42, row_masks_42)."""
    graphs: List[Tuple[int, int, int, List[int]]] = []
    cur_meta: Optional[Tuple[int, int, int]] = None
    cur_masks: List[int] = []
    header_re = re.compile(
        r"^GRAPH\s+(\d+)\s+.*exact_E_K5_star=(\d+)\s+opt_mask42=(0x[0-9a-fA-F]+)"
    )
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        m = header_re.match(line)
        if m:
            cur_meta = (int(m.group(1)), int(m.group(2)), int(m.group(3), 16))
            cur_masks = []
        elif cur_meta is not None and line.lower().startswith("0x"):
            cur_masks.append(int(line, 16))
            if len(cur_masks) == 42:
                graphs.append((cur_meta[0], cur_meta[1], cur_meta[2], cur_masks))
                cur_meta = None
    return graphs


def strip_lean_comments(src: str) -> str:
    """Remove Lean 4 block `/- ... -/` and line `-- ...` comments."""
    out: List[str] = []
    i = 0
    n = len(src)
    depth = 0
    while i < n:
        if src[i : i + 2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and src[i : i + 2] == "-/":
            depth -= 1
            i += 2
        elif depth == 0 and src[i : i + 2] == "--":
            while i < n and src[i] != "\n":
                i += 1
        else:
            if depth == 0:
                out.append(src[i])
            i += 1
    return "".join(out)


def parse_lean_adj_constants(path: Path) -> Tuple[Dict[str, List[int]], str]:
    raw = path.read_text(encoding="utf-8")
    clean = strip_lean_comments(raw)
    defs: Dict[str, List[int]] = {}
    pattern = re.compile(r"def\s+(M_42_A|M_42_B|G_star_1|G_star_2)\s*:\s*AdjMatrix\s*:=\s*\[(.*?)\]", re.S)
    for m in pattern.finditer(clean):
        name = m.group(1)
        hex_tokens = re.findall(r"0x[0-9a-fA-F]+", m.group(2))
        defs[name] = [int(tok, 16) for tok in hex_tokens]
    return defs, clean


# ---------------------------------------------------------------------------
# 4. Main Verification Pipeline
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description="Standalone referee verifier for M(5,5;43) <= 2 assets.")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="Root directory (workspace or release_bundle).",
    )
    args = parser.parse_args()

    t0 = time.perf_counter()
    cat_path, pool_path, lean_path = resolve_artifact_paths(args.root)

    print("=" * 78)
    print("STANDALONE REFEREE VERIFICATION REPORT (Pure Python 3 Standard Library)")
    print("=" * 78)
    print(f"  Catalog Path : {cat_path}")
    print(f"  656-Pool Path: {pool_path}")
    print(f"  Lean 4 Path  : {lean_path}\n")

    # -----------------------------------------------------------------------
    # Check 1: witness_k43_e2_catalog.txt (E_{K5} == 2, Bi-Pyramid, Aut >= 2)
    # -----------------------------------------------------------------------
    t_cat = time.perf_counter()
    witnesses = parse_witness_catalog(cat_path)
    if len(witnesses) != 4:
        raise AssertionError(f"Expected 4 oriented witnesses in catalog, found {len(witnesses)}")

    print("[Check 1/3] Auditing Critical K_43 Witnesses (Plain 2D Boolean 5-Nested Loops)...")
    for idx, (hdr, masks) in enumerate(witnesses):
        mat = masks_to_bool_matrix(43, masks)
        cliques = enumerate_monochromatic_k5_plain(43, mat)
        if len(cliques) != 2:
            raise AssertionError(f"Witness {idx} has {len(cliques)} monochromatic K_5s, expected 2!")

        col0, v0 = cliques[0]
        col1, v1 = cliques[1]
        if col0 != col1:
            raise AssertionError(f"Witness {idx} cliques do not have identical color: {col0} vs {col1}")

        spine = sorted(set(v0) & set(v1))
        poles = sorted(set(v0) ^ set(v1))
        if len(spine) != 4 or len(poles) != 2:
            raise AssertionError(f"Witness {idx} is not a 4-spine bi-pyramid: spine={spine}, poles={poles}")

        pole_edge = "RED" if mat[poles[0]][poles[1]] else "BLUE"
        if pole_edge == col0:
            raise AssertionError(f"Witness {idx} poles {poles} share clique color (would form K_6!)")

        auts = find_all_automorphisms(43, mat)
        if len(auts) < 2:
            raise AssertionError(f"Witness {idx} failed reflection symmetry check: |Aut|={len(auts)}")

        # Verify explicit non-trivial involution properties on G*_1 (idx=0) and G*_2 (idx=1)
        inv = [pi for pi in auts if pi != list(range(43))][0]
        fixed_pts = [u for u in range(43) if inv[u] == u]
        two_cycles = sum(1 for u in range(43) if u < inv[u] and inv[inv[u]] == u)
        if len(fixed_pts) != 1 or two_cycles != 21:
            raise AssertionError(f"Witness {idx} involution cycle structure unexpected: fixed={fixed_pts}")
        if inv[poles[0]] != poles[1]:
            raise AssertionError(f"Witness {idx} involution did not exchange poles {poles}!")

        red_edges = sum(sum(1 for x in row if x) for row in mat) // 2
        tag = " (G*_1)" if idx == 0 else (" (G*_2)" if idx == 1 else "")
        print(
            f"  Witness #{idx}{tag:7s}: PASS | E_K5 == 2 ({col0}) | edges={red_edges} | "
            f"spine={spine} | poles={poles} ({pole_edge}) | |Aut|={len(auts)} (fixed v={fixed_pts[0]})"
        )
    print(f"  -> Check 1 PASSED in {time.perf_counter() - t_cat:.2f}s.\n")

    # -----------------------------------------------------------------------
    # Check 2: k42_pool_656.txt (656 Zero-K5 Mothers & Non-Isomorphism)
    # -----------------------------------------------------------------------
    t_pool = time.perf_counter()
    pool = parse_pool_656(pool_path)
    if len(pool) != 656:
        raise AssertionError(f"Expected 656 mother graphs in k42_pool_656.txt, found {len(pool)}")

    print("[Check 2/3] Auditing All 656 (5, 5; 42) Mother Graphs (Zero-K5 & Pairwise Distinctness)...")
    buckets: Dict[str, List[Tuple[int, List[List[bool]], List[int]]]] = {}
    min_verified_ext = 999
    e_star_counts: Dict[int, int] = {}

    for gid, claimed_e_star, opt_m42, masks42 in pool:
        mat42 = masks_to_bool_matrix(42, masks42)
        if not has_zero_monochromatic_k5_plain(42, mat42):
            raise AssertionError(f"Mother GRAPH {gid} contains a monochromatic K_5!")

        # Also verify the stitched 43-vertex graph using opt_mask42 achieves claimed_e_star >= 2!
        masks43 = [masks42[u] | (((opt_m42 >> u) & 1) << 42) for u in range(42)] + [opt_m42]
        mat43 = masks_to_bool_matrix(43, masks43)
        ext_cliques = enumerate_monochromatic_k5_plain(43, mat43)
        if len(ext_cliques) != claimed_e_star:
            raise AssertionError(
                f"Mother GRAPH {gid} opt_mask42 yielded {len(ext_cliques)} K_5s, header claimed {claimed_e_star}"
            )
        min_verified_ext = min(min_verified_ext, len(ext_cliques))
        e_star_counts[claimed_e_star] = e_star_counts.get(claimed_e_star, 0) + 1

        sig, v_lab = compute_wl_signature(42, mat42, rounds=3)
        bucket = buckets.setdefault(sig, [])
        for prev_id, prev_mat, prev_lab in bucket:
            if are_isomorphic_exact(42, mat42, v_lab, prev_mat, prev_lab):
                raise AssertionError(f"Duplicate isomorphic mother graphs detected: #{gid} ~= #{prev_id}!")
        bucket.append((gid, mat42, v_lab))

    print(f"  Zero-K5 5-Loop Verification : 656 / 656 PASSED (100% strictly K_5-free)")
    print(f"  Distinct WL Invariant Hashes: {len(buckets)} / 656 unique (0 isomorphic collisions)")
    print(
        f"  Stitched opt_mask42 Audit   : 656 / 656 matched header E_K5^* "
        f"(min E_K5^* = {min_verified_ext}, count(E_K5^*=2) = {e_star_counts.get(2, 0)})"
    )
    print(f"  -> Check 2 PASSED in {time.perf_counter() - t_pool:.2f}s.\n")

    # -----------------------------------------------------------------------
    # Check 3: certificate_m55_43.lean Bit-for-Bit & Axiom Hygiene Audit
    # -----------------------------------------------------------------------
    t_lean = time.perf_counter()
    print("[Check 3/3] Auditing Lean 4 Certificate Bit-for-Bit Consistency & Axiom Hygiene...")
    lean_defs, clean_lean = parse_lean_adj_constants(lean_path)
    required_defs = ("M_42_A", "M_42_B", "G_star_1", "G_star_2")
    for name in required_defs:
        if name not in lean_defs:
            raise AssertionError(f"Missing definition `{name}` in {lean_path}")

    # Forbidden trust shortcuts in active (non-comment) Lean code
    for forbidden in (r"\bsorry\b", r"\badmit\b", r"\bnative_decide\b", r"\baxiom\b"):
        if re.search(forbidden, clean_lean):
            raise AssertionError(f"Forbidden token `{forbidden}` found in active Lean code!")

    if lean_defs["G_star_1"] != witnesses[0][1]:
        raise AssertionError("Bit mismatch between Lean `G_star_1` and catalog `WITNESS 0`!")
    if lean_defs["G_star_2"] != witnesses[1][1]:
        raise AssertionError("Bit mismatch between Lean `G_star_2` and catalog `WITNESS 1`!")

    pool_mask_map = {tuple(masks42): gid for gid, _, _, masks42 in pool}
    if tuple(lean_defs["M_42_A"]) not in pool_mask_map:
        raise AssertionError("Lean `M_42_A` not found bit-for-bit in k42_pool_656.txt!")
    if tuple(lean_defs["M_42_B"]) not in pool_mask_map:
        raise AssertionError("Lean `M_42_B` not found bit-for-bit in k42_pool_656.txt!")

    id_a = pool_mask_map[tuple(lean_defs["M_42_A"])]
    id_b = pool_mask_map[tuple(lean_defs["M_42_B"])]
    print(f"  Lean `G_star_1` (43x64 bits): 100% BIT-IDENTICAL to Catalog WITNESS 0 (G*_1)")
    print(f"  Lean `G_star_2` (43x64 bits): 100% BIT-IDENTICAL to Catalog WITNESS 1 (G*_2)")
    print(f"  Lean `M_42_A`   (42x64 bits): 100% BIT-IDENTICAL to k42_pool_656 GRAPH {id_a}")
    print(f"  Lean `M_42_B`   (42x64 bits): 100% BIT-IDENTICAL to k42_pool_656 GRAPH {id_b}")
    print("  Lean Trust Hygiene          : ZERO `sorry`, `admit`, `axiom`, or `native_decide`")
    print(f"  -> Check 3 PASSED in {time.perf_counter() - t_lean:.3f}s.\n")

    print("=" * 78)
    print(f"ALL REFEREE VERIFICATION CHECKS PASSED (Total Time: {time.perf_counter() - t0:.2f}s)")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
