==============================================================================
ANCILLARY DATA & VERIFICATION GUIDE FOR ARXIV SUBMISSION (anc/README_DATA.txt)
==============================================================================

Paper Title : Critical Bi-Pyramid Rigidity, Exact 42-Bit Hypergraph Stitching
              over the 656 (5,5;42) Catalog, and Formal Certification of
              M(5,5;43) <= 2
Author      : Zihan Yin (University of Electronic Science and Technology of China)
MSC 2020    : 05C55, 05D10 (Primary); 68V15, 68R10 (Secondary)

1. OVERVIEW OF COMPANION REPRODUCIBILITY ARTIFACTS
------------------------------------------------------------------------------
The full reproducibility archive (also available at https://github.com/00sodj/ramsey-r55-k43)
provides three independent layers of machine verification:

  (a) Pure Python 3 Referee Verifier (`verify_standalone.py`):
      Uses ONLY the Python 3 standard library (zero external packages). In ~11
      seconds on a standard laptop/desktop, it independently verifies via plain
      2D boolean 5-nested loops:
        - `witness_k43_e2_catalog.txt`: all 4 oriented (2 unoriented: G*_1, G*_2)
          43-vertex critical colorings have exactly 2 monochromatic K_5s forming
          a 4-spine bi-pyramid (K_6 - e) with |Aut(G)| = 2;
        - `k42_pool_656.txt`: all 656 oriented (328 unoriented) (5,5;42) mother
          graphs satisfy E_{K5}(G_42) = 0, possess 656 pairwise distinct 3-round
          Weisfeiler-Leman invariants, and achieve their claimed E_{K5}^* >= 2;
        - `certificate_m55_43.lean`: hardcoded hexadecimal matrices match the
          catalog files 100% bit-for-bit with zero `sorry` or `native_decide`.

  (b) Zero-Dependency Lean 4 Kernel Certificate (`certificate_m55_43.lean`):
      Verified with `leanprover/lean4:v4.36.0` in 34.08 s (`lean certificate_m55_43.lean`)
      using pure kernel definitional reduction (`by rfl`, zero external libraries,
      zero `sorryAx`, zero `Lean.ofReduceBool`), certifying `R(5,5) > 42` and
      `M(5,5;43) <= 2`.

  (c) Single-File C++17 Proof Engines (`src/*.cpp`):
      - `anatomy_canonical_e2.cpp`: exact S_43 automorphism/isomorphism & Jacobi
        eigenvalue dissection (`canonical_e2_anatomy.txt`);
      - `prove_local_rigidity.cpp`: exact k=22 (2^231) SAC-B&B & 252,083,534-state
        bounded Hamming ball rigidity prover (`local_rigidity_proof_log.txt`);
      - `census_k42_656.cpp`: 656-class (5,5;42) census & zero-cutoff 42-bit
        hypergraph B&B stitcher (`census_k42_656_report.txt`).

2. DATA ENCODING FORMAT
------------------------------------------------------------------------------
Each n-vertex 2-edge-coloring (n = 42 or n = 43) is stored as n lines of 64-bit
hexadecimal integers `0x...` (rows u = 0 .. n-1). Bit v of row u is 1 iff edge
{u, v} is colored Red, and 0 (for v != u) iff edge {u, v} is colored Blue.
