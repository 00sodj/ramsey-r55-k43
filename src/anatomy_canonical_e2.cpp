// ============================================================================
// Stage 5 - Task 1: Algebraic & Combinatorial Anatomy of the 2 Canonical
// E_{K5} = 2 Critical Bi-Pyramid Witnesses (anatomy_canonical_e2.cpp)
// Single-File C++17, Zero External Dependencies
//
// Responsibilities:
//   1. Loads witness_k43_e2_catalog.txt (4 oriented witnesses -> 2 unoriented
//      canonical representatives G*_1 and G*_2 up to complementation G <-> ~G).
//   2. Verifies 100% via bitwise-free 5-nested-loop check (962,598 5-tuples)
//      and constructs explicit isomorphism bijections proving:
//        WITNESS 2 ~= complement(G*_1), WITNESS 3 ~= complement(G*_2),
//        and G*_1 !~= G*_2, G*_1 !~= complement(G*_2).
//   3. Exact Automorphism Group Aut(G*_i) via 1-WL color refinement + complete
//      S_43 backtracking: computes |Aut(G*_i)|, cycle decompositions, complete
//      vertex orbit partitions, and group action on the 4-clique spine W and
//      bi-pyramid poles {a, b}.
//   4. High-precision (long double) cyclic Jacobi eigenvalue solver: computes
//      exact spectra of A(G*_i), A(~G*_i), and Seidel matrix S(G*_i), cross-
//      checked against trace identities sum(lambda^2)=2|E|, sum(lambda^3)=6*K3.
//   5. Complete degree distribution, exact Red/Blue K3 & K4 counts, spine edge
//      saddle barrier anatomy, and exact dissection of all spine-punctured
//      42-vertex zero-K5 mother graphs (G*_i - w for w in W), including exact
//      isomorphism classes among punctured mothers.
//   6. Writes publication-grade report to canonical_e2_anatomy.txt.
// ============================================================================

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#if defined(_MSC_VER)
#include <intrin.h>
#endif

namespace anatomy_e2 {

static constexpr int N43 = 43;
static constexpr int N42 = 42;
static constexpr uint64_t MASK43 = (1ULL << N43) - 1ULL;
static constexpr uint64_t MASK42 = (1ULL << N42) - 1ULL;

[[nodiscard]] inline int popcnt64(uint64_t x) noexcept {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_popcountll(x);
#elif defined(_MSC_VER)
    return static_cast<int>(__popcnt64(x));
#else
    int c = 0; while (x) { x &= (x - 1ULL); ++c; } return c;
#endif
}

[[nodiscard]] inline int ctz64(uint64_t x) noexcept {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_ctzll(x);
#elif defined(_MSC_VER)
    unsigned long idx = 0; _BitScanForward64(&idx, x); return static_cast<int>(idx);
#else
    int c = 0; while ((x & 1ULL) == 0ULL) { x >>= 1; ++c; } return c;
#endif
}

// ----------------------------------------------------------------------------
// Pure Bitwise-Free 5-Nested-Loop Exact Verifiers (N=43 and N=42)
// ----------------------------------------------------------------------------
struct Clique5 {
    bool is_red;
    std::array<int, 5> v;
};

template<int N>
[[nodiscard]] int verify_exact_k5_plain(
    const std::array<uint64_t, N>& adj,
    std::vector<Clique5>& out_cliques) {

    std::array<std::array<bool, N>, N> E{};
    for (int u = 0; u < N; ++u) {
        uint64_t row = adj[u];
        for (int v = 0; v < N; ++v) {
            E[u][v] = (row % 2ULL != 0ULL);
            row /= 2ULL;
        }
    }

    out_cliques.clear();
    int count = 0;
    for (int a = 0; a < N - 4; ++a) {
        for (int b = a + 1; b < N - 3; ++b) {
            const bool ab = E[a][b];
            for (int c = b + 1; c < N - 2; ++c) {
                if (E[a][c] != ab || E[b][c] != ab) continue;
                for (int d = c + 1; d < N - 1; ++d) {
                    if (E[a][d] != ab || E[b][d] != ab || E[c][d] != ab) continue;
                    for (int e = d + 1; e < N; ++e) {
                        if (E[a][e] == ab && E[b][e] == ab && E[c][e] == ab && E[d][e] == ab) {
                            ++count;
                            if (out_cliques.size() < 32) {
                                out_cliques.push_back({ab, {a, b, c, d, e}});
                            }
                        }
                    }
                }
            }
        }
    }
    return count;
}

// ----------------------------------------------------------------------------
// Exact 1-WL Refinement + Backtracking Automorphism & Isomorphism Engine
// Guaranteed 100% exact over S_N (no heuristic approximations).
// ----------------------------------------------------------------------------
template<int N>
std::array<int, N> compute_1wl_colors(const std::array<uint64_t, N>& A) {
    static constexpr uint64_t VMASK = (1ULL << N) - 1ULL;
    std::array<uint64_t, N> CA{};
    for (int u = 0; u < N; ++u) CA[u] = (~A[u]) & VMASK & ~(1ULL << u);

    // Seed with (deg, local red triangles, local blue triangles)
    std::array<int, N> col{};
    std::vector<std::tuple<int, int, int>> init_sig(N);
    for (int u = 0; u < N; ++u) {
        int dr = popcnt64(A[u]);
        int tr = 0, tb = 0;
        uint64_t mr = A[u];
        while (mr) { int v = ctz64(mr); mr &= (mr - 1ULL); tr += popcnt64(A[v] & mr); }
        uint64_t mb = CA[u];
        while (mb) { int v = ctz64(mb); mb &= (mb - 1ULL); tb += popcnt64(CA[v] & mb); }
        init_sig[u] = {dr, tr, tb};
    }

    auto compress = [&](const auto& keys, std::array<int, N>& out_col) -> int {
        std::vector<int> ord(N);
        std::iota(ord.begin(), ord.end(), 0);
        std::sort(ord.begin(), ord.end(), [&](int a, int b) { return keys[a] < keys[b]; });
        int cid = 0;
        out_col[ord[0]] = 0;
        for (int i = 1; i < N; ++i) {
            if (keys[ord[i]] != keys[ord[i - 1]]) ++cid;
            out_col[ord[i]] = cid;
        }
        return cid + 1;
    };

    int num_classes = compress(init_sig, col);
    while (true) {
        std::vector<std::pair<int, std::vector<int>>> next_keys(N);
        for (int u = 0; u < N; ++u) {
            std::vector<int> mult(num_classes, 0);
            uint64_t m = A[u];
            while (m) {
                int v = ctz64(m); m &= (m - 1ULL);
                ++mult[col[v]];
            }
            next_keys[u] = {col[u], std::move(mult)};
        }
        std::array<int, N> ncol{};
        int next_classes = compress(next_keys, ncol);
        col = ncol;
        if (next_classes == num_classes) break;
        num_classes = next_classes;
    }
    return col;
}

// Compute canonical 1-WL signature shared identically by isomorphic graphs
template<int N>
std::vector<std::string> compute_joint_wl_labels(const std::array<uint64_t, N>& A) {
    static constexpr uint64_t VMASK = (1ULL << N) - 1ULL;
    std::array<uint64_t, N> CA{};
    for (int u = 0; u < N; ++u) CA[u] = (~A[u]) & VMASK & ~(1ULL << u);

    std::vector<std::string> lab(N);
    for (int u = 0; u < N; ++u) {
        int dr = popcnt64(A[u]);
        int tr = 0, tb = 0;
        uint64_t mr = A[u];
        while (mr) { int v = ctz64(mr); mr &= (mr - 1ULL); tr += popcnt64(A[v] & mr); }
        uint64_t mb = CA[u];
        while (mb) { int v = ctz64(mb); mb &= (mb - 1ULL); tb += popcnt64(CA[v] & mb); }
        lab[u] = std::to_string(dr) + ":" + std::to_string(tr) + ":" + std::to_string(tb);
    }

    for (int round = 0; round < 4; ++round) {
        std::vector<std::string> nlab(N);
        for (int u = 0; u < N; ++u) {
            std::vector<std::string> rn, bn;
            for (int v = 0; v < N; ++v) {
                if (v == u) continue;
                if ((A[u] >> v) & 1ULL) rn.push_back(lab[v]);
                else bn.push_back(lab[v]);
            }
            std::sort(rn.begin(), rn.end());
            std::sort(bn.begin(), bn.end());
            std::ostringstream oss;
            oss << lab[u] << "|R(";
            for (const auto& s : rn) oss << s << ",";
            oss << ")|B(";
            for (const auto& s : bn) oss << s << ",";
            oss << ")";
            nlab[u] = oss.str();
        }
        // Hash/compress strings only within G is NOT joint across two graphs unless we hash deterministically!
        // Use 64-bit FNV-1a + length pair string so labels remain short and deterministic across graphs!
        for (int u = 0; u < N; ++u) {
            uint64_t h1 = 14695981039346656037ULL;
            uint64_t h2 = 1099511628211ULL;
            for (unsigned char c : nlab[u]) {
                h1 ^= c; h1 *= 1099511628211ULL;
                h2 = (h2 * 1315423911ULL) ^ (c + 0x9e3779b97f4a7c15ULL);
            }
            std::ostringstream hs;
            hs << std::hex << h1 << "_" << h2;
            lab[u] = hs.str();
        }
    }
    return lab;
}

// Enumerate ALL isomorphisms pi: V(G1) -> V(G2) such that (u,v) in G1 <=> (pi[u], pi[v]) in G2.
// If stop_at_first == true, stops as soon as 1 isomorphism is found.
template<int N>
std::vector<std::array<int, N>> find_all_isomorphisms(
    const std::array<uint64_t, N>& G1,
    const std::array<uint64_t, N>& G2,
    bool stop_at_first = false) {

    std::vector<std::array<int, N>> results;
    const auto lab1 = compute_joint_wl_labels<N>(G1);
    const auto lab2 = compute_joint_wl_labels<N>(G2);

    // Check multiset equality of WL labels first
    auto s1 = lab1, s2 = lab2;
    std::sort(s1.begin(), s1.end());
    std::sort(s2.begin(), s2.end());
    if (s1 != s2) return results;

    // Candidate target vertices in G2 for each vertex u in G1
    std::array<std::vector<int>, N> cands{};
    for (int u = 0; u < N; ++u) {
        for (int v = 0; v < N; ++v) {
            if (lab1[u] == lab2[v]) cands[u].push_back(v);
        }
        if (cands[u].empty()) return results;
    }

    // Order vertices of G1 by smallest candidate list size first (fail-first branching)
    std::array<int, N> order{};
    std::iota(order.begin(), order.end(), 0);
    std::sort(order.begin(), order.end(), [&](int a, int b) {
        if (cands[a].size() != cands[b].size()) return cands[a].size() < cands[b].size();
        return a < b;
    });

    std::array<int, N> pi{};
    pi.fill(-1);
    uint64_t used_g2 = 0ULL;

    auto dfs = [&](auto& self, int depth) -> void {
        if (stop_at_first && !results.empty()) return;
        if (depth == N) {
            results.push_back(pi);
            return;
        }
        const int u = order[depth];
        for (int v : cands[u]) {
            if ((used_g2 >> v) & 1ULL) continue;
            // Check adjacency consistency with all previously mapped vertices
            bool ok = true;
            for (int d = 0; d < depth; ++d) {
                const int u_prev = order[d];
                const int v_prev = pi[u_prev];
                const bool e1 = ((G1[u] >> u_prev) & 1ULL) != 0ULL;
                const bool e2 = ((G2[v] >> v_prev) & 1ULL) != 0ULL;
                if (e1 != e2) { ok = false; break; }
            }
            if (!ok) continue;
            pi[u] = v;
            used_g2 |= (1ULL << v);
            self(self, depth + 1);
            used_g2 &= ~(1ULL << v);
            pi[u] = -1;
            if (stop_at_first && !results.empty()) return;
        }
    };

    dfs(dfs, 0);
    return results;
}

template<int N>
std::string format_cycle_decomposition(const std::array<int, N>& pi) {
    std::array<bool, N> vis{};
    std::ostringstream oss;
    int non_fixed = 0;
    for (int i = 0; i < N; ++i) {
        if (vis[i]) continue;
        if (pi[i] == i) { vis[i] = true; continue; }
        ++non_fixed;
        oss << "(";
        int cur = i;
        bool first = true;
        while (!vis[cur]) {
            vis[cur] = true;
            if (!first) oss << " ";
            first = false;
            oss << cur;
            cur = pi[cur];
        }
        oss << ")";
    }
    if (non_fixed == 0) return "id (identity)";
    return oss.str();
}

// ----------------------------------------------------------------------------
// High-Precision Cyclic Jacobi Symmetric Eigenvalue Solver (long double)
// Returns eigenvalues sorted descending: lambda_1 >= lambda_2 >= ... >= lambda_N
// ----------------------------------------------------------------------------
template<int N>
std::array<double, N> symmetric_eigenvalues_jacobi(
    std::array<std::array<long double, N>, N> M) {

    static constexpr int MAX_SWEEPS = 80;
    static constexpr long double EPS = 1e-15L;

    for (int sweep = 0; sweep < MAX_SWEEPS; ++sweep) {
        long double off_norm = 0.0L;
        for (int p = 0; p < N; ++p)
            for (int q = p + 1; q < N; ++q)
                off_norm += M[p][q] * M[p][q];
        if (std::sqrt(off_norm) < EPS) break;

        for (int p = 0; p < N - 1; ++p) {
            for (int q = p + 1; q < N; ++q) {
                const long double apq = M[p][q];
                if (std::abs(apq) < 1e-18L) continue;
                const long double app = M[p][p];
                const long double aqq = M[q][q];
                const long double tau = (aqq - app) / (2.0L * apq);
                const long double t = (tau >= 0.0L)
                    ? (1.0L / (tau + std::sqrt(1.0L + tau * tau)))
                    : (-1.0L / (-tau + std::sqrt(1.0L + tau * tau)));
                const long double c = 1.0L / std::sqrt(1.0L + t * t);
                const long double s = t * c;

                M[p][p] = app - t * apq;
                M[q][q] = aqq + t * apq;
                M[p][q] = M[q][p] = 0.0L;

                for (int r = 0; r < N; ++r) {
                    if (r == p || r == q) continue;
                    const long double mrp = M[r][p];
                    const long double mrq = M[r][q];
                    M[r][p] = M[p][r] = c * mrp - s * mrq;
                    M[r][q] = M[q][r] = s * mrp + c * mrq;
                }
            }
        }
    }

    std::array<double, N> evals{};
    for (int i = 0; i < N; ++i) evals[i] = static_cast<double>(M[i][i]);
    std::sort(evals.begin(), evals.end(), std::greater<double>());
    return evals;
}

// ----------------------------------------------------------------------------
// Subgraph Counters (Exact K3, K4, K5, vertex q4)
// ----------------------------------------------------------------------------
template<int N>
struct SubgraphStats {
    int32_t edges_red = 0;
    int32_t edges_blue = 0;
    int32_t k3_red = 0;
    int32_t k3_blue = 0;
    int32_t k3_mixed = 0;
    int32_t k4_red = 0;
    int32_t k4_blue = 0;
    int32_t k5_red = 0;
    int32_t k5_blue = 0;
    std::array<int32_t, N> deg_red{};
    std::array<int32_t, N> q4_red_v{};
    std::array<int32_t, N> q4_blue_v{};
    std::array<int32_t, N> q4_tot_v{};
    double q4_mean = 0.0;
    double q4_var = 0.0;
};

template<int N>
SubgraphStats<N> compute_subgraph_stats(const std::array<uint64_t, N>& adj) {
    static constexpr uint64_t VMASK = (1ULL << N) - 1ULL;
    std::array<uint64_t, N> cadj{};
    SubgraphStats<N> st{};

    int64_t RB_wedge = 0;
    for (int u = 0; u < N; ++u) {
        cadj[u] = (~adj[u]) & VMASK & ~(1ULL << u);
        st.deg_red[u] = popcnt64(adj[u]);
        st.edges_red += st.deg_red[u];
        RB_wedge += int64_t(st.deg_red[u]) * int64_t((N - 1) - st.deg_red[u]);
    }
    st.edges_red /= 2;
    st.edges_blue = (N * (N - 1) / 2) - st.edges_red;
    st.k3_mixed = static_cast<int32_t>(RB_wedge / 2);

    auto scan = [](const std::array<uint64_t, N>& G,
                   int32_t& c3, int32_t& c4, int32_t& c5,
                   std::array<int32_t, N>& q4v) {
        for (int u = 0; u < N; ++u) {
            uint64_t m1 = G[u] & ~((1ULL << (u + 1)) - 1ULL);
            while (m1) {
                const int v = ctz64(m1); m1 &= (m1 - 1ULL);
                const uint64_t n1 = G[u] & G[v];
                uint64_t m2 = n1 & m1;
                while (m2) {
                    const int w = ctz64(m2); m2 &= (m2 - 1ULL);
                    ++c3;
                    const uint64_t n2 = n1 & G[w];
                    uint64_t m3 = n2 & m2;
                    while (m3) {
                        const int x = ctz64(m3); m3 &= (m3 - 1ULL);
                        ++c4;
                        ++q4v[u]; ++q4v[v]; ++q4v[w]; ++q4v[x];
                        c5 += popcnt64(n2 & G[x] & m3);
                    }
                }
            }
        }
    };

    scan(adj,  st.k3_red,  st.k4_red,  st.k5_red,  st.q4_red_v);
    scan(cadj, st.k3_blue, st.k4_blue, st.k5_blue, st.q4_blue_v);

    double s1 = 0.0, s2 = 0.0;
    for (int u = 0; u < N; ++u) {
        st.q4_tot_v[u] = st.q4_red_v[u] + st.q4_blue_v[u];
        s1 += st.q4_tot_v[u];
        s2 += double(st.q4_tot_v[u]) * st.q4_tot_v[u];
    }
    st.q4_mean = s1 / N;
    st.q4_var  = s2 / N - st.q4_mean * st.q4_mean;
    return st;
}

// ----------------------------------------------------------------------------
// Load all 4 witnesses from witness_k43_e2_catalog.txt
// ----------------------------------------------------------------------------
struct CatalogWitness {
    int id = 0;
    std::string header;
    std::array<uint64_t, N43> adj{};
};

std::vector<CatalogWitness> load_catalog(const std::string& path) {
    std::ifstream ifs(path);
    std::vector<CatalogWitness> out;
    std::string line;
    CatalogWitness cur{};
    int row = 0;
    bool in_w = false;

    while (std::getline(ifs, line)) {
        const auto p = line.find_first_not_of(" \t\r\n");
        if (p == std::string::npos) continue;
        if (line.rfind("WITNESS ", p) == p) {
            cur = CatalogWitness{};
            cur.id = static_cast<int>(out.size());
            cur.header = line.substr(p);
            row = 0;
            in_w = true;
        } else if (in_w && (line.rfind("0x", p) == p || line.rfind("0X", p) == p)) {
            if (row < N43) {
                cur.adj[row++] = std::stoull(line.substr(p), nullptr, 16) & MASK43;
                if (row == N43) {
                    for (int u = 0; u < N43; ++u) cur.adj[u] &= ~(1ULL << u);
                    out.push_back(cur);
                    in_w = false;
                }
            }
        }
    }
    return out;
}

inline std::array<uint64_t, N43> complement_43(const std::array<uint64_t, N43>& A) {
    std::array<uint64_t, N43> C{};
    for (int u = 0; u < N43; ++u) C[u] = (~A[u]) & MASK43 & ~(1ULL << u);
    return C;
}

inline std::array<uint64_t, N42> puncture_vertex_43(const std::array<uint64_t, N43>& A, int drop_v) {
    std::array<uint64_t, N42> P{};
    for (int u = 0; u < N43; ++u) {
        if (u == drop_v) continue;
        const int mu = (u < drop_v) ? u : (u - 1);
        for (int v = u + 1; v < N43; ++v) {
            if (v == drop_v) continue;
            const int mv = (v < drop_v) ? v : (v - 1);
            if ((A[u] >> v) & 1ULL) {
                P[mu] |= (1ULL << mv);
                P[mv] |= (1ULL << mu);
            }
        }
    }
    return P;
}

} // namespace anatomy_e2

int main(int argc, char** argv) {
    using namespace anatomy_e2;
    const auto t0 = std::chrono::steady_clock::now();

    std::string cat_path = "witness_k43_e2_catalog.txt";
    if (!std::ifstream(cat_path).good() && std::ifstream("data/witness_k43_e2_catalog.txt").good()) {
        cat_path = "data/witness_k43_e2_catalog.txt";
    }
    std::string out_path = "canonical_e2_anatomy.txt";
    if (argc >= 2) cat_path = argv[1];
    if (argc >= 3) out_path = argv[2];

    const auto witnesses = load_catalog(cat_path);
    if (witnesses.size() < 4) {
        std::cerr << "Error: Expected 4 witnesses in " << cat_path
                  << ", found " << witnesses.size() << "\n";
        return 1;
    }

    // Verify all 4 witnesses via bitwise-free 5-nested-loop check
    for (const auto& w : witnesses) {
        std::vector<Clique5> cl;
        const int c5 = verify_exact_k5_plain<N43>(w.adj, cl);
        if (c5 != 2) {
            std::cerr << "FATAL: Witness " << w.id << " failed 5-loop check: c5=" << c5 << "\n";
            return 2;
        }
    }

    // Canonical unoriented representatives:
    //   G*_1 = WITNESS 0 (edges=449, 2Red_0Blue; complement is isomorphic to WITNESS 2)
    //   G*_2 = WITNESS 1 (edges=455, 2Red_0Blue; complement is isomorphic to WITNESS 3)
    const auto& G1 = witnesses[0].adj;
    const auto& G2 = witnesses[1].adj;
    const auto comp_G1 = complement_43(G1);
    const auto comp_G2 = complement_43(G2);

    const auto iso_cG1_W2 = find_all_isomorphisms<N43>(comp_G1, witnesses[2].adj, true);
    const auto iso_cG2_W3 = find_all_isomorphisms<N43>(comp_G2, witnesses[3].adj, true);
    const auto iso_G1_G2  = find_all_isomorphisms<N43>(G1, G2, true);
    const auto iso_G1_cG2 = find_all_isomorphisms<N43>(G1, comp_G2, true);

    std::ostringstream rep;
    rep << "================================================================================\n";
    rep << "STAGE 5 - TASK 1: ALGEBRAIC & COMBINATORIAL ANATOMY OF CANONICAL E_{K5}=2 GRAPHS\n";
    rep << "================================================================================\n\n";
    rep << "[0] CATALOG EQUIVALENCE & COMPLEMENTATION AUDIT\n";
    rep << "  - Bitwise-free 5-loop verification (962,598 5-tuples/graph): 4/4 PASSED (E_K5 == 2)\n";
    rep << "  - Exact Isomorphism Check ~G*_1 ~= WITNESS 2 : "
        << (!iso_cG1_W2.empty() ? "VERIFIED (Explicit bijection constructed)" : "FAILED") << "\n";
    rep << "  - Exact Isomorphism Check ~G*_2 ~= WITNESS 3 : "
        << (!iso_cG2_W3.empty() ? "VERIFIED (Explicit bijection constructed)" : "FAILED") << "\n";
    rep << "  - Exact Non-Isomorphism   G*_1 !~= G*_2      : "
        << (iso_G1_G2.empty() ? "PROVED (0 isomorphisms in S_43)" : "ISOMORPHIC?!") << "\n";
    rep << "  - Exact Non-Isomorphism   G*_1 !~= ~G*_2     : "
        << (iso_G1_cG2.empty() ? "PROVED (0 isomorphisms in S_43)" : "ISOMORPHIC?!") << "\n\n";

    struct PuncturedMother {
        std::string label;
        int rep_idx;
        int dropped_v;
        std::array<uint64_t, N42> adj;
        size_t aut_size;
        SubgraphStats<N42> st;
        double lambda1;
        double lambda2_abs;
        double lambda_min;
    };
    std::vector<PuncturedMother> all_punctured_mothers;

    const std::array<std::pair<std::string, std::array<uint64_t, N43>>, 2> reps = {{
        {"G*_1 (Canonical Class A, WITNESS 0 / best_v3_seed_301.txt)", G1},
        {"G*_2 (Canonical Class B, WITNESS 1 / best_v3_seed_302.txt)", G2}
    }};

    for (int r_idx = 0; r_idx < 2; ++r_idx) {
        const auto& name = reps[r_idx].first;
        const auto& A = reps[r_idx].second;
        const auto CA = complement_43(A);

        std::vector<Clique5> cl;
        (void)verify_exact_k5_plain<N43>(A, cl);
        const auto st = compute_subgraph_stats<N43>(A);
        const auto auts = find_all_isomorphisms<N43>(A, A, false);
        const auto anti_auts = find_all_isomorphisms<N43>(A, CA, false);

        // Extract bi-pyramid spine W and poles {a, b}
        std::set<int> s0(cl[0].v.begin(), cl[0].v.end());
        std::set<int> s1(cl[1].v.begin(), cl[1].v.end());
        std::vector<int> spine, poles;
        for (int v : s0) {
            if (s1.count(v)) spine.push_back(v);
            else poles.push_back(v);
        }
        for (int v : s1) {
            if (!s0.count(v)) poles.push_back(v);
        }

        // Compute vertex orbits under Aut(G*_i)
        std::array<bool, N43> vis_orb{};
        std::vector<std::vector<int>> orbits;
        std::map<int, int> orbit_size_hist;
        std::array<int, N43> v_to_orb{};
        for (int u = 0; u < N43; ++u) {
            if (vis_orb[u]) continue;
            std::set<int> orb;
            for (const auto& pi : auts) orb.insert(pi[u]);
            std::vector<int> ov(orb.begin(), orb.end());
            const int oid = static_cast<int>(orbits.size());
            for (int x : ov) { vis_orb[x] = true; v_to_orb[x] = oid; }
            ++orbit_size_hist[static_cast<int>(ov.size())];
            orbits.push_back(std::move(ov));
        }

        // Eigenvalue spectra: A(G), A(~G), and Seidel matrix S = J - I - 2A
        std::array<std::array<long double, N43>, N43> matA{}, matCA{}, matSeidel{};
        for (int u = 0; u < N43; ++u) {
            for (int v = 0; v < N43; ++v) {
                if (u == v) continue;
                const bool r = ((A[u] >> v) & 1ULL) != 0ULL;
                matA[u][v] = r ? 1.0L : 0.0L;
                matCA[u][v] = r ? 0.0L : 1.0L;
                matSeidel[u][v] = r ? -1.0L : 1.0L;
            }
        }
        const auto eigA = symmetric_eigenvalues_jacobi<N43>(matA);
        const auto eigCA = symmetric_eigenvalues_jacobi<N43>(matCA);
        const auto eigS = symmetric_eigenvalues_jacobi<N43>(matSeidel);

        double tr1 = 0.0, tr2 = 0.0, tr3 = 0.0;
        double max_nontriv_abs = 0.0;
        for (int i = 0; i < N43; ++i) {
            tr1 += eigA[i];
            tr2 += eigA[i] * eigA[i];
            tr3 += eigA[i] * eigA[i] * eigA[i];
            if (i >= 1) max_nontriv_abs = std::max(max_nontriv_abs, std::abs(eigA[i]));
        }

        rep << "================================================================================\n";
        rep << "[" << (r_idx + 1) << "] CANONICAL REPRESENTATIVE " << name << "\n";
        rep << "================================================================================\n";

        rep << "\n  1.1 Exact Automorphism Group & Orbit Decomposition:\n";
        rep << "      |Aut(G)| (color-preserving)        = " << auts.size() << "\n";
        rep << "      |AntiAut(G)| (G -> ~G)             = " << anti_auts.size()
            << " (since |E_R|=" << st.edges_red << " != |E_B|=" << st.edges_blue << ")\n";
        rep << "      |Aut^pm(G)| (full group)           = " << (auts.size() + anti_auts.size()) << "\n";
        rep << "      Group elements in cycle notation:\n";
        for (size_t gi = 0; gi < auts.size(); ++gi) {
            rep << "        g_" << gi << " = " << format_cycle_decomposition<N43>(auts[gi]) << "\n";
        }
        rep << "      Total Vertex Orbits                = " << orbits.size() << " (";
        bool first_h = true;
        for (const auto& [sz, cnt] : orbit_size_hist) {
            if (!first_h) rep << ", ";
            first_h = false;
            rep << cnt << " orbit(s) of size " << sz;
        }
        rep << ")\n";
        rep << "      Explicit Orbit Partition of V_43:\n        ";
        for (size_t oi = 0; oi < orbits.size(); ++oi) {
            rep << "{";
            for (size_t k = 0; k < orbits[oi].size(); ++k)
                rep << orbits[oi][k] << (k + 1 < orbits[oi].size() ? "," : "");
            rep << "}" << (oi + 1 < orbits.size() ? " " : "");
            if ((oi + 1) % 10 == 0 && oi + 1 < orbits.size()) rep << "\n        ";
        }
        rep << "\n";

        rep << "\n  1.2 Bi-Pyramid Core Topology & Group Action on W and {a, b}:\n";
        rep << "      Monochromatic K5 #0 [" << (cl[0].is_red ? "RED" : "BLUE") << "] : {"
            << cl[0].v[0] << "," << cl[0].v[1] << "," << cl[0].v[2] << "," << cl[0].v[3] << "," << cl[0].v[4] << "}\n";
        rep << "      Monochromatic K5 #1 [" << (cl[1].is_red ? "RED" : "BLUE") << "] : {"
            << cl[1].v[0] << "," << cl[1].v[1] << "," << cl[1].v[2] << "," << cl[1].v[3] << "," << cl[1].v[4] << "}\n";
        rep << "      Shared 4-Clique Spine W            : {"
            << spine[0] << ", " << spine[1] << ", " << spine[2] << ", " << spine[3] << "} (|W| = 4)\n";
        rep << "      Bi-Pyramid Poles {a, b}            : a = " << poles[0] << ", b = " << poles[1]
            << " | edge (a,b) color = " << (((A[poles[0]] >> poles[1]) & 1ULL) ? "RED" : "BLUE (opposite!)") << "\n";
        rep << "      Symmetry Action on Spine W         :\n";
        for (int w : spine) {
            rep << "        v=" << std::setw(2) << w << " -> Orbit #" << std::setw(2) << v_to_orb[w]
                << " {";
            const auto& ob = orbits[v_to_orb[w]];
            for (size_t k = 0; k < ob.size(); ++k) rep << ob[k] << (k + 1 < ob.size() ? "," : "");
            rep << "} (deg_R=" << st.deg_red[w] << ", q4=" << st.q4_tot_v[w] << ")\n";
        }
        rep << "      Symmetry Action on Poles {a, b}    :\n";
        for (int p : poles) {
            rep << "        pole=" << std::setw(2) << p << " -> Orbit #" << std::setw(2) << v_to_orb[p]
                << " {";
            const auto& ob = orbits[v_to_orb[p]];
            for (size_t k = 0; k < ob.size(); ++k) rep << ob[k] << (k + 1 < ob.size() ? "," : "");
            rep << "} (deg_R=" << st.deg_red[p] << ", q4=" << st.q4_tot_v[p] << ")\n";
        }
        const bool poles_swapped = (v_to_orb[poles[0]] == v_to_orb[poles[1]]);
        rep << "      Pole-Exchange Symmetry Conclusion  : "
            << (poles_swapped
                ? "Poles a and b lie in the SAME Aut-orbit (an involution swaps C_0 <-> C_1!)."
                : "Poles a and b lie in DISTINCT singleton orbits (|Aut|=1 asymmetric locking!).") << "\n";

        // Spine 6-edge barrier table
        rep << "      6 Spine Edges Saddle Barrier Profile (flipping RED -> BLUE):\n";
        for (int i = 0; i < 4; ++i) {
            for (int j = i + 1; j < 4; ++j) {
                const int u = spine[i], v = spine[j];
                uint64_t M_opp = CA[u] & CA[v];
                int opp_born = 0;
                uint64_t r1 = M_opp;
                while (r1) {
                    int x = ctz64(r1); r1 &= (r1 - 1ULL);
                    uint64_t r2 = CA[x] & r1;
                    while (r2) { int y = ctz64(r2); r2 &= (r2 - 1ULL); opp_born += popcnt64(CA[y] & r2); }
                }
                rep << "        spine_edge (" << std::setw(2) << u << "," << std::setw(2) << v
                    << ") : destroys=2 RED K5 | creates=" << opp_born
                    << " BLUE K5 | net_dC5 = " << std::showpos << (opp_born - 2) << std::noshowpos
                    << (opp_born == 2 ? "  <-- ZERO-BARRIER SADDLE!" : "") << "\n";
            }
        }

        // Degree & Subgraph Distributions
        std::map<int, int> deg_hist;
        std::array<int32_t, N43> sorted_deg = st.deg_red;
        std::sort(sorted_deg.begin(), sorted_deg.end());
        for (int d : sorted_deg) ++deg_hist[d];

        rep << "\n  1.3 Complete Degree Sequence & Exact Subgraph Census:\n";
        rep << "      Edges (Red / Blue / Total)         : " << st.edges_red << " / " << st.edges_blue << " / 903\n";
        rep << "      Red Degree Distribution            :";
        for (const auto& [d, cnt] : deg_hist) rep << " deg_" << d << "=" << cnt;
        rep << "\n      Full Sorted Red Degree Sequence    : [";
        for (int i = 0; i < N43; ++i) rep << sorted_deg[i] << (i + 1 < N43 ? "," : "");
        rep << "]\n";
        rep << "      Exact Triangle (K3) Census         : Red K3 = " << st.k3_red
            << ", Blue K3 = " << st.k3_blue
            << ", Monochromatic K3 = " << (st.k3_red + st.k3_blue)
            << ", 2-Colored K3 = " << st.k3_mixed
            << " (Sum = " << (st.k3_red + st.k3_blue + st.k3_mixed) << " == C(43,3) = 12341)\n";
        rep << "      Exact 4-Clique (K4) Census         : Red K4 = " << st.k4_red
            << ", Blue K4 = " << st.k4_blue
            << ", Total Monochromatic K4 = " << (st.k4_red + st.k4_blue) << "\n";

        auto qmin = *std::min_element(st.q4_tot_v.begin(), st.q4_tot_v.end());
        auto qmax = *std::max_element(st.q4_tot_v.begin(), st.q4_tot_v.end());
        rep << "      Vertex K4 Load q4(v) Profile       : min = " << qmin
            << ", max = " << qmax
            << ", mean = " << std::fixed << std::setprecision(4) << st.q4_mean
            << ", Var(q4) = " << std::setprecision(4) << st.q4_var << "\n";

        // Eigenvalue Spectrum
        rep << "\n  1.4 Adjacency & Seidel Eigenvalue Spectrum (Cyclic Jacobi, 1e-15 precision):\n";
        rep << "      Perron-Frobenius Spectral Radius   : lambda_1(A) = " << std::fixed << std::setprecision(8) << eigA[0] << "\n";
        rep << "      2nd Largest / Smallest Eigenvalue  : lambda_2(A) = " << eigA[1]
            << ", lambda_43(A) = " << eigA[N43 - 1] << "\n";
        rep << "      Max Non-Trivial |lambda_j(A)|      : lambda_max_2 = " << max_nontriv_abs
            << " (Paley-43 benchmark sqrt(43)/2 = " << (std::sqrt(43.0) / 2.0) << ")\n";
        rep << "      Complement Spectral Extremes       : lambda_1(~A) = " << eigCA[0]
            << ", lambda_2(~A) = " << eigCA[1] << ", lambda_43(~A) = " << eigCA[N43 - 1] << "\n";
        rep << "      Seidel Matrix S = J - I - 2A Range : mu_1(S) = " << eigS[0]
            << ", mu_43(S) = " << eigS[N43 - 1] << "\n";
        rep << "      Spectral Moment Cross-Checks       : Tr(A) = " << std::setprecision(6) << tr1
            << " (exact 0), Tr(A^2)/2 = " << (tr2 / 2.0) << " (exact " << st.edges_red
            << "), Tr(A^3)/6 = " << (tr3 / 6.0) << " (exact " << st.k3_red << ")\n";
        rep << "      All 43 Eigenvalues of A(G) (descending):\n";
        for (int i = 0; i < N43; ++i) {
            if (i % 6 == 0) rep << "        ";
            rep << std::setw(11) << std::fixed << std::setprecision(6) << eigA[i]
                << ((i + 1 < N43 && (i + 1) % 6 != 0) ? ", " : "");
            if ((i + 1) % 6 == 0 || i + 1 == N43) rep << "\n";
        }

        // Punctured 42-Vertex Zero-K5 Mother Graphs
        rep << "\n  1.5 Spine-Punctured 42-Vertex Zero-K5 Mother Graphs (G - w for w in W):\n";
        int c5_0_cnt = 0, c5_1_cnt = 0, c5_2_cnt = 0;
        for (int v = 0; v < N43; ++v) {
            auto pv = puncture_vertex_43(A, v);
            std::vector<Clique5> pcl;
            int pc = verify_exact_k5_plain<N42>(pv, pcl);
            if (pc == 0) ++c5_0_cnt;
            else if (pc == 1) ++c5_1_cnt;
            else ++c5_2_cnt;
        }
        rep << "      All 43 Single-Vertex Deletions     : E_K5=0 on " << c5_0_cnt
            << " vertices (== 4 spine vertices W), E_K5=1 on " << c5_1_cnt
            << " vertices (== 2 poles), E_K5=2 on " << c5_2_cnt << " vertices\n";

        for (int w : spine) {
            const auto P = puncture_vertex_43(A, w);
            std::vector<Clique5> pcl;
            const int pc = verify_exact_k5_plain<N42>(P, pcl);
            if (pc != 0) {
                std::cerr << "FATAL: Spine puncture had K5 != 0!\n";
                return 3;
            }
            const auto pst = compute_subgraph_stats<N42>(P);
            const auto pauts = find_all_isomorphisms<N42>(P, P, false);

            std::array<std::array<long double, N42>, N42> matP{};
            for (int u = 0; u < N42; ++u)
                for (int v = 0; v < N42; ++v)
                    if (u != v && ((P[u] >> v) & 1ULL)) matP[u][v] = 1.0L;
            const auto peig = symmetric_eigenvalues_jacobi<N42>(matP);
            double p_l2 = 0.0;
            for (int i = 1; i < N42; ++i) p_l2 = std::max(p_l2, std::abs(peig[i]));

            std::map<int, int> pdeg_hist;
            for (int d : pst.deg_red) ++pdeg_hist[d];

            std::ostringstream dstr;
            for (const auto& [d, cnt] : pdeg_hist) dstr << "d" << d << ":" << cnt << " ";

            rep << "        [G_" << (r_idx + 1) << " - v" << std::setw(2) << w << "] "
                << "5-Loop E_K5=0 PASS | |Aut|=" << pauts.size()
                << " | edges=" << pst.edges_red
                << " | deg={" << dstr.str() << "}"
                << "| K3=(" << pst.k3_red << "," << pst.k3_blue << ")"
                << " | K4=(" << pst.k4_red << "," << pst.k4_blue << ")"
                << " | lambda_1=" << std::fixed << std::setprecision(5) << peig[0]
                << ", max|lambda_j|=" << p_l2 << "\n";

            all_punctured_mothers.push_back({
                "G*_" + std::to_string(r_idx + 1) + " - v_" + std::to_string(w),
                r_idx + 1, w, P, pauts.size(), pst, peig[0], p_l2, peig[N42 - 1]
            });
        }
        rep << "\n";
    }

    // Cross-isomorphism classification among the 8 spine-punctured 42-vertex mother graphs
    std::vector<int> p_class(all_punctured_mothers.size(), -1);
    int num_oriented_p = 0;
    for (size_t i = 0; i < all_punctured_mothers.size(); ++i) {
        if (p_class[i] != -1) continue;
        p_class[i] = num_oriented_p++;
        for (size_t j = i + 1; j < all_punctured_mothers.size(); ++j) {
            if (p_class[j] != -1) continue;
            if (!find_all_isomorphisms<N42>(all_punctured_mothers[i].adj, all_punctured_mothers[j].adj, true).empty()) {
                p_class[j] = p_class[i];
            }
        }
    }

    std::vector<int> p_unoriented_class(all_punctured_mothers.size(), -1);
    int num_unoriented_p = 0;
    for (size_t i = 0; i < all_punctured_mothers.size(); ++i) {
        if (p_unoriented_class[i] != -1) continue;
        p_unoriented_class[i] = num_unoriented_p++;
        std::array<uint64_t, N42> comp_i{};
        for (int u = 0; u < N42; ++u) comp_i[u] = (~all_punctured_mothers[i].adj[u]) & MASK42 & ~(1ULL << u);
        for (size_t j = i + 1; j < all_punctured_mothers.size(); ++j) {
            if (p_unoriented_class[j] != -1) continue;
            if (!find_all_isomorphisms<N42>(all_punctured_mothers[i].adj, all_punctured_mothers[j].adj, true).empty() ||
                !find_all_isomorphisms<N42>(comp_i, all_punctured_mothers[j].adj, true).empty()) {
                p_unoriented_class[j] = p_unoriented_class[i];
            }
        }
    }

    rep << "================================================================================\n";
    rep << "[3] CROSS-ISOMORPHISM CLASSIFICATION OF THE 8 SPINE-PUNCTURED (5,5; 42) MOTHERS\n";
    rep << "================================================================================\n";
    rep << "  - Distinct Oriented (5,5; 42) Isomorphism Classes   : " << num_oriented_p << " / 8\n";
    rep << "  - Distinct Unoriented (up to G <-> ~G) Classes      : " << num_unoriented_p << " / 8\n";
    for (size_t i = 0; i < all_punctured_mothers.size(); ++i) {
        rep << "    * " << std::setw(14) << std::left << all_punctured_mothers[i].label << std::right
            << " -> Oriented Class #" << p_class[i]
            << ", Unoriented Class #" << p_unoriented_class[i]
            << " (|Aut|=" << all_punctured_mothers[i].aut_size
            << ", edges=" << all_punctured_mothers[i].st.edges_red
            << ", K4=" << all_punctured_mothers[i].st.k4_red << "/" << all_punctured_mothers[i].st.k4_blue << ")\n";
    }

    const double elapsed_ms = std::chrono::duration<double, std::milli>(
        std::chrono::steady_clock::now() - t0).count();
    rep << "\nCompleted exact anatomy in " << std::fixed << std::setprecision(2) << elapsed_ms << " ms.\n";

    std::ofstream ofs(out_path, std::ios::out | std::ios::trunc);
    ofs << rep.str();
    ofs.close();

    std::cout << rep.str();
    return 0;
}
