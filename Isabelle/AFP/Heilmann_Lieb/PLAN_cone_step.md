# Plan for `cone_step` (analytic core of Heilmann–Lieb in Isabelle)

Statement (Interlacing.thy): if `in_cone S rs`, then there is `ts` with `length ts = Suc (length rs)`,
`[:0,1:] * lin_prod rs - S = lin_prod ts` and `in_cone (lin_prod rs) ts`.

Write P = lin_prod rs = ∏(x − r_i), S = Σ_i c_i P_i with P_i = lin_prod (omit i rs), c_i ≥ 0, Q = x·P − S.

## Step A — reduction to simple poles with positive weights
1. Group equal roots: let s_1 < … < s_k be the distinct roots in rs, with multiplicities m_j, and C_j = Σ_{i : r_i = s_j} c_i ≥ 0.
   Then S = Σ_j C_j · P / (x − s_j), where P/(x − s_j) = lin_prod (remove1 s_j rs).
2. Let J = {j : C_j > 0} and P1 = ∏_{j∈J} (x − s_j), and let R = lin_prod (rs minus one copy of each s_j, j ∈ J), so that
   P = R · P1. Then S = R · S1 with S1 = Σ_{j∈J} C_j P1/(x − s_j), and Q = R · Q1 with Q1 = x·P1 − S1.

## Step B — the simple case (distinct poles s_1 < … < s_k, all C_j > 0)
3. Q1 is monic of degree k + 1.
4. Signs: Q1(s_j) = −C_j · ∏_{l≠j}(s_j − s_l), whose sign is (−1)^{k−j+1}, since ∏_{l≠j}(s_j − s_l) has sign (−1)^{k−j}.
   Q1(x) → +∞ as x → +∞ (monic), and Q1 has sign (−1)^{k+1} for x → −∞.
5. By the intermediate value theorem (`poly_IVT_pos` / `poly_IVT_neg`), Q1 has a root t_0 < s_1, a root t_j in each interval (s_j, s_{j+1}),
   and a root t_k > s_k. These k + 1 roots are distinct and the degree is k + 1, so Q1 = ∏_{l=0}^{k} (x − t_l).
6. Lagrange: P1 has degree k < k + 1 = deg Q1 and the t_l are distinct, so P1 = Σ_l d_l · Q1/(x − t_l) with
   d_l = P1(t_l) / Q1'(t_l) = P1(t_l) / ∏_{m≠l}(t_l − t_m).
7. d_l ≥ 0: P1(t_l) has sign (−1)^{k−l} (exactly k − l of the s_j lie above t_l), and ∏_{m≠l}(t_l − t_m) has sign (−1)^{k−l}.

## Step C — back to the general case
8. ts = (roots of R) @ [t_0, …, t_k]: length = (length rs − |J|) + |J| + 1 = length rs + 1, and Q = R·Q1 = lin_prod ts.
9. P = R·P1 = Σ_l d_l · R·Q1/(x − t_l): this is in the cone of ts, with coefficient d_l on the factor omitting t_l and 0 on
   the factors omitting a root of R. Use `in_cone_perm` to put ts in any order.
10. Degenerate case J = ∅ (S = 0): Q = x·P, ts = 0 # rs, and P = Q/(x − 0) is in the cone (coefficient 1 on the omitted 0).

## Suggested lemmas for the agents (each one small)
- `lagrange_cone`: for distinct ts and a polynomial p with degree p < length ts, p = Σ_l (poly p t_l / ∏_{m≠l}(t_l − t_m)) · lin_prod (omit l ts).
- `sign_prod_sub`: the sign of ∏_{l≠j}(s_j − s_l) for a strictly sorted list.
- `simple_case`: Step B for a strictly sorted list s with positive weights C.
- `group_roots`: Step A, S as a combination over the distinct roots.
- `cone_step`: assembly of A, B and C.
