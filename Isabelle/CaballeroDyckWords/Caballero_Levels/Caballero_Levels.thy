(*  Title:      Caballero_Levels.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Marín, paper II on Rodríguez Caballero's parenthesis problem (in preparation), Proposition 8.x (prop:levels):
   for a non-decreasing vector c = (c_{-a}, ..., c_a) with 0 <= c_h <= b, the generating polynomial of the
   deficits T - H_i(j) multiplied by Q is a sum of clusters.

   Q is kept abstract: an element of a commutative ring with R_s (1 - z^s) = Q for 1 <= s <= a+1 (in the paper,
   Q is the product of the cyclotomic polynomials Phi_d, d <= a+1, and R_s = Q/(1-z^s)). The identity holds for any
   such triple.
*)
theory Caballero_Levels
  imports Complex_Main
begin

section \<open>Exponents and one geometric segment\<close>

text \<open>z^k for an integer exponent (only used with k >= 0).\<close>
definition zi :: "'a::comm_ring_1 \<Rightarrow> int \<Rightarrow> 'a" where
  "zi z k = z ^ nat k"

lemma zi_add: "0 \<le> k \<Longrightarrow> 0 \<le> l \<Longrightarrow> zi z (k + l) = zi z k * zi z l"
  by (simp add: zi_def nat_add_distrib power_add)

lemma zi_nat: "zi z (int s) = z ^ s"
  by (simp add: zi_def)

lemma sum_snoc_int:
  fixes g :: "int \<Rightarrow> 'b::comm_monoid_add"
  assumes "l \<le> u + 1"
  shows "sum g {l..u + 1} = sum g {l..u} + g (u + 1)"
proof -
  have "{l..u + 1} = insert (u + 1) {l..u}" using assms by auto
  then show ?thesis by (simp add: add.commute)
qed

text \<open>A segment of slope s starting at exponent E: Q times the geometric sum is R (z^(E+s) - z^(E+s k+s)).\<close>
lemma segment:
  fixes z Q R :: "'a::comm_ring_1" and s :: nat and E p :: int
  assumes RQ: "R * (1 - z ^ s) = Q" and E: "0 \<le> E"
  shows "Q * (\<Sum>y = p + 1..p + int k. zi z (E + int s * (y - p)))
      = R * (zi z (E + int s) - zi z (E + int s * int k + int s))"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have s0: "0 \<le> int s" by simp
  let ?g = "\<lambda>y. zi z (E + int s * (y - p))"
  have sn: "sum ?g {p + 1..p + int k + 1} = sum ?g {p + 1..p + int k} + ?g (p + int k + 1)"
    by (rule sum_snoc_int) simp
  have rg: "{p + 1..p + int (Suc k)} = {p + 1..p + int k + 1}" by (simp add: algebra_simps)
  have g1: "?g (p + int k + 1) = zi z (E + int s * (int k + 1))" by (simp add: algebra_simps)
  have "Q * sum ?g {p + 1..p + int (Suc k)}
      = Q * sum ?g {p + 1..p + int k} + Q * zi z (E + int s * (int k + 1))"
    using sn rg g1 by (simp add: algebra_simps)
  also have "Q * sum ?g {p + 1..p + int k}
      = R * (zi z (E + int s) - zi z (E + int s * int k + int s))" using Suc by simp
  finally have X: "Q * sum ?g {p + 1..p + int (Suc k)}
      = R * (zi z (E + int s) - zi z (E + int s * int k + int s)) + Q * zi z (E + int s * (int k + 1))" .
  have Y: "R * (zi z (E + int s) - zi z (E + int s * int k + int s)) + Q * zi z (E + int s * (int k + 1))
      = R * (zi z (E + int s) - zi z (E + int s * int (Suc k) + int s))"
  proof -
    let ?e = "E + int s * int k + int s"
    have e1: "E + int s * (int k + 1) = ?e" by (simp add: algebra_simps)
    have e2: "E + int s * int (Suc k) + int s = ?e + int s" by (simp add: algebra_simps)
    have pos: "0 \<le> ?e" using E by simp
    have z2: "zi z (?e + int s) = zi z ?e * z ^ s" using zi_add[OF pos s0, of z] by (simp only: zi_nat)
    show ?thesis unfolding e1 e2 z2 by (subst RQ[symmetric]) (simp add: algebra_simps)
  qed
  show ?case using X Y by simp
qed

section \<open>One row: the deficit function and its kinks\<close>

text \<open>Psi y = sum_{r=0}^{a} (y - q_r)_+ with q_r = c_{i-a+r} - c_{i-a}, as in the proof of the paper.\<close>
definition Psi :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int" where
  "Psi a q y = (\<Sum>r = 0..a. max 0 (y - q r))"

text \<open>B_r = z^(r+1) R_(r+1) - z^r R_r.\<close>
definition Bcl :: "'a::comm_ring_1 \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "Bcl z R r = z ^ (r + 1) * R (r + 1) - z ^ r * R r"

locale row =
  fixes a :: nat and q :: "nat \<Rightarrow> int" and z Q :: "'a::comm_ring_1" and R :: "nat \<Rightarrow> 'a"
  assumes RQ: "\<And>s. 1 \<le> s \<Longrightarrow> s \<le> a + 1 \<Longrightarrow> R s * (1 - z ^ s) = Q"
    and q0: "q 0 = 0"
    and qmono: "\<And>r s. r \<le> s \<Longrightarrow> s \<le> a \<Longrightarrow> q r \<le> q s"
begin

lemma q_nonneg: "r \<le> a \<Longrightarrow> 0 \<le> q r"
  using qmono[of 0 r] q0 by simp

lemma Psi_lin:
  assumes k: "k \<le> a" and y1: "q k \<le> y" and y2: "k < a \<Longrightarrow> y \<le> q (k + 1)"
  shows "Psi a q y = (\<Sum>r = 0..k. y - q r)"
proof -
  have split: "{0..a} = {0..k} \<union> {k + 1..a}" using k by auto
  have dis: "{0..k} \<inter> {k + 1..a} = {}" by auto
  have A: "(\<Sum>r = 0..k. max 0 (y - q r)) = (\<Sum>r = 0..k. y - q r)"
  proof (rule sum.cong[OF refl])
    fix r assume r: "r \<in> {0..k}"
    then have "q r \<le> q k" using qmono[of r k] k by simp
    then show "max 0 (y - q r) = y - q r" using y1 by simp
  qed
  have B: "(\<Sum>r = k + 1..a. max 0 (y - q r)) = 0"
  proof (intro sum.neutral ballI)
    fix r assume r: "r \<in> {k + 1..a}"
    then have "k < a" by simp
    then have "y \<le> q (k + 1)" using y2 by simp
    also have "q (k + 1) \<le> q r" using qmono[of "k + 1" r] r by simp
    finally have yr: "y \<le> q r" .
    show "max 0 (y - q r) = 0" using yr by (auto simp: max_def)
  qed
  have U: "(\<Sum>r \<in> {0..k} \<union> {k + 1..a}. max 0 (y - q r))
      = (\<Sum>r = 0..k. max 0 (y - q r)) + (\<Sum>r = k + 1..a. max 0 (y - q r))"
    by (rule sum.union_disjoint) (use dis in simp_all)
  show ?thesis unfolding Psi_def split U using A B by simp
qed

lemma Psi_zero: "Psi a q 0 = 0"
proof -
  have "\<And>r. r \<in> {0..a} \<Longrightarrow> max 0 (0 - q r) = 0" using q_nonneg by simp
  then show ?thesis unfolding Psi_def by (simp add: sum.neutral)
qed

lemma Psi_seg:
  assumes k: "k \<le> a" and y1: "q k \<le> y" and y2: "k < a \<Longrightarrow> y \<le> q (k + 1)"
  shows "Psi a q y = Psi a q (q k) + int (k + 1) * (y - q k)"
proof -
  have "q k \<le> q k" by simp
  have y3: "k < a \<Longrightarrow> q k \<le> q (k + 1)" using qmono[of k "k + 1"] by simp
  have "Psi a q (q k) = (\<Sum>r = 0..k. q k - q r)" by (rule Psi_lin[OF k order_refl y3])
  moreover have "Psi a q y = (\<Sum>r = 0..k. y - q r)" by (rule Psi_lin[OF k y1 y2])
  moreover have "(\<Sum>r = 0..k. y - q r) = (\<Sum>r = 0..k. q k - q r) + int (k + 1) * (y - q k)"
  proof -
    have "\<And>r. y - q r = (q k - q r) + (y - q k)" by simp
    then have "(\<Sum>r = 0..k. y - q r) = (\<Sum>r = 0..k. (q k - q r) + (y - q k))" by simp
    also have "\<dots> = (\<Sum>r = 0..k. q k - q r) + (\<Sum>r = 0..k. y - q k)" by (rule sum.distrib)
    also have "(\<Sum>r = 0..k. y - q k) = int (k + 1) * (y - q k)" by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
qed

lemma Psi_nonneg: "0 \<le> Psi a q y"
  unfolding Psi_def by (rule sum_nonneg) simp

lemma zi_addn: "0 \<le> E \<Longrightarrow> zi z (E + int s) = zi z E * z ^ s"
  using zi_add[of E "int s" z] by (simp only: zi_nat)

text \<open>Ladder: Q times the sum of z^Psi over y = 1..q_k, up to the k-th kink.\<close>
lemma ladder:
  assumes "k \<le> a"
  shows "Q * (\<Sum>y = 1..q k. zi z (Psi a q y))
    = zi z 1 * R 1 + (\<Sum>r = 1..k. zi z (Psi a q (q r)) * Bcl z R r)
      - zi z (Psi a q (q k) + int (k + 1)) * R (k + 1)"
  using assms
proof (induction k)
  case 0
  have "zi z (0 + int (0 + 1)) = zi z 1" by simp
  then show ?case by (simp add: q0 Psi_zero)
next
  case (Suc k)
  then have kA: "k < a" and kA': "k \<le> a" by simp_all
  let ?p = "q k" and ?E = "Psi a q (q k)"
  have pn: "0 \<le> ?p" using q_nonneg[OF kA'] .
  have gap: "q k \<le> q (k + 1)" using qmono[of k "k + 1"] kA by simp
  obtain n where n: "q (Suc k) = ?p + int n" using gap by (metis le_Suc_ex zle_iff_zadd Suc_eq_plus1 int_ops(5))
  have E0: "0 \<le> ?E" by (rule Psi_nonneg)
  have rs: "R (k + 1) * (1 - z ^ (k + 1)) = Q" by (rule RQ) (use kA in simp_all)
  have sets: "{1..?p + int n} = {1..?p} \<union> {?p + 1..?p + int n}" using pn by auto
  have dis: "{1..?p} \<inter> {?p + 1..?p + int n} = {}" by auto
  have split: "(\<Sum>y \<in> {1..?p + int n}. zi z (Psi a q y))
      = (\<Sum>y = 1..?p. zi z (Psi a q y)) + (\<Sum>y = ?p + 1..?p + int n. zi z (Psi a q y))"
    unfolding sets by (rule sum.union_disjoint) (use dis in simp_all)
  have seg_eq: "(\<Sum>y = ?p + 1..?p + int n. zi z (Psi a q y))
      = (\<Sum>y = ?p + 1..?p + int n. zi z (?E + int (k + 1) * (y - ?p)))"
  proof (rule sum.cong[OF refl])
    fix y assume y: "y \<in> {?p + 1..?p + int n}"
    then have y1: "q k \<le> y" and y2: "y \<le> q (k + 1)" using n by simp_all
    show "zi z (Psi a q y) = zi z (?E + int (k + 1) * (y - ?p))"
      using Psi_seg[OF kA' y1] y2 by simp
  qed
  have seg: "Q * (\<Sum>y = ?p + 1..?p + int n. zi z (Psi a q y))
      = R (k + 1) * (zi z (?E + int (k + 1)) - zi z (?E + int (k + 1) * int n + int (k + 1)))"
    unfolding seg_eq using segment[OF rs E0, of ?p n] by simp
  have psi1: "Psi a q (q (k + 1)) = ?E + int (k + 1) * int n"
    using Psi_seg[OF kA' gap order_refl] n by simp
  have IH: "Q * (\<Sum>y = 1..?p. zi z (Psi a q y))
      = zi z 1 * R 1 + (\<Sum>r = 1..k. zi z (Psi a q (q r)) * Bcl z R r)
        - zi z (?E + int (k + 1)) * R (k + 1)" using Suc.IH kA' by simp
  let ?P1 = "Psi a q (q (k + 1))"
  have P1: "0 \<le> ?P1" by (rule Psi_nonneg)
  have e1: "zi z (?P1 + int (k + 1)) = zi z ?P1 * z ^ (k + 1)" by (rule zi_addn[OF P1])
  have e2: "zi z (?P1 + int (k + 1 + 1)) = zi z ?P1 * z ^ (k + 1 + 1)"
    using zi_addn[OF P1, of "k + 1 + 1"] by simp
  have "Q * (\<Sum>y = 1..q (k + 1). zi z (Psi a q y))
      = Q * (\<Sum>y = 1..?p. zi z (Psi a q y)) + Q * (\<Sum>y = ?p + 1..?p + int n. zi z (Psi a q y))"
    using split n by (simp add: algebra_simps)
  also have "\<dots> = zi z 1 * R 1 + (\<Sum>r = 1..k. zi z (Psi a q (q r)) * Bcl z R r)
        - R (k + 1) * zi z (?P1 + int (k + 1))"
    using IH seg psi1 by (simp add: algebra_simps)
  also have "\<dots> = zi z 1 * R 1 + (\<Sum>r = 1..Suc k. zi z (Psi a q (q r)) * Bcl z R r)
        - zi z (?P1 + int (k + 1 + 1)) * R (k + 1 + 1)"
    unfolding e1 e2 Bcl_def by (simp add: algebra_simps)
  finally show ?case by simp
qed

text \<open>The whole row: the last segment, of slope a+1, runs up to Y >= q_a.\<close>
lemma row_identity:
  assumes Y: "q a \<le> Y"
  shows "Q * (\<Sum>y = 1..Y. zi z (Psi a q y))
    = zi z 1 * R 1 + (\<Sum>r = 1..a. zi z (Psi a q (q r)) * Bcl z R r)
      - zi z (Psi a q Y + int (a + 1)) * R (a + 1)"
proof -
  let ?p = "q a" and ?E = "Psi a q (q a)"
  have pn: "0 \<le> ?p" using q_nonneg[of a] by simp
  obtain n where n0: "Y - q a = int n" using zero_le_imp_eq_int[of "Y - q a"] Y by auto
  then have n: "Y = ?p + int n" by simp
  have E0: "0 \<le> ?E" by (rule Psi_nonneg)
  have rs: "R (a + 1) * (1 - z ^ (a + 1)) = Q" by (rule RQ) simp_all
  have sets: "{1..?p + int n} = {1..?p} \<union> {?p + 1..?p + int n}" using pn by auto
  have dis: "{1..?p} \<inter> {?p + 1..?p + int n} = {}" by auto
  have split: "(\<Sum>y \<in> {1..?p + int n}. zi z (Psi a q y))
      = (\<Sum>y = 1..?p. zi z (Psi a q y)) + (\<Sum>y = ?p + 1..?p + int n. zi z (Psi a q y))"
    unfolding sets by (rule sum.union_disjoint) (use dis in simp_all)
  have seg_eq: "(\<Sum>y = ?p + 1..?p + int n. zi z (Psi a q y))
      = (\<Sum>y = ?p + 1..?p + int n. zi z (?E + int (a + 1) * (y - ?p)))"
  proof (rule sum.cong[OF refl])
    fix y assume y: "y \<in> {?p + 1..?p + int n}"
    then have y1: "q a \<le> y" by simp
    show "zi z (Psi a q y) = zi z (?E + int (a + 1) * (y - ?p))"
      using Psi_seg[OF order_refl y1] by simp
  qed
  have seg: "Q * (\<Sum>y = ?p + 1..?p + int n. zi z (Psi a q y))
      = R (a + 1) * (zi z (?E + int (a + 1)) - zi z (?E + int (a + 1) * int n + int (a + 1)))"
    unfolding seg_eq using segment[OF rs E0, of ?p n] by simp
  have psiY: "Psi a q Y = ?E + int (a + 1) * int n"
    using Psi_seg[OF order_refl Y] n0 by simp
  have lad: "Q * (\<Sum>y = 1..?p. zi z (Psi a q y))
      = zi z 1 * R 1 + (\<Sum>r = 1..a. zi z (Psi a q (q r)) * Bcl z R r)
        - zi z (?E + int (a + 1)) * R (a + 1)" by (rule ladder) simp
  have "Q * (\<Sum>y = 1..Y. zi z (Psi a q y))
      = Q * (\<Sum>y = 1..?p. zi z (Psi a q y)) + Q * (\<Sum>y = ?p + 1..?p + int n. zi z (Psi a q y))"
    using split n by (simp add: algebra_simps)
  also have "\<dots> = zi z 1 * R 1 + (\<Sum>r = 1..a. zi z (Psi a q (q r)) * Bcl z R r)
        - zi z (Psi a q Y + int (a + 1)) * R (a + 1)"
    using lad seg psiY by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma Psi_nonpos: "y \<le> 0 \<Longrightarrow> Psi a q y = 0"
proof -
  assume y: "y \<le> 0"
  have "\<And>r. r \<in> {0..a} \<Longrightarrow> max 0 (y - q r) = 0"
  proof -
    fix r assume r: "r \<in> {0..a}"
    have "0 \<le> q r" using q_nonneg r by simp
    then show "max 0 (y - q r) = 0" using y by (auto simp: max_def)
  qed
  then show ?thesis unfolding Psi_def by (simp add: sum.neutral)
qed

text \<open>Psi at a kink: Psi(q_r) = sum_{t<r} (t+1)(q_{t+1} - q_t).\<close>
lemma Psi_kink:
  assumes "r \<le> a"
  shows "Psi a q (q r) = (\<Sum>t < r. int (t + 1) * (q (t + 1) - q t))"
proof -
  have "Psi a q (q r) = (\<Sum>s = 0..r. q r - q s)"
    by (rule Psi_lin[OF assms order_refl]) (use qmono[of r "r + 1"] in simp)
  also have "\<dots> = (\<Sum>t < r. int (t + 1) * (q (t + 1) - q t))" using assms
  proof (induction r)
    case 0
    show ?case by simp
  next
    case (Suc r)
    have "(\<Sum>s = 0..Suc r. q (Suc r) - q s) = (\<Sum>s = 0..r. q (Suc r) - q s) + (q (Suc r) - q (Suc r))"
      by simp
    also have "(\<Sum>s = 0..r. q (Suc r) - q s) = (\<Sum>s = 0..r. q r - q s) + int (r + 1) * (q (Suc r) - q r)"
    proof -
      have "\<And>s. q (Suc r) - q s = (q r - q s) + (q (Suc r) - q r)" by simp
      then have "(\<Sum>s = 0..r. q (Suc r) - q s) = (\<Sum>s = 0..r. (q r - q s) + (q (Suc r) - q r))" by simp
      also have "\<dots> = (\<Sum>s = 0..r. q r - q s) + (\<Sum>s = 0..r. q (Suc r) - q r)" by (rule sum.distrib)
      also have "(\<Sum>s = 0..r. q (Suc r) - q r) = int (r + 1) * (q (Suc r) - q r)" by simp
      finally show ?thesis .
    qed
    also have "(\<Sum>s = 0..r. q r - q s) = (\<Sum>t < r. int (t + 1) * (q (t + 1) - q t))"
      using Suc.IH Suc.prems by simp
    finally show ?case by simp
  qed
  finally show ?thesis .
qed

end

section \<open>The whole vector c: definitions of the paper\<close>

definition fcl :: "int \<Rightarrow> int \<Rightarrow> int" where
  "fcl b v = min (b + 1) (max 0 (v + 1))"

text \<open>H_i(j) = sum_{l=0}^{a} f(c_{i-l} + j).\<close>
definition Hval :: "nat \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "Hval a b c i j = (\<Sum>l = 0..a. fcl b (c (i - int l) + j))"

text \<open>G_c(z) = sum over the multiset Z(c) of z^(T - v), with T = (a+1)(b+1); here as the double sum over
  the rows 0 <= i <= a and the columns 0 <= j <= b, whose values are Z(c).\<close>
definition Gc :: "nat \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a" where
  "Gc a b c z = (\<Sum>i = 0..int a. \<Sum>j = 0..b. zi z (int (a + 1) * (b + 1) - Hval a b c i j))"

text \<open>w_{i,r} = sum_{t=0}^{r-1} (t+1)(c_{i-a+t+1} - c_{i-a+t}).\<close>
definition wlev :: "nat \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "wlev a c i r = (\<Sum>t < r. int (t + 1) * (c (i - int a + int t + 1) - c (i - int a + int t)))"

lemma fcl_deficit: "0 \<le> v \<Longrightarrow> (b + 1) - fcl b v = max 0 (b - v)"
  by (auto simp: fcl_def max_def min_def)

lemma sum_int_nat:
  fixes g :: "int \<Rightarrow> 'b::comm_monoid_add"
  shows "(\<Sum>h = l..l + int n. g h) = (\<Sum>r = 0..n. g (l + int r))"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have e: "l + int (Suc n) = (l + int n) + 1" by simp
  have "(\<Sum>h = l..l + int (Suc n). g h) = (\<Sum>h = l..l + int n + 1. g h)" by (subst e) (rule refl)
  also have "\<dots> = (\<Sum>h = l..l + int n. g h) + g (l + int n + 1)" by (rule sum_snoc_int) simp
  also have "\<dots> = (\<Sum>r = 0..n. g (l + int r)) + g (l + int (Suc n))" using Suc by (simp add: algebra_simps)
  finally show ?case by simp
qed

locale levels =
  fixes a :: nat and b :: int and c :: "int \<Rightarrow> int" and z Q :: "'a::comm_ring_1" and R :: "nat \<Rightarrow> 'a"
  assumes RQ: "\<And>s. 1 \<le> s \<Longrightarrow> s \<le> a + 1 \<Longrightarrow> R s * (1 - z ^ s) = Q"
    and cmono: "\<And>h h'. - int a \<le> h \<Longrightarrow> h \<le> h' \<Longrightarrow> h' \<le> int a \<Longrightarrow> c h \<le> c h'"
    and c_ge: "\<And>h. - int a \<le> h \<Longrightarrow> h \<le> int a \<Longrightarrow> 0 \<le> c h"
    and c_le: "\<And>h. - int a \<le> h \<Longrightarrow> h \<le> int a \<Longrightarrow> c h \<le> b"
begin

text \<open>Row i: T - H_i(j) = Psi(Y - j), with q_r = c_{i-a+r} - c_{i-a} and Y = b - c_{i-a}.\<close>
lemma deficit_eq:
  assumes i: "0 \<le> i" "i \<le> int a" and j: "0 \<le> j"
  shows "int (a + 1) * (b + 1) - Hval a b c i j
    = Psi a (\<lambda>r. c (i - int a + int r) - c (i - int a)) (b - c (i - int a) - j)"
proof -
  let ?q = "\<lambda>r. c (i - int a + int r) - c (i - int a)"
  have "int (a + 1) * (b + 1) = (\<Sum>l = 0..a. b + 1)" by simp
  then have "int (a + 1) * (b + 1) - Hval a b c i j
      = (\<Sum>l = 0..a. (b + 1) - fcl b (c (i - int l) + j))"
    unfolding Hval_def by (simp add: sum_subtractf)
  also have "\<dots> = (\<Sum>l = 0..a. max 0 (b - (c (i - int l) + j)))"
  proof (rule sum.cong[OF refl])
    fix l assume l: "l \<in> {0..a}"
    then have "0 \<le> c (i - int l)" using c_ge i by simp
    with j show "(b + 1) - fcl b (c (i - int l) + j) = max 0 (b - (c (i - int l) + j))"
      by (intro fcl_deficit) simp
  qed
  also have "\<dots> = (\<Sum>r = 0..a. max 0 (b - (c (i - int (a - r)) + j)))"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>r. a - r" and j = "\<lambda>l. a - l"]) auto
  also have "\<dots> = Psi a ?q (b - c (i - int a) - j)"
    unfolding Psi_def
  proof (rule sum.cong[OF refl])
    fix r assume r: "r \<in> {0..a}"
    then have ra: "r \<le> a" by simp
    have "int (a - r) = int a - int r" by (rule of_nat_diff[OF ra])
    then have e: "i - int (a - r) = i - int a + int r" by simp
    show "max 0 (b - (c (i - int (a - r)) + j)) = max 0 (b - c (i - int a) - j - ?q r)"
      by (simp add: e algebra_simps)
  qed
  finally show ?thesis .
qed

text \<open>The identity of the paper for one row i.\<close>
lemma per_row:
  assumes i: "0 \<le> i" "i \<le> int a"
  shows "Q * (\<Sum>j = 0..b. zi z (int (a + 1) * (b + 1) - Hval a b c i j))
    = of_int (c (i - int a) + 1) * Q + zi z 1 * R 1
      + (\<Sum>r = 1..a. zi z (wlev a c i r) * Bcl z R r)
      - zi z (int (a + 1) * (b + 1) - (\<Sum>h = i - int a..i. c h)) * R (a + 1)"
proof -
  define q :: "nat \<Rightarrow> int" where "q r = c (i - int a + int r) - c (i - int a)" for r
  define h0 where "h0 = i - int a"
  define Y where "Y = b - c h0"
  have h0a: "- int a \<le> h0" "h0 \<le> int a" using i by (simp_all add: h0_def)
  have rng: "\<And>r. r \<le> a \<Longrightarrow> - int a \<le> h0 + int r \<and> h0 + int r \<le> int a"
    using i by (simp add: h0_def)
  have qd: "\<And>r. q r = c (h0 + int r) - c h0" by (simp add: q_def h0_def)
  have fq: "q = (\<lambda>r. c (i - int a + int r) - c (i - int a))" by (rule ext) (simp add: q_def)
  interpret rw: row a q z Q R
  proof
    show "\<And>s. 1 \<le> s \<Longrightarrow> s \<le> a + 1 \<Longrightarrow> R s * (1 - z ^ s) = Q" by (rule RQ)
    show "q 0 = 0" by (simp add: qd)
    fix r s :: nat assume rs: "r \<le> s" "s \<le> a"
    have "h0 + int r \<le> h0 + int s" using rs by simp
    from cmono[OF _ this] rng[of r] rng[of s] rs show "q r \<le> q s" by (simp add: qd)
  qed
  have c0: "0 \<le> c h0" using c_ge h0a by simp
  have ci: "c i \<le> b" using c_le i by simp
  have qa: "q a = c i - c h0" by (simp add: qd h0_def)
  have Yge: "q a \<le> Y" using qa ci by (simp add: Y_def)
  have Y0: "0 \<le> Y" using Yge rw.q_nonneg[of a] by simp
  \<comment> \<open>the deficits of the row\<close>
  have A: "(\<Sum>j = 0..b. zi z (int (a + 1) * (b + 1) - Hval a b c i j))
      = (\<Sum>j = 0..b. zi z (Psi a q (Y - j)))"
  proof (rule sum.cong[OF refl])
    fix j assume j: "j \<in> {0..b}"
    have "int (a + 1) * (b + 1) - Hval a b c i j = Psi a (\<lambda>r. c (i - int a + int r) - c (i - int a)) (b - c (i - int a) - j)"
      by (rule deficit_eq[OF i]) (use j in simp)
    then show "zi z (int (a + 1) * (b + 1) - Hval a b c i j) = zi z (Psi a q (Y - j))"
      by (simp add: fq Y_def h0_def)
  qed
  have B: "(\<Sum>j = 0..b. zi z (Psi a q (Y - j))) = (\<Sum>y = - c h0..Y. zi z (Psi a q y))"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>j. Y - j" and j = "\<lambda>y. Y - y"]) (auto simp: Y_def)
  have sets: "{- c h0..Y} = {- c h0..0} \<union> {1..Y}" using c0 Y0 by auto
  have dis: "{- c h0..0} \<inter> {1..Y} = {}" by auto
  have C: "(\<Sum>y \<in> {- c h0..Y}. zi z (Psi a q y))
      = (\<Sum>y = - c h0..0. zi z (Psi a q y)) + (\<Sum>y = 1..Y. zi z (Psi a q y))"
    unfolding sets by (rule sum.union_disjoint) (use dis in simp_all)
  have D: "(\<Sum>y = - c h0..0. zi z (Psi a q y)) = of_int (c h0 + 1)"
  proof -
    have "\<And>y. y \<in> {- c h0..0} \<Longrightarrow> zi z (Psi a q y) = 1"
      using rw.Psi_nonpos by (simp add: zi_def)
    then have "(\<Sum>y = - c h0..0. zi z (Psi a q y)) = (\<Sum>y = - c h0..0. (1::'a))" by (rule sum.cong[OF refl])
    also have "\<dots> = of_nat (nat (c h0 + 1))" by simp
    also have "\<dots> = of_int (c h0 + 1)" using c0 by (simp add: of_nat_nat)
    finally show ?thesis .
  qed
  have E: "(\<Sum>r = 1..a. zi z (Psi a q (q r)) * Bcl z R r) = (\<Sum>r = 1..a. zi z (wlev a c i r) * Bcl z R r)"
  proof (rule sum.cong[OF refl])
    fix r assume r: "r \<in> {1..a}"
    then have ra: "r \<le> a" by simp
    have "Psi a q (q r) = wlev a c i r"
      unfolding rw.Psi_kink[OF ra] wlev_def by (rule sum.cong[OF refl]) (simp add: q_def algebra_simps)
    then show "zi z (Psi a q (q r)) * Bcl z R r = zi z (wlev a c i r) * Bcl z R r" by simp
  qed
  have G: "Psi a q Y + int (a + 1) = int (a + 1) * (b + 1) - (\<Sum>h = i - int a..i. c h)"
  proof -
    have "Psi a q Y = (\<Sum>r = 0..a. Y - q r)" unfolding Psi_def
    proof (rule sum.cong[OF refl])
      fix r assume r: "r \<in> {0..a}"
      have "q r \<le> q a" by (rule rw.qmono) (use r in simp_all)
      then show "max 0 (Y - q r) = Y - q r" using Yge by (simp add: max_def)
    qed
    also have "\<dots> = (\<Sum>r = 0..a. b - c (h0 + int r))" by (rule sum.cong[OF refl]) (simp add: qd Y_def)
    also have "\<dots> = int (a + 1) * b - (\<Sum>r = 0..a. c (h0 + int r))" by (simp add: sum_subtractf)
    finally have P: "Psi a q Y = int (a + 1) * b - (\<Sum>r = 0..a. c (h0 + int r))" .
    have "(\<Sum>h = i - int a..i. c h) = (\<Sum>h = h0..h0 + int a. c h)" by (simp add: h0_def)
    also have "\<dots> = (\<Sum>r = 0..a. c (h0 + int r))" by (rule sum_int_nat)
    finally show ?thesis using P by (simp add: algebra_simps)
  qed
  have RI: "Q * (\<Sum>y = 1..Y. zi z (Psi a q y))
      = zi z 1 * R 1 + (\<Sum>r = 1..a. zi z (Psi a q (q r)) * Bcl z R r)
        - zi z (Psi a q Y + int (a + 1)) * R (a + 1)" by (rule rw.row_identity[OF Yge])
  have "Q * (\<Sum>j = 0..b. zi z (int (a + 1) * (b + 1) - Hval a b c i j))
      = Q * ((\<Sum>y = - c h0..0. zi z (Psi a q y)) + (\<Sum>y = 1..Y. zi z (Psi a q y)))"
    using A B C by simp
  also have "\<dots> = of_int (c h0 + 1) * Q + Q * (\<Sum>y = 1..Y. zi z (Psi a q y))"
    using D by (simp add: algebra_simps)
  also have "\<dots> = of_int (c h0 + 1) * Q + zi z 1 * R 1
      + (\<Sum>r = 1..a. zi z (wlev a c i r) * Bcl z R r)
      - zi z (int (a + 1) * (b + 1) - (\<Sum>h = i - int a..i. c h)) * R (a + 1)"
    using RI E G by simp
  finally show ?thesis by (simp add: h0_def)
qed

section \<open>Proposition prop:levels\<close>

text \<open>Q G_c = (S+a+1) Q + (a+1) z R_1 + sum_{r=1}^{a} (sum_{i=0}^{a} z^{w_{i,r}}) B_r
  - sum_{i=0}^{a} z^{T - sum_{h in W_i} c_h} R_{a+1}, with S = sum_{h=-a}^{0} c_h, T = (a+1)(b+1).\<close>
theorem prop_levels:
  "Q * Gc a b c z
    = of_int ((\<Sum>h = - int a..0. c h) + int (a + 1)) * Q + of_nat (a + 1) * (zi z 1 * R 1)
      + (\<Sum>r = 1..a. (\<Sum>i = 0..int a. zi z (wlev a c i r)) * Bcl z R r)
      - (\<Sum>i = 0..int a. zi z (int (a + 1) * (b + 1) - (\<Sum>h = i - int a..i. c h))) * R (a + 1)"
proof -
  let ?T = "int (a + 1) * (b + 1)"
  have step: "Q * Gc a b c z = (\<Sum>i = 0..int a. Q * (\<Sum>j = 0..b. zi z (?T - Hval a b c i j)))"
    unfolding Gc_def by (simp add: sum_distrib_left)
  have rows: "(\<Sum>i = 0..int a. Q * (\<Sum>j = 0..b. zi z (?T - Hval a b c i j)))
    = (\<Sum>i = 0..int a. of_int (c (i - int a) + 1) * Q + zi z 1 * R 1
      + (\<Sum>r = 1..a. zi z (wlev a c i r) * Bcl z R r)
      - zi z (?T - (\<Sum>h = i - int a..i. c h)) * R (a + 1))"
  proof (rule sum.cong[OF refl])
    fix i assume i: "i \<in> {0..int a}"
    show "Q * (\<Sum>j = 0..b. zi z (?T - Hval a b c i j))
      = of_int (c (i - int a) + 1) * Q + zi z 1 * R 1
        + (\<Sum>r = 1..a. zi z (wlev a c i r) * Bcl z R r)
        - zi z (?T - (\<Sum>h = i - int a..i. c h)) * R (a + 1)"
      by (rule per_row) (use i in simp_all)
  qed
  have s1: "(\<Sum>i = 0..int a. (of_int (c (i - int a) + 1) :: 'a) * Q) = of_int ((\<Sum>h = - int a..0. c h) + int (a + 1)) * Q"
  proof -
    have "(\<Sum>i = 0..int a. c (i - int a)) = (\<Sum>h = - int a..0. c h)"
    proof -
      have "(\<Sum>i = 0..int a. c (i - int a)) = (\<Sum>r = 0..a. c (0 + int r - int a))"
        using sum_int_nat[of "\<lambda>i. c (i - int a)" 0 a] by simp
      also have "\<dots> = (\<Sum>h = - int a..0. c h)"
        using sum_int_nat[of c "- int a" a] by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    then have "(\<Sum>i = 0..int a. c (i - int a) + 1) = (\<Sum>h = - int a..0. c h) + int (a + 1)"
      by (simp add: sum.distrib)
    then have h2: "(\<Sum>i = 0..int a. (of_int (c (i - int a) + 1) :: 'a)) = of_int ((\<Sum>h = - int a..0. c h) + int (a + 1))"
      by (metis (no_types, lifting) of_int_sum sum.cong)
    show ?thesis by (simp only: sum_distrib_right[symmetric] h2)
  qed
  have s2: "(\<Sum>i = 0..int a. zi z 1 * R 1) = of_nat (a + 1) * (zi z 1 * R 1)"
    by (simp add: algebra_simps)
  have s3: "(\<Sum>i = 0..int a. \<Sum>r = 1..a. zi z (wlev a c i r) * Bcl z R r)
      = (\<Sum>r = 1..a. (\<Sum>i = 0..int a. zi z (wlev a c i r)) * Bcl z R r)"
    by (subst sum.swap) (simp add: sum_distrib_right)
  have s4: "(\<Sum>i = 0..int a. zi z (?T - (\<Sum>h = i - int a..i. c h)) * R (a + 1))
      = (\<Sum>i = 0..int a. zi z (?T - (\<Sum>h = i - int a..i. c h))) * R (a + 1)"
    by (simp add: sum_distrib_right)
  show ?thesis
    unfolding step rows
    by (simp only: sum_subtractf sum.distrib s1 s2 s3 s4)
qed

end

section \<open>The second half of prop:levels: c = g(n,m,e) with no coordinate clipped\<close>

text \<open>kappa_{i,r}(e) = sum_{t=0}^{r-1} (t+1) eta_{i-a+t}, with eta_h = e_{h+1} - e_h; T_r = r(r+1)/2.\<close>
definition kappa :: "nat \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "kappa a e i r = (\<Sum>t < r. int (t + 1) * (e (i - int a + int t + 1) - e (i - int a + int t)))"

definition Tn :: "nat \<Rightarrow> int" where
  "Tn r = (\<Sum>t < r. int (t + 1))"

lemma Tn_formula: "2 * Tn r = int r * (int r + 1)"
  by (induction r) (simp_all add: Tn_def algebra_simps)

text \<open>w_{i,r} = T_r m + kappa_{i,r}(e) when c_h = n + h m + e_h on the window.\<close>
lemma wlev_unclipped:
  assumes "\<And>h. i - int a \<le> h \<Longrightarrow> h \<le> i \<Longrightarrow> c h = n + h * m + e h"
    and "r \<le> a"
  shows "wlev a c i r = Tn r * m + kappa a e i r"
proof -
  have "\<And>t. t \<in> {..<r} \<Longrightarrow>
      int (t + 1) * (c (i - int a + int t + 1) - c (i - int a + int t))
      = int (t + 1) * m + int (t + 1) * (e (i - int a + int t + 1) - e (i - int a + int t))"
  proof -
    fix t assume t: "t \<in> {..<r}"
    then have "t < a" using assms(2) by simp
    then have h1: "i - int a + int t + 1 \<le> i" and h2: "i - int a \<le> i - int a + int t + 1"
      and h3: "i - int a \<le> i - int a + int t" and h4: "i - int a + int t \<le> i" by simp_all
    have d: "c (i - int a + int t + 1) - c (i - int a + int t)
        = m + (e (i - int a + int t + 1) - e (i - int a + int t))"
      using assms(1)[OF h2 h1] assms(1)[OF h3 h4] by (simp add: algebra_simps)
    show "int (t + 1) * (c (i - int a + int t + 1) - c (i - int a + int t))
      = int (t + 1) * m + int (t + 1) * (e (i - int a + int t + 1) - e (i - int a + int t))"
      by (simp only: d) (simp add: algebra_simps)
  qed
  then have "wlev a c i r = (\<Sum>t < r. int (t + 1) * m + int (t + 1) * (e (i - int a + int t + 1) - e (i - int a + int t)))"
    unfolding wlev_def by (rule sum.cong[OF refl])
  also have "\<dots> = (\<Sum>t < r. int (t + 1)) * m + kappa a e i r"
    unfolding kappa_def by (subst sum.distrib) (simp only: sum_distrib_right)
  finally show ?thesis by (simp add: Tn_def)
qed

lemma sum_window_h:
  "2 * (\<Sum>h = l..l + int n. h) = int (n + 1) * (2 * l + int n)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have e: "l + int (Suc n) = (l + int n) + 1" by simp
  have "(\<Sum>h = l..l + int (Suc n). h) = (\<Sum>h = l..l + int n + 1. h)" by (subst e) (rule refl)
  also have "\<dots> = (\<Sum>h = l..l + int n. h) + (l + int n + 1)" by (rule sum_snoc_int) simp
  finally have "2 * (\<Sum>h = l..l + int (Suc n). h) = 2 * (\<Sum>h = l..l + int n. h) + 2 * (l + int n + 1)" by simp
  then show ?case using Suc by (simp add: algebra_simps)
qed

text \<open>The exponent of the last cluster: T - sum_{h in W_i} c_h
  = (a+1)(b+1-n) - m * sum_{h in W_i} h - sum_{h in W_i} e_h, and 2 sum_{h in W_i} h = (a+1)(2i - a).\<close>
lemma window_unclipped:
  assumes "\<And>h. i - int a \<le> h \<Longrightarrow> h \<le> i \<Longrightarrow> c h = n + h * m + e h"
  shows "int (a + 1) * (b + 1) - (\<Sum>h = i - int a..i. c h)
      = int (a + 1) * (b + 1 - n) - m * (\<Sum>h = i - int a..i. h) - (\<Sum>h = i - int a..i. e h)"
    and "2 * (\<Sum>h = i - int a..i. h) = int (a + 1) * (2 * i - int a)"
proof -
  have "(\<Sum>h = i - int a..i. c h) = (\<Sum>h = i - int a..i. n + h * m + e h)"
    by (rule sum.cong[OF refl]) (use assms in simp)
  also have "\<dots> = int (a + 1) * n + m * (\<Sum>h = i - int a..i. h) + (\<Sum>h = i - int a..i. e h)"
  proof -
    have "card {i - int a..i} = a + 1" by simp
    then show ?thesis by (simp add: sum.distrib sum_distrib_left algebra_simps)
  qed
  finally show "int (a + 1) * (b + 1) - (\<Sum>h = i - int a..i. c h)
      = int (a + 1) * (b + 1 - n) - m * (\<Sum>h = i - int a..i. h) - (\<Sum>h = i - int a..i. e h)"
    by (simp add: algebra_simps)
next
  have "i = (i - int a) + int a" by simp
  then show "2 * (\<Sum>h = i - int a..i. h) = int (a + 1) * (2 * i - int a)"
    using sum_window_h[of "i - int a" a] by (simp add: algebra_simps)
qed

section \<open>Non-vacuity of the hypotheses\<close>

text \<open>An instance: a = 1, b = 2, c = (0,0,1) on h = -1,0,1, z = 2 and Q = (1-z)(1-z^2) = 3 in the integers,
  with R_1 = Q/(1-z) = -3, R_2 = Q/(1-z^2) = -1.\<close>
interpretation levels_example: levels 1 2 "\<lambda>h. if h = 1 then 1 else 0" 2 3 "\<lambda>s. if s = 1 then - 3 else - 1"
  by unfold_locales (auto simp: le_Suc_eq)

end
