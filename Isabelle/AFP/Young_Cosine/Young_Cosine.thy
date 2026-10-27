(*  Title:      Young_Cosine.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Young's cosine inequality

    The partial sums of the cosine series sum cos (k x) / k are bounded below by -1, for every n and every real x
    (W. H. Young, 1913). The proof takes a global minimum of the sum on [0, 2 pi]: at an interior critical point
    either sin (n x / 2) = 0, and the induction hypothesis applies, or sin ((n + 1) x / 2) = 0, where a double Abel
    summation (Fejer's method) with the convex coefficients a_0 = 2, a_k = 1/k gives the bound.
    The companion Fejer--Jackson inequality (the sine sums are positive on (0, pi)) is formalized in Lean:
    Formalizations.Analysis.SpecialFunctions.Trigonometric.FejerJackson.

    Main results:
    * young_cosine: -1 <= sum k = 1..n. cos (k x) / k.
*)

section \<open>Young's cosine inequality\<close>

theory Young_Cosine
  imports "HOL-Analysis.Analysis"
begin
subsection \<open>Young's inequality: Abel summation twice\<close>

text \<open>
  We prove Young's inequality \cite{Young1913}: \<open>-1 \<le> (\<Sum>k=1..n. cos (k x) / k)\<close>.
  Route: global minimum of the cosine sum on \<open>[0, 2\<pi>]\<close>. At an interior critical point either
  \<open>sin (n x / 2) = 0\<close> (then \<open>cos (n x) = 1\<close> and the induction hypothesis applies) or
  \<open>sin ((n+1) x / 2) = 0\<close>. In the latter case a double Abel summation (Fejér's method) gives the
  bound, using that the Fejér kernel of order \<open>n\<close> vanishes there.
\<close>

definition cs :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "cs n x = (\<Sum>k=1..n. cos (real k * x) / real k)"

lemma cs_Suc: "cs (Suc n) x = cs n x + cos (real (Suc n) * x) / real (Suc n)"
  by (simp add: cs_def)

lemma cs_0: "cs 0 x = 0"
  by (simp add: cs_def)

lemma cs_zero_arg: "0 \<le> cs n 0"
  by (simp add: cs_def sum_nonneg)

lemma cs_two_pi: "0 \<le> cs n (2 * pi)"
proof -
  have "cos (real k * (2 * pi)) = 1" for k
    using cos_2npi[of k] by (simp add: algebra_simps)
  then show ?thesis by (simp add: cs_def sum_nonneg)
qed

lemma continuous_cs: "continuous_on UNIV (cs n)"
proof (induction n)
  case 0
  then show ?case by (simp add: cs_def)
next
  case (Suc n)
  have "cs (Suc n) = (\<lambda>x. cs n x + cos (real (Suc n) * x) / real (Suc n))"
    by (rule ext) (rule cs_Suc)
  moreover have "continuous_on UNIV (\<lambda>x. cs n x + cos (real (Suc n) * x) / real (Suc n))"
    using Suc by (intro continuous_intros) auto
  ultimately show ?case by simp
qed

lemma DERIV_cs: "DERIV (cs n) x :> - (\<Sum>k=1..n. sin (real k * x))"
proof (induction n)
  case 0
  then show ?case by (simp add: cs_def)
next
  case (Suc n)
  have eq: "cs (Suc n) = (\<lambda>x. cs n x + cos (real (Suc n) * x) / real (Suc n))"
    by (rule ext) (rule cs_Suc)
  have pos: "real (Suc n) \<noteq> 0" by simp
  have d: "DERIV (\<lambda>x. cos (real (Suc n) * x) / real (Suc n)) x :> - sin (real (Suc n) * x)"
  proof -
    have "DERIV (\<lambda>x. cos (real (Suc n) * x) / real (Suc n)) x
          :> - sin (real (Suc n) * x) * real (Suc n) / real (Suc n)"
      by (auto intro!: derivative_eq_intros)
    then show ?thesis using pos by simp
  qed
  have "DERIV (\<lambda>x. cs n x + cos (real (Suc n) * x) / real (Suc n)) x
        :> - (\<Sum>k=1..n. sin (real k * x)) + - sin (real (Suc n) * x)"
    by (rule DERIV_add[OF Suc d])
  then show ?case by (simp add: eq)
qed

lemma cs_periodic: "cs n (x - 2 * pi * of_int m) = cs n x"
proof -
  have "cos (real k * (x - 2 * pi * of_int m)) = cos (real k * x)" for k
  proof -
    have "real k * (x - 2 * pi * of_int m) = real k * x - (2 * pi) * of_int (int k * m)"
      by (simp add: algebra_simps)
    then show ?thesis by (simp only: cos_diff cos_int_2pin sin_int_2pin)
  qed
  then show ?thesis by (simp add: cs_def)
qed

lemma sin_telescope:
  "2 * sin (x / 2) * (\<Sum>k=1..n. sin (real k * x)) = cos (x / 2) - cos ((real n + 1 / 2) * x)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have a: "(real (Suc n) + 1 / 2) * x = real (Suc n) * x + x / 2"
    by (simp add: algebra_simps)
  have b: "(real n + 1 / 2) * x = real (Suc n) * x - x / 2"
    by (simp add: algebra_simps)
  have "cos ((real n + 1 / 2) * x) - cos ((real (Suc n) + 1 / 2) * x)
        = 2 * sin (x / 2) * sin (real (Suc n) * x)"
    unfolding a b by (simp add: cos_add cos_diff)
  then show ?case
    using Suc by (simp add: algebra_simps)
qed

lemma crit_cases:
  assumes "(\<Sum>k=1..n. sin (real k * x)) = 0"
    and "0 < x" "x < 2 * pi"
  shows "sin (real n * x / 2) = 0 \<or> sin (real (Suc n) * x / 2) = 0"
proof -
  have "0 < sin (x / 2)" using assms(2,3) by (intro sin_gt_zero) auto
  have h: "cos ((real n + 1 / 2) * x) = cos (x / 2)"
    using sin_telescope[of x n] assms(1) by simp
  have e1: "(real n + 1 / 2) * x = real (Suc n) * x / 2 + real n * x / 2"
    by (simp add: field_simps)
  have e2: "x / 2 = real (Suc n) * x / 2 - real n * x / 2"
    by (simp add: field_simps)
  have "cos ((real n + 1 / 2) * x) - cos (x / 2)
        = - 2 * sin (real (Suc n) * x / 2) * sin (real n * x / 2)"
  proof -
    have g: "cos (real (Suc n) * x / 2 + real n * x / 2) - cos (real (Suc n) * x / 2 - real n * x / 2)
          = - 2 * sin (real (Suc n) * x / 2) * sin (real n * x / 2)"
      by (simp add: cos_add cos_diff)
    show ?thesis using g by (simp only: e1[symmetric] e2[symmetric])
  qed
  then have "sin (real (Suc n) * x / 2) * sin (real n * x / 2) = 0" using h by simp
  then show ?thesis by auto
qed

subsubsection \<open>Abstract double Abel summation\<close>

definition Dsum :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Dsum u k = (\<Sum>i\<le>k. u i)"

definition Ssum :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Ssum u k = (\<Sum>i\<le>k. Dsum u i)"

lemma sum_atMost_Suc': "(\<Sum>k\<le>Suc n. f k) = (\<Sum>k\<le>n. f k) + f (Suc n)"
  by (simp add: atMost_Suc add.commute)

lemma Dsum_0: "Dsum u 0 = u 0" by (simp add: Dsum_def)
lemma Dsum_Suc: "Dsum u (Suc k) = Dsum u k + u (Suc k)"
  by (simp add: Dsum_def sum_atMost_Suc')
lemma Ssum_0: "Ssum u 0 = u 0" by (simp add: Ssum_def Dsum_0)
lemma Ssum_Suc: "Ssum u (Suc k) = Ssum u k + Dsum u (Suc k)"
  by (simp add: Ssum_def sum_atMost_Suc')

lemma abel2:
  "(\<Sum>k\<le>Suc m. a k * u k)
   = (\<Sum>k<m. (a k - 2 * a (Suc k) + a (Suc (Suc k))) * Ssum u k)
     + (a m - a (Suc m)) * Ssum u m + a (Suc m) * Dsum u (Suc m)"
proof (induction m)
  case 0
  show ?case
    by (simp add: sum_atMost_Suc' Dsum_Suc Dsum_0 Ssum_0 algebra_simps)
next
  case (Suc m)
  have l: "(\<Sum>k\<le>Suc (Suc m). a k * u k)
      = (\<Sum>k\<le>Suc m. a k * u k) + a (Suc (Suc m)) * u (Suc (Suc m))"
    by (rule sum_atMost_Suc')
  have r: "(\<Sum>k<Suc m. (a k - 2 * a (Suc k) + a (Suc (Suc k))) * Ssum u k)
     = (\<Sum>k<m. (a k - 2 * a (Suc k) + a (Suc (Suc k))) * Ssum u k)
       + (a m - 2 * a (Suc m) + a (Suc (Suc m))) * Ssum u m"
    by (rule sum.lessThan_Suc)
  show ?case
    unfolding l r Suc.IH Dsum_Suc[of u "Suc m"] Ssum_Suc[of u m]
    by (simp add: algebra_simps)
qed

subsubsection \<open>The cosine sequence\<close>

definition uc :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "uc x k = (if k = 0 then 1 / 2 else cos (real k * x))"

lemma Dsum_uc: "Dsum (uc x) k * (2 * sin (x / 2)) = sin ((real k + 1 / 2) * x)"
proof (induction k)
  case 0
  then show ?case by (simp add: Dsum_0 uc_def)
next
  case (Suc k)
  have a: "(real (Suc k) + 1 / 2) * x = real (Suc k) * x + x / 2"
    by (simp add: algebra_simps)
  have b: "(real k + 1 / 2) * x = real (Suc k) * x - x / 2"
    by (simp add: algebra_simps)
  have "sin ((real (Suc k) + 1 / 2) * x) - sin ((real k + 1 / 2) * x)
        = 2 * sin (x / 2) * cos (real (Suc k) * x)"
    unfolding a b by (simp add: sin_add sin_diff)
  then show ?case
    using Suc by (simp add: Dsum_Suc uc_def algebra_simps)
qed

lemma Ssum_uc: "Ssum (uc x) k * (4 * (sin (x / 2))\<^sup>2) = 1 - cos (real (Suc k) * x)"
proof (induction k)
  case 0
  have "cos x = cos (2 * (x / 2))" by simp
  then have "cos x = 1 - 2 * (sin (x / 2))\<^sup>2" by (simp only: cos_double_sin)
  then show ?case by (simp add: Ssum_0 uc_def)
next
  case (Suc k)
  have a: "(real k + 3 / 2) * x = real (Suc k) * x + x / 2"
    by (simp add: algebra_simps)
  have b: "(real k + 3 / 2) * x = real (Suc (Suc k)) * x - x / 2"
    by (simp add: algebra_simps)
  have c: "cos (real (Suc k) * x) - cos (real (Suc (Suc k)) * x)
        = 2 * sin (x / 2) * sin ((real k + 3 / 2) * x)"
  proof -
    have "cos ((real k + 3 / 2) * x - x / 2) - cos ((real k + 3 / 2) * x + x / 2)
          = 2 * sin (x / 2) * sin ((real k + 3 / 2) * x)"
      by (simp add: cos_add cos_diff)
    moreover have "(real k + 3 / 2) * x - x / 2 = real (Suc k) * x"
      by (simp add: algebra_simps)
    moreover have "(real k + 3 / 2) * x + x / 2 = real (Suc (Suc k)) * x"
      by (simp add: algebra_simps)
    ultimately show ?thesis by simp
  qed
  have d: "Dsum (uc x) (Suc k) * (2 * sin (x / 2)) = sin ((real k + 3 / 2) * x)"
    using Dsum_uc[of x "Suc k"] by (simp add: algebra_simps)
  have "Ssum (uc x) (Suc k) * (4 * (sin (x / 2))\<^sup>2)
        = Ssum (uc x) k * (4 * (sin (x / 2))\<^sup>2)
          + 2 * sin (x / 2) * (Dsum (uc x) (Suc k) * (2 * sin (x / 2)))"
    by (simp add: Ssum_Suc power2_eq_square algebra_simps)
  also have "\<dots> = 1 - cos (real (Suc k) * x) + 2 * sin (x / 2) * sin ((real k + 3 / 2) * x)"
    using Suc d by simp
  also have "\<dots> = 1 - cos (real (Suc (Suc k)) * x)" using c by simp
  finally show ?case .
qed

lemma nonneg_from_mult: "0 \<le> a * b \<Longrightarrow> 0 < b \<Longrightarrow> 0 \<le> (a::real)"
proof -
  assume h: "0 \<le> a * b" and b: "0 < b"
  then have "0 \<le> (a * b) / b" by (intro divide_nonneg_pos)
  moreover have "(a * b) / b = a" using b by simp
  ultimately show ?thesis by simp
qed

lemma Ssum_uc_nonneg:
  assumes "0 < sin (x / 2)"
  shows "0 \<le> Ssum (uc x) k"
proof (rule nonneg_from_mult)
  show "0 \<le> Ssum (uc x) k * (4 * (sin (x / 2))\<^sup>2)"
    using Ssum_uc[of x k] cos_le_one[of "real (Suc k) * x"] by simp
  show "0 < 4 * (sin (x / 2))\<^sup>2" using assms by simp
qed

definition ay :: "nat \<Rightarrow> real" where
  "ay k = (if k = 0 then 2 else 1 / real k)"

lemma ay_convex: "0 \<le> ay k - 2 * ay (Suc k) + ay (Suc (Suc k))"
proof (cases k)
  case 0
  then show ?thesis by (simp add: ay_def)
next
  case (Suc j)
  have "0 \<le> 1 / real (Suc j) - 2 / real (Suc (Suc j)) + 1 / real (Suc (Suc (Suc j)))"
  proof -
    let ?q = "real j"
    have p1: "0 < ?q + 1" and p2: "0 < ?q + 2" and p3: "0 < ?q + 3" by simp_all
    have e1: "real (Suc j) = ?q + 1" and e2: "real (Suc (Suc j)) = ?q + 2"
      and e3: "real (Suc (Suc (Suc j))) = ?q + 3" by (simp_all add: algebra_simps)
    have "2 / (?q + 2) \<le> 1 / (?q + 1) + 1 / (?q + 3)"
      by (simp add: divide_simps p1 p2 p3) (simp add: algebra_simps)
    then show ?thesis unfolding e1 e2 e3 by simp
  qed
  then show ?thesis using Suc by (simp add: ay_def algebra_simps)
qed

lemma ay_sum: "(\<Sum>k\<le>n. ay k * uc x k) = 1 + cs n x"
proof (induction n)
  case 0
  then show ?case by (simp add: ay_def uc_def cs_0)
next
  case (Suc n)
  then show ?case by (simp add: sum_atMost_Suc' cs_Suc ay_def uc_def)
qed

lemma young_case2:
  assumes x: "0 < x" "x < 2 * pi" and z: "sin (real (Suc (Suc (Suc p))) * x / 2) = 0"
  shows "-1 \<le> cs (Suc (Suc p)) x"
proof -
  define n where "n = Suc (Suc p)"
  have sp: "0 < sin (x / 2)" using x by (intro sin_gt_zero) auto
  have cN: "cos (real (Suc n) * x) = 1"
  proof -
    have "cos (2 * (real (Suc n) * x / 2)) = 1 - 2 * (sin (real (Suc n) * x / 2))\<^sup>2"
      by (rule cos_double_sin)
    then show ?thesis using z unfolding n_def by simp
  qed
  have sN: "sin (real (Suc n) * x) = 0"
  proof -
    have "sin (2 * (real (Suc n) * x / 2)) = 2 * sin (real (Suc n) * x / 2) * cos (real (Suc n) * x / 2)"
      by (rule sin_double)
    then show ?thesis using z unfolding n_def by simp
  qed
  have Dn: "Dsum (uc x) n = - 1 / 2"
  proof -
    have e: "(real n + 1 / 2) * x = real (Suc n) * x - x / 2" by (simp add: algebra_simps)
    have "sin ((real n + 1 / 2) * x) = - sin (x / 2)"
      unfolding e sin_diff sN cN by simp
    then have "Dsum (uc x) n * (2 * sin (x / 2)) = - sin (x / 2)"
      using Dsum_uc[of x n] by simp
    then have "(2 * Dsum (uc x) n + 1) * sin (x / 2) = 0" by (simp add: algebra_simps)
    then have "2 * Dsum (uc x) n + 1 = 0" using sp by simp
    then show ?thesis by simp
  qed
  have Sn: "Ssum (uc x) (Suc p) = 1 / 2"
  proof -
    have e: "real (Suc (Suc p)) * x = real (Suc n) * x - x" unfolding n_def by (simp add: algebra_simps)
    have c1: "cos (real (Suc (Suc p)) * x) = cos x"
      unfolding e cos_diff sN cN by simp
    have c2: "cos x = 1 - 2 * (sin (x / 2))\<^sup>2"
    proof -
      have "cos (2 * (x / 2)) = 1 - 2 * (sin (x / 2))\<^sup>2" by (rule cos_double_sin)
      then show ?thesis by simp
    qed
    have "Ssum (uc x) (Suc p) * (4 * (sin (x / 2))\<^sup>2) = 2 * (sin (x / 2))\<^sup>2"
      using Ssum_uc[of x "Suc p"] c1 c2 by simp
    then show ?thesis using sp by (simp add: field_simps)
  qed
  have ab: "(\<Sum>k\<le>Suc (Suc p). ay k * uc x k)
     = (\<Sum>k<Suc p. (ay k - 2 * ay (Suc k) + ay (Suc (Suc k))) * Ssum (uc x) k)
       + (ay (Suc p) - ay (Suc (Suc p))) * Ssum (uc x) (Suc p)
       + ay (Suc (Suc p)) * Dsum (uc x) (Suc (Suc p))"
    by (rule abel2)
  have first: "1 / 4 \<le> (\<Sum>k<Suc p. (ay k - 2 * ay (Suc k) + ay (Suc (Suc k))) * Ssum (uc x) k)"
  proof -
    have "(\<Sum>k<Suc p. (ay k - 2 * ay (Suc k) + ay (Suc (Suc k))) * Ssum (uc x) k)
        = (ay 0 - 2 * ay 1 + ay 2) * Ssum (uc x) 0
          + (\<Sum>k<p. (ay (Suc k) - 2 * ay (Suc (Suc k)) + ay (Suc (Suc (Suc k)))) * Ssum (uc x) (Suc k))"
      by (subst sum.lessThan_Suc_shift) (simp add: numeral_2_eq_2)
    moreover have "0 \<le> (\<Sum>k<p. (ay (Suc k) - 2 * ay (Suc (Suc k)) + ay (Suc (Suc (Suc k)))) * Ssum (uc x) (Suc k))"
      by (intro sum_nonneg mult_nonneg_nonneg ay_convex Ssum_uc_nonneg sp)
    moreover have "(ay 0 - 2 * ay 1 + ay 2) * Ssum (uc x) 0 = 1 / 4"
    proof -
      have s0: "Ssum (uc x) 0 = 1 / 2" by (simp add: Ssum_0 uc_def)
      have a0: "ay 0 = 2" and a1: "ay 1 = 1" and a2: "ay 2 = 1 / 2" by (simp_all add: ay_def)
      show ?thesis by (simp only: s0 a0 a1 a2) simp
    qed
    ultimately show ?thesis by linarith
  qed
  have alg: "0 \<le> 1 / 4 + (ay (Suc p) - ay (Suc (Suc p))) * (1 / 2) + ay (Suc (Suc p)) * (- 1 / 2)"
  proof -
    let ?q = "real p"
    have p1: "0 < ?q + 1" and p2: "0 < ?q + 2" by simp_all
    have q0: "0 \<le> ?q" by simp
    have "0 \<le> 1 / 4 + (1 / (?q + 1) - 1 / (?q + 2)) * (1 / 2) + 1 / (?q + 2) * (- 1 / 2)"
      by (simp add: divide_simps p1 p2) (simp add: algebra_simps power2_eq_square add_nonneg_nonneg)
    then show ?thesis by (simp add: ay_def algebra_simps)
  qed
  have "0 \<le> 1 + cs n x"
    unfolding ay_sum[where n=n and x=x, symmetric] unfolding n_def
    using ab first alg Sn Dn[unfolded n_def] by simp
  then show ?thesis unfolding n_def by simp
qed

subsection \<open>Young's inequality\<close>

lemma cs_ge_range:
  assumes ih: "\<forall>y. -1 \<le> cs (Suc p) y"
    and y: "y \<in> {0..2 * pi}"
  shows "-1 \<le> cs (Suc (Suc p)) y"
proof -
  define f where "f = cs (Suc (Suc p))"
  have comp: "compact {0..2 * pi}" by simp
  have ne: "{0..2 * pi} \<noteq> ({}::real set)" using pi_gt_zero by simp
  have cont: "continuous_on {0..2 * pi} f"
    unfolding f_def using continuous_cs by (rule continuous_on_subset) simp
  obtain s where s: "s \<in> {0..2 * pi}" and smin: "\<forall>z\<in>{0..2 * pi}. f s \<le> f z"
    using continuous_attains_inf[OF comp ne cont] by blast
  have "-1 \<le> f s"
  proof (cases "0 < s \<and> s < 2 * pi")
    case False
    then have "s = 0 \<or> s = 2 * pi" using s by auto
    then have "0 \<le> f s" unfolding f_def using cs_zero_arg cs_two_pi by auto
    then show ?thesis by simp
  next
    case True
    define d where "d = min s (2 * pi - s)"
    have dpos: "0 < d" using True unfolding d_def by simp
    have lm: "\<forall>z. \<bar>s - z\<bar> < d \<longrightarrow> f s \<le> f z"
    proof (intro allI impI)
      fix z assume "\<bar>s - z\<bar> < d"
      then have "z \<in> {0..2 * pi}" unfolding d_def by (auto simp: abs_less_iff min_def split: if_splits)
      then show "f s \<le> f z" using smin by blast
    qed
    have D: "DERIV f s :> - (\<Sum>k=1..Suc (Suc p). sin (real k * s))"
      unfolding f_def by (rule DERIV_cs)
    have "- (\<Sum>k=1..Suc (Suc p). sin (real k * s)) = 0"
      by (rule DERIV_local_min[OF D dpos lm])
    then have crit: "(\<Sum>k=1..Suc (Suc p). sin (real k * s)) = 0" by simp
    from crit_cases[OF crit True[THEN conjunct1] True[THEN conjunct2]]
    show ?thesis
    proof
      assume h: "sin (real (Suc (Suc p)) * s / 2) = 0"
      have "cos (2 * (real (Suc (Suc p)) * s / 2)) = 1 - 2 * (sin (real (Suc (Suc p)) * s / 2))\<^sup>2"
        by (rule cos_double_sin)
      then have "cos (real (Suc (Suc p)) * s) = 1" using h by simp
      then have "f s = cs (Suc p) s + 1 / real (Suc (Suc p))"
        unfolding f_def by (simp add: cs_Suc)
      moreover have "-1 \<le> cs (Suc p) s" using ih by blast
      moreover have "0 \<le> 1 / real (Suc (Suc p))" by simp
      ultimately show ?thesis by linarith
    next
      assume h: "sin (real (Suc (Suc (Suc p))) * s / 2) = 0"
      show ?thesis unfolding f_def
        by (rule young_case2[OF True[THEN conjunct1] True[THEN conjunct2] h])
    qed
  qed
  moreover have "f s \<le> f y" using smin y by blast
  ultimately show ?thesis unfolding f_def by simp
qed

lemma cs_ge_all: "-1 \<le> cs n x"
proof (induction n arbitrary: x)
  case 0
  then show ?case by (simp add: cs_0)
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by (simp add: cs_def)
  next
    case (Suc p)
    define m where "m = \<lfloor>x / (2 * pi)\<rfloor>"
    define y where "y = x - 2 * pi * of_int m"
    have "0 \<le> x / (2 * pi) - of_int m" "x / (2 * pi) - of_int m < 1"
      unfolding m_def by linarith+
    then have "0 \<le> y" "y \<le> 2 * pi" unfolding y_def
      by (auto simp: field_simps)
    then have "-1 \<le> cs (Suc (Suc p)) y"
      by (intro cs_ge_range) (use Suc.IH Suc in auto)
    then show ?thesis using Suc unfolding y_def by (simp add: cs_periodic)
  qed
qed

theorem young_cosine:
  shows "-1 \<le> (\<Sum>k=1..n. cos (real k * x) / real k)"
  using cs_ge_all[of n x] unfolding cs_def .

end
