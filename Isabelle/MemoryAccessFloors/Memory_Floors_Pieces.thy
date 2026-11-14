(*  Title:      Memory_Floors_Pieces.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    Elementary pieces of the memory-floor notes A (memory-floors.tex) and B (sec_robust.tex):
    (A) the memory-cycle channel (Proposition "memory cycle with a reset"): composition of the channels
        E_{p,c} and the floor r(p,c) = (1-p)/6 + (1-c)/3;
    (B) the correlated-offset remark: sufficient condition for the optimality of the square pulse;
    (C) vertex inequalities of the threshold for very unequal rates (Proposition "very unequal rates");
    (D) the second-order kernel of Proposition "when the resonant pulse is exactly optimal";
    (E) the elementary parts of the planar exposure lemma.
    Everything is over the reals (and complex 2x2 matrices for the channel); no dynamics is formalised.
*)
theory Memory_Floors_Pieces
  imports "HOL-Analysis.Analysis"
begin

section \<open>A. The memory-cycle channel\<close>

text \<open>A 2x2 matrix is the quadruple (rho00, rho01, rho10, rho11). The channel E_{p,c}
  sends it to (rho00 + (1-p) rho11, c rho01, c rho10, p rho11).\<close>

type_synonym cmat = "complex \<times> complex \<times> complex \<times> complex"

definition chan :: "real \<Rightarrow> real \<Rightarrow> cmat \<Rightarrow> cmat" where
  "chan p c r = (case r of (a, b, d, e) \<Rightarrow>
     (a + of_real (1 - p) * e, of_real c * b, of_real c * d, of_real p * e))"

definition valid_chan :: "real \<Rightarrow> real \<Rightarrow> bool" where
  "valid_chan p c \<longleftrightarrow> 0 \<le> p \<and> 0 \<le> c \<and> c \<le> sqrt p \<and> sqrt p \<le> 1"

definition rfloor :: "real \<Rightarrow> real \<Rightarrow> real" where
  "rfloor p c = (1 - p) / 6 + (1 - c) / 3"

theorem chan_comp: "chan p2 c2 (chan p1 c1 r) = chan (p1 * p2) (c1 * c2) r"
  by (cases r) (simp add: chan_def algebra_simps)

theorem chan_comp_entrywise:
  fixes a b d e :: complex and p1 c1 p2 c2 :: real
  shows "chan p2 c2 (chan p1 c1 (a, b, d, e))
       = (a + of_real (1 - p1 * p2) * e, of_real (c1 * c2) * b, of_real (c1 * c2) * d, of_real (p1 * p2) * e)"
  by (simp add: chan_def algebra_simps)

theorem valid_chan_comp:
  assumes "valid_chan p1 c1" and "valid_chan p2 c2"
  shows "valid_chan (p1 * p2) (c1 * c2)"
proof -
  have s1: "0 \<le> sqrt p1" and s2: "0 \<le> sqrt p2" using assms unfolding valid_chan_def by (simp_all add: real_sqrt_ge_zero)
  have "c1 * c2 \<le> sqrt p1 * sqrt p2"
    using assms unfolding valid_chan_def by (intro mult_mono) simp_all
  moreover have "sqrt p1 * sqrt p2 \<le> 1"
    using assms unfolding valid_chan_def by (intro mult_le_one) simp_all
  ultimately show ?thesis
    using assms unfolding valid_chan_def by (simp add: real_sqrt_mult)
qed

theorem cycle_channel:
  "chan pr cr (chan e1 e2 (chan pw cw r)) = chan (pw * e1 * pr) (cw * e2 * cr) r"
  by (simp add: chan_comp)

theorem rfloor_antimono_p:
  assumes "p \<le> p'"
  shows "rfloor p' c \<le> rfloor p c"
  using assms unfolding rfloor_def by simp

theorem rfloor_antimono_c:
  assumes "c \<le> c'"
  shows "rfloor p c' \<le> rfloor p c"
  using assms unfolding rfloor_def by simp

theorem cycle_floor:
  fixes p1 p2 c1 c2 P C e1 e2 :: real
  assumes "0 \<le> p1" and "p1 \<le> P" and "0 \<le> p2" and "p2 \<le> P"
    and "0 \<le> c1" and "c1 \<le> C" and "0 \<le> c2" and "c2 \<le> C"
    and "0 \<le> e1" and "e1 \<le> 1" and "0 \<le> e2" and "e2 \<le> 1"
  shows "(1 - P\<^sup>2 * e1) / 6 + (1 - C\<^sup>2 * e2) / 3 \<le> rfloor (p1 * p2 * e1) (c1 * c2 * e2)"
proof -
  have pp: "p1 * p2 \<le> P * P" using assms(1-4) by (intro mult_mono) simp_all
  have cc: "c1 * c2 \<le> C * C" using assms(5-8) by (intro mult_mono) simp_all
  have "p1 * p2 * e1 \<le> P * P * e1" using pp assms(9) by (intro mult_right_mono)
  moreover have "c1 * c2 * e2 \<le> C * C * e2" using cc assms(11) by (intro mult_right_mono)
  moreover have "P\<^sup>2 * e1 = P * P * e1" and "C\<^sup>2 * e2 = C * C * e2" by (simp_all add: power2_eq_square)
  ultimately have h1: "1 - P\<^sup>2 * e1 \<le> 1 - p1 * p2 * e1" and h2: "1 - C\<^sup>2 * e2 \<le> 1 - c1 * c2 * e2"
    by linarith+
  have "(1 - P\<^sup>2 * e1) / 6 \<le> (1 - p1 * p2 * e1) / 6" by (rule divide_right_mono[OF h1]) simp
  moreover have "(1 - C\<^sup>2 * e2) / 3 \<le> (1 - c1 * c2 * e2) / 3" by (rule divide_right_mono[OF h2]) simp
  ultimately show ?thesis unfolding rfloor_def by (rule add_mono)
qed

section \<open>B. Correlated offsets: the square pulse\<close>

theorem square_corr:
  fixes A0 z0 sq sm C V x y u :: real
  assumes "0 < z0" and "A0 = pi / 2 * z0" and "0 \<le> sq" and "0 \<le> sm" and "0 \<le> C"
    and "V = sq + sm - 2 * C" and "0 \<le> V" and "0 \<le> x" and "0 \<le> y" and "0 \<le> u" and "u \<le> z0"
    and "(z0 - u)\<^sup>2 \<le> x * y"
    and "V \<le> pi / 2 * sqrt ((sq + C) * (sm + C))"
  shows "0 \<le> 2 * V * (u\<^sup>2 - z0\<^sup>2) + 2 * A0 * ((sq + C) * x + (sm + C) * y)
              + sq * x\<^sup>2 + 2 * C * x * y + sm * y\<^sup>2"
proof -
  define a where "a = sq + C"
  define b where "b = sm + C"
  define s where "s = sqrt (a * b)"
  have a0: "0 \<le> a" and b0: "0 \<le> b" unfolding a_def b_def using assms(3-5) by simp_all
  have ab0: "0 \<le> a * b" using a0 b0 by (rule mult_nonneg_nonneg)
  have s0: "0 \<le> s" unfolding s_def by (rule real_sqrt_ge_zero[OF ab0])
  have s2: "s\<^sup>2 = a * b" unfolding s_def using ab0 by (simp add: real_sqrt_pow2)
  have zu: "0 \<le> z0 - u" using assms(11) by simp
  have h1: "2 * s * (z0 - u) \<le> a * x + b * y"
  proof -
    have "(2 * s * (z0 - u))\<^sup>2 = 4 * s\<^sup>2 * (z0 - u)\<^sup>2" by (simp add: power_mult_distrib)
    also have "\<dots> = 4 * (a * b) * (z0 - u)\<^sup>2" using s2 by simp
    also have "\<dots> \<le> 4 * (a * b) * (x * y)"
    proof (rule mult_left_mono[OF assms(12)])
      show "0 \<le> 4 * (a * b)" using ab0 by simp
    qed
    also have "\<dots> \<le> (a * x + b * y)\<^sup>2"
    proof -
      have "0 \<le> (a * x - b * y)\<^sup>2" by simp
      then show ?thesis by (simp add: power2_eq_square algebra_simps)
    qed
    finally have "(2 * s * (z0 - u))\<^sup>2 \<le> (a * x + b * y)\<^sup>2" .
    moreover have "0 \<le> a * x + b * y" using a0 b0 assms(8,9) by simp
    ultimately show ?thesis by (rule power2_le_imp_le)
  qed
  have t1: "pi * z0 * (2 * s * (z0 - u)) \<le> pi * z0 * (a * x + b * y)"
    using h1 assms(1) pi_gt_zero by (intro mult_left_mono) simp_all
  have h2: "2 * V * z0 \<le> pi * z0 * s"
  proof -
    have "V \<le> pi / 2 * s" using assms(13) unfolding s_def a_def b_def by simp
    then have "2 * z0 * V \<le> 2 * z0 * (pi / 2 * s)" using assms(1) by (intro mult_left_mono) simp_all
    then show ?thesis by (simp add: algebra_simps)
  qed
  have t2: "2 * V * z0 * (z0 - u) \<le> pi * z0 * s * (z0 - u)"
    using h2 zu by (intro mult_right_mono)
  have t3: "0 \<le> V * (z0 - u)\<^sup>2" using assms(7) by simp
  have q: "0 \<le> sq * x\<^sup>2 + 2 * C * x * y + sm * y\<^sup>2"
    using assms(3-5,8,9) by (simp add: power2_eq_square)
  have e: "2 * V * (u\<^sup>2 - z0\<^sup>2) + 2 * A0 * ((sq + C) * x + (sm + C) * y)
           + sq * x\<^sup>2 + 2 * C * x * y + sm * y\<^sup>2
         = - 2 * V * (z0 - u) * (z0 + u) + pi * z0 * (a * x + b * y)
           + (sq * x\<^sup>2 + 2 * C * x * y + sm * y\<^sup>2)"
    unfolding assms(2) a_def b_def by (simp add: power2_eq_square algebra_simps)
  have "- 2 * V * (z0 - u) * (z0 + u) + 4 * V * z0 * (z0 - u) = 2 * V * (z0 - u)\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  then show ?thesis using e t1 t2 t3 q by linarith
qed

theorem square_corr_far:
  fixes A0 z0 sq sm C V x y u :: real
  assumes "0 < z0" and "0 \<le> A0" and "0 \<le> sq" and "0 \<le> sm" and "0 \<le> C"
    and "V = sq + sm - 2 * C" and "0 \<le> V" and "0 \<le> x" and "0 \<le> y" and "z0 < u"
  shows "0 \<le> 2 * V * (u\<^sup>2 - z0\<^sup>2) + 2 * A0 * ((sq + C) * x + (sm + C) * y)
              + sq * x\<^sup>2 + 2 * C * x * y + sm * y\<^sup>2"
proof -
  have "z0\<^sup>2 \<le> u\<^sup>2" using assms(1,10) by (intro power_mono) simp_all
  then have t1: "0 \<le> 2 * V * (u\<^sup>2 - z0\<^sup>2)" using assms(7) by simp
  have t2: "0 \<le> 2 * A0 * ((sq + C) * x + (sm + C) * y)"
    using assms(2-5,8,9) by simp
  have t3: "0 \<le> sq * x\<^sup>2 + 2 * C * x * y + sm * y\<^sup>2"
    using assms(3-5,8,9) by (simp add: power2_eq_square)
  show ?thesis using t1 t2 t3 by linarith
qed

theorem square_corr_uncorrelated_fails:
  fixes sq sm :: real
  assumes "0 < sq" and "0 < sm"
  shows "pi / 2 * sqrt (sq * sm) < sq + sm"
proof -
  define s where "s = sqrt (sq * sm)"
  have ab0: "0 \<le> sq * sm" using assms by simp
  have s0: "0 \<le> s" unfolding s_def by (rule real_sqrt_ge_zero[OF ab0])
  have s2: "s\<^sup>2 = sq * sm" unfolding s_def using ab0 by (simp add: real_sqrt_pow2)
  have "s\<^sup>2 \<le> ((sq + sm) / 2)\<^sup>2"
  proof -
    have "((sq + sm) / 2)\<^sup>2 - s\<^sup>2 = ((sq - sm) / 2)\<^sup>2"
      using s2 by (simp add: power2_eq_square algebra_simps)
    moreover have "0 \<le> ((sq - sm) / 2)\<^sup>2" by simp
    ultimately show ?thesis by linarith
  qed
  moreover have "0 \<le> (sq + sm) / 2"
  proof (rule divide_nonneg_nonneg)
    show "0 \<le> sq + sm" using assms by (intro add_nonneg_nonneg) (simp_all add: less_imp_le)
    show "0 \<le> (2::real)" by simp
  qed
  ultimately have "s \<le> (sq + sm) / 2" by (rule power2_le_imp_le)
  moreover have "0 \<le> pi / 2" using pi_gt_zero by linarith
  ultimately have "pi / 2 * s \<le> pi / 2 * ((sq + sm) / 2)" by (rule mult_left_mono)
  also have "\<dots> < sq + sm"
  proof -
    have p4: "pi / 4 < 1" using pi_less_4 by linarith
    have pos: "0 < sq + sm" using assms by (rule add_pos_pos)
    have "pi / 2 * ((sq + sm) / 2) = pi / 4 * (sq + sm)" by (simp add: algebra_simps)
    also have "\<dots> < 1 * (sq + sm)" by (rule mult_strict_right_mono[OF p4 pos])
    also have "\<dots> = sq + sm" by simp
    finally show ?thesis .
  qed
  finally show ?thesis unfolding s_def .
qed

theorem square_corr_equal_variances:
  fixes s0 kappa :: real
  assumes "0 < s0" and "0 \<le> kappa"
  shows "s0 + s0 - 2 * (kappa * s0) \<le> pi / 2 * sqrt ((s0 + kappa * s0) * (s0 + kappa * s0))
         \<longleftrightarrow> (4 - pi) / (4 + pi) \<le> kappa"
proof -
  have t0: "0 \<le> s0 + kappa * s0" using assms by simp
  have sq: "sqrt ((s0 + kappa * s0) * (s0 + kappa * s0)) = s0 * (1 + kappa)"
  proof -
    have "s0 * (1 + kappa) = s0 + kappa * s0" by (simp add: algebra_simps)
    then show ?thesis using t0 by (simp only: real_sqrt_abs2 abs_of_nonneg)
  qed
  have "s0 + s0 - 2 * (kappa * s0) \<le> pi / 2 * sqrt ((s0 + kappa * s0) * (s0 + kappa * s0))
        \<longleftrightarrow> s0 * (2 - 2 * kappa) \<le> s0 * (pi / 2 * (1 + kappa))"
    using sq by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> 2 - 2 * kappa \<le> pi / 2 * (1 + kappa)" using assms(1) by simp
  also have "\<dots> \<longleftrightarrow> 4 - pi \<le> kappa * (4 + pi)" by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> (4 - pi) / (4 + pi) \<le> kappa"
  proof -
    have hp: "0 < 4 + pi" using pi_gt_zero by linarith
    show ?thesis by (rule pos_divide_le_eq[OF hp, symmetric])
  qed
  finally show ?thesis .
qed

section \<open>C. Vertex inequalities for very unequal rates\<close>

theorem omega_le_kappa_iff:
  fixes delta a P :: real
  assumes "1 < delta" and "2 < a" and "a\<^sup>2 = delta\<^sup>2 + P"
  shows "sqrt (delta\<^sup>2 - 1) \<le> sqrt (a\<^sup>2 - 4) \<longleftrightarrow> 3 \<le> P"
proof -
  have d2: "1 < delta\<^sup>2"
  proof -
    have "1\<^sup>2 < delta\<^sup>2" using assms(1) by (intro power_strict_mono) simp_all
    then show ?thesis by simp
  qed
  have a2: "4 < a\<^sup>2"
  proof -
    have "2\<^sup>2 < a\<^sup>2" using assms(2) by (intro power_strict_mono) simp_all
    then show ?thesis by simp
  qed
  have "sqrt (delta\<^sup>2 - 1) \<le> sqrt (a\<^sup>2 - 4) \<longleftrightarrow> delta\<^sup>2 - 1 \<le> a\<^sup>2 - 4"
  proof
    assume h: "sqrt (delta\<^sup>2 - 1) \<le> sqrt (a\<^sup>2 - 4)"
    have x0: "0 \<le> delta\<^sup>2 - 1" using d2 by simp
    have "(sqrt (delta\<^sup>2 - 1))\<^sup>2 \<le> (sqrt (a\<^sup>2 - 4))\<^sup>2"
      by (rule power_mono[OF h real_sqrt_ge_zero[OF x0]])
    then show "delta\<^sup>2 - 1 \<le> a\<^sup>2 - 4" using d2 a2 by (simp add: real_sqrt_pow2)
  next
    assume "delta\<^sup>2 - 1 \<le> a\<^sup>2 - 4"
    then show "sqrt (delta\<^sup>2 - 1) \<le> sqrt (a\<^sup>2 - 4)" by (rule real_sqrt_le_mono)
  qed
  also have "\<dots> \<longleftrightarrow> 3 \<le> P" using assms(3) by linarith
  finally show ?thesis .
qed

theorem vertex_ineq:
  fixes delta a P :: real
  assumes "1 < delta" and "3 \<le> P" and "a\<^sup>2 = delta\<^sup>2 + P"
  shows "2 * delta\<^sup>2 - 3 \<le> a\<^sup>2 * (sqrt (delta\<^sup>2 - 1))\<^sup>2 - delta ^ 4"
proof -
  have d2: "1 < delta\<^sup>2" using assms(1) by (simp add: one_less_power)
  have "(sqrt (delta\<^sup>2 - 1))\<^sup>2 = delta\<^sup>2 - 1" using d2 by (simp add: real_sqrt_pow2)
  then have "a\<^sup>2 * (sqrt (delta\<^sup>2 - 1))\<^sup>2 - delta ^ 4 - (2 * delta\<^sup>2 - 3) = (P - 3) * (delta\<^sup>2 - 1)"
    using assms(3) by (simp add: power4_eq_xxxx power2_eq_square algebra_simps)
  moreover have "0 \<le> (P - 3) * (delta\<^sup>2 - 1)" using assms(2) d2 by simp
  ultimately show ?thesis by linarith
qed

theorem delta_sq_over_omega_lt_a:
  fixes delta a P :: real
  assumes "1 < delta" and "3 \<le> P" and "a\<^sup>2 = delta\<^sup>2 + P" and "0 < a" and "3 / 2 < delta\<^sup>2"
  shows "delta\<^sup>2 / sqrt (delta\<^sup>2 - 1) < a"
proof -
  have d2: "1 < delta\<^sup>2" using assms(1) by (simp add: one_less_power)
  define Om where "Om = sqrt (delta\<^sup>2 - 1)"
  have Op: "0 < Om" unfolding Om_def using d2 by simp
  have O2: "Om\<^sup>2 = delta\<^sup>2 - 1" unfolding Om_def using d2 by (simp add: real_sqrt_pow2)
  have v: "2 * delta\<^sup>2 - 3 \<le> a\<^sup>2 * Om\<^sup>2 - delta ^ 4"
    unfolding Om_def by (rule vertex_ineq[OF assms(1-3)])
  have d4: "(delta\<^sup>2)\<^sup>2 = delta ^ 4" by (simp flip: power_mult)
  have aO: "(a * Om)\<^sup>2 = a\<^sup>2 * Om\<^sup>2" by (simp add: power_mult_distrib)
  have "(delta\<^sup>2)\<^sup>2 < (a * Om)\<^sup>2" using v assms(5) d4 aO by linarith
  moreover have "0 \<le> a * Om" using assms(4) Op by (intro mult_nonneg_nonneg) simp_all
  ultimately have "delta\<^sup>2 < a * Om" by (rule power2_less_imp_less)
  then show ?thesis unfolding Om_def[symmetric] using Op by (simp add: divide_less_eq algebra_simps)
qed

theorem final_bound:
  fixes u w h Om :: real
  assumes "0 < u" and "0 < w" and "0 < h" and "0 < Om" and "h + 2 * Om * u \<le> w"
  shows "u < w / (2 * Om)"
    and "2 \<le> Om \<Longrightarrow> 2 * u - w / 2 < 0"
proof -
  have "u * (2 * Om) < w" using assms by (simp add: algebra_simps)
  then show "u < w / (2 * Om)" using assms(4) by (simp add: less_divide_eq)
  show "2 \<le> Om \<Longrightarrow> 2 * u - w / 2 < 0"
  proof -
    assume "2 \<le> Om"
    then have "4 * u \<le> 2 * Om * u" using assms(1) by (simp add: mult_right_mono)
    then show ?thesis using \<open>u * (2 * Om) < w\<close> by (simp add: algebra_simps)
  qed
qed

section \<open>D. The second-order kernel of the exact optimality of the resonant pulse\<close>

definition f_res :: "real \<Rightarrow> real \<Rightarrow> real" where
  "f_res D t = (t - D)\<^sup>2 + t\<^sup>2"

definition f_env :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "f_env D x t = (if t \<le> x then f_res D t else (t - D)\<^sup>2 + 2 * x * t - x\<^sup>2)"

theorem f_res_min:
  fixes D t :: real
  shows "D\<^sup>2 / 2 \<le> f_res D t" and "f_res D (D / 2) = D\<^sup>2 / 2"
proof -
  have e: "f_res D t - D\<^sup>2 / 2 = 2 * (t - D / 2)\<^sup>2" unfolding f_res_def
    by (simp add: power2_eq_square algebra_simps)
  have n: "0 \<le> (t - D / 2)\<^sup>2" by simp
  show "D\<^sup>2 / 2 \<le> f_res D t" using e n by linarith
  show "f_res D (D / 2) = D\<^sup>2 / 2" unfolding f_res_def by (simp add: power2_eq_square algebra_simps)
qed

lemma f_env_tail:
  fixes t D x :: real
  shows "(t - D)\<^sup>2 + 2 * x * t - x\<^sup>2 = (t - D + x)\<^sup>2 + 2 * x * (D - x)"
  by (simp add: power2_eq_square algebra_simps)

theorem f_env_large:
  fixes D x t :: real
  assumes "0 < D" and "D / 2 \<le> x" and "0 \<le> t"
  shows "D\<^sup>2 / 2 \<le> f_env D x t" and "f_env D x (D / 2) = D\<^sup>2 / 2"
proof -
  show "D\<^sup>2 / 2 \<le> f_env D x t"
  proof (cases "t \<le> x")
    case True
    then show ?thesis unfolding f_env_def using f_res_min(1) by simp
  next
    case False
    then have tx: "x < t" by simp
    have "(2 * x - D)\<^sup>2 \<le> (t - D + x)\<^sup>2" using assms(2) tx by (intro power_mono) simp_all
    moreover have "0 \<le> (D - 2 * x)\<^sup>2" by simp
    moreover have "(2 * x - D)\<^sup>2 + 2 * x * (D - x) - D\<^sup>2 / 2 = (D - 2 * x)\<^sup>2 / 2"
      by (simp add: power2_eq_square algebra_simps)
    moreover have "f_env D x t = (t - D + x)\<^sup>2 + 2 * x * (D - x)"
      unfolding f_env_def using False f_env_tail by simp
    ultimately show ?thesis by linarith
  qed
  show "f_env D x (D / 2) = D\<^sup>2 / 2"
    unfolding f_env_def using assms(2) f_res_min(2) by simp
qed

theorem f_env_small:
  fixes D x t :: real
  assumes "0 < D" and "0 \<le> x" and "x < D / 2" and "0 \<le> t"
  shows "2 * x * (D - x) \<le> f_env D x t"
    and "f_env D x (D - x) = 2 * x * (D - x)"
    and "D\<^sup>2 / 2 - 2 * x * (D - x) = (D - 2 * x)\<^sup>2 / 2"
proof -
  show "2 * x * (D - x) \<le> f_env D x t"
  proof (cases "t \<le> x")
    case True
    have "f_res D t - f_res D x = 2 * (t - x) * (t + x - D)"
      unfolding f_res_def by (simp add: power2_eq_square algebra_simps)
    moreover have "0 \<le> 2 * (t - x) * (t + x - D)"
    proof (intro mult_nonpos_nonpos)
      show "2 * (t - x) \<le> 0" using True by simp
      show "t + x - D \<le> 0" using True assms(3) by linarith
    qed
    moreover have "f_res D x - 2 * x * (D - x) = (D - 2 * x)\<^sup>2"
      unfolding f_res_def by (simp add: power2_eq_square algebra_simps)
    moreover have "0 \<le> (D - 2 * x)\<^sup>2" by simp
    moreover have "f_env D x t = f_res D t" unfolding f_env_def using True by simp
    ultimately show ?thesis by linarith
  next
    case False
    have "f_env D x t = (t - D + x)\<^sup>2 + 2 * x * (D - x)"
      unfolding f_env_def using False f_env_tail by simp
    moreover have "0 \<le> (t - D + x)\<^sup>2" by simp
    moreover have "0 \<le> x * (D - x)" using assms(2,3) by simp
    ultimately show ?thesis by linarith
  qed
  show "f_env D x (D - x) = 2 * x * (D - x)"
    unfolding f_env_def using assms(3) by (simp add: f_env_tail)
  show "D\<^sup>2 / 2 - 2 * x * (D - x) = (D - 2 * x)\<^sup>2 / 2"
    by (simp add: power2_eq_square algebra_simps)
qed

section \<open>E. Elementary parts of the planar exposure lemma\<close>

definition a_z :: "real \<Rightarrow> real \<Rightarrow> real" where
  "a_z z phi = phi - (1 + z) * tan (phi / 2)"

definition b_z :: "real \<Rightarrow> real \<Rightarrow> real" where
  "b_z z phi = phi + (1 - z) * cot (phi / 2)"

lemma cos_half_pos:
  fixes phi :: real
  assumes "- pi < phi" and "phi < pi"
  shows "0 < cos (phi / 2)"
  using assms by (intro cos_gt_zero_pi) simp_all

lemma one_plus_cos:
  fixes phi :: real
  shows "1 + cos phi = 2 * (cos (phi / 2))\<^sup>2"
proof -
  have "cos phi = cos (2 * (phi / 2))" by simp
  also have "\<dots> = 2 * (cos (phi / 2))\<^sup>2 - 1" by (rule cos_double_cos)
  finally show ?thesis by simp
qed

lemma one_minus_cos:
  fixes phi :: real
  shows "1 - cos phi = 2 * (sin (phi / 2))\<^sup>2"
proof -
  have "cos phi = cos (2 * (phi / 2))" by simp
  also have "\<dots> = 1 - 2 * (sin (phi / 2))\<^sup>2" by (rule cos_double_sin)
  finally show ?thesis by simp
qed

theorem a_z_deriv:
  fixes z phi :: real
  assumes "- pi < phi" and "phi < pi"
  shows "(a_z z has_real_derivative (cos phi - z) / (1 + cos phi)) (at phi)"
proof -
  define c where "c = cos (phi / 2)"
  have cp: "0 < c" unfolding c_def by (rule cos_half_pos[OF assms])
  have h: "((\<lambda>t. t - (1 + z) * tan (t / 2)) has_real_derivative
            1 - (1 + z) * (inverse (c\<^sup>2) * (1 / 2))) (at phi)"
    unfolding c_def using cp[unfolded c_def]
    by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  have e: "1 - (1 + z) * (inverse (c\<^sup>2) * (1 / 2)) = (cos phi - z) / (1 + cos phi)"
  proof -
    have "1 + cos phi = 2 * c\<^sup>2" unfolding c_def by (rule one_plus_cos)
    moreover have "cos phi = 2 * c\<^sup>2 - 1" using calculation by simp
    ultimately show ?thesis using cp by (simp add: field_simps)
  qed
  show ?thesis unfolding a_z_def using h e by simp
qed

theorem b_z_deriv:
  fixes z phi :: real
  assumes "0 < phi" and "phi < pi"
  shows "(b_z z has_real_derivative (z - cos phi) / (1 - cos phi)) (at phi)"
proof -
  have sp: "0 < sin (phi / 2)" using assms by (intro sin_gt_zero) simp_all
  have sne: "sin (phi / 2) \<noteq> 0" using sp by simp
  have h: "((\<lambda>t. t + (1 - z) * (cos (t / 2) / sin (t / 2))) has_real_derivative
            1 + (1 - z) * ((- sin (phi / 2) * (1 / 2) * sin (phi / 2)
                            - cos (phi / 2) * (cos (phi / 2) * (1 / 2))) / (sin (phi / 2))\<^sup>2)) (at phi)"
    using sne by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)
      (simp only: diff_divide_distrib add_divide_distrib[symmetric] right_diff_distrib, simp add: algebra_simps)
  have n: "- sin (phi / 2) * (1 / 2) * sin (phi / 2) - cos (phi / 2) * (cos (phi / 2) * (1 / 2)) = - (1 / 2)"
  proof -
    have "- sin (phi / 2) * (1 / 2) * sin (phi / 2) - cos (phi / 2) * (cos (phi / 2) * (1 / 2))
          = - ((sin (phi / 2))\<^sup>2 + (cos (phi / 2))\<^sup>2) / 2"
      by (simp add: power2_eq_square algebra_simps)
    then show ?thesis by simp
  qed
  have cp: "cos phi = 1 - 2 * (sin (phi / 2))\<^sup>2" using one_minus_cos[of phi] by linarith
  have s2: "(sin (phi / 2))\<^sup>2 \<noteq> 0" using sne by simp
  have e: "1 + (1 - z) * ((- sin (phi / 2) * (1 / 2) * sin (phi / 2)
                            - cos (phi / 2) * (cos (phi / 2) * (1 / 2))) / (sin (phi / 2))\<^sup>2)
           = (z - cos phi) / (1 - cos phi)"
    unfolding n cp using s2 by (simp add: field_simps)
  show ?thesis unfolding b_z_def cot_def using h e by simp
qed

lemma arccos_facts:
  fixes z :: real
  assumes "0 \<le> z" and "z < 1"
  shows "0 < arccos z" and "arccos z \<le> pi / 2" and "cos (arccos z) = z"
proof -
  have zl: "- 1 \<le> z" and zu: "z \<le> 1" using assms by linarith+
  have c: "cos (arccos z) = z" by (rule cos_arccos[OF zl zu])
  have lb: "0 \<le> arccos z" by (rule arccos_lbound[OF zl zu])
  show "0 < arccos z"
  proof (rule ccontr)
    assume "\<not> 0 < arccos z"
    then have "arccos z = 0" using lb by simp
    then have "z = 1" using c by simp
    then show False using assms(2) by simp
  qed
  show "arccos z \<le> pi / 2" by (rule arccos_le_pi2[OF assms(1) zu])
  show "cos (arccos z) = z" by (rule c)
qed

theorem a_z_deriv_nonneg:
  fixes z phi :: real
  assumes "0 \<le> z" and "z < 1" and "0 < phi" and "phi \<le> arccos z"
  shows "0 \<le> (cos phi - z) / (1 + cos phi)"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have "cos (arccos z) \<le> cos phi"
    using assms(3,4) d2 pi_gt_zero by (intro cos_monotone_0_pi_le) linarith+
  then have "z \<le> cos phi" using arccos_facts(3)[OF assms(1,2)] by simp
  moreover have "0 < 1 + cos phi"
  proof -
    have "0 \<le> cos phi" using assms(3,4) d2 by (intro cos_ge_zero) simp_all
    then show ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

theorem b_z_deriv_nonpos:
  fixes z phi :: real
  assumes "0 \<le> z" and "z < 1" and "0 < phi" and "phi \<le> arccos z"
  shows "(z - cos phi) / (1 - cos phi) \<le> 0"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have "cos (arccos z) \<le> cos phi"
    using assms(3,4) d2 pi_gt_zero by (intro cos_monotone_0_pi_le) linarith+
  then have zc: "z \<le> cos phi" using arccos_facts(3)[OF assms(1,2)] by simp
  have "0 < sin (phi / 2)" using assms(3,4) d2 by (intro sin_gt_zero) simp_all
  then have "0 < 1 - cos phi" using one_minus_cos[of phi] by simp
  then show ?thesis using zc by (intro divide_nonpos_pos) simp_all
qed

theorem a_z_at_d:
  fixes z :: real
  assumes "0 \<le> z" and "z < 1"
  shows "a_z z (arccos z) = arccos z - sin (arccos z)"
proof -
  define d where "d = arccos z"
  have d0: "0 < d" unfolding d_def by (rule arccos_facts(1)[OF assms])
  have d2: "d \<le> pi / 2" unfolding d_def by (rule arccos_facts(2)[OF assms])
  have zc: "z = cos d" unfolding d_def using arccos_facts(3)[OF assms] by simp
  have c: "0 < cos (d / 2)" using d0 d2 by (intro cos_gt_zero_pi) simp_all
  have "(1 + cos d) * tan (d / 2) = sin d"
  proof -
    have sd: "2 * (cos (d / 2) * sin (d / 2)) = sin d"
      using sin_double[of "d / 2"] by (simp add: mult_ac)
    show ?thesis using c sd by (simp add: one_plus_cos tan_def field_simps power2_eq_square)
  qed
  then show ?thesis unfolding a_z_def d_def[symmetric] using zc by simp
qed

theorem b_z_at_d:
  fixes z :: real
  assumes "0 \<le> z" and "z < 1"
  shows "b_z z (arccos z) = arccos z + sin (arccos z)"
proof -
  define d where "d = arccos z"
  have d0: "0 < d" unfolding d_def by (rule arccos_facts(1)[OF assms])
  have d2: "d \<le> pi / 2" unfolding d_def by (rule arccos_facts(2)[OF assms])
  have zc: "z = cos d" unfolding d_def using arccos_facts(3)[OF assms] by simp
  have s: "0 < sin (d / 2)" using d0 d2 by (intro sin_gt_zero) simp_all
  have "(1 - cos d) * cot (d / 2) = sin d"
  proof -
    have sd: "2 * (cos (d / 2) * sin (d / 2)) = sin d"
      using sin_double[of "d / 2"] by (simp add: mult_ac)
    show ?thesis using s sd by (simp add: one_minus_cos cot_def field_simps power2_eq_square)
  qed
  then show ?thesis unfolding b_z_def d_def[symmetric] using zc by simp
qed

theorem a_z_tendsto_zero:
  fixes z :: real
  shows "(a_z z \<longlongrightarrow> 0) (at 0)"
proof -
  have "(a_z z has_real_derivative (cos 0 - z) / (1 + cos 0)) (at 0)"
    by (rule a_z_deriv) simp_all
  then have "isCont (a_z z) 0" by (rule DERIV_isCont)
  then have "(a_z z \<longlongrightarrow> a_z z 0) (at 0)" by (simp add: isCont_def)
  moreover have "a_z z 0 = 0" unfolding a_z_def by simp
  ultimately show ?thesis by simp
qed

theorem a_z_mono:
  fixes z p1 p2 :: real
  assumes "0 \<le> z" and "z < 1" and "0 < p1" and "p1 \<le> p2" and "p2 \<le> arccos z"
  shows "a_z z p1 \<le> a_z z p2"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have D: "\<exists>y. DERIV (a_z z) x :> y \<and> 0 \<le> y" if x1: "p1 \<le> x" and x2: "x \<le> p2" for x
  proof -
    have r1: "- pi < x" and r2: "x < pi" using x1 x2 assms(3,5) d2 pi_gt_zero by linarith+
    have "(a_z z has_real_derivative (cos x - z) / (1 + cos x)) (at x)"
      by (rule a_z_deriv[OF r1 r2])
    moreover have "0 \<le> (cos x - z) / (1 + cos x)"
      using x1 x2 assms by (intro a_z_deriv_nonneg) linarith+
    ultimately show ?thesis by blast
  qed
  show ?thesis
    by (rule DERIV_nonneg_imp_nondecreasing[OF assms(4)]) (blast intro: D)
qed

theorem b_z_antimono:
  fixes z p1 p2 :: real
  assumes "0 \<le> z" and "z < 1" and "0 < p1" and "p1 \<le> p2" and "p2 \<le> arccos z"
  shows "b_z z p2 \<le> b_z z p1"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have D: "\<exists>y. DERIV (b_z z) x :> y \<and> y \<le> 0" if x1: "p1 \<le> x" and x2: "x \<le> p2" for x
  proof -
    have r1: "0 < x" and r2: "x < pi" using x1 x2 assms(3,5) d2 pi_gt_zero by linarith+
    have "(b_z z has_real_derivative (z - cos x) / (1 - cos x)) (at x)"
      by (rule b_z_deriv[OF r1 r2])
    moreover have "(z - cos x) / (1 - cos x) \<le> 0"
      using x1 x2 assms by (intro b_z_deriv_nonpos) linarith+
    ultimately show ?thesis by blast
  qed
  show ?thesis
    by (rule DERIV_nonpos_imp_nonincreasing[OF assms(4)]) (blast intro: D)
qed

theorem a_z_range:
  fixes z y :: real
  assumes "0 \<le> z" and "z < 1" and "0 < y" and "y \<le> arccos z - sin (arccos z)"
  shows "\<exists>phi. 0 < phi \<and> phi \<le> arccos z \<and> a_z z phi = y"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have d0: "0 < arccos z" by (rule arccos_facts(1)[OF assms(1,2)])
  have "\<exists>phi. 0 \<le> phi \<and> phi \<le> arccos z \<and> a_z z phi = y"
  proof (rule IVT[where f = "a_z z"])
    show "a_z z 0 \<le> y" unfolding a_z_def using assms(3) by simp
    show "y \<le> a_z z (arccos z)" using a_z_at_d[OF assms(1,2)] assms(4) by simp
    show "0 \<le> arccos z" using d0 by simp
    show "\<forall>x. 0 \<le> x \<and> x \<le> arccos z \<longrightarrow> isCont (a_z z) x"
    proof (intro allI impI)
      fix x assume x: "0 \<le> x \<and> x \<le> arccos z"
      have r1: "- pi < x" and r2: "x < pi" using x d2 pi_gt_zero by linarith+
      have "(a_z z has_real_derivative (cos x - z) / (1 + cos x)) (at x)"
        by (rule a_z_deriv[OF r1 r2])
      then show "isCont (a_z z) x" by (rule DERIV_isCont)
    qed
  qed
  then obtain phi where p: "0 \<le> phi" "phi \<le> arccos z" "a_z z phi = y" by blast
  have "phi \<noteq> 0" using p(3) assms(3) unfolding a_z_def by auto
  then have "0 < phi" using p(1) by simp
  then show ?thesis using p(2,3) by blast
qed

theorem cos_sq_half_integral:
  fixes L :: real
  assumes "0 \<le> L"
  shows "((\<lambda>alpha. (cos (alpha / 2))\<^sup>2) has_integral (L / 2 + sin L / 2)) {0..L}"
proof -
  define F where "F alpha = alpha / 2 + sin alpha / 2" for alpha :: real
  have D: "(F has_vector_derivative (cos (x / 2))\<^sup>2) (at x within {0..L})" for x :: real
  proof -
    have "(F has_real_derivative 1 / 2 + cos x / 2) (at x)"
      unfolding F_def by (auto intro!: derivative_eq_intros)
    moreover have "1 / 2 + cos x / 2 = (cos (x / 2))\<^sup>2"
      using one_plus_cos[of x] by simp
    ultimately have "(F has_real_derivative (cos (x / 2))\<^sup>2) (at x)" by simp
    then have "(F has_vector_derivative (cos (x / 2))\<^sup>2) (at x)"
      by (simp add: has_real_derivative_iff_has_vector_derivative)
    then show ?thesis by (rule has_vector_derivative_at_within)
  qed
  have "((\<lambda>alpha. (cos (alpha / 2))\<^sup>2) has_integral (F L - F 0)) {0..L}"
    by (rule fundamental_theorem_of_calculus) (use assms D in auto)
  then show ?thesis unfolding F_def by simp
qed

theorem odd_turns_integral:
  fixes k :: nat
  shows "((\<lambda>alpha. (cos (alpha / 2))\<^sup>2) has_integral ((2 * real k + 1) * pi / 2))
         {0..(2 * real k + 1) * pi}"
proof -
  define L where "L = (2 * real k + 1) * pi"
  have L0: "0 \<le> L" unfolding L_def by simp
  have "sin L = 0"
  proof -
    have "L = real (2 * k + 1) * pi" unfolding L_def by simp
    then show ?thesis by (simp only: sin_npi)
  qed
  then show ?thesis using cos_sq_half_integral[OF L0] unfolding L_def[symmetric] by (simp add: L_def)
qed

end
