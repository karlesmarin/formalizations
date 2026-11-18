(*  Title:      Induced_Rate_Optimum.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Algebraic and analytic core of the theorem on rates induced by the coupling (memory-floor notes):
    (T2a) the optimal constant amplitude for a rest rate X and an induced rate K g^2 (arithmetic-geometric
          mean, the threshold K G^2 <= X, equipartition);
    (T2b) the same for a power law K g^k, k > 1: critical point and the induced share X/(k-1);
    (T3a) pointwise AM-GM with a cap on the amplitude;
    (T3b) weighted Cauchy-Schwarz in finite form (superadditivity step of the profile bound) and its
          consequence for lower bounds on the pairwise kernels;
    (T3c) the extreme pair of integrals, whose normalised overlap is 2/pi.
    Everything is over the reals; the reduction of the master equation to the first-order density is
    a written proof and is not formalised.
*)
theory Induced_Rate_Optimum
  imports "HOL-Analysis.Analysis"
begin

section \<open>A. Constant amplitude with a quadratic induced rate (T2a)\<close>

text \<open>The cost of a constant pulse of amplitude g is (X + K g^2)/g: X is the rest rate, K g^2 the induced one.\<close>

theorem amgm_amplitude:
  fixes X K g :: real
  assumes "0 < X" "0 < K" "0 < g"
  shows "2 * sqrt (X * K) \<le> (X + K * g\<^sup>2) / g"
proof -
  have sX: "sqrt X ^ 2 = X" and sK: "sqrt K ^ 2 = K" using assms by simp_all
  have "(sqrt X - sqrt K * g) ^ 2 = X - 2 * (sqrt X * sqrt K) * g + K * g\<^sup>2"
    by (simp add: power2_diff power_mult_distrib sX sK algebra_simps)
  moreover have "(sqrt X - sqrt K * g) ^ 2 \<ge> 0" by simp
  ultimately have "2 * (sqrt X * sqrt K) * g \<le> X + K * g\<^sup>2" by linarith
  then show ?thesis
    using assms by (simp add: real_sqrt_mult pos_le_divide_eq)
qed

theorem amgm_amplitude_equality:
  fixes X K :: real
  assumes "0 < X" "0 < K"
  shows "(X + K * (sqrt (X / K))\<^sup>2) / sqrt (X / K) = 2 * sqrt (X * K)"
proof -
  let ?s = "sqrt (X / K)"
  have spos: "0 < ?s" using assms by simp
  have s2: "?s ^ 2 = X / K" using assms by simp
  have h: "?s * sqrt K = sqrt X"
    using assms by (simp add: real_sqrt_mult[symmetric])
  have sX: "sqrt X * sqrt X = X" using assms by simp
  have "2 * sqrt (X * K) * ?s = 2 * (sqrt X * (sqrt K * ?s))"
    by (simp add: real_sqrt_mult algebra_simps)
  also have "\<dots> = 2 * X" using h sX by (simp add: algebra_simps)
  finally have e: "2 * sqrt (X * K) * ?s = 2 * X" .
  have "X + K * ?s\<^sup>2 = 2 * X" using assms s2 by simp
  then have num: "X + K * ?s\<^sup>2 = 2 * sqrt (X * K) * ?s" using e by simp
  show ?thesis using num spos by simp
qed

theorem equipartition:
  fixes X K :: real
  assumes "0 < X" "0 < K"
  shows "K * (sqrt (X / K))\<^sup>2 = X"
  using assms by simp

theorem full_coupling_optimal:
  fixes X K G g :: real
  assumes "0 < X" "0 < K" "0 < G" "K * G\<^sup>2 \<le> X" "0 < g" "g \<le> G"
  shows "(X + K * G\<^sup>2) / G \<le> (X + K * g\<^sup>2) / g"
proof -
  have kg: "K * g * G \<le> X"
  proof -
    have "g * G \<le> G * G" using assms by (intro mult_right_mono) simp_all
    then have "K * (g * G) \<le> K * (G * G)" using assms by (intro mult_left_mono) simp_all
    moreover have "K * G\<^sup>2 = K * (G * G)" by (simp add: power2_eq_square)
    moreover have "K * g * G = K * (g * G)" by (simp add: mult.assoc)
    ultimately show ?thesis using assms(4) by linarith
  qed
  have key: "(X + K * g\<^sup>2) * G - (X + K * G\<^sup>2) * g = (G - g) * (X - K * g * G)"
    by (simp add: power2_eq_square algebra_simps)
  have "0 \<le> (G - g) * (X - K * g * G)"
    using assms kg by (intro mult_nonneg_nonneg) simp_all
  then have "(X + K * G\<^sup>2) * g \<le> (X + K * g\<^sup>2) * G" using key by linarith
  have "(X + K * g\<^sup>2) / g - (X + K * G\<^sup>2) / G
      = ((X + K * g\<^sup>2) * G - (X + K * G\<^sup>2) * g) / (g * G)"
    using assms by (simp add: field_simps)
  moreover have "0 \<le> ((X + K * g\<^sup>2) * G - (X + K * G\<^sup>2) * g) / (g * G)"
    using assms \<open>(X + K * G\<^sup>2) * g \<le> (X + K * g\<^sup>2) * G\<close> by (intro divide_nonneg_pos) simp_all
  ultimately show ?thesis by linarith
qed

text \<open>The control: without the threshold the statement fails (X = 1, K = 1, G = 4, g = 1).\<close>

lemma threshold_needed:
  "\<not> ((1::real) + 1 * 4\<^sup>2) / 4 \<le> (1 + 1 * 1\<^sup>2) / 1"
  by (simp add: power2_eq_square)

section \<open>B. Power-law induced rate (T2b)\<close>

definition cost_pow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "cost_pow k X K g = (X + K * g powr k) / g"

definition gstar_pow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "gstar_pow k X K = (X / ((k - 1) * K)) powr (1 / k)"

theorem cost_pow_derivative:
  fixes k X K g :: real
  assumes "0 < g"
  shows "(cost_pow k X K has_real_derivative (K * (k - 1) * g powr k - X) / g\<^sup>2) (at g)"
proof -
  have ph: "g powr (k - 1) * g = g powr k"
    using assms by (simp add: powr_diff powr_minus_divide)
  have "((\<lambda>x. (X + K * x powr k) / x) has_real_derivative
      (K * (k * g powr (k - 1)) * g - (X + K * g powr k)) / g\<^sup>2) (at g)"
    using assms by (intro derivative_eq_intros) (auto simp: power2_eq_square algebra_simps)
  moreover have eq: "K * (k * g powr (k - 1)) * g - (X + K * g powr k)
      = K * (k - 1) * g powr k - X"
  proof -
    have "K * (k * g powr (k - 1)) * g = K * k * (g powr (k - 1) * g)"
      by (simp add: algebra_simps)
    then show ?thesis using ph by (simp add: algebra_simps)
  qed
  ultimately show ?thesis unfolding cost_pow_def by (simp only: eq)
qed

theorem gstar_pow_pos:
  assumes "1 < k" "0 < X" "0 < K"
  shows "0 < gstar_pow k X K"
  using assms unfolding gstar_pow_def by (simp add: powr_gt_zero)

theorem gstar_pow_power:
  fixes k X K :: real
  assumes "1 < k" "0 < X" "0 < K"
  shows "gstar_pow k X K powr k = X / ((k - 1) * K)"
proof -
  have p: "0 < X / ((k - 1) * K)" using assms by simp
  have k0: "k \<noteq> 0" using assms by linarith
  have e1: "1 / k * k = (1::real)" using k0 by simp
  have h: "gstar_pow k X K powr k = (X / ((k - 1) * K)) powr (1 / k * k)"
    unfolding gstar_pow_def by (rule powr_powr)
  have h2: "gstar_pow k X K powr k = (X / ((k - 1) * K)) powr 1" using h by (simp only: e1)
  have h3: "(X / ((k - 1) * K)) powr 1 = X / ((k - 1) * K)"
    by (rule powr_one) (rule less_imp_le[OF p])
  show ?thesis using h2 h3 by (rule trans)
qed

theorem gstar_pow_induced_share:
  fixes k X K :: real
  assumes "1 < k" "0 < X" "0 < K"
  shows "K * gstar_pow k X K powr k = X / (k - 1)"
    and "(k - 1) * K * gstar_pow k X K powr k = X"
proof -
  have k1: "k - 1 \<noteq> 0" using assms by linarith
  show "K * gstar_pow k X K powr k = X / (k - 1)"
    using gstar_pow_power[OF assms] k1 assms by (simp add: field_simps)
  show "(k - 1) * K * gstar_pow k X K powr k = X"
    using gstar_pow_power[OF assms] k1 assms by (simp add: field_simps)
qed

theorem cost_pow_derivative_zero_at_gstar:
  fixes k X K :: real
  assumes "1 < k" "0 < X" "0 < K"
  shows "(K * (k - 1) * gstar_pow k X K powr k - X) / (gstar_pow k X K)\<^sup>2 = 0"
  using gstar_pow_induced_share(2)[OF assms] by (simp add: algebra_simps)

theorem cost_pow_derivative_zero_iff:
  fixes k X K g :: real
  assumes "1 < k" "0 < X" "0 < K" "0 < g"
  shows "(K * (k - 1) * g powr k - X) / g\<^sup>2 = 0 \<longleftrightarrow> g = gstar_pow k X K"
proof
  have k0: "k \<noteq> 0" and k1: "k - 1 \<noteq> 0" using assms by linarith+
  assume "(K * (k - 1) * g powr k - X) / g\<^sup>2 = 0"
  then have "K * (k - 1) * g powr k = X" using assms by simp
  then have "g powr k = X / ((k - 1) * K)" using k1 assms by (simp add: field_simps)
  then have "(g powr k) powr (1 / k) = gstar_pow k X K" unfolding gstar_pow_def by simp
  moreover have "(g powr k) powr (1 / k) = g" using assms k0 by (simp add: powr_powr)
  ultimately show "g = gstar_pow k X K" by simp
next
  assume "g = gstar_pow k X K"
  then show "(K * (k - 1) * g powr k - X) / g\<^sup>2 = 0"
    using cost_pow_derivative_zero_at_gstar[OF assms(1-3)] by simp
qed

section \<open>C. Pointwise AM-GM with a cap (T3a)\<close>

theorem amgm_pointwise:
  fixes A B g :: real
  assumes "0 < A" "0 < B" "0 < g"
  shows "2 * sqrt (A * B) \<le> A / g + B * g"
proof -
  have "A / g + B * g = (A + B * g\<^sup>2) / g" using assms by (simp add: field_simps power2_eq_square)
  then show ?thesis using amgm_amplitude[OF assms] by simp
qed

theorem amgm_pointwise_equality:
  fixes A B :: real
  assumes "0 < A" "0 < B"
  shows "A / sqrt (A / B) + B * sqrt (A / B) = 2 * sqrt (A * B)"
proof -
  have "A / sqrt (A / B) + B * sqrt (A / B) = (A + B * (sqrt (A / B))\<^sup>2) / sqrt (A / B)"
    using assms by (simp add: field_simps power2_eq_square)
  then show ?thesis using amgm_amplitude_equality[OF assms] by simp
qed

theorem amgm_pointwise_cap:
  fixes A B G g :: real
  assumes "0 < A" "0 < B" "0 < g" "g \<le> G" "G \<le> sqrt (A / B)"
  shows "A / G + B * G \<le> A / g + B * g"
proof -
  have G: "0 < G" using assms by linarith
  have "G\<^sup>2 \<le> (sqrt (A / B))\<^sup>2" using assms G by (intro power_mono) simp_all
  then have "G\<^sup>2 \<le> A / B" using assms by simp
  then have "G\<^sup>2 * B \<le> A / B * B" using assms by (intro mult_right_mono) simp_all
  then have "B * G\<^sup>2 \<le> A" using assms by (simp add: algebra_simps)
  then have "(A + B * G\<^sup>2) / G \<le> (A + B * g\<^sup>2) / g"
    using full_coupling_optimal[of A B G g] assms G by (simp add: algebra_simps)
  moreover have "A / G + B * G = (A + B * G\<^sup>2) / G" using G by (simp add: field_simps power2_eq_square)
  moreover have "A / g + B * g = (A + B * g\<^sup>2) / g" using assms by (simp add: field_simps power2_eq_square)
  ultimately show ?thesis by simp
qed

section \<open>D. Weighted Cauchy-Schwarz, finite form (T3b)\<close>

lemma cs_sqrt_sum:
  fixes u v :: "'a \<Rightarrow> real"
  assumes "finite S" "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> u s" "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> v s"
  shows "(\<Sum>s\<in>S. sqrt (u s * v s)) \<le> sqrt (sum u S) * sqrt (sum v S)"
proof -
  have cs: "(\<Sum>s\<in>S. sqrt (u s) * sqrt (v s)) ^ 2 \<le> (\<Sum>s\<in>S. (sqrt (u s)) ^ 2) * (\<Sum>s\<in>S. (sqrt (v s)) ^ 2)"
    by (rule Cauchy_Schwarz_ineq_sum)
  have e1: "(\<Sum>s\<in>S. (sqrt (u s)) ^ 2) = sum u S" using assms by (intro sum.cong) simp_all
  have e2: "(\<Sum>s\<in>S. (sqrt (v s)) ^ 2) = sum v S" using assms by (intro sum.cong) simp_all
  have e3: "(\<Sum>s\<in>S. sqrt (u s * v s)) = (\<Sum>s\<in>S. sqrt (u s) * sqrt (v s))"
    using assms by (intro sum.cong) (simp_all add: real_sqrt_mult)
  have su: "0 \<le> sum u S" and sv: "0 \<le> sum v S" using assms by (simp_all add: sum_nonneg)
  have "(sqrt (sum u S) * sqrt (sum v S)) ^ 2 = sum u S * sum v S"
    using su sv by (simp add: power_mult_distrib)
  then have "(\<Sum>s\<in>S. sqrt (u s) * sqrt (v s)) ^ 2 \<le> (sqrt (sum u S) * sqrt (sum v S)) ^ 2"
    using cs e1 e2 by simp
  then have "(\<Sum>s\<in>S. sqrt (u s) * sqrt (v s)) \<le> sqrt (sum u S) * sqrt (sum v S)"
    by (rule power2_le_imp_le) (intro mult_nonneg_nonneg real_sqrt_ge_zero su sv)
  then show ?thesis using e3 by simp
qed

theorem weighted_cauchy_schwarz:
  fixes a f :: "'i \<Rightarrow> real" and b f' :: "'j \<Rightarrow> real"
  assumes I: "finite I" and J: "finite J"
    and a0: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> a i" and b0: "\<And>j. j \<in> J \<Longrightarrow> 0 \<le> b j"
    and f0: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" and g0: "\<And>j. j \<in> J \<Longrightarrow> 0 \<le> f' j"
    and ap: "0 < sum a I" and bp: "0 < sum b J"
  shows "(\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * sqrt (f i * f' j)) / sqrt (sum a I * sum b J)
       \<le> sqrt ((\<Sum>i\<in>I. a i * f i) * (\<Sum>j\<in>J. b j * f' j))"
proof -
  let ?u = "\<lambda>p. a (fst p) * b (snd p) * f (fst p)"
  let ?v = "\<lambda>p. a (fst p) * b (snd p) * f' (snd p)"
  have P: "finite (I \<times> J)" using I J by simp
  have u0: "\<And>p. p \<in> I \<times> J \<Longrightarrow> 0 \<le> ?u p"
    using a0 b0 f0 by (auto intro!: mult_nonneg_nonneg)
  have v0: "\<And>p. p \<in> I \<times> J \<Longrightarrow> 0 \<le> ?v p"
    using a0 b0 g0 by (auto intro!: mult_nonneg_nonneg)
  have cs: "(\<Sum>p\<in>I \<times> J. sqrt (?u p * ?v p)) \<le> sqrt (sum ?u (I \<times> J)) * sqrt (sum ?v (I \<times> J))"
    by (rule cs_sqrt_sum[OF P u0 v0])
  have lhs: "(\<Sum>p\<in>I \<times> J. sqrt (?u p * ?v p)) = (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * sqrt (f i * f' j))"
  proof -
    have "(\<Sum>p\<in>I \<times> J. sqrt (?u p * ?v p)) = (\<Sum>p\<in>I \<times> J. a (fst p) * b (snd p) * sqrt (f (fst p) * f' (snd p)))"
    proof (rule sum.cong[OF refl])
      fix p assume p: "p \<in> I \<times> J"
      have ab: "0 \<le> a (fst p) * b (snd p)" using p a0 b0 by (auto intro!: mult_nonneg_nonneg)
      have e: "?u p * ?v p = (a (fst p) * b (snd p)) ^ 2 * (f (fst p) * f' (snd p))"
        by (simp add: power2_eq_square algebra_simps)
      have "sqrt (?u p * ?v p) = sqrt ((a (fst p) * b (snd p)) ^ 2 * (f (fst p) * f' (snd p)))"
        by (rule arg_cong[where f = sqrt]) (rule e)
      also have "\<dots> = sqrt ((a (fst p) * b (snd p)) ^ 2) * sqrt (f (fst p) * f' (snd p))"
        by (rule real_sqrt_mult)
      also have "\<dots> = a (fst p) * b (snd p) * sqrt (f (fst p) * f' (snd p))"
        using ab by (simp only: real_sqrt_abs abs_of_nonneg)
      finally show "sqrt (?u p * ?v p) = a (fst p) * b (snd p) * sqrt (f (fst p) * f' (snd p))" .
    qed
    also have "\<dots> = (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * sqrt (f i * f' j))"
      by (simp add: sum.cartesian_product case_prod_unfold)
    finally show ?thesis .
  qed
  have su: "sum ?u (I \<times> J) = sum b J * (\<Sum>i\<in>I. a i * f i)"
    by (simp add: sum.cartesian_product case_prod_unfold sum_distrib_left sum_distrib_right algebra_simps)
  have sv: "sum ?v (I \<times> J) = sum a I * (\<Sum>j\<in>J. b j * f' j)"
  proof -
    have "sum ?v (I \<times> J) = sum (case_prod (\<lambda>i j. a i * (b j * f' j))) (I \<times> J)"
      by (simp add: mult.assoc case_prod_unfold)
    also have "\<dots> = (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * (b j * f' j))"
      by (rule sum.cartesian_product[symmetric])
    also have "\<dots> = sum a I * (\<Sum>j\<in>J. b j * f' j)"
      by (simp add: sum_distrib_left[symmetric] sum_distrib_right[symmetric])
    finally show ?thesis .
  qed
  have A0: "0 \<le> (\<Sum>i\<in>I. a i * f i)" using a0 f0 by (intro sum_nonneg mult_nonneg_nonneg) auto
  have B0: "0 \<le> (\<Sum>j\<in>J. b j * f' j)" using b0 g0 by (intro sum_nonneg mult_nonneg_nonneg) auto
  have rhs: "sqrt (sum ?u (I \<times> J)) * sqrt (sum ?v (I \<times> J))
      = sqrt (sum a I * sum b J) * sqrt ((\<Sum>i\<in>I. a i * f i) * (\<Sum>j\<in>J. b j * f' j))"
    unfolding su sv using A0 B0 ap bp
    by (simp add: real_sqrt_mult[symmetric] algebra_simps)
  have sp: "0 < sqrt (sum a I * sum b J)" using ap bp by simp
  have key: "(\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * sqrt (f i * f' j))
      \<le> sqrt ((\<Sum>i\<in>I. a i * f i) * (\<Sum>j\<in>J. b j * f' j)) * sqrt (sum a I * sum b J)"
    using cs lhs rhs by (simp add: mult.commute)
  show ?thesis using sp key by (simp add: pos_divide_le_eq)
qed

text \<open>Consequence: a lower bound on every pairwise kernel gives a lower bound on the profile integral.\<close>

theorem kernel_lower_bound:
  fixes a :: "'i \<Rightarrow> real" and b :: "'j \<Rightarrow> real" and kap :: "'i \<Rightarrow> 'j \<Rightarrow> real" and k0 :: real
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> a i" "\<And>j. j \<in> J \<Longrightarrow> 0 \<le> b j"
    and "\<And>i j. i \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> k0 \<le> kap i j"
  shows "k0 * sum a I * sum b J \<le> (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * kap i j)"
proof -
  have "k0 * sum a I * sum b J = (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * k0)"
    by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
  also have "\<dots> \<le> (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * kap i j)"
    using assms by (intro sum_mono) (auto intro!: mult_left_mono mult_nonneg_nonneg sum_mono)
  finally show ?thesis .
qed

text \<open>Both together: if sqrt (f_i f'_j) >= k0 pointwise then sqrt (A B) >= k0 sqrt (a b).\<close>

theorem profile_lower_bound:
  fixes a f :: "'i \<Rightarrow> real" and b f' :: "'j \<Rightarrow> real" and k0 :: real
  assumes I: "finite I" and J: "finite J"
    and a0: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> a i" and b0: "\<And>j. j \<in> J \<Longrightarrow> 0 \<le> b j"
    and f0: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" and g0: "\<And>j. j \<in> J \<Longrightarrow> 0 \<le> f' j"
    and ap: "0 < sum a I" and bp: "0 < sum b J" and k00: "0 \<le> k0"
    and ker: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> k0 \<le> sqrt (f i * f' j)"
  shows "k0 * sqrt (sum a I * sum b J) \<le> sqrt ((\<Sum>i\<in>I. a i * f i) * (\<Sum>j\<in>J. b j * f' j))"
proof -
  have s: "0 < sqrt (sum a I * sum b J)" using ap bp by simp
  have "k0 * sum a I * sum b J \<le> (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * sqrt (f i * f' j))"
    by (rule kernel_lower_bound[OF a0 b0 ker])
  then have "k0 * sum a I * sum b J / sqrt (sum a I * sum b J)
      \<le> (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * sqrt (f i * f' j)) / sqrt (sum a I * sum b J)"
    using s by (intro divide_right_mono) simp_all
  moreover have "k0 * sum a I * sum b J / sqrt (sum a I * sum b J) = k0 * sqrt (sum a I * sum b J)"
  proof -
    have sq: "(sqrt (sum a I * sum b J)) ^ 2 = sum a I * sum b J"
      using ap bp by simp
    then have ss: "sqrt (sum a I * sum b J) * sqrt (sum a I * sum b J) = sum a I * sum b J"
      by (simp add: power2_eq_square)
    have sne: "sqrt (sum a I * sum b J) \<noteq> 0" by (rule not_sym[OF less_imp_neq[OF s]])
    have "k0 * sum a I * sum b J = k0 * sqrt (sum a I * sum b J) * sqrt (sum a I * sum b J)"
      by (simp only: mult.assoc ss)
    then show ?thesis by (simp add: divide_eq_eq sne)
  qed
  ultimately have "k0 * sqrt (sum a I * sum b J)
      \<le> (\<Sum>i\<in>I. \<Sum>j\<in>J. a i * b j * sqrt (f i * f' j)) / sqrt (sum a I * sum b J)" by simp
  also have "\<dots> \<le> sqrt ((\<Sum>i\<in>I. a i * f i) * (\<Sum>j\<in>J. b j * f' j))"
    by (rule weighted_cauchy_schwarz[OF I J a0 b0 f0 g0 ap bp])
  finally show ?thesis .
qed

section \<open>E. The extreme pair (T3c)\<close>

lemma has_int_sin_cos: "((\<lambda>t. sin t * cos t) has_integral 1 / 2) {0..pi / 2}"
proof -
  have D: "((\<lambda>t. (sin t)\<^sup>2 / 2) has_vector_derivative sin x * cos x) (at x within {0..pi / 2})"
    for x :: real
  proof -
    have "((\<lambda>t. (sin t)\<^sup>2 / 2) has_real_derivative sin x * cos x) (at x)"
      by (rule DERIV_cong) (auto intro!: derivative_eq_intros)
    then show "((\<lambda>t. (sin t)\<^sup>2 / 2) has_vector_derivative sin x * cos x) (at x within {0..pi / 2})"
      by (simp add: has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
  qed
  have "((\<lambda>t. sin t * cos t) has_integral (sin (pi / 2))\<^sup>2 / 2 - (sin 0)\<^sup>2 / 2) {0..pi / 2}"
    by (rule fundamental_theorem_of_calculus) (use D in auto)
  then show ?thesis by simp
qed

lemma has_int_cos2: "((\<lambda>t. (cos t)\<^sup>2) has_integral pi / 4) {0..pi / 2}"
proof -
  have D: "((\<lambda>t. (t + sin t * cos t) / 2) has_vector_derivative (cos x)\<^sup>2) (at x within {0..pi / 2})"
    for x :: real
  proof -
    have "((\<lambda>t. (t + sin t * cos t) / 2) has_real_derivative (1 + (cos x * cos x + sin x * - sin x)) / 2) (at x)"
      by (auto intro!: derivative_eq_intros)
    moreover have "(1 + (cos x * cos x + sin x * - sin x)) / 2 = (cos x)\<^sup>2"
      using sin_cos_squared_add[of x] by (simp add: power2_eq_square algebra_simps)
    ultimately show "((\<lambda>t. (t + sin t * cos t) / 2) has_vector_derivative (cos x)\<^sup>2) (at x within {0..pi / 2})"
      by (simp add: has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
  qed
  have "((\<lambda>t. (cos t)\<^sup>2) has_integral (pi / 2 + sin (pi / 2) * cos (pi / 2)) / 2 - (0 + sin 0 * cos 0) / 2) {0..pi / 2}"
    by (rule fundamental_theorem_of_calculus) (use D in auto)
  then show ?thesis by simp
qed

lemma has_int_sin2: "((\<lambda>t. (sin t)\<^sup>2) has_integral pi / 4) {0..pi / 2}"
proof -
  have D: "((\<lambda>t. (t - sin t * cos t) / 2) has_vector_derivative (sin x)\<^sup>2) (at x within {0..pi / 2})"
    for x :: real
  proof -
    have "((\<lambda>t. (t - sin t * cos t) / 2) has_real_derivative (1 - (cos x * cos x + sin x * - sin x)) / 2) (at x)"
      by (auto intro!: derivative_eq_intros)
    moreover have "(1 - (cos x * cos x + sin x * - sin x)) / 2 = (sin x)\<^sup>2"
      using sin_cos_squared_add[of x] by (simp add: power2_eq_square algebra_simps)
    ultimately show "((\<lambda>t. (t - sin t * cos t) / 2) has_vector_derivative (sin x)\<^sup>2) (at x within {0..pi / 2})"
      by (simp add: has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
  qed
  have "((\<lambda>t. (sin t)\<^sup>2) has_integral (pi / 2 - sin (pi / 2) * cos (pi / 2)) / 2 - (0 - sin 0 * cos 0) / 2) {0..pi / 2}"
    by (rule fundamental_theorem_of_calculus) (use D in auto)
  then show ?thesis by simp
qed

theorem integral_sin_cos: "integral {0..pi / 2} (\<lambda>t. sin t * cos t) = 1 / 2"
  using has_int_sin_cos by (rule integral_unique)

theorem integral_cos_squared: "integral {0..pi / 2} (\<lambda>t. (cos t)\<^sup>2) = pi / 4"
  using has_int_cos2 by (rule integral_unique)

theorem integral_sin_squared: "integral {0..pi / 2} (\<lambda>t. (sin t)\<^sup>2) = pi / 4"
  using has_int_sin2 by (rule integral_unique)

theorem extreme_pair_overlap:
  "integral {0..pi / 2} (\<lambda>t. sin t * cos t)
     / sqrt (integral {0..pi / 2} (\<lambda>t. (cos t)\<^sup>2) * integral {0..pi / 2} (\<lambda>t. (sin t)\<^sup>2)) = 2 / pi"
proof -
  have pp: "0 < pi" by (rule pi_gt_zero)
  have "sqrt (pi / 4 * (pi / 4)) = sqrt ((pi / 4) ^ 2)" by (simp add: power2_eq_square)
  also have "\<dots> = \<bar>pi / 4\<bar>" by (rule real_sqrt_abs)
  also have "\<dots> = pi / 4" using pp by simp
  finally have r: "sqrt (pi / 4 * (pi / 4)) = pi / 4" .
  show ?thesis
    unfolding integral_sin_cos integral_cos_squared integral_sin_squared r
    using pp by (simp add: field_simps)
qed

text \<open>Here sin t * cos t = sqrt (cos^2 t * sin^2 t) on [0, pi/2], so the integral above is the kernel
  of the pair (cos^2, sin^2).\<close>

lemma sqrt_cos2_sin2:
  assumes "0 \<le> t" "t \<le> pi / 2"
  shows "sqrt ((cos t)\<^sup>2 * (sin t)\<^sup>2) = sin t * cos t"
proof -
  have pp: "0 < pi" by (rule pi_gt_zero)
  have c: "0 \<le> cos t" using assms pp by (intro cos_ge_zero) linarith+
  have s: "0 \<le> sin t" using assms pp by (intro sin_ge_zero) linarith+
  have "sqrt ((cos t)\<^sup>2 * (sin t)\<^sup>2) = sqrt ((cos t)\<^sup>2) * sqrt ((sin t)\<^sup>2)"
    by (rule real_sqrt_mult)
  also have "\<dots> = \<bar>cos t\<bar> * \<bar>sin t\<bar>" by (simp only: real_sqrt_abs)
  also have "\<dots> = sin t * cos t" using c s by simp
  finally show ?thesis .
qed

end
