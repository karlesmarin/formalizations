(*  Title:      Unitarity_Density.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    Algebraic core of Theorem 4 (induced rates, every pulse) for the qubit-memory exchange of one excitation.
    Formalised:
      (U1) a 2x2 unitary matrix preserves the inner product; if U psi = e^{i chi} m with m = (0,1), then for
           q = (1,0):  <m|U q> = e^{i chi} <psi|q>  and hence |<m|U q>| = |<psi|q>|.
      (U2) the density rho(P) = (gq P + pq P(2-P) + gm (1-P) + pm (1-P)(1+P))/3 is nonnegative on 0 <= P <= 1
           and equals the density of Lemma 1 for P = cos^2 theta (every P in [0,1] is of this form).
      (U3) the pointwise bound A + B g^2 >= c_G |theta'| with c_G = min over 0 < g <= G of A/g + B g
           (closed form, lower bound for all A,B >= 0, attained when A > 0).
      (U4) integration of (U3) over [0,T] (integrability is a hypothesis).
    Not formalised: the Lindblad master equation, the passage from jumps to the density, the change of variables
    to an integral in theta from 0 to pi/2, and continuity of c_G (so integrability in U4 is assumed).
*)

theory Unitarity_Density
  imports "HOL-Analysis.Analysis"
begin

section \<open>U1: unitarity and the transition amplitude\<close>

text \<open>Vectors of C^2 are pairs of complex numbers; the matrix \<open>U = ((a,b),(c,d))\<close> acts on them.\<close>

definition ip :: "complex \<times> complex \<Rightarrow> complex \<times> complex \<Rightarrow> complex" where
  "ip u v = cnj (fst u) * fst v + cnj (snd u) * snd v"

definition app :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<times> complex \<Rightarrow> complex \<times> complex" where
  "app a b c d u = (a * fst u + b * snd u, c * fst u + d * snd u)"

text \<open>@{text "U^H U = I"} written entrywise.\<close>
definition unitary2 :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool" where
  "unitary2 a b c d \<longleftrightarrow>
     cnj a * a + cnj c * c = 1 \<and> cnj a * b + cnj c * d = 0 \<and>
     cnj b * a + cnj d * c = 0 \<and> cnj b * b + cnj d * d = 1"

lemma ip_preserved:
  assumes "unitary2 a b c d"
  shows "ip (app a b c d u) (app a b c d v) = ip u v"
proof -
  from assms have h1: "cnj a * a + cnj c * c = 1" and h2: "cnj a * b + cnj c * d = 0"
    and h3: "cnj b * a + cnj d * c = 0" and h4: "cnj b * b + cnj d * d = 1"
    unfolding unitary2_def by simp_all
  have "ip (app a b c d u) (app a b c d v) =
      cnj (fst u) * fst v * (cnj a * a + cnj c * c) + cnj (fst u) * snd v * (cnj a * b + cnj c * d)
    + cnj (snd u) * fst v * (cnj b * a + cnj d * c) + cnj (snd u) * snd v * (cnj b * b + cnj d * d)"
    by (simp add: ip_def app_def algebra_simps)
  also have "\<dots> = ip u v" using h1 h2 h3 h4 by (simp add: ip_def)
  finally show ?thesis .
qed

theorem unitary_transition_amplitude:
  assumes U: "unitary2 a b c d" and psi: "app a b c d psi = (0, cis chi)"
  shows "ip (0, 1) (app a b c d (1, 0)) = cis chi * ip psi (1, 0)"
    and "cmod (ip (0, 1) (app a b c d (1, 0))) = cmod (ip psi (1, 0))"
proof -
  have P: "ip (app a b c d psi) (app a b c d (1, 0)) = ip psi (1, 0)" by (rule ip_preserved[OF U])
  have L: "ip (app a b c d psi) (app a b c d (1, 0)) = cnj (cis chi) * c"
    using psi by (simp add: ip_def app_def)
  have R: "ip (0, 1) (app a b c d (1, 0)) = c" by (simp add: ip_def app_def)
  have one: "cis chi * cnj (cis chi) = 1" by (simp add: cis_cnj cis_mult)
  have "c = cis chi * (cnj (cis chi) * c)" using one by (simp add: algebra_simps)
  also have "\<dots> = cis chi * ip psi (1, 0)" using P L by simp
  finally have C: "c = cis chi * ip psi (1, 0)" .
  show "ip (0, 1) (app a b c d (1, 0)) = cis chi * ip psi (1, 0)" using R C by simp
  show "cmod (ip (0, 1) (app a b c d (1, 0))) = cmod (ip psi (1, 0))"
    using R C by (simp add: norm_mult)
qed

corollary unitary_population:
  assumes "unitary2 a b c d" "app a b c d psi = (0, cis chi)"
  shows "(cmod (ip (0, 1) (app a b c d (1, 0))))\<^sup>2 = (cmod (fst psi))\<^sup>2"
proof -
  have "cmod (ip psi (1, 0)) = cmod (fst psi)" by (simp add: ip_def)
  then show ?thesis using unitary_transition_amplitude(2)[OF assms] by simp
qed

section \<open>U2: the density\<close>

definition rho :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "rho P gq pq gm pm =
     (gq * P + pq * (P * (2 - P)) + gm * (1 - P) + pm * ((1 - P) * (1 + P))) / 3"

theorem rho_nonneg:
  assumes "0 \<le> P" "P \<le> 1" "0 \<le> gq" "0 \<le> pq" "0 \<le> gm" "0 \<le> pm"
  shows "0 \<le> rho P gq pq gm pm"
proof -
  have a: "0 \<le> gq * P" using assms by simp
  have b: "0 \<le> pq * (P * (2 - P))" using assms by (intro mult_nonneg_nonneg) auto
  have c: "0 \<le> gm * (1 - P)" using assms by (intro mult_nonneg_nonneg) auto
  have d: "0 \<le> pm * ((1 - P) * (1 + P))" using assms by (intro mult_nonneg_nonneg) auto
  show ?thesis unfolding rho_def using a b c d by simp
qed

theorem rho_cos_squared:
  "rho ((cos \<theta>)\<^sup>2) gq pq gm pm =
     gq / 3 * (cos \<theta>)\<^sup>2 + pq / 3 * ((cos \<theta>)\<^sup>2 * (1 + (sin \<theta>)\<^sup>2))
     + gm / 3 * (sin \<theta>)\<^sup>2 + pm / 3 * ((sin \<theta>)\<^sup>2 * (1 + (cos \<theta>)\<^sup>2))"
proof -
  obtain c where c: "c = (cos \<theta>)\<^sup>2" by simp
  have s: "(sin \<theta>)\<^sup>2 = 1 - c" using c by (simp add: sin_squared_eq)
  show ?thesis unfolding rho_def by (simp only: c[symmetric] s) (simp add: field_simps)
qed

theorem population_is_cos_squared:
  assumes "0 \<le> P" "P \<le> 1"
  shows "\<exists>\<theta>. 0 \<le> \<theta> \<and> \<theta> \<le> pi / 2 \<and> (cos \<theta>)\<^sup>2 = P"
proof -
  have s0: "0 \<le> sqrt P" using assms by simp
  have s1: "sqrt P \<le> 1" using assms by (simp add: real_sqrt_le_1_iff)
  let ?t = "arccos (sqrt P)"
  have "0 \<le> ?t" using arccos_lbound[of "sqrt P"] s0 s1 by simp
  moreover have "?t \<le> pi / 2" using arccos_le_pi2[OF s0 s1] .
  moreover have m1: "-1 \<le> sqrt P" using s0 by linarith
  have "cos ?t = sqrt P" using cos_arccos[OF m1 s1] .
  then have "(cos ?t)\<^sup>2 = P" using assms by simp
  ultimately show ?thesis by blast
qed

section \<open>U3: the pointwise bound\<close>

definition cG :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "cG A B G = (if 0 < B \<and> sqrt (A / B) \<le> G then 2 * sqrt (A * B) else A / G + B * G)"

lemma amgm_div:
  assumes "0 \<le> A" "0 \<le> B" "0 < g"
  shows "2 * sqrt (A * B) \<le> A / g + B * g"
proof -
  have e: "(A / g) * (B * g) = A * B" using assms(3) by (simp add: field_simps)
  have x0: "0 \<le> A / g + B * g" using assms by (intro add_nonneg_nonneg mult_nonneg_nonneg) auto
  have sq: "(A / g + B * g)\<^sup>2 = (A / g - B * g)\<^sup>2 + 4 * ((A / g) * (B * g))"
    by (simp add: power2_eq_square algebra_simps)
  have "(2 * sqrt (A * B))\<^sup>2 = 4 * (A * B)"
    using assms by (simp add: power_mult_distrib)
  also have "\<dots> \<le> (A / g + B * g)\<^sup>2" using sq e by simp
  finally show ?thesis by (rule power2_le_imp_le[OF _ x0])
qed

theorem cG_lower_bound:
  assumes "0 \<le> A" "0 \<le> B" "0 < g" "g \<le> G"
  shows "cG A B G \<le> A / g + B * g"
proof (cases "0 < B \<and> sqrt (A / B) \<le> G")
  case True
  then show ?thesis unfolding cG_def using amgm_div[OF assms(1,2,3)] by simp
next
  case False
  note nb = False
  have G0: "0 < G" using assms(3,4) by simp
  have cg: "cG A B G = A / G + B * G" unfolding cG_def by (rule if_not_P[OF nb])
  show ?thesis
  proof (cases "B = 0")
    case True
    have "A / G \<le> A / g"
      by (rule divide_left_mono[OF assms(4) assms(1)]) (use assms(3) G0 in simp)
    then show ?thesis using True cg by simp
  next
    case B0: False
    have Bp: "0 < B" using assms(2) B0 by simp
    from nb Bp have ns: "G < sqrt (A / B)" by auto
    have "sqrt (G\<^sup>2) < sqrt (A / B)" using ns G0 by simp
    then have "G\<^sup>2 < A / B" by (simp only: real_sqrt_less_iff)
    then have AG: "B * G\<^sup>2 < A" using Bp by (simp add: less_divide_eq mult.commute)
    have bg: "B * g * G \<le> B * G\<^sup>2"
      using assms(3,4) Bp by (simp add: power2_eq_square algebra_simps mult_left_mono)
    have f1: "0 \<le> G - g" using assms(4) by simp
    have f2: "0 \<le> A - B * g * G" using AG bg by simp
    have "A / g + B * g - (A / G + B * G) = (G - g) * (A - B * g * G) / (g * G)"
      using assms(3) G0 by (simp add: field_simps power2_eq_square)
    also have "\<dots> \<ge> 0" using f1 f2 assms(3) G0 by (intro divide_nonneg_pos mult_nonneg_nonneg) auto
    finally show ?thesis using cg by simp
  qed
qed

theorem cG_nonneg:
  assumes "0 \<le> A" "0 \<le> B" "0 < G"
  shows "0 \<le> cG A B G"
  unfolding cG_def using assms by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg divide_nonneg_pos)

theorem cG_attained:
  assumes "0 < A" "0 \<le> B" "0 < G"
  shows "\<exists>g. 0 < g \<and> g \<le> G \<and> A / g + B * g = cG A B G"
proof (cases "0 < B \<and> sqrt (A / B) \<le> G")
  case True
  then have Bp: "0 < B" and le: "sqrt (A / B) \<le> G" by simp_all
  obtain s where s: "0 < s" "A = s\<^sup>2" using assms(1) by (metis real_sqrt_gt_0_iff real_sqrt_pow2 less_eq_real_def)
  obtain t where t: "0 < t" "B = t\<^sup>2" using Bp by (metis real_sqrt_gt_0_iff real_sqrt_pow2 less_eq_real_def)
  have rA: "sqrt (A / B) = s / t" using s t by (intro real_sqrt_unique) (simp_all add: power_divide)
  have rAB: "sqrt (A * B) = s * t" using s t by (intro real_sqrt_unique) (simp_all add: power_mult_distrib)
  have "s / t \<le> G" using le rA by simp
  moreover have "0 < s / t" using s t by simp
  moreover have "A / (s / t) + B * (s / t) = cG A B G"
    unfolding cG_def using True rAB by (simp add: s t field_simps power2_eq_square)
  ultimately show ?thesis by blast
next
  case False
  then have "cG A B G = A / G + B * G" unfolding cG_def by (rule if_not_P)
  then show ?thesis using assms(3) by (intro exI[of _ G]) simp
qed

theorem cG_closed_form_infimum_zero:
  assumes "0 < B" "0 < G"
  shows "cG 0 B G = 0"
  unfolding cG_def using assms by simp

theorem cG_pointwise:
  assumes "0 \<le> A" "0 \<le> B" "0 < g" "g \<le> G" "\<bar>th'\<bar> \<le> g"
  shows "cG A B G * \<bar>th'\<bar> \<le> A + B * g\<^sup>2"
    and "(A / g + B * g) * \<bar>th'\<bar> \<le> A + B * g\<^sup>2"
proof -
  have G0: "0 < G" using assms(3,4) by simp
  have c0: "0 \<le> cG A B G" by (rule cG_nonneg[OF assms(1,2) G0])
  have lo: "cG A B G \<le> A / g + B * g" by (rule cG_lower_bound[OF assms(1-4)])
  have x0: "0 \<le> A / g + B * g" using c0 lo by linarith
  have eq: "g * (A / g + B * g) = A + B * g\<^sup>2" using assms(3) by (simp add: field_simps power2_eq_square)
  have "cG A B G * \<bar>th'\<bar> \<le> cG A B G * g" by (rule mult_left_mono[OF assms(5) c0])
  also have "\<dots> \<le> (A / g + B * g) * g" by (rule mult_right_mono[OF lo]) (use assms(3) in simp)
  also have "\<dots> = A + B * g\<^sup>2" using eq by (simp add: mult.commute)
  finally show "cG A B G * \<bar>th'\<bar> \<le> A + B * g\<^sup>2" .
  have "(A / g + B * g) * \<bar>th'\<bar> \<le> (A / g + B * g) * g" by (rule mult_left_mono[OF assms(5) x0])
  also have "\<dots> = A + B * g\<^sup>2" using eq by (simp add: mult.commute)
  finally show "(A / g + B * g) * \<bar>th'\<bar> \<le> A + B * g\<^sup>2" .
qed

section \<open>U4: integration of the pointwise bound\<close>

theorem integral_cG_bound:
  fixes A B g dth :: "real \<Rightarrow> real"
  assumes pos: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> A t \<and> 0 \<le> B t \<and> 0 < g t \<and> g t \<le> G \<and> \<bar>dth t\<bar> \<le> g t"
    and i1: "(\<lambda>t. A t + B t * (g t)\<^sup>2) integrable_on {0..T}"
    and i2: "(\<lambda>t. cG (A t) (B t) G * \<bar>dth t\<bar>) integrable_on {0..T}"
  shows "integral {0..T} (\<lambda>t. cG (A t) (B t) G * \<bar>dth t\<bar>) \<le> integral {0..T} (\<lambda>t. A t + B t * (g t)\<^sup>2)"
proof (rule integral_le[OF i2 i1])
  fix t assume t: "t \<in> {0..T}"
  from pos[OF t] have h: "0 \<le> A t" "0 \<le> B t" "0 < g t" "g t \<le> G" "\<bar>dth t\<bar> \<le> g t" by simp_all
  show "cG (A t) (B t) G * \<bar>dth t\<bar> \<le> A t + B t * (g t)\<^sup>2" by (rule cG_pointwise(1)[OF h])
qed

end
