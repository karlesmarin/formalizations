(*  Title:      Storage_Function.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Memory-floors note, Proposition "unequal" (very unequal dephasing rates, fixed phase, no detuning),
    in units G = 1.  The swap equations
        va' = -q va - g u,  u' = g va - m u,  w' = -4 g y,  y' = g w - 2 a y,
    with q = a + d, m = a - d, a = (q + m)/2, d = (q - m)/2, a continuous control 0 <= g <= 1, and
    va(0) = 1, u(0) = 0, w(0) = 1, y(0) = 0.  Put Om^2 = d^2 - 1 and kap^2 = a^2 - 4.
    (A) the reductions to the Metzler forms (y, z) and (u, h);  (B) the invariant cones;
    (C) strict positivity of w and h;  (D) the algebraic sign of the logarithmic derivative of the
    storage function N / D, N = va - chi_- u, D = theta_+ w - y;  (E) the bound 2 Om u < w, whence
    p + 2 c < 1/2 for p = (1 - w)/2 and c = u, provided q m >= 3 and |q - m| >= 2 sqrt 5.
*)
theory Storage_Function
  imports Metzler_Cone
begin

section \<open>A. Reductions\<close>

lemma reduce_yz:
  fixes w y g :: "real \<Rightarrow> real" and a th t :: real
  assumes thp: "0 < th" and rel: "4 * th\<^sup>2 - 2 * a * th + 1 = 0"
    and dw: "(w has_real_derivative - 4 * g t * y t) (at t)"
    and dy: "(y has_real_derivative g t * w t - 2 * a * y t) (at t)"
  shows "(y has_real_derivative (g t / th - 2 * a) * y t + g t / th * (th * w t - y t)) (at t)"
    and "((\<lambda>s. th * w s - y s) has_real_derivative
          (1 - g t) * 2 * a * y t + (- (g t / th)) * (th * w t - y t)) (at t)"
proof -
  have ne: "th \<noteq> 0" using thp by simp
  have e1: "(g t / th - 2 * a) * y t + g t / th * (th * w t - y t) = g t * w t - 2 * a * y t"
    using ne by (simp add: field_simps)
  show "(y has_real_derivative (g t / th - 2 * a) * y t + g t / th * (th * w t - y t)) (at t)"
    unfolding e1 by (rule dy)
  have prod: "th * (2 * a - 4 * th) = 1" using rel by (simp add: algebra_simps power2_eq_square)
  have inv: "1 / th = 2 * a - 4 * th"
  proof -
    have "1 / th = th * (2 * a - 4 * th) / th" using prod by simp
    also have "\<dots> = 2 * a - 4 * th" using ne by simp
    finally show ?thesis .
  qed
  have gd: "g t / th = g t * (2 * a - 4 * th)"
  proof -
    have "g t / th = g t * (1 / th)" by simp
    also have "\<dots> = g t * (2 * a - 4 * th)" unfolding inv by simp
    finally show ?thesis .
  qed
  have d: "((\<lambda>s. th * w s - y s) has_real_derivative th * (- 4 * g t * y t) - (g t * w t - 2 * a * y t)) (at t)"
    by (rule DERIV_diff[OF DERIV_cmult[OF dw] dy])
  have "(1 - g t) * 2 * a * y t + (- (g t / th)) * (th * w t - y t)
        - (th * (- 4 * g t * y t) - (g t * w t - 2 * a * y t)) = g t * w t * (1 - th * (2 * a - 4 * th))"
    unfolding gd by algebra
  also have "\<dots> = 0" using prod by simp
  finally have "(1 - g t) * 2 * a * y t + (- (g t / th)) * (th * w t - y t)
        = th * (- 4 * g t * y t) - (g t * w t - 2 * a * y t)" by simp
  then show "((\<lambda>s. th * w s - y s) has_real_derivative
          (1 - g t) * 2 * a * y t + (- (g t / th)) * (th * w t - y t)) (at t)" using d by simp
qed

lemma reduce_uh:
  fixes va u g :: "real \<Rightarrow> real" and q m chi t :: real
  assumes chi: "chi\<^sup>2 + (q - m) * chi + 1 = 0"
    and dva: "(va has_real_derivative - q * va t - g t * u t) (at t)"
    and du: "(u has_real_derivative g t * va t - m * u t) (at t)"
  shows "(u has_real_derivative (g t * chi - m) * u t + g t * (va t - chi * u t)) (at t)"
    and "((\<lambda>s. va s - chi * u s) has_real_derivative
          (1 - g t) * (1 + chi\<^sup>2) * u t + (- (q + g t * chi)) * (va t - chi * u t)) (at t)"
proof -
  have e1: "(g t * chi - m) * u t + g t * (va t - chi * u t) = g t * va t - m * u t" by (simp add: algebra_simps)
  show "(u has_real_derivative (g t * chi - m) * u t + g t * (va t - chi * u t)) (at t)"
    unfolding e1 by (rule du)
  have d: "((\<lambda>s. va s - chi * u s) has_real_derivative (- q * va t - g t * u t) - chi * (g t * va t - m * u t)) (at t)"
    by (rule DERIV_diff[OF dva DERIV_cmult[OF du]])
  have "(1 - g t) * (1 + chi\<^sup>2) * u t + (- (q + g t * chi)) * (va t - chi * u t)
        - ((- q * va t - g t * u t) - chi * (g t * va t - m * u t)) = u t * (chi\<^sup>2 + (q - m) * chi + 1)"
    by algebra
  also have "\<dots> = 0" using chi by simp
  finally have "(1 - g t) * (1 + chi\<^sup>2) * u t + (- (q + g t * chi)) * (va t - chi * u t)
        = (- q * va t - g t * u t) - chi * (g t * va t - m * u t)" by simp
  then show "((\<lambda>s. va s - chi * u s) has_real_derivative
          (1 - g t) * (1 + chi\<^sup>2) * u t + (- (q + g t * chi)) * (va t - chi * u t)) (at t)" using d by simp
qed

section \<open>B. The two invariant cones\<close>

theorem cone_yz:
  fixes g y z :: "real \<Rightarrow> real" and th a T :: real
  assumes T0: "0 \<le> T" and gc: "continuous_on {0..T} g" and g01: "\<forall>t\<in>{0..T}. 0 \<le> g t \<and> g t \<le> 1"
    and thp: "0 < th" and a0: "0 \<le> a"
    and dy: "\<forall>t\<in>{0..T}. (y has_real_derivative (g t / th - 2 * a) * y t + g t / th * z t) (at t)"
    and dz: "\<forall>t\<in>{0..T}. (z has_real_derivative (1 - g t) * 2 * a * y t + (- (g t / th)) * z t) (at t)"
    and y0: "0 \<le> y 0" and z0: "0 \<le> z 0"
  shows "\<forall>t\<in>{0..T}. 0 \<le> y t \<and> 0 \<le> z t"
proof -
  have ne: "th \<noteq> 0" using thp by simp
  have c11: "continuous_on {0..T} (\<lambda>t. g t / th - 2 * a)"
    by (intro continuous_intros gc) (use ne in simp)
  have c12: "continuous_on {0..T} (\<lambda>t. g t / th)" by (intro continuous_intros gc) (use ne in simp)
  have c21: "continuous_on {0..T} (\<lambda>t. (1 - g t) * 2 * a)" using gc by (intro continuous_intros)
  have c22: "continuous_on {0..T} (\<lambda>t. - (g t / th))" by (intro continuous_intros gc) (use ne in simp)
  have n12: "\<forall>t\<in>{0..T}. 0 \<le> g t / th" using g01 thp by (simp add: divide_nonneg_pos)
  have n21: "\<forall>t\<in>{0..T}. 0 \<le> (1 - g t) * 2 * a"
  proof
    fix t assume t: "t \<in> {0..T}"
    then have "0 \<le> 1 - g t" using g01 by force
    then show "0 \<le> (1 - g t) * 2 * a" using a0 by (intro mult_nonneg_nonneg) simp_all
  qed
  show ?thesis
    by (rule metzler_cone_2x2[OF T0 c11 c12 c21 c22 n12 n21 dy dz y0 z0])
qed

theorem cone_uh:
  fixes g u h :: "real \<Rightarrow> real" and q m chi T :: real
  assumes T0: "0 \<le> T" and gc: "continuous_on {0..T} g" and g01: "\<forall>t\<in>{0..T}. 0 \<le> g t \<and> g t \<le> 1"
    and du: "\<forall>t\<in>{0..T}. (u has_real_derivative (g t * chi - m) * u t + g t * h t) (at t)"
    and dh: "\<forall>t\<in>{0..T}. (h has_real_derivative (1 - g t) * (1 + chi\<^sup>2) * u t + (- (q + g t * chi)) * h t) (at t)"
    and u0: "0 \<le> u 0" and h0: "0 \<le> h 0"
  shows "\<forall>t\<in>{0..T}. 0 \<le> u t \<and> 0 \<le> h t"
proof -
  have c11: "continuous_on {0..T} (\<lambda>t. g t * chi - m)" using gc by (intro continuous_intros)
  have c12: "continuous_on {0..T} g" by (rule gc)
  have c21: "continuous_on {0..T} (\<lambda>t. (1 - g t) * (1 + chi\<^sup>2))" using gc by (intro continuous_intros)
  have c22: "continuous_on {0..T} (\<lambda>t. - (q + g t * chi))" using gc by (intro continuous_intros)
  have n12: "\<forall>t\<in>{0..T}. 0 \<le> g t" using g01 by blast
  have n21: "\<forall>t\<in>{0..T}. 0 \<le> (1 - g t) * (1 + chi\<^sup>2)"
  proof
    fix t assume t: "t \<in> {0..T}"
    then have "0 \<le> 1 - g t" using g01 by force
    then show "0 \<le> (1 - g t) * (1 + chi\<^sup>2)" by (intro mult_nonneg_nonneg) simp_all
  qed
  show ?thesis
    by (rule metzler_cone_2x2[OF T0 c11 c12 c21 c22 n12 n21 du dh u0 h0])
qed

section \<open>C. Strict positivity from a one-sided bound on the derivative\<close>

lemma exp_growth_lower:
  fixes f f' :: "real \<Rightarrow> real" and B T :: real
  assumes T0: "0 \<le> T" and df: "\<forall>t\<in>{0..T}. (f has_real_derivative f' t) (at t)"
    and bd: "\<forall>t\<in>{0..T}. 0 \<le> f' t + B * f t" and f0: "0 < f 0"
  shows "\<forall>t\<in>{0..T}. 0 < f t"
proof
  fix t assume t: "t \<in> {0..T}"
  have mono: "f 0 * exp (B * 0) \<le> f t * exp (B * t)"
  proof (rule DERIV_nonneg_imp_nondecreasing[of 0 t "\<lambda>s. f s * exp (B * s)"])
    show "0 \<le> t" using t by simp
    fix s :: real
    assume s0: "0 \<le> s" and st: "s \<le> t"
    then have sm: "s \<in> {0..T}" using t by simp
    have de: "((\<lambda>s. exp (B * s)) has_real_derivative exp (B * s) * B) (at s)" by (auto intro!: derivative_eq_intros)
    have "((\<lambda>s. f s * exp (B * s)) has_real_derivative f' s * exp (B * s) + exp (B * s) * B * f s) (at s)"
      by (rule DERIV_mult[OF df[rule_format, OF sm] de])
    moreover have "0 \<le> f' s * exp (B * s) + exp (B * s) * B * f s"
    proof -
      have "f' s * exp (B * s) + exp (B * s) * B * f s = exp (B * s) * (f' s + B * f s)" by (simp add: algebra_simps)
      then show ?thesis using bd sm by (simp add: mult_nonneg_nonneg)
    qed
    ultimately show "\<exists>d. DERIV (\<lambda>s. f s * exp (B * s)) s :> d \<and> 0 \<le> d" by blast
  qed
  have pos: "0 < f t * exp (B * t)" using mono f0 by simp
  show "0 < f t"
  proof (rule ccontr)
    assume "\<not> 0 < f t"
    then have "f t \<le> 0" by simp
    then have "f t * exp (B * t) \<le> 0" by (intro mult_nonpos_nonneg) simp_all
    then show False using pos by simp
  qed
qed

section \<open>D. The sign of the logarithmic derivative of the storage function\<close>

lemma log_step:
  fixes a d Om kap g va u w y :: real
  assumes a0: "0 < a" and Om0: "0 < Om" and OmE: "Om\<^sup>2 = d\<^sup>2 - 1" and k0: "0 < kap" and kE: "kap\<^sup>2 = a\<^sup>2 - 4"
    and a3: "d\<^sup>2 + 3 \<le> a\<^sup>2" and d5: "5 \<le> d\<^sup>2"
    and g0: "0 \<le> g" and g1: "g \<le> 1"
    and h0: "0 \<le> va - (- d + Om) * u" and u0: "0 \<le> u" and y0: "0 \<le> y"
    and N0: "0 < va - (- d - Om) * u" and D0: "0 < (a + kap) / 4 * w - y"
  shows "((- (a + d) * va - g * u) - (- d - Om) * (g * va - (a - d) * u)) * ((a + kap) / 4 * w - y)
      \<le> (va - (- d - Om) * u) * ((a + kap) / 4 * (- 4 * g * y) - (g * w - 2 * a * y))"
proof -
  define th where "th = (a + kap) / 4"
  define N where "N = va - (- d - Om) * u"
  define D where "D = th * w - y"
  define h where "h = va - (- d + Om) * u"
  have Omk: "Om \<le> kap"
  proof -
    have sq: "Om\<^sup>2 \<le> kap\<^sup>2" using OmE kE a3 by simp
    show ?thesis by (rule power2_le_imp_le[OF sq]) (use k0 in simp)
  qed
  have aOm: "d\<^sup>2 < a * Om"
  proof -
    have s1: "(d\<^sup>2)\<^sup>2 < (a * Om)\<^sup>2"
    proof -
      have "(a * Om)\<^sup>2 = a\<^sup>2 * (d\<^sup>2 - 1)" using OmE by (simp add: power_mult_distrib)
      moreover have "(d\<^sup>2 + 3) * (d\<^sup>2 - 1) \<le> a\<^sup>2 * (d\<^sup>2 - 1)" using a3 d5 by (intro mult_right_mono) simp_all
      moreover have "(d\<^sup>2)\<^sup>2 < (d\<^sup>2 + 3) * (d\<^sup>2 - 1)" using d5 by (simp add: algebra_simps power2_eq_square)
      ultimately show ?thesis by linarith
    qed
    have "0 \<le> a * Om" using a0 Om0 by simp
    then show ?thesis by (rule power2_less_imp_less[OF s1])
  qed
  have a_d: "0 < a + d"
  proof -
    show ?thesis
    proof (rule ccontr)
      assume "\<not> 0 < a + d"
      then have "a \<le> - d" by simp
      then have "a\<^sup>2 \<le> (- d)\<^sup>2" using a0 by (intro power_mono) simp_all
      then show False using a3 by simp
    qed
  qed
  have thk: "th * (a - kap) = 1" unfolding th_def using kE by (simp add: algebra_simps power2_eq_square)
  have th0: "0 < th" unfolding th_def using a0 k0 by simp
  (* N' = (1 - g) N0v + g N1v and D' = (1 - g) D0v + g D1v *)
  define Nd where "Nd = (\<lambda>x. (- (a + d) * va - x * u) - (- d - Om) * (x * va - (a - d) * u))"
  define Dd where "Dd = (\<lambda>x. th * (- 4 * x * y) - (x * w - 2 * a * y))"
  have aff: "Nd g * D - N * Dd g = (1 - g) * (Nd 0 * D - N * Dd 0) + g * (Nd 1 * D - N * Dd 1)"
    unfolding Nd_def Dd_def by algebra
  have N1: "Nd 1 = - (a - Om) * N"
  proof -
    have "Nd 1 + (a - Om) * N = u * (d\<^sup>2 - 1 - Om\<^sup>2)" unfolding Nd_def N_def by algebra
    then have "Nd 1 + (a - Om) * N = 0" using OmE by simp
    then show ?thesis by argo
  qed
  have D1: "Dd 1 = - (a - kap) * D"
  proof -
    have hth: "4 * th = a + kap" unfolding th_def by simp
    have "Dd 1 + (a - kap) * D = w * (th * (a - kap) - 1) + y * (a + kap - 4 * th)"
      unfolding Dd_def D_def by algebra
    then have "Dd 1 + (a - kap) * D = 0" using thk hth by simp
    then show ?thesis by argo
  qed
  have P1: "Nd 1 * D - N * Dd 1 \<le> 0"
  proof -
    have "Nd 1 * D - N * Dd 1 = (Om - kap) * (N * D)" unfolding N1 D1 by algebra
    moreover have "(Om - kap) * (N * D) \<le> 0"
      using Omk N0 D0 unfolding N_def D_def th_def by (intro mult_nonpos_nonneg) simp_all
    ultimately show ?thesis by simp
  qed
  have Nd0: "Nd 0 = - (a + d) * h - 2 * (a * Om - d\<^sup>2) * u"
    unfolding Nd_def h_def by algebra
  have P0: "Nd 0 * D - N * Dd 0 \<le> 0"
  proof -
    have n0: "Nd 0 \<le> 0"
    proof -
      have "0 \<le> (a + d) * h" using a_d h0 unfolding h_def by (intro mult_nonneg_nonneg) simp_all
      moreover have "0 \<le> 2 * (a * Om - d\<^sup>2) * u" using aOm u0 by (intro mult_nonneg_nonneg) simp_all
      ultimately show ?thesis unfolding Nd0 by argo
    qed
    have "Dd 0 = 2 * a * y" unfolding Dd_def by simp
    then have "0 \<le> Dd 0" using a0 y0 by simp
    moreover have "0 \<le> N" using N0 unfolding N_def by simp
    ultimately have "0 \<le> N * Dd 0" by (simp add: mult_nonneg_nonneg)
    moreover have "Nd 0 * D \<le> 0" using n0 D0 unfolding D_def th_def by (intro mult_nonpos_nonneg) simp_all
    ultimately show ?thesis by simp
  qed
  have "Nd g * D - N * Dd g \<le> 0"
  proof -
    have "(1 - g) * (Nd 0 * D - N * Dd 0) \<le> 0" using g1 P0 by (intro mult_nonneg_nonpos) simp_all
    moreover have "g * (Nd 1 * D - N * Dd 1) \<le> 0" using g0 P1 by (intro mult_nonneg_nonpos) simp_all
    ultimately show ?thesis unfolding aff by simp
  qed
  then show ?thesis unfolding Nd_def Dd_def N_def D_def th_def by simp
qed

section \<open>E. The storage-function bound for the swap system\<close>

theorem unequal_storage_bound:
  fixes a d Om kap :: real and g va u w y :: "real \<Rightarrow> real" and T :: real
  assumes a0: "0 < a" and Om0: "0 < Om" and OmE: "Om\<^sup>2 = d\<^sup>2 - 1" and k0: "0 < kap" and kE: "kap\<^sup>2 = a\<^sup>2 - 4"
    and a3: "d\<^sup>2 + 3 \<le> a\<^sup>2" and d5: "5 \<le> d\<^sup>2"
    and T0: "0 \<le> T" and gc: "continuous_on {0..T} g" and g01: "\<forall>t\<in>{0..T}. 0 \<le> g t \<and> g t \<le> 1"
    and dva: "\<forall>t\<in>{0..T}. (va has_real_derivative - (a + d) * va t - g t * u t) (at t)"
    and du: "\<forall>t\<in>{0..T}. (u has_real_derivative g t * va t - (a - d) * u t) (at t)"
    and dw: "\<forall>t\<in>{0..T}. (w has_real_derivative - 4 * g t * y t) (at t)"
    and dy: "\<forall>t\<in>{0..T}. (y has_real_derivative g t * w t - 2 * a * y t) (at t)"
    and ini: "va 0 = 1" "u 0 = 0" "w 0 = 1" "y 0 = 0"
  shows "\<forall>t\<in>{0..T}. 0 < w t \<and> 0 \<le> y t \<and> 0 \<le> u t \<and> 2 * Om * u t < w t"
    and "\<forall>t\<in>{0..T}. (1 - w t) / 2 + 2 * u t < 1 / 2"
proof -
  define thn where "thn = (a - kap) / 4"
  define thp where "thp = (a + kap) / 4"
  define chp where "chp = - d + Om"
  define chm where "chm = - d - Om"
  have kA: "kap < a"
  proof -
    have sq: "kap\<^sup>2 < a\<^sup>2" using kE by simp
    show ?thesis by (rule power2_less_imp_less[OF sq]) (use a0 in simp)
  qed
  have thn0: "0 < thn" unfolding thn_def using kA by simp
  have thp0: "0 < thp" unfolding thp_def using a0 k0 by simp
  have relm: "4 * thn\<^sup>2 - 2 * a * thn + 1 = 0" unfolding thn_def using kE by (simp add: algebra_simps power2_eq_square) argo
  have relp: "4 * thp\<^sup>2 - 2 * a * thp + 1 = 0" unfolding thp_def using kE by (simp add: algebra_simps power2_eq_square) argo
  have chrel: "chp\<^sup>2 + ((a + d) - (a - d)) * chp + 1 = 0" unfolding chp_def using OmE by (simp add: algebra_simps power2_eq_square)
  have Om2: "2 \<le> Om"
  proof -
    have sq: "2\<^sup>2 \<le> Om\<^sup>2" using OmE d5 by simp
    show ?thesis by (rule power2_le_imp_le[OF sq]) (use Om0 in simp)
  qed
  (* cone for (y, z) *)
  define z where "z = (\<lambda>t. thn * w t - y t)"
  have dyz: "\<forall>t\<in>{0..T}. (y has_real_derivative (g t / thn - 2 * a) * y t + g t / thn * z t) (at t)
      \<and> (z has_real_derivative (1 - g t) * 2 * a * y t + (- (g t / thn)) * z t) (at t)"
  proof
    fix t assume t: "t \<in> {0..T}"
    have r1: "(y has_real_derivative (g t / thn - 2 * a) * y t + g t / thn * (thn * w t - y t)) (at t)"
      and r2: "((\<lambda>s. thn * w s - y s) has_real_derivative
          (1 - g t) * 2 * a * y t + (- (g t / thn)) * (thn * w t - y t)) (at t)"
      using reduce_yz[where w = w and y = y and g = g and a = a and th = thn and t = t, OF thn0 relm dw[rule_format, OF t] dy[rule_format, OF t]] by blast+
    show "(y has_real_derivative (g t / thn - 2 * a) * y t + g t / thn * z t) (at t)
      \<and> (z has_real_derivative (1 - g t) * 2 * a * y t + (- (g t / thn)) * z t) (at t)"
      unfolding z_def using r1 r2 by blast
  qed
  have dy1: "\<forall>t\<in>{0..T}. (y has_real_derivative (g t / thn - 2 * a) * y t + g t / thn * z t) (at t)"
    using dyz by blast
  have dz1: "\<forall>t\<in>{0..T}. (z has_real_derivative (1 - g t) * 2 * a * y t + (- (g t / thn)) * z t) (at t)"
    using dyz by blast
  have y0': "0 \<le> y 0" using ini by simp
  have z0': "0 \<le> z 0" using ini thn0 unfolding z_def by simp
  have cyz: "\<forall>t\<in>{0..T}. 0 \<le> y t \<and> 0 \<le> z t"
    by (rule cone_yz[OF T0 gc g01 thn0 _ dy1 dz1 y0' z0']) (use a0 in simp)
  (* w > 0 *)
  have wnn: "\<forall>t\<in>{0..T}. 0 \<le> w t"
  proof
    fix t assume t: "t \<in> {0..T}"
    have "thn * w t = z t + y t" unfolding z_def by simp
    moreover have "0 \<le> z t + y t" using cyz t by force
    ultimately have pz: "0 \<le> thn * w t" by simp
    show "0 \<le> w t"
    proof (rule ccontr)
      assume "\<not> 0 \<le> w t"
      then have "w t < 0" by simp
      then have "thn * w t < 0" using thn0 by (intro mult_pos_neg)
      then show False using pz by simp
    qed
  qed
  have wpos: "\<forall>t\<in>{0..T}. 0 < w t"
  proof (rule exp_growth_lower[of T w "\<lambda>t. - 4 * g t * y t" "4 * thn"])
    show "0 \<le> T" by (rule T0)
    show "\<forall>t\<in>{0..T}. (w has_real_derivative - 4 * g t * y t) (at t)" by (rule dw)
    show "0 < w 0" using ini by simp
    show "\<forall>t\<in>{0..T}. 0 \<le> - 4 * g t * y t + 4 * thn * w t"
    proof
      fix t assume t: "t \<in> {0..T}"
      have gt: "0 \<le> g t" "g t \<le> 1" using g01 t by blast+
      have yz: "y t \<le> thn * w t" using cyz t unfolding z_def by force
      have wn: "0 \<le> w t" using wnn t by blast
      have "g t * y t \<le> g t * (thn * w t)" using gt(1) yz by (intro mult_left_mono)
      also have "\<dots> \<le> 1 * (thn * w t)" using gt(2) thn0 wn by (intro mult_right_mono) simp_all
      finally show "0 \<le> - 4 * g t * y t + 4 * thn * w t" by linarith
    qed
  qed
  (* cone for (u, h) *)
  define h where "h = (\<lambda>t. va t - chp * u t)"
  have duh: "\<forall>t\<in>{0..T}. (u has_real_derivative (g t * chp - (a - d)) * u t + g t * h t) (at t)
      \<and> (h has_real_derivative (1 - g t) * (1 + chp\<^sup>2) * u t + (- ((a + d) + g t * chp)) * h t) (at t)"
  proof
    fix t assume t: "t \<in> {0..T}"
    have r1: "(u has_real_derivative (g t * chp - (a - d)) * u t + g t * (va t - chp * u t)) (at t)"
      and r2: "((\<lambda>s. va s - chp * u s) has_real_derivative
          (1 - g t) * (1 + chp\<^sup>2) * u t + (- ((a + d) + g t * chp)) * (va t - chp * u t)) (at t)"
      using reduce_uh[where va = va and u = u and g = g and q = "a + d" and m = "a - d" and chi = chp and t = t, OF chrel dva[rule_format, OF t] du[rule_format, OF t]] by blast+
    show "(u has_real_derivative (g t * chp - (a - d)) * u t + g t * h t) (at t)
      \<and> (h has_real_derivative (1 - g t) * (1 + chp\<^sup>2) * u t + (- ((a + d) + g t * chp)) * h t) (at t)"
      unfolding h_def using r1 r2 by blast
  qed
  have du1: "\<forall>t\<in>{0..T}. (u has_real_derivative (g t * chp - (a - d)) * u t + g t * h t) (at t)"
    using duh by blast
  have dh1: "\<forall>t\<in>{0..T}. (h has_real_derivative (1 - g t) * (1 + chp\<^sup>2) * u t + (- ((a + d) + g t * chp)) * h t) (at t)"
    using duh by blast
  have u0': "0 \<le> u 0" using ini by simp
  have h0': "0 \<le> h 0" using ini unfolding h_def by simp
  have cuh: "\<forall>t\<in>{0..T}. 0 \<le> u t \<and> 0 \<le> h t"
    by (rule cone_uh[OF T0 gc g01 du1 dh1 u0' h0'])
  have hpos: "\<forall>t\<in>{0..T}. 0 < h t"
  proof (rule exp_growth_lower[of T h "\<lambda>t. (1 - g t) * (1 + chp\<^sup>2) * u t + (- ((a + d) + g t * chp)) * h t"
        "\<bar>a + d\<bar> + \<bar>chp\<bar>"])
    show "0 \<le> T" by (rule T0)
    show "\<forall>t\<in>{0..T}. (h has_real_derivative (1 - g t) * (1 + chp\<^sup>2) * u t + (- ((a + d) + g t * chp)) * h t) (at t)"
      using duh by blast
    show "0 < h 0" using ini unfolding h_def by simp
    show "\<forall>t\<in>{0..T}. 0 \<le> (1 - g t) * (1 + chp\<^sup>2) * u t + (- ((a + d) + g t * chp)) * h t + (\<bar>a + d\<bar> + \<bar>chp\<bar>) * h t"
    proof
      fix t assume t: "t \<in> {0..T}"
      have gt: "0 \<le> g t" "g t \<le> 1" using g01 t by blast+
      have un: "0 \<le> u t" and hn: "0 \<le> h t" using cuh t by blast+
      have t1: "0 \<le> (1 - g t) * (1 + chp\<^sup>2) * u t" using gt(2) un by (intro mult_nonneg_nonneg) simp_all
      have "g t * chp \<le> g t * \<bar>chp\<bar>" using gt(1) by (intro mult_left_mono) simp_all
      also have "\<dots> \<le> 1 * \<bar>chp\<bar>" using gt(2) by (intro mult_right_mono) simp_all
      finally have c1: "g t * chp \<le> \<bar>chp\<bar>" by simp
      have "(a + d) \<le> \<bar>a + d\<bar>" by simp
      then have "0 \<le> \<bar>a + d\<bar> + \<bar>chp\<bar> - ((a + d) + g t * chp)" using c1 by linarith
      then have "0 \<le> (\<bar>a + d\<bar> + \<bar>chp\<bar> - ((a + d) + g t * chp)) * h t" using hn by (intro mult_nonneg_nonneg)
      then show "0 \<le> (1 - g t) * (1 + chp\<^sup>2) * u t + (- ((a + d) + g t * chp)) * h t + (\<bar>a + d\<bar> + \<bar>chp\<bar>) * h t"
        using t1 by (simp add: algebra_simps)
    qed
  qed
  (* storage function *)
  define Nf where "Nf = (\<lambda>t. va t - chm * u t)"
  define Df where "Df = (\<lambda>t. thp * w t - y t)"
  have Nrel: "\<And>t. Nf t = h t + 2 * Om * u t" unfolding Nf_def h_def chm_def chp_def by (simp add: algebra_simps)
  have Dpos: "0 < Df t" if t: "t \<in> {0..T}" for t
  proof -
    have hd: "thp - thn = kap / 2" unfolding thp_def thn_def by (simp add: field_simps)
    have "Df t = (thp - thn) * w t + z t" unfolding Df_def z_def by (simp add: algebra_simps)
    also have "\<dots> = (kap / 2) * w t + z t" unfolding hd by simp
    finally have "Df t = (kap / 2) * w t + z t" .
    moreover have "0 < (kap / 2) * w t" using k0 wpos t by (intro mult_pos_pos) simp_all
    moreover have "0 \<le> z t" using cyz t by blast
    ultimately show "0 < Df t" by simp
  qed
  have Npos: "0 < Nf t" if t: "t \<in> {0..T}" for t
  proof -
    have "0 \<le> 2 * Om * u t" using Om0 cuh t by (intro mult_nonneg_nonneg) simp_all
    moreover have "0 < h t" using hpos t by blast
    ultimately show "0 < Nf t" unfolding Nrel by simp
  qed
  define Nf' where "Nf' = (\<lambda>t. (- (a + d) * va t - g t * u t) - chm * (g t * va t - (a - d) * u t))"
  define Df' where "Df' = (\<lambda>t. thp * (- 4 * g t * y t) - (g t * w t - 2 * a * y t))"
  have dN: "\<forall>t\<in>{0..T}. (Nf has_real_derivative Nf' t) (at t)"
  proof
    fix t assume t: "t \<in> {0..T}"
    show "(Nf has_real_derivative Nf' t) (at t)"
      unfolding Nf_def Nf'_def by (rule DERIV_diff[OF dva[rule_format, OF t] DERIV_cmult[OF du[rule_format, OF t]]])
  qed
  have dD: "\<forall>t\<in>{0..T}. (Df has_real_derivative Df' t) (at t)"
  proof
    fix t assume t: "t \<in> {0..T}"
    show "(Df has_real_derivative Df' t) (at t)"
      unfolding Df_def Df'_def by (rule DERIV_diff[OF DERIV_cmult[OF dw[rule_format, OF t]] dy[rule_format, OF t]])
  qed
  have lg: "\<forall>t\<in>{0..T}. Nf' t * Df t \<le> Nf t * Df' t"
  proof
    fix t assume t: "t \<in> {0..T}"
    have gt: "0 \<le> g t" "g t \<le> 1" using g01 t by blast+
    have h0: "0 \<le> va t - (- d + Om) * u t" using cuh t unfolding h_def chp_def by force
    have un: "0 \<le> u t" using cuh t by blast
    have yn: "0 \<le> y t" using cyz t by blast
    have Nt: "0 < va t - (- d - Om) * u t" using Npos[OF t] unfolding Nf_def chm_def by simp
    have Dt: "0 < (a + kap) / 4 * w t - y t" using Dpos[OF t] unfolding Df_def thp_def by simp
    have ls: "((- (a + d) * va t - g t * u t) - (- d - Om) * (g t * va t - (a - d) * u t)) * ((a + kap) / 4 * w t - y t)
      \<le> (va t - (- d - Om) * u t) * ((a + kap) / 4 * (- 4 * g t * y t) - (g t * w t - 2 * a * y t))"
      by (rule log_step[OF a0 Om0 OmE k0 kE a3 d5 gt(1) gt(2) h0 un yn Nt Dt])
    show "Nf' t * Df t \<le> Nf t * Df' t"
      using ls unfolding Nf'_def Df'_def Nf_def Df_def chm_def thp_def by simp
  qed
  have ratio: "\<forall>t\<in>{0..T}. Nf t / Df t \<le> Nf 0 / Df 0"
  proof
    fix t assume t: "t \<in> {0..T}"
    have sub: "{0..t} \<subseteq> {0..T}" using t by simp
    have t0: "0 \<le> t" using t by simp
    have r1: "\<forall>s\<in>{0..t}. (Nf has_real_derivative Nf' s) (at s)" using dN sub by blast
    have r2: "\<forall>s\<in>{0..t}. (Df has_real_derivative Df' s) (at s)" using dD sub by blast
    have r3: "\<forall>s\<in>{0..t}. 0 < Df s" using Dpos sub by blast
    have r4: "\<forall>s\<in>{0..t}. Nf' s * Df s \<le> Nf s * Df' s" using lg sub by blast
    show "Nf t / Df t \<le> Nf 0 / Df 0" by (rule ratio_nonincreasing[OF t0 r1 r2 r3 r4])
  qed
  have N0: "Nf 0 = 1" and D0: "Df 0 = thp" using ini unfolding Nf_def Df_def by simp_all
  have key: "\<forall>t\<in>{0..T}. 2 * Om * u t < w t"
  proof
    fix t assume t: "t \<in> {0..T}"
    have "Nf t / Df t \<le> 1 / thp" using ratio t N0 D0 by simp
    then have "Nf t \<le> Df t / thp" using Dpos t thp0 by (simp add: field_simps)
    also have "\<dots> = w t - y t / thp" unfolding Df_def using thp0 by (simp add: field_simps)
    also have "\<dots> \<le> w t" using cyz t thp0 by (simp add: divide_nonneg_pos)
    finally have "Nf t \<le> w t" .
    moreover have "Nf t = h t + 2 * Om * u t" by (rule Nrel)
    ultimately show "2 * Om * u t < w t" using hpos t by force
  qed
  show "\<forall>t\<in>{0..T}. 0 < w t \<and> 0 \<le> y t \<and> 0 \<le> u t \<and> 2 * Om * u t < w t"
    using wpos cyz cuh key by blast
  show "\<forall>t\<in>{0..T}. (1 - w t) / 2 + 2 * u t < 1 / 2"
  proof
    fix t assume t: "t \<in> {0..T}"
    have un: "0 \<le> u t" using cuh t by blast
    have "2 * (2 * u t) \<le> Om * (2 * u t)" using Om2 un by (intro mult_right_mono) simp_all
    then have "4 * u t < w t" using key t by force
    then show "(1 - w t) / 2 + 2 * u t < 1 / 2" by argo
  qed
qed

end
