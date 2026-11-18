(*  Title:      Pop_Lyapunov_Step.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The Lyapunov step of Theorems thm:pop / thm:fixed of the memory-floor note A (memory-floors.tex, section "Fixed
    durations, and a proof without the maximum principle"), with the derivative identity taken as a HYPOTHESIS.

    What is formalised.
    (1) dini_danskin: Dini-Danskin lemma.  K compact (metric), F jointly continuous on K x [a,b], for each k the
        derivative of t |-> F k t is H k t (within [a,b]) with H jointly continuous, v t = max_{k in K} F k t.  If c
        bounds H k t over the ACTIVE k (F k t = v t), then for every eps > 0 there is delta > 0 with
        v s <= v t + (c + eps) (s - t) for t < s < t + delta, i.e. the right upper Dini derivative of v at t is <= c.
        (Also max_continuous: v is continuous.)
    (2) dini_monotone: v continuous on [a,b] whose right upper Dini derivative is <= 0 on [a,b) (in the epsilon form
        above, with c = 0) is non-increasing.
    (3) Locale pop_lyapunov: the memory problem with index set K = [0,1] x [0,2 pi] (the shrinking range tau in
        [0, T - t] is handled by REPARAMETRISING tau = u (T - t), u in [0,1]; K is fixed), F_{u,theta}(t) =
        tr(E_{u(T-t),theta} R(t)) written with the entries A, B, z of E_{tau,0} (E_ab = i z e^{i theta}), the
        derivative identity
            dF/dt = H_{g(t)} - u H_{g_theta}   and   dF/du = (T - t) H_{g_theta}
        as ASSUMPTIONS, and the cases (i)-(iv) of the paper derived from the maximality of the active index over u and
        theta (stationarity in u, one-sidedness at u = 0, 1; stationarity and sign in theta: Re(conj(E_ab) rho) >= 0
        and alignment of K with E_ab), using H_max, h0_negative, case_i ... case_iv of Fixed_Duration_Core.  Inside:
        v_antitone (v(t) = V_{T-t}(R(t)) non-increasing, for gamma_min > 0) and pb_bound (p_b(T) <= V_T(R(0))).
    The definitions and lemmas of Fixed_Duration_Core (H_max, h0_negative, H_aligned_cases, case_i ... case_iv,
    lyapunov_conclusion) are reused from the copy Fixed_Duration_Core.thy in this folder (identical to the file of
    formalizations/Isabelle/MemoryAccessFloors).

    What is ASSUMED (not proved): the derivative identity for dF/dt and dF/du (a matrix identity for the generator of
    the master equation); existence and regularity of R(t), E_{tau,0} and of the control g (here g, R, A, B, z are
    CONTINUOUS, and F has the two derivatives above; the paper allows measurable g and uses almost-everywhere
    derivatives, which is NOT covered); the structure E_ab = i z e^{i theta} with A, B, z independent of theta; the
    end conditions E = projector on b at u = 0 and at t = T; positivity (a, b >= 0, A, B >= 0); non-degeneracy
    v(t) > 0 for t < T (R(t) <> 0); the rates >= gamma_min > 0.
    What is NOT formalised: the evaluation of V_T(R(0)) as max_s p_res(s) (here it is v(0), the maximum over K of
    F at t = 0); the Lipschitz property of v; the limit gamma_min -> 0 (epsilon_limit of Fixed_Duration_Core is
    not instantiated); measurable controls; the identification of H with the derivative along the master equation.
    Hence: the Lyapunov step is formalised GIVEN the derivative identity; this is not "thm:pop formalised".
*)

theory Pop_Lyapunov_Step
  imports Fixed_Duration_Core
begin

section \<open>Part 1: the Dini-Danskin lemma\<close>

text \<open>Parametrisation chosen: the index set K is fixed and compact; the shrinking range of the paper is handled by
  the reparametrisation tau = u (T - t) in the application (locale below), not here.\<close>

lemma seq_cont:
  assumes "continuous_on S f" and "\<And>n. x n \<in> S" and "x \<longlonglongrightarrow> a" and "a \<in> S"
  shows "(\<lambda>n. f (x n)) \<longlonglongrightarrow> f a"
proof -
  have "eventually (\<lambda>n. x n \<in> S) sequentially" by (rule always_eventually, rule allI, rule assms(2))
  from continuous_on_tendsto_compose[OF assms(1) assms(3) assms(4) this] show ?thesis .
qed

lemma dini_danskin:
  fixes F :: "'k::metric_space \<Rightarrow> real \<Rightarrow> real" and H :: "'k \<Rightarrow> real \<Rightarrow> real" and v :: "real \<Rightarrow> real"
  assumes cK: "compact K"
    and Fc: "continuous_on (K \<times> {a..b}) (\<lambda>p. F (fst p) (snd p))"
    and Hc: "continuous_on (K \<times> {a..b}) (\<lambda>p. H (fst p) (snd p))"
    and der: "\<And>k x. k \<in> K \<Longrightarrow> x \<in> {a..b} \<Longrightarrow> (F k has_real_derivative H k x) (at x within {a..b})"
    and vmax: "\<And>t. t \<in> {a..b} \<Longrightarrow> (\<forall>k\<in>K. F k t \<le> v t) \<and> (\<exists>k\<in>K. F k t = v t)"
    and t: "t \<in> {a..b}"
    and c: "\<And>k. k \<in> K \<Longrightarrow> F k t = v t \<Longrightarrow> H k t \<le> c"
    and eps: "0 < eps"
  shows "\<exists>delta>0. \<forall>s. t < s \<longrightarrow> s < t + delta \<longrightarrow> s \<le> b \<longrightarrow> v s \<le> v t + (c + eps) * (s - t)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have bad: "\<And>delta. 0 < delta \<Longrightarrow> \<exists>s. t < s \<and> s < t + delta \<and> s \<le> b \<and> \<not> v s \<le> v t + (c + eps) * (s - t)"
    by auto
  have "\<forall>n::nat. \<exists>s. t < s \<and> s < t + 1 / real (Suc n) \<and> s \<le> b \<and> v t + (c + eps) * (s - t) < v s"
  proof
    fix n :: nat
    have "0 < 1 / real (Suc n)" by simp
    from bad[OF this] show "\<exists>s. t < s \<and> s < t + 1 / real (Suc n) \<and> s \<le> b \<and> v t + (c + eps) * (s - t) < v s"
      by (auto simp: not_le)
  qed
  then obtain s0 where s0: "\<And>n. t < s0 n" "\<And>n. s0 n < t + 1 / real (Suc n)" "\<And>n. s0 n \<le> b"
    "\<And>n. v t + (c + eps) * (s0 n - t) < v (s0 n)"
    by (metis (no_types))
  have s0ab: "\<And>n. s0 n \<in> {a..b}"
  proof -
    fix n
    have "a \<le> t" using t by simp
    then show "s0 n \<in> {a..b}" using s0(1)[of n] s0(3)[of n] by simp
  qed
  have "\<forall>n. \<exists>k\<in>K. F k (s0 n) = v (s0 n)" using vmax s0ab by blast
  then obtain k0 where k0: "\<And>n. k0 n \<in> K" "\<And>n. F (k0 n) (s0 n) = v (s0 n)" by (metis (no_types))
  from cK obtain l r where l: "l \<in> K" and r: "strict_mono r" and kl: "(k0 \<circ> r) \<longlonglongrightarrow> l"
    using k0(1) by (metis compact_eq_seq_compact_metric seq_compact_def)
  define s where "s = s0 \<circ> r"
  define k where "k = k0 \<circ> r"
  have sk: "\<And>n. s n \<in> {a..b}" "\<And>n. k n \<in> K" unfolding s_def k_def using s0ab k0(1) by simp_all
  have sgt: "\<And>n. t < s n" unfolding s_def using s0(1) by simp
  have slt: "\<And>n. s n < t + 1 / real (Suc (r n))" unfolding s_def using s0(2) by simp
  have st: "s \<longlonglongrightarrow> t"
  proof (rule tendsto_sandwich[of "\<lambda>n. t" s sequentially "\<lambda>n. t + 1 / real (Suc (r n))"])
    show "eventually (\<lambda>n. t \<le> s n) sequentially" using sgt by (simp add: less_imp_le)
    show "eventually (\<lambda>n. s n \<le> t + 1 / real (Suc (r n))) sequentially" using slt by (simp add: less_imp_le)
    show "(\<lambda>n. t) \<longlonglongrightarrow> t" by simp
    have h1: "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> (0::real)"
      using LIMSEQ_Suc[OF lim_1_over_n] by simp
    have h2: "(\<lambda>n. 1 / real (Suc (r n))) \<longlonglongrightarrow> 0"
      using LIMSEQ_subseq_LIMSEQ[OF h1 r] by (simp add: o_def)
    then show "(\<lambda>n. t + 1 / real (Suc (r n))) \<longlonglongrightarrow> t"
      using tendsto_add[OF tendsto_const[of t] h2] by simp
  qed
  have Fseq: "\<And>kk. kk \<in> K \<Longrightarrow> (\<lambda>n. F kk (s n)) \<longlonglongrightarrow> F kk t"
  proof -
    fix kk assume kk: "kk \<in> K"
    have pk: "(\<lambda>n. (kk, s n)) \<longlonglongrightarrow> (kk, t)" using st by (intro tendsto_intros)
    have "(\<lambda>n. (\<lambda>p. F (fst p) (snd p)) (kk, s n)) \<longlonglongrightarrow> (\<lambda>p. F (fst p) (snd p)) (kk, t)"
      using seq_cont[OF Fc _ pk] kk sk t by simp
    then show "(\<lambda>n. F kk (s n)) \<longlonglongrightarrow> F kk t" by simp
  qed
  have kl': "k \<longlonglongrightarrow> l" using kl by (simp add: k_def)
  have pair: "(\<lambda>n. (k n, s n)) \<longlonglongrightarrow> (l, t)" by (rule tendsto_Pair[OF kl' st])
  have Fl: "(\<lambda>n. F (k n) (s n)) \<longlonglongrightarrow> F l t"
    using seq_cont[OF Fc _ pair] sk l t by simp
  have Fkn: "\<And>n. F (k n) (s n) = v (s n)" unfolding k_def s_def using k0(2) by simp
  have lmax: "\<And>kk. kk \<in> K \<Longrightarrow> F kk t \<le> F l t"
  proof -
    fix kk assume kk: "kk \<in> K"
    have "\<And>n. F kk (s n) \<le> F (k n) (s n)" using vmax sk(1) kk Fkn by auto
    from tendsto_le[OF sequentially_bot Fl Fseq[OF kk]] this show "F kk t \<le> F l t" by simp
  qed
  have lact: "F l t = v t"
  proof -
    obtain k1 where k1: "k1 \<in> K" "F k1 t = v t" using vmax t by blast
    have "F l t \<le> v t" using vmax t l by blast
    moreover have "v t \<le> F l t" using lmax[OF k1(1)] k1(2) by simp
    ultimately show ?thesis by simp
  qed
  have cl: "H l t \<le> c" by (rule c[OF l lact])
  \<comment> \<open>mean value theorem on [t, s n]\<close>
  have mvt_n: "\<And>n. \<exists>xi. t < xi \<and> xi < s n \<and> F (k n) (s n) - F (k n) t = H (k n) xi * (s n - t)"
  proof -
    fix n
    have kn: "k n \<in> K" by (rule sk)
    have sub: "{t..s n} \<subseteq> {a..b}" using t sk(1)[of n] by auto
    have Fkc: "continuous_on {a..b} (F (k n))"
    proof -
      have "continuous_on {a..b} (\<lambda>x. (\<lambda>p. F (fst p) (snd p)) (k n, x))"
        by (rule continuous_on_compose2[OF Fc]) (use kn in \<open>auto intro!: continuous_intros\<close>)
      then show ?thesis by simp
    qed
    have d: "\<And>x. t < x \<Longrightarrow> x < s n \<Longrightarrow> (F (k n) has_derivative (*) (H (k n) x)) (at x)"
    proof -
      fix x assume x: "t < x" "x < s n"
      have xi: "x \<in> {a..b}" using x sub by auto
      have "x \<in> interior {a..b}" using x sub t sk(1)[of n] by (auto simp: interior_atLeastAtMost_real)
      then have "at x within {a..b} = at x" by (rule at_within_interior)
      then show "(F (k n) has_derivative (*) (H (k n) x)) (at x)"
        using der[OF kn xi] by (simp add: has_field_derivative_def)
    qed
    from mvt[OF sgt[of n] continuous_on_subset[OF Fkc sub] d]
    obtain xi where "t < xi" "xi < s n" "F (k n) (s n) - F (k n) t = H (k n) xi * (s n - t)" by blast
    then show "\<exists>xi. t < xi \<and> xi < s n \<and> F (k n) (s n) - F (k n) t = H (k n) xi * (s n - t)" by blast
  qed
  then obtain xi where xi: "\<And>n. t < xi n" "\<And>n. xi n < s n"
    "\<And>n. F (k n) (s n) - F (k n) t = H (k n) (xi n) * (s n - t)" by (metis (no_types))
  have xiab: "\<And>n. xi n \<in> {a..b}"
  proof -
    fix n
    have "a \<le> t" "t < xi n" "xi n < s n" "s n \<le> b" using t xi(1,2)[of n] sk(1)[of n] by auto
    then show "xi n \<in> {a..b}" by simp
  qed
  have xit: "xi \<longlonglongrightarrow> t"
    by (rule tendsto_sandwich[of "\<lambda>n. t" xi sequentially s]) (use xi st in \<open>auto intro!: always_eventually less_imp_le\<close>)
  have Hl: "(\<lambda>n. H (k n) (xi n)) \<longlonglongrightarrow> H l t"
  proof -
    have pr: "(\<lambda>n. (k n, xi n)) \<longlonglongrightarrow> (l, t)" using kl' xit by (rule tendsto_Pair)
    show ?thesis
      using seq_cont[OF Hc _ pr] sk(2) xiab l t by simp
  qed
  have ineq: "\<And>n. c + eps < H (k n) (xi n)"
  proof -
    fix n
    have "v (s n) - v t \<le> F (k n) (s n) - F (k n) t" using Fkn[of n] vmax[OF t] sk(2)[of n] by auto
    moreover have "v t + (c + eps) * (s n - t) < v (s n)" using s0 unfolding s_def by simp
    ultimately have "(c + eps) * (s n - t) < H (k n) (xi n) * (s n - t)" using xi(3)[of n] by linarith
    then show "c + eps < H (k n) (xi n)" using sgt[of n] by (simp add: mult_less_cancel_right)
  qed
  have "c + eps \<le> H l t" using tendsto_lowerbound[OF Hl _ sequentially_bot] ineq by (simp add: less_imp_le)
  with cl eps show False by linarith
qed

lemma max_continuous:
  fixes F :: "'k::metric_space \<Rightarrow> real \<Rightarrow> real" and v :: "real \<Rightarrow> real"
  assumes cK: "compact K"
    and Fc: "continuous_on (K \<times> {a..b}) (\<lambda>p. F (fst p) (snd p))"
    and vmax: "\<And>t. t \<in> {a..b} \<Longrightarrow> (\<forall>k\<in>K. F k t \<le> v t) \<and> (\<exists>k\<in>K. F k t = v t)"
  shows "continuous_on {a..b} v"
proof -
  have "compact (K \<times> {a..b})" using cK by (intro compact_Times compact_Icc)
  from compact_uniformly_continuous[OF Fc this] have uc: "uniformly_continuous_on (K \<times> {a..b}) (\<lambda>p. F (fst p) (snd p))" .
  have "uniformly_continuous_on {a..b} v"
  unfolding uniformly_continuous_on_def
  proof (intro allI impI)
    fix e :: real assume e: "0 < e"
    have e2: "0 < e / 2" using e by simp
    from uc[unfolded uniformly_continuous_on_def, rule_format, OF e2] obtain d where d: "0 < d"
      and dd: "\<And>x x'. x \<in> K \<times> {a..b} \<Longrightarrow> x' \<in> K \<times> {a..b} \<Longrightarrow> dist x' x < d \<Longrightarrow>
         dist (F (fst x') (snd x')) (F (fst x) (snd x)) < e / 2" by blast
    have key: "\<And>s t. s \<in> {a..b} \<Longrightarrow> t \<in> {a..b} \<Longrightarrow> dist s t < d \<Longrightarrow> v s \<le> v t + e / 2"
    proof -
      fix s t assume s: "s \<in> {a..b}" and t: "t \<in> {a..b}" and st: "dist s t < d"
      obtain k where k: "k \<in> K" "F k s = v s" using vmax s by blast
      have "dist (k, s) (k, t) < d" using st by (simp add: dist_prod_def)
      from dd[of "(k, t)" "(k, s)"] this k s t have h: "dist (F k s) (F k t) < e / 2" by simp
      have "F k t \<le> v t" using vmax t k by blast
      have "\<bar>F k s - F k t\<bar> < e / 2" using h by (simp add: dist_real_def)
      then have "F k s - F k t < e / 2" by (rule order_le_less_trans[OF abs_ge_self])
      with k(2) show "v s \<le> v t + e / 2" using `F k t \<le> v t` by linarith
    qed
    show "\<exists>d>0. \<forall>x\<in>{a..b}. \<forall>x'\<in>{a..b}. dist x' x < d \<longrightarrow> dist (v x') (v x) < e"
    proof (intro exI[where x = d] conjI ballI impI)
      show "0 < d" by (rule d)
      fix x x' assume x: "x \<in> {a..b}" and x': "x' \<in> {a..b}" and dx: "dist x' x < d"
      have "v x' \<le> v x + e / 2" by (rule key[OF x' x dx])
      moreover have "v x \<le> v x' + e / 2" using key[OF x x'] dx by (simp add: dist_commute)
      ultimately show "dist (v x') (v x) < e" using e by (auto simp: dist_real_def abs_less_iff)
    qed
  qed
  then show ?thesis by (rule uniformly_continuous_imp_continuous)
qed

section \<open>Part 2: monotonicity from the right upper Dini derivative\<close>

lemma dini_monotone:
  fixes v :: "real \<Rightarrow> real"
  assumes vc: "continuous_on {a..b} v"
    and dini: "\<And>t eps. a \<le> t \<Longrightarrow> t < b \<Longrightarrow> 0 < eps \<Longrightarrow>
       \<exists>delta>0. \<forall>s. t < s \<longrightarrow> s < t + delta \<longrightarrow> s \<le> b \<longrightarrow> v s \<le> v t + eps * (s - t)"
    and x: "a \<le> x" and xy: "x \<le> y" and y: "y \<le> b"
  shows "v y \<le> v x"
proof (rule ccontr)
  assume "\<not> v y \<le> v x"
  then have gap: "v x < v y" by simp
  define eps where "eps = (v y - v x) / (y - x + 1)"
  have eps0: "0 < eps" unfolding eps_def using gap xy by (simp add: divide_pos_pos)
  define w where "w t = v t - v x - eps * (t - x)" for t
  have wc: "continuous_on {x..y} w" unfolding w_def
    by (intro continuous_intros continuous_on_subset[OF vc]) (use x y in auto)
  have wy: "0 < w y"
  proof -
    have "eps * (y - x) < v y - v x"
    proof -
      have "eps * (y - x + 1) = v y - v x" unfolding eps_def using xy by (simp add: field_simps)
      then show ?thesis using eps0 by (simp add: algebra_simps)
    qed
    then show ?thesis unfolding w_def by simp
  qed
  define S where "S = {t \<in> {x..y}. w t \<le> 0}"
  have Sc: "closed S" unfolding S_def
    by (intro continuous_on_closed_Collect_le wc continuous_on_const closed_atLeastAtMost)
  have xS: "x \<in> S" unfolding S_def w_def using xy by simp
  have Sb: "bdd_above S" unfolding S_def by (intro bdd_aboveI[of _ y]) auto
  define m where "m = Sup S"
  have mS: "m \<in> S" unfolding m_def by (rule closed_contains_Sup[OF _ Sb Sc]) (use xS in auto)
  have mxy: "x \<le> m" "m \<le> y" "w m \<le> 0" using mS unfolding S_def by auto
  have my: "m \<noteq> y" using mS wy unfolding S_def by auto
  then have mlt: "m < y" using mxy by simp
  obtain delta where delta: "0 < delta"
    and dl: "\<And>s. m < s \<Longrightarrow> s < m + delta \<Longrightarrow> s \<le> b \<Longrightarrow> v s \<le> v m + eps * (s - m)"
    using dini[OF _ _ eps0, of m] x mxy mlt y by (metis order_trans order_less_le_trans)
  define s where "s = min (m + delta / 2) y"
  have s1: "m < s" unfolding s_def using delta mlt by simp
  have s2: "s < m + delta" unfolding s_def using delta by simp
  have s3: "s \<le> y" unfolding s_def by simp
  have "v s \<le> v m + eps * (s - m)" using dl[OF s1 s2] s3 y by simp
  then have "w s \<le> w m" unfolding w_def by (simp add: algebra_simps)
  then have "s \<in> S" unfolding S_def using mxy s1 s3 by auto
  then have "s \<le> m" unfolding m_def by (rule cSup_upper[OF _ Sb])
  with s1 show False by simp
qed

section \<open>Part 3: the memory problem, derivative identity as hypothesis\<close>

subsection \<open>Elementary facts on the phase\<close>

lemma exists_reduced:
  "\<exists>th'\<in>{0..2 * pi}. cos th' = cos th \<and> sin th' = sin th"
proof -
  define n where "n = \<lfloor>th / (2 * pi)\<rfloor>"
  define th' where "th' = th - 2 * pi * of_int n"
  have p: "0 < 2 * pi" by simp
  have "of_int n \<le> th / (2 * pi)" unfolding n_def by (rule of_int_floor_le)
  then have lo: "2 * pi * of_int n \<le> th" using p by (simp add: le_divide_eq mult.commute)
  have "th / (2 * pi) < of_int n + 1" unfolding n_def by (rule floor_correct[THEN conjunct2, simplified])
  then have hi: "th < 2 * pi * (of_int n + 1)" using p by (simp add: divide_less_eq mult.commute)
  have "th' \<in> {0..2 * pi}" unfolding th'_def using lo hi by (auto simp: algebra_simps)
  moreover have "cos th' = cos th" "sin th' = sin th"
    unfolding th'_def by (simp_all add: cos_diff sin_diff)
  ultimately show ?thesis by blast
qed

lemma max_deriv_01:
  fixes phi :: "real \<Rightarrow> real"
  assumes der: "(phi has_real_derivative d) (at u within {0..1})" and u: "u \<in> {0..1}"
    and mx: "\<And>u'. u' \<in> {0..1} \<Longrightarrow> phi u' \<le> phi u"
  shows "u = 0 \<Longrightarrow> d \<le> 0" and "0 < u \<Longrightarrow> u < 1 \<Longrightarrow> d = 0" and "u = 1 \<Longrightarrow> 0 \<le> d"
proof -
  show "u = 0 \<Longrightarrow> d \<le> 0"
  proof -
    assume u0: "u = 0"
    have "((\<lambda>y. (phi y - phi 0) / (y - 0)) \<longlongrightarrow> d) (at_right (0::real))"
      using der u0 by (simp add: has_field_derivative_iff at_within_Icc_at_right)
    moreover have "eventually (\<lambda>y. (phi y - phi 0) / (y - 0) \<le> 0) (at_right (0::real))"
      unfolding eventually_at_right[OF zero_less_one]
      by (intro exI[where x = 1] conjI) (use mx u0 in \<open>auto simp: divide_nonpos_pos\<close>)
    ultimately show "d \<le> 0" by (rule tendsto_upperbound) simp
  qed
  show "0 < u \<Longrightarrow> u < 1 \<Longrightarrow> d = 0"
  proof -
    assume u1: "0 < u" "u < 1"
    have "u \<in> interior {0..1}" using u1 by (simp add: interior_atLeastAtMost_real)
    then have "at u within {0..1} = at u" by (rule at_within_interior)
    with der have d1: "(phi has_real_derivative d) (at u)" by simp
    show "d = 0"
      by (rule DERIV_local_max[OF d1, of "min u (1 - u)"]) (use u1 mx in \<open>auto simp: abs_less_iff min_less_iff_conj\<close>)
  qed
  show "u = 1 \<Longrightarrow> 0 \<le> d"
  proof -
    assume u1: "u = 1"
    have "((\<lambda>y. (phi y - phi 1) / (y - 1)) \<longlongrightarrow> d) (at_left (1::real))"
      using der u1 by (simp add: has_field_derivative_iff at_within_Icc_at_left)
    moreover have "eventually (\<lambda>y. 0 \<le> (phi y - phi 1) / (y - 1)) (at_left (1::real))"
      unfolding eventually_at_left[OF zero_less_one]
      by (intro exI[where x = 0] conjI) (use mx u1 in \<open>auto simp: divide_nonpos_neg\<close>)
    ultimately show "0 \<le> d" by (rule tendsto_lowerbound) simp
  qed
qed

lemma lift_k:
  assumes "continuous_on ({0..1} \<times> {0..T}) (\<lambda>q. f (fst q) (snd q))"
  shows "continuous_on (({0..1} \<times> {0..2 * pi}) \<times> {0..T}) (\<lambda>p. f (fst (fst p)) (snd p))"
proof -
  have "continuous_on (({0..1} \<times> {0..2 * pi}) \<times> {0..T}) (\<lambda>p. (\<lambda>q. f (fst q) (snd q)) (fst (fst p), snd p))"
    by (rule continuous_on_compose2[OF assms]) (auto intro!: continuous_intros)
  then show ?thesis by simp
qed

lemma lift_t:
  assumes "continuous_on {0..T} f"
  shows "continuous_on (X \<times> {0..T}) (\<lambda>p. f (snd p))"
  by (rule continuous_on_compose2[OF assms]) (auto intro!: continuous_intros)

lemma Re_cnj_pulse: "Re (cnj (Eab_pulse z th) * rho) = z * (Im rho * cos th - Re rho * sin th)"
  by (simp add: Eab_pulse_def algebra_simps)

lemma Eab_pulse_Re: "Re (Eab_pulse z th) = - z * sin th" and Eab_pulse_Im: "Im (Eab_pulse z th) = z * cos th"
  by (simp_all add: Eab_pulse_def)

lemma poly_id1:
  fixes x y s c :: real
  assumes "s ^ 2 + c ^ 2 = 1" and "x * c + y * s = 0"
  shows "- (y * c - x * s) * s = x"
proof -
  have "- (y * c - x * s) * s = x * (s ^ 2 + c ^ 2) - (x * c + y * s) * c"
    by (simp add: algebra_simps power2_eq_square)
  also have "\<dots> = x" using assms by simp
  finally show ?thesis .
qed

lemma poly_id2:
  fixes x y s c :: real
  assumes "s ^ 2 + c ^ 2 = 1" and "x * c + y * s = 0"
  shows "(y * c - x * s) * c = y"
proof -
  have "(y * c - x * s) * c = y * (s ^ 2 + c ^ 2) - (x * c + y * s) * s"
    by (simp add: algebra_simps power2_eq_square)
  also have "\<dots> = y" using assms by simp
  finally show ?thesis .
qed

lemma rho_aligned:
  assumes z: "z \<noteq> 0" and st: "Re rho * cos th + Im rho * sin th = 0"
  shows "rho = of_real ((Im rho * cos th - Re rho * sin th) / z) * Eab_pulse z th"
proof (rule complex_eqI)
  define x where "x = Re rho"
  define y where "y = Im rho"
  have sc: "sin th ^ 2 + cos th ^ 2 = 1" by simp
  have z1: "x * cos th + y * sin th = 0" using st unfolding x_def y_def by simp
  show "Re rho = Re (of_real ((Im rho * cos th - Re rho * sin th) / z) * Eab_pulse z th)"
  proof -
    have "Re (of_real ((y * cos th - x * sin th) / z) * Eab_pulse z th) = - (y * cos th - x * sin th) * sin th"
      using z by (simp add: Eab_pulse_Re field_simps)
    also have "\<dots> = x" by (rule poly_id1[OF sc z1])
    finally show ?thesis unfolding x_def y_def by simp
  qed
  show "Im rho = Im (of_real ((Im rho * cos th - Re rho * sin th) / z) * Eab_pulse z th)"
  proof -
    have "Im (of_real ((y * cos th - x * sin th) / z) * Eab_pulse z th) = (y * cos th - x * sin th) * cos th"
      using z by (simp add: Eab_pulse_Im field_simps)
    also have "\<dots> = y" by (rule poly_id2[OF sc z1])
    finally show ?thesis unfolding x_def y_def by simp
  qed
qed

lemma wmax_norm:
  assumes "0 \<le> G" and "K \<noteq> 0"
  shows "norm (wmax G K) = G"
  using assms by (simp add: wmax_def norm_divide norm_mult)

lemma g_th_exists:
  assumes "norm w = G"
  shows "\<exists>th\<in>{0..2 * pi}. g_th G th = w"
proof (cases "w = 0")
  case True
  then have "G = 0" using assms by simp
  then show ?thesis using True by (intro bexI[of _ 0]) (simp_all add: g_th_def)
next
  case False
  obtain r a where ra: "w = Complex (r * cos a) (r * sin a)"
  proof -
    from polar_Ex[of "Re w" "Im w"] obtain r a where "Re w = r * cos a" "Im w = r * sin a" by blast
    then show ?thesis by (intro that[of r a] complex_eqI) simp_all
  qed
  define a' where "a' = (if 0 \<le> r then a else a + pi)"
  have sq: "(r * cos a)\<^sup>2 + (r * sin a)\<^sup>2 = r\<^sup>2"
    by (simp add: power_mult_distrib flip: distrib_left)
  have nr: "norm w = \<bar>r\<bar>" using ra sq by (simp add: norm_complex_def)
  obtain th where th: "th \<in> {0..2 * pi}" "cos th = cos a'" "sin th = sin a'"
    using exists_reduced[of a'] by blast
  have "w = of_real G * cis th"
  proof (cases "0 \<le> r")
    case True
    then have "G = r" using nr assms by simp
    then show ?thesis using ra True th unfolding a'_def by (intro complex_eqI) simp_all
  next
    case False
    then have "G = - r" using nr assms by simp
    then show ?thesis using ra False th unfolding a'_def by (intro complex_eqI) simp_all
  qed
  then show ?thesis using th(1) by (intro bexI[of _ th]) (simp_all add: g_th_def)
qed

subsection \<open>The locale\<close>

locale pop_data =
  fixes T G gq gm Gam :: real
    and a b :: "real \<Rightarrow> real" and rho g :: "real \<Rightarrow> complex"
    and A B z :: "real \<Rightarrow> real \<Rightarrow> real"
begin

definition Kset :: "(real \<times> real) set" where "Kset = {0..1} \<times> {0..2 * pi}"

text \<open>Index (u, theta) of the reparametrised family: tau = u (T - t); F is tr(E_{tau,theta} R(t)).\<close>
definition Fk :: "real \<times> real \<Rightarrow> real \<Rightarrow> real" where
  "Fk k t = ffun (A (fst k) t) (B (fst k) t) (Eab_pulse (z (fst k) t) (snd k)) (a t) (b t) (rho t)"

definition h0k :: "real \<times> real \<Rightarrow> real \<Rightarrow> real" where
  "h0k k t = h0f gq gm Gam (A (fst k) t) (B (fst k) t) (Eab_pulse (z (fst k) t) (snd k)) (a t) (b t) (rho t)"

definition Kk :: "real \<times> real \<Rightarrow> real \<Rightarrow> complex" where
  "Kk k t = Kf (A (fst k) t) (B (fst k) t) (Eab_pulse (z (fst k) t) (snd k)) (a t) (b t) (rho t)"

text \<open>H_{g_theta} of the active functional (the derivative of F in tau).\<close>
definition Hth :: "real \<times> real \<Rightarrow> real \<Rightarrow> real" where
  "Hth k t = Hfun (h0k k t) (Kk k t) (g_th G (snd k))"

text \<open>The derivative identity of the paper: d/dt F_{u,theta} = H_{g(t)} - u H_{g_theta}.\<close>
definition Dk :: "real \<times> real \<Rightarrow> real \<Rightarrow> real" where
  "Dk k t = Hfun (h0k k t) (Kk k t) (g t) - fst k * Hth k t"

text \<open>The Lyapunov function v(t) = V_{T-t}(R(t)) = max over K of F.  The SUP is over the nonempty compact set Kset
  of a continuous function, so it is attained: this is proved in lemma vmax (not a default value).\<close>
definition vf :: "real \<Rightarrow> real" where "vf t = (SUP k\<in>Kset. Fk k t)"

lemma Fk_formula:
  "Fk (u, th) t = A u t * a t + B u t * b t + 2 * (z u t * (Im (rho t) * cos th - Re (rho t) * sin th))"
  by (simp only: Fk_def ffun_def Re_cnj_pulse fst_conv snd_conv)

end

locale pop_lyapunov = pop_data T G gq gm Gam a b rho g A B z
  for T G gq gm Gam :: real and a b :: "real \<Rightarrow> real" and rho g :: "real \<Rightarrow> complex"
    and A B z :: "real \<Rightarrow> real \<Rightarrow> real" +
  fixes gmin :: real
  assumes T0: "0 \<le> T" and G0: "0 \<le> G"
    and gmin0: "0 < gmin" and gq_ge: "gmin \<le> gq" and gm_ge: "gmin \<le> gm" and Gam_ge: "gmin \<le> Gam"
    and ab_nonneg: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> a t \<and> 0 \<le> b t"
    and AB_nonneg: "\<And>u t. u \<in> {0..1} \<Longrightarrow> t \<in> {0..T} \<Longrightarrow> 0 \<le> A u t \<and> 0 \<le> B u t"
    and g_bound: "\<And>t. t \<in> {0..T} \<Longrightarrow> norm (g t) \<le> G"
    \<comment> \<open>regularity (continuity) of R, g and of the entries of E_{tau,0}: ASSUMED\<close>
    and cont_a: "continuous_on {0..T} a" and cont_b: "continuous_on {0..T} b"
    and cont_rho: "continuous_on {0..T} rho" and cont_g: "continuous_on {0..T} g"
    and cont_A: "continuous_on ({0..1} \<times> {0..T}) (\<lambda>q. A (fst q) (snd q))"
    and cont_B: "continuous_on ({0..1} \<times> {0..T}) (\<lambda>q. B (fst q) (snd q))"
    and cont_z: "continuous_on ({0..1} \<times> {0..T}) (\<lambda>q. z (fst q) (snd q))"
    \<comment> \<open>E_{0,theta} is the projector on b: at u = 0 (tau = 0) and at t = T (tau = 0)\<close>
    and E_start: "\<And>t. t \<in> {0..T} \<Longrightarrow> A 0 t = 0 \<and> B 0 t = 1 \<and> z 0 t = 0"
    and E_end: "\<And>u. u \<in> {0..1} \<Longrightarrow> A u T = 0 \<and> B u T = 1 \<and> z u T = 0"
    \<comment> \<open>non-degeneracy: R(t) <> 0, h > 0 give V_h(R) > 0\<close>
    and v_pos: "\<And>t. t \<in> {0..T} \<Longrightarrow> t < T \<Longrightarrow> 0 < vf t"
    \<comment> \<open>THE DERIVATIVE IDENTITY (hypothesis): in t and in tau = u (T - t)\<close>
    and der_t: "\<And>k t. k \<in> Kset \<Longrightarrow> t \<in> {0..T} \<Longrightarrow> (Fk k has_real_derivative Dk k t) (at t within {0..T})"
    and der_u: "\<And>u th t. (u, th) \<in> Kset \<Longrightarrow> t \<in> {0..T} \<Longrightarrow> t < T \<Longrightarrow>
        ((\<lambda>u'. Fk (u', th) t) has_real_derivative ((T - t) * Hth (u, th) t)) (at u within {0..1})"
begin

lemma compact_Kset: "compact Kset" unfolding Kset_def by (intro compact_Times compact_Icc)

lemma Fk_cont: "continuous_on (Kset \<times> {0..T}) (\<lambda>p. Fk (fst p) (snd p))"
proof -
  have cA': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. A (fst (fst p)) (snd p))" unfolding Kset_def by (rule lift_k[OF cont_A])
  have cB': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. B (fst (fst p)) (snd p))" unfolding Kset_def by (rule lift_k[OF cont_B])
  have cz': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. z (fst (fst p)) (snd p))" unfolding Kset_def by (rule lift_k[OF cont_z])
  have ca': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. a (snd p))" by (rule lift_t[OF cont_a])
  have cb': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. b (snd p))" by (rule lift_t[OF cont_b])
  have cr': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. rho (snd p))" by (rule lift_t[OF cont_rho])
  show ?thesis
    by (simp add: Fk_def ffun_def Eab_pulse_def, intro continuous_intros cA' cB' cz' ca' cb' cr')
qed

lemma Dk_cont: "continuous_on (Kset \<times> {0..T}) (\<lambda>p. Dk (fst p) (snd p))"
proof -
  have cA': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. A (fst (fst p)) (snd p))" unfolding Kset_def by (rule lift_k[OF cont_A])
  have cB': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. B (fst (fst p)) (snd p))" unfolding Kset_def by (rule lift_k[OF cont_B])
  have cz': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. z (fst (fst p)) (snd p))" unfolding Kset_def by (rule lift_k[OF cont_z])
  have ca': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. a (snd p))" by (rule lift_t[OF cont_a])
  have cb': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. b (snd p))" by (rule lift_t[OF cont_b])
  have cr': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. rho (snd p))" by (rule lift_t[OF cont_rho])
  have cg': "continuous_on (Kset \<times> {0..T}) (\<lambda>p. g (snd p))" by (rule lift_t[OF cont_g])
  show ?thesis
    by (simp add: Dk_def Hth_def h0k_def Kk_def Hfun_def h0f_def Kf_def g_th_def Eab_pulse_def,
        intro continuous_intros cA' cB' cz' ca' cb' cr' cg')
qed

lemma vmax:
  assumes t: "t \<in> {0..T}"
  shows "(\<forall>k\<in>Kset. Fk k t \<le> vf t) \<and> (\<exists>k\<in>Kset. Fk k t = vf t)"
proof -
  have cK: "continuous_on Kset (\<lambda>k. Fk k t)"
  proof -
    have "continuous_on Kset (\<lambda>k. (\<lambda>p. Fk (fst p) (snd p)) (k, t))"
      by (rule continuous_on_compose2[OF Fk_cont]) (use t in \<open>auto intro!: continuous_intros\<close>)
    then show ?thesis by simp
  qed
  have ne: "Kset \<noteq> {}" unfolding Kset_def using pi_gt_zero by auto
  obtain x where x: "x \<in> Kset" "\<And>y. y \<in> Kset \<Longrightarrow> Fk y t \<le> Fk x t"
    using continuous_attains_sup[OF compact_Kset ne cK] by blast
  have bd: "bdd_above ((\<lambda>k. Fk k t) ` Kset)" by (rule bdd_aboveI[of _ "Fk x t"]) (use x(2) in auto)
  have "vf t = Fk x t" unfolding vf_def
    by (intro antisym cSUP_least[OF ne] cSUP_upper[OF x(1) bd]) (use x(2) in auto)
  then show ?thesis using x by auto
qed

lemma vf_cont: "continuous_on {0..T} vf"
  by (rule max_continuous[OF compact_Kset Fk_cont vmax])

lemma u_conditions:
  assumes k: "(u, th) \<in> Kset" and t: "t \<in> {0..T}" "t < T" and act: "Fk (u, th) t = vf t"
  shows "u = 0 \<Longrightarrow> Hth (u, th) t \<le> 0" and "0 < u \<Longrightarrow> u < 1 \<Longrightarrow> Hth (u, th) t = 0"
    and "u = 1 \<Longrightarrow> 0 \<le> Hth (u, th) t"
proof -
  have u: "u \<in> {0..1}" and th: "th \<in> {0..2 * pi}" using k unfolding Kset_def by auto
  have mx: "\<And>u'. u' \<in> {0..1} \<Longrightarrow> Fk (u', th) t \<le> Fk (u, th) t"
    using vmax[OF t(1)] act th unfolding Kset_def by auto
  note md = max_deriv_01[OF der_u[OF k t] u mx]
  have Tt: "0 < T - t" using t(2) by simp
  show "u = 0 \<Longrightarrow> Hth (u, th) t \<le> 0" using md(1) Tt by (simp add: mult_le_0_iff not_less)
  show "0 < u \<Longrightarrow> u < 1 \<Longrightarrow> Hth (u, th) t = 0" using md(2) Tt by simp
  show "u = 1 \<Longrightarrow> 0 \<le> Hth (u, th) t" using md(3) Tt by (simp add: zero_le_mult_iff not_less)
qed

subsection \<open>The active functional: cases (iii), (iv), (i)-(ii) of the paper\<close>

lemma act_all_theta:
  assumes k: "(u, th) \<in> Kset" and t: "t \<in> {0..T}" and act: "Fk (u, th) t = vf t"
  shows "Fk (u, th') t \<le> Fk (u, th) t"
proof -
  obtain th'' where th'': "th'' \<in> {0..2 * pi}" "cos th'' = cos th'" "sin th'' = sin th'"
    using exists_reduced[of th'] by blast
  have u: "u \<in> {0..1}" using k unfolding Kset_def by auto
  have "(u, th'') \<in> Kset" unfolding Kset_def using u th''(1) by simp
  then have "Fk (u, th'') t \<le> vf t" using vmax[OF t] by blast
  moreover have "Fk (u, th') t = Fk (u, th'') t" by (simp add: Fk_formula th'')
  ultimately show ?thesis using act by simp
qed

lemma case_u0:
  assumes t: "t \<in> {0..T}" "t < T" and th: "th \<in> {0..2 * pi}" and act: "Fk (0, th) t = vf t"
  shows "Dk (0, th) t \<le> 0"
proof -
  have e: "A 0 t = 0" "B 0 t = 1" "z 0 t = 0" using E_start[OF t(1)] by simp_all
  have Fk0: "\<And>th'. Fk (0, th') t = b t" by (simp add: Fk_formula e)
  have ex: "\<And>th'. th' \<in> {0..2 * pi} \<Longrightarrow> Hth (0, th') t \<le> 0"
  proof -
    fix th' assume th': "th' \<in> {0..2 * pi}"
    have k': "(0, th') \<in> Kset" unfolding Kset_def using th' by simp
    have "Fk (0, th') t = vf t" using Fk0 act by simp
    from u_conditions(1)[OF k' t this] show "Hth (0, th') t \<le> 0" by simp
  qed
  have Hth0: "\<And>th'. Hth (0, th') t =
      Hfun (h0f gq gm Gam 0 1 0 (a t) (b t) (rho t)) (Kf 0 1 0 (a t) (b t) (rho t)) (g_th G th')"
    by (simp add: Hth_def h0k_def Kk_def e Eab_pulse_def)
  have hh: "h0f gq gm Gam 0 1 0 (a t) (b t) (rho t) = - gm * b t" by (simp add: h0f_def)
  have KK: "Kf 0 1 0 (a t) (b t) (rho t) = rho t" by (simp add: Kf_def)
  have bnn: "0 \<le> b t" using ab_nonneg[OF t(1)] by simp
  have gmnn: "0 \<le> gm" using gm_ge gmin0 by simp
  have cond: "- gm * b t + 2 * G * norm (rho t) \<le> 0"
  proof (cases "rho t = 0")
    case True
    have "0 \<le> gm * b t" using gmnn bnn by (rule mult_nonneg_nonneg)
    then show ?thesis using True by simp
  next
    case False
    obtain th' where th': "th' \<in> {0..2 * pi}" "g_th G th' = wmax G (rho t)"
      using g_th_exists[where w = "wmax G (rho t)" and G = G] wmax_norm[OF G0 False] by blast
    have "Hth (0, th') t \<le> 0" by (rule ex[OF th'(1)])
    then have "Hfun (- gm * b t) (rho t) (wmax G (rho t)) \<le> 0"
      using Hth0[of th'] hh KK th'(2) by simp
    moreover have "Hfun (- gm * b t) (rho t) (wmax G (rho t)) = - gm * b t + 2 * G * norm (rho t)"
      by (rule H_max_attained(2)[OF G0])
    ultimately show ?thesis by simp
  qed
  have "Hfun (h0f gq gm Gam 0 1 0 (a t) (b t) (rho t)) (Kf 0 1 0 (a t) (b t) (rho t)) (g t) \<le> 0"
    by (rule case_iv_nonpos[where w = "g t" and G = G and gq = gq and gm = gm and Gam = Gam and a = "a t"
        and b = "b t" and rho = "rho t"]) (use g_bound[OF t(1)] cond in simp_all)
  then show ?thesis by (simp add: Dk_def h0k_def Kk_def e Eab_pulse_def)
qed

lemma case_z0:
  assumes t: "t \<in> {0..T}" "t < T" and k: "(u, th) \<in> Kset" and act: "Fk (u, th) t = vf t"
    and u0: "0 < u" and z0: "z u t = 0"
  shows False
proof -
  have uu: "u \<in> {0..1}" using k unfolding Kset_def by auto
  have Fz: "\<And>th'. Fk (u, th') t = A u t * a t + B u t * b t" by (simp add: Fk_formula z0)
  have ex: "\<And>th'. th' \<in> {0..2 * pi} \<Longrightarrow> 0 \<le> Hth (u, th') t"
  proof -
    fix th' assume th': "th' \<in> {0..2 * pi}"
    have k': "(u, th') \<in> Kset" unfolding Kset_def using th' uu by simp
    have a': "Fk (u, th') t = vf t" using Fz act by simp
    show "0 \<le> Hth (u, th') t"
    proof (cases "u < 1")
      case True then show ?thesis using u_conditions(2)[OF k' t a' u0 True] by simp
    next
      case False then have "u = 1" using uu by simp
      then show ?thesis using u_conditions(3)[OF k' t a'] by simp
    qed
  qed
  define h where "h = h0f gq gm Gam (A u t) (B u t) 0 (a t) (b t) (rho t)"
  define K where "K = Kf (A u t) (B u t) 0 (a t) (b t) (rho t)"
  have Hth0: "\<And>th'. Hth (u, th') t = Hfun h K (g_th G th')"
    by (simp add: Hth_def h0k_def Kk_def h_def K_def z0 Eab_pulse_def)
  have AB: "0 \<le> A u t" "0 \<le> B u t" using AB_nonneg[OF uu t(1)] by simp_all
  have ab: "0 \<le> a t" "0 \<le> b t" using ab_nonneg[OF t(1)] by simp_all
  have fpos: "0 < ffun (A u t) (B u t) 0 (a t) (b t) (rho t)"
    using v_pos[OF t] act by (simp add: Fk_def z0 Eab_pulse_def)
  have "h < 0" unfolding h_def
    by (rule h0_negative[where gmin = gmin and gq = gq and gm = gm and Gam = Gam and A = "A u t" and B = "B u t"
        and Eab = 0 and a = "a t" and b = "b t" and rho = "rho t"])
       (use gmin0 gq_ge gm_ge Gam_ge AB ab fpos in simp_all)
  have "\<exists>th'\<in>{0..2 * pi}. Hfun h K (g_th G th') < 0" by (rule case_iii[OF \<open>h < 0\<close>])
  then obtain th' where th': "th' \<in> {0..2 * pi}" "Hfun h K (g_th G th') < 0" by blast
  then show False using ex[OF th'(1)] Hth0[of th'] by simp
qed

lemma case_zne:
  assumes t: "t \<in> {0..T}" "t < T" and k: "(u, th) \<in> Kset" and act: "Fk (u, th) t = vf t"
    and u0: "0 < u" and z0: "z u t \<noteq> 0"
  shows "Dk (u, th) t \<le> 0"
proof -
  have uu: "u \<in> {0..1}" using k unfolding Kset_def by auto
  define x where "x = Re (rho t)"
  define y where "y = Im (rho t)"
  define E where "E = Eab_pulse (z u t) th"
  have allth: "\<And>th'. Fk (u, th') t \<le> Fk (u, th) t" by (rule act_all_theta[OF k t(1) act])
  have Fform: "\<And>th'. Fk (u, th') t = A u t * a t + B u t * b t + 2 * (z u t * (y * cos th' - x * sin th'))"
    by (simp add: Fk_formula x_def y_def)
  \<comment> \<open>sign: Re(conj E rho) >= 0 (maximality over the phase, compare theta + pi)\<close>
  have P: "0 \<le> Re (cnj E * rho t)"
  proof -
    have "Fk (u, th + pi) t \<le> Fk (u, th) t" by (rule allth)
    then have "A u t * a t + B u t * b t + 2 * (z u t * (y * cos (th + pi) - x * sin (th + pi)))
        \<le> A u t * a t + B u t * b t + 2 * (z u t * (y * cos th - x * sin th))" using Fform by simp
    then have "0 \<le> z u t * (y * cos th - x * sin th)"
      by (simp add: algebra_simps)
    moreover have "Re (cnj E * rho t) = z u t * (y * cos th - x * sin th)"
      unfolding E_def x_def y_def by (rule Re_cnj_pulse)
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>stationarity in the phase\<close>
  have stat: "Re (rho t) * cos th + Im (rho t) * sin th = 0"
  proof -
    let ?f = "\<lambda>th'. A u t * a t + B u t * b t + 2 * (z u t * (y * cos th' - x * sin th'))"
    have d: "(?f has_real_derivative 2 * (z u t * (y * (- sin th) - x * cos th))) (at th)"
      by (rule derivative_eq_intros refl | simp)+
    have "2 * (z u t * (y * (- sin th) - x * cos th)) = 0"
      by (rule DERIV_local_max[OF d zero_less_one]) (use allth Fform in auto)
    then have "z u t * (x * cos th + y * sin th) = 0"
    proof -
      assume h0: "2 * (z u t * (y * (- sin th) - x * cos th)) = 0"
      have "z u t * (x * cos th + y * sin th) = - (1 / 2) * (2 * (z u t * (y * (- sin th) - x * cos th)))"
        by (simp add: algebra_simps)
      then show ?thesis using h0 by simp
    qed
    then show ?thesis using z0 by (simp add: x_def y_def)
  qed
  have rhoE: "rho t = of_real ((Im (rho t) * cos th - Re (rho t) * sin th) / z u t) * E"
    unfolding E_def by (rule rho_aligned[OF z0 stat])
  obtain c0 where c0: "rho t = of_real c0 * E" using rhoE by blast
  have Kal: "Kk (u, th) t = of_real ((a t - b t) + c0 * (B u t - A u t)) * Eab_pulse (z u t) th"
  proof -
    have "Kk (u, th) t = E * of_real (a t - b t) + rho t * of_real (B u t - A u t)"
      by (simp add: Kk_def Kf_def E_def)
    also have "\<dots> = of_real ((a t - b t) + c0 * (B u t - A u t)) * E"
      by (subst c0) (simp add: algebra_simps)
    finally show ?thesis by (simp add: E_def)
  qed
  have AB: "0 \<le> A u t" "0 \<le> B u t" using AB_nonneg[OF uu t(1)] by simp_all
  have ab: "0 \<le> a t" "0 \<le> b t" using ab_nonneg[OF t(1)] by simp_all
  have fpos: "0 < ffun (A u t) (B u t) E (a t) (b t) (rho t)"
    using v_pos[OF t] act by (simp add: Fk_def E_def)
  have hneg0: "h0f gq gm Gam (A u t) (B u t) E (a t) (b t) (rho t) < 0"
    by (rule h0_negative[where gmin = gmin and gq = gq and gm = gm and Gam = Gam and A = "A u t" and B = "B u t"
        and Eab = E and a = "a t" and b = "b t" and rho = "rho t"])
       (use gmin0 gq_ge gm_ge Gam_ge AB ab P fpos in simp_all)
  have hneg: "h0k (u, th) t < 0" using hneg0 by (simp add: h0k_def E_def)
  have gt: "norm (g t) \<le> G" by (rule g_bound[OF t(1)])
  show ?thesis
  proof (cases "u < 1")
    case True
    have H0: "Hfun (h0k (u, th) t) (Kk (u, th) t) (g_th G th) = 0"
      using u_conditions(2)[OF k t act u0 True] by (simp add: Hth_def)
    have "Hfun (h0k (u, th) t) (Kk (u, th) t) (g t) \<le> 0"
      by (rule case_i(2)[OF Kal G0 hneg H0 gt])
    then show ?thesis using u_conditions(2)[OF k t act u0 True] by (simp add: Dk_def)
  next
    case False
    then have u1: "u = 1" using uu by simp
    have H0: "0 \<le> Hfun (h0k (u, th) t) (Kk (u, th) t) (g_th G th)"
      using u_conditions(3)[OF k t act u1] by (simp add: Hth_def)
    have "Hfun (h0k (u, th) t) (Kk (u, th) t) (g t) \<le> Hfun (h0k (u, th) t) (Kk (u, th) t) (g_th G th)"
      by (rule case_ii(2)[OF Kal G0 hneg H0 gt])
    then show ?thesis using u1 by (simp add: Dk_def Hth_def)
  qed
qed

theorem active_nonpos:
  assumes t: "t \<in> {0..T}" "t < T" and k: "k \<in> Kset" and act: "Fk k t = vf t"
  shows "Dk k t \<le> 0"
proof -
  obtain u th where kk: "k = (u, th)" by (cases k)
  have uu: "u \<in> {0..1}" and th: "th \<in> {0..2 * pi}" using k kk unfolding Kset_def by auto
  show ?thesis
  proof (cases "u = 0")
    case True then show ?thesis using case_u0[OF t th] act kk by simp
  next
    case False
    then have u0: "0 < u" using uu by simp
    show ?thesis
    proof (cases "z u t = 0")
      case True then show ?thesis using case_z0[OF t _ _ u0 True] k kk act by blast
    next
      case False then show ?thesis using case_zne[OF t _ _ u0 False] k kk act by blast
    qed
  qed
qed

subsection \<open>The Lyapunov step\<close>

theorem vf_dini:
  assumes t: "t \<in> {0..T}" "t < T" and eps: "0 < eps"
  shows "\<exists>delta>0. \<forall>s. t < s \<longrightarrow> s < t + delta \<longrightarrow> s \<le> T \<longrightarrow> vf s \<le> vf t + eps * (s - t)"
proof -
  have "\<exists>delta>0. \<forall>s. t < s \<longrightarrow> s < t + delta \<longrightarrow> s \<le> T \<longrightarrow> vf s \<le> vf t + (0 + eps) * (s - t)"
    by (rule dini_danskin[where K = Kset and F = Fk and H = Dk and a = 0 and b = T and c = 0,
        OF compact_Kset Fk_cont Dk_cont der_t vmax t(1) active_nonpos[OF t] eps])
       (use t in auto)
  then show ?thesis by simp
qed

theorem v_antitone:
  assumes "0 \<le> s" and "s \<le> t" and "t \<le> T"
  shows "vf t \<le> vf s"
  by (rule dini_monotone[where a = 0 and b = T and x = s and y = t, OF vf_cont _ assms(1,2,3)])
     (use vf_dini in auto)

theorem pb_bound: "b T \<le> vf 0"
proof -
  have "\<exists>k\<in>Kset. Fk k T = vf T" using vmax[of T] T0 by auto
  then obtain u th where "Fk (u, th) T = vf T" "u \<in> {0..1}" unfolding Kset_def by auto
  then have vT: "vf T = b T" using E_end by (simp add: Fk_formula)
  have "b T = (\<lambda>h (x::real). vf (T - h)) 0 ((\<lambda>t. t) T)" using vT by simp
  show ?thesis
    by (rule lyapunov_conclusion[where V = "\<lambda>h (x::real). vf (T - h)" and R = "\<lambda>t. t" and pb = "b T"
        and M = "vf 0" and T = T])
       (use vT v_antitone T0 in simp_all)
qed

end

end

