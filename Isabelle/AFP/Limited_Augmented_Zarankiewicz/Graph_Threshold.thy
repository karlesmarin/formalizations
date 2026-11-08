(*  Title:      Graph_Threshold.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Graph_Threshold
  imports "HOL-Analysis.Analysis"
begin

text \<open>The critical threshold of a graphical simple game. For a graph on k vertices there is a
fractional vertex cover whose weight on every independent set is at most the integer part of
k squared over four, divided by k. This is Hof, Theorem 7.2 of his thesis, and footnote 7 of
Hof, Kern, Kurz and Paulusma, SAGT 2018. The proof is the minimal norm argument. The point
of minimal Euclidean norm of the closed convex set of fractional vertex covers exists by the
closest point theorem of HOL-Analysis. Its variational inequality bounds the weight of an
independent set by k over four minus the squared distance to the constant one half vector.
For odd k, the levels of the minimal point are analysed: at each level c the number of
vertices with value one half plus c and with value one half minus c are balanced by the
variational inequality, which forces the squared distance to be at least one over four k
unless the minimal point is the constant one half vector.\<close>

section \<open>Definitions\<close>

definition fcover :: "('n \<Rightarrow> 'n \<Rightarrow> bool) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "fcover E p \<longleftrightarrow> (\<forall>v. 0 \<le> p $ v) \<and> (\<forall>u v. E u v \<longrightarrow> 1 \<le> p $ u + p $ v)"

definition indep :: "('n \<Rightarrow> 'n \<Rightarrow> bool) \<Rightarrow> 'n set \<Rightarrow> bool" where
  "indep E I \<longleftrightarrow> (\<forall>u\<in>I. \<forall>v\<in>I. \<not> E u v)"

definition sqn :: "real^'n \<Rightarrow> real" where
  "sqn p = (\<Sum>v\<in>UNIV. (p $ v)\<^sup>2)"

definition minimal :: "('n::finite \<Rightarrow> 'n \<Rightarrow> bool) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "minimal E p \<longleftrightarrow> fcover E p \<and> (\<forall>q. fcover E q \<longrightarrow> sqn p \<le> sqn q)"

text \<open>Symmetry and absence of loops are not needed by the proof, so the theorems hold for any
edge relation. The statements for graphs follow by specialisation.\<close>

section \<open>Small helper lemmas\<close>

lemma sum_ind:
  fixes a :: real
  shows "(\<Sum>v\<in>(UNIV::'n::finite set). if P v then a else 0) = real (card {v. P v}) * a"
proof -
  have "(\<Sum>v\<in>(UNIV::'n set) \<inter> {v. P v}. a) = (\<Sum>v\<in>UNIV. if v \<in> {v. P v} then a else 0)"
    by (rule sum.inter_restrict) simp
  then show ?thesis by simp
qed

lemma sum_mem:
  fixes f :: "'n::finite \<Rightarrow> real"
  shows "(\<Sum>v\<in>UNIV. if v \<in> I then f v else 0) = (\<Sum>v\<in>I. f v)"
proof -
  have "(\<Sum>v\<in>(UNIV::'n set) \<inter> I. f v) = (\<Sum>v\<in>UNIV. if v \<in> I then f v else 0)"
    by (rule sum.inter_restrict) simp
  then show ?thesis by simp
qed

lemma card_pos: "0 < CARD('n::finite)"
  by (simp add: card_gt_0_iff)

lemma finite_min_pos:
  fixes f :: "'a \<Rightarrow> real"
  assumes "finite X" "\<forall>x\<in>X. 0 < f x"
  shows "\<exists>e>0. \<forall>x\<in>X. e \<le> f x"
  using assms
proof (induction X)
  case empty
  then show ?case by (intro exI[where x = 1]) auto
next
  case (insert x F)
  then obtain e where e: "0 < e" "\<forall>y\<in>F. e \<le> f y" by auto
  have fx: "0 < f x" using insert by auto
  show ?case
  proof (intro exI[where x = "min e (f x)"] conjI ballI)
    show "0 < min e (f x)" using e fx by simp
    fix y assume "y \<in> insert x F"
    then show "min e (f x) \<le> f y"
    proof
      assume "y = x"
      then show ?thesis by simp
    next
      assume "y \<in> F"
      then show ?thesis using e by (meson min.cobounded1 order_trans)
    qed
  qed
qed

section \<open>The minimal point\<close>

lemma sqn_norm: "sqn p = (norm p)\<^sup>2"
proof -
  have "sqn p = inner p p" by (simp add: sqn_def inner_vec_def power2_eq_square)
  then show ?thesis by (simp add: power2_norm_eq_inner)
qed

lemma closed_fcover: "closed {p::real^'n::finite. fcover E p}"
proof -
  have eq: "{p::real^'n. fcover E p} =
      (\<Inter>v. {p. 0 \<le> p $ v}) \<inter> (\<Inter>u. \<Inter>v\<in>{v. E u v}. {p. 1 \<le> p $ u + p $ v})"
    by (auto simp: fcover_def)
  have "closed ((\<Inter>v. {p::real^'n. 0 \<le> p $ v}) \<inter>
      (\<Inter>u. \<Inter>v\<in>{v. E u v}. {p. 1 \<le> p $ u + p $ v}))"
    by (auto intro!: closed_Int closed_INT closed_Collect_le continuous_intros)
  then show ?thesis using eq by simp
qed

lemma exists_minimal: "\<exists>p. minimal E (p::real^'n::finite)"
proof -
  let ?Q = "{p::real^'n. fcover E p}"
  have ne: "?Q \<noteq> {}"
  proof -
    have "fcover E (\<chi> v. 1)" by (simp add: fcover_def)
    then show ?thesis by auto
  qed
  obtain p where p: "p \<in> ?Q" "\<forall>y\<in>?Q. dist 0 p \<le> dist 0 y"
    using closest_point_exists[OF closed_fcover ne, where a = 0] by blast
  have "minimal E p"
    unfolding minimal_def
  proof (intro conjI allI impI)
    show "fcover E p" using p by simp
    fix q assume q: "fcover E q"
    then have "norm p \<le> norm q" using p by (simp add: dist_norm)
    then have "(norm p)\<^sup>2 \<le> (norm q)\<^sup>2" by (simp add: power_mono)
    then show "sqn p \<le> sqn q" by (simp add: sqn_norm)
  qed
  then show ?thesis by blast
qed

lemma fcover_segment:
  assumes "fcover E p" "fcover E q" "0 \<le> t" "t \<le> 1"
  shows "fcover E (p + t *\<^sub>R (q - p))"
  unfolding fcover_def
proof (intro conjI allI impI)
  fix v
  have "0 \<le> (1 - t) * p $ v + t * q $ v"
    using assms by (auto simp: fcover_def intro!: add_nonneg_nonneg mult_nonneg_nonneg)
  then show "0 \<le> (p + t *\<^sub>R (q - p)) $ v" by (simp add: algebra_simps)
next
  fix u v assume e: "E u v"
  have a: "1 \<le> p $ u + p $ v" and b: "1 \<le> q $ u + q $ v"
    using assms e by (auto simp: fcover_def)
  have "(1 - t) * 1 \<le> (1 - t) * (p $ u + p $ v)"
    using a assms(4) by (intro mult_left_mono) auto
  moreover have "t * 1 \<le> t * (q $ u + q $ v)"
    using b assms(3) by (intro mult_left_mono) auto
  ultimately show "1 \<le> (p + t *\<^sub>R (q - p)) $ u + (p + t *\<^sub>R (q - p)) $ v"
    by (simp add: algebra_simps)
qed

lemma sqn_segment:
  fixes p q :: "real^'n::finite"
  shows "sqn (p + t *\<^sub>R (q - p)) = sqn p + 2 * t * (\<Sum>v\<in>UNIV. p $ v * (q $ v - p $ v))
      + t\<^sup>2 * (\<Sum>v\<in>UNIV. (q $ v - p $ v)\<^sup>2)"
proof -
  have pt: "\<And>v. (p $ v + t * (q $ v - p $ v))\<^sup>2 =
      (p $ v)\<^sup>2 + 2 * t * (p $ v * (q $ v - p $ v)) + t\<^sup>2 * (q $ v - p $ v)\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  show ?thesis
    unfolding sqn_def
    by (simp add: pt sum.distrib sum_distrib_left)
qed

lemma variational:
  fixes p q :: "real^'n::finite"
  assumes m: "minimal E p" and q: "fcover E q"
  shows "0 \<le> (\<Sum>v\<in>UNIV. p $ v * (q $ v - p $ v))"
proof (rule ccontr)
  define S where "S = (\<Sum>v\<in>UNIV. p $ v * (q $ v - p $ v))"
  define N where "N = (\<Sum>v\<in>UNIV. (q $ v - p $ v)\<^sup>2)"
  assume "\<not> 0 \<le> (\<Sum>v\<in>UNIV. p $ v * (q $ v - p $ v))"
  then have S: "S < 0" by (simp add: S_def)
  have N: "0 \<le> N" by (simp add: N_def sum_nonneg)
  define t where "t = min 1 (- S / (N + 1))"
  have qpos: "0 < - S / (N + 1)" using S N by (intro divide_pos_pos) auto
  have tpos: "0 < t" using qpos by (simp add: t_def)
  have t1: "t \<le> 1" by (simp add: t_def)
  have tS: "t * (N + 1) \<le> - S"
  proof -
    have th: "t \<le> - S / (N + 1)" by (simp add: t_def)
    have n1: "0 < N + 1" using N by simp
    have "t * (N + 1) \<le> (- S / (N + 1)) * (N + 1)" by (rule mult_right_mono[OF th]) (use n1 in simp)
    moreover have "(- S / (N + 1)) * (N + 1) = - S" using n1 by (simp add: field_simps)
    ultimately show ?thesis by simp
  qed
  have cov: "fcover E (p + t *\<^sub>R (q - p))"
    using fcover_segment[OF _ q tpos[THEN less_imp_le] t1] m by (simp add: minimal_def)
  have "sqn p \<le> sqn (p + t *\<^sub>R (q - p))" using m cov by (simp add: minimal_def)
  then have "0 \<le> 2 * t * S + t\<^sup>2 * N"
    by (simp add: sqn_segment S_def N_def)
  moreover have "2 * t * S + t\<^sup>2 * N = t * (2 * S + t * N)"
    by (simp add: power2_eq_square algebra_simps)
  ultimately have "0 \<le> t * (2 * S + t * N)" by simp
  then have h: "0 \<le> 2 * S + t * N" using tpos by (simp add: zero_le_mult_iff)
  have "t * N \<le> t * (N + 1)" using tpos by (simp add: algebra_simps)
  then show False using h tS S by linarith
qed

section \<open>The basic bound on an independent set\<close>

lemma dev_expand:
  fixes p :: "real^'n::finite"
  shows "(\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2) =
      (\<Sum>v\<in>UNIV. (p $ v)\<^sup>2) - (\<Sum>v\<in>UNIV. p $ v) + real CARD('n) / 4"
proof -
  have "\<And>v. (p $ v - 1/2)\<^sup>2 = ((p $ v)\<^sup>2 - p $ v) + 1/4"
    by (simp add: power2_eq_square algebra_simps)
  then show ?thesis by (simp add: sum.distrib sum_subtractf)
qed

lemma indep_bound:
  fixes p :: "real^'n::finite"
  assumes m: "minimal E p" and I: "indep E I"
  shows "(\<Sum>v\<in>I. p $ v) \<le> real CARD('n) / 4 - (\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2)"
proof -
  define q :: "real^'n" where "q = (\<chi> v. if v \<in> I then 0 else 1)"
  have qv: "\<And>v. q $ v = (if v \<in> I then 0 else 1)" by (simp add: q_def)
  have cq: "fcover E q"
    unfolding fcover_def
  proof (intro conjI allI impI)
    fix v show "0 \<le> q $ v" by (simp add: qv)
  next
    fix u v assume e: "E u v"
    then have "u \<notin> I \<or> v \<notin> I" using I by (auto simp: indep_def)
    then show "1 \<le> q $ u + q $ v" by (auto simp: qv)
  qed
  have var: "0 \<le> (\<Sum>v\<in>UNIV. p $ v * (q $ v - p $ v))" by (rule variational[OF m cq])
  have pt: "\<And>v. p $ v * (q $ v - p $ v) =
      (p $ v - (p $ v)\<^sup>2) - (if v \<in> I then p $ v else 0)"
    by (simp add: qv power2_eq_square algebra_simps)
  have "(\<Sum>v\<in>UNIV. p $ v * (q $ v - p $ v)) =
      (\<Sum>v\<in>UNIV. p $ v) - (\<Sum>v\<in>UNIV. (p $ v)\<^sup>2) - (\<Sum>v\<in>I. p $ v)"
    by (simp add: pt sum_subtractf sum_mem[where f = "\<lambda>v. p $ v"])
  then show ?thesis using var by (simp add: dev_expand)
qed

section \<open>Levels of the minimal point\<close>

lemma level_balance:
  fixes p :: "real^'n::finite"
  assumes m: "minimal E p" and pos: "\<forall>v. 0 < p $ v" and c: "0 < c"
  shows "real (card {v. p $ v - 1/2 = c}) * (1/2 + c)
      = real (card {v. p $ v - 1/2 = -c}) * (1/2 - c)"
proof -
  define w :: "'n \<Rightarrow> real" where
    "w = (\<lambda>v. if p $ v - 1/2 = c then 1 else if p $ v - 1/2 = -c then -1 else 0)"
  have wb: "\<And>v. w v = 1 \<or> w v = -1 \<or> w v = 0" by (simp add: w_def)
  obtain e1 where e1: "0 < e1" "\<forall>v. e1 \<le> p $ v"
    using finite_min_pos[where X = "UNIV::'n set" and f = "\<lambda>v. p $ v"] pos by auto
  define X2 where "X2 = {(u, v). E u v \<and> 1 < p $ u + p $ v}"
  obtain e2 where e2: "0 < e2" "\<forall>x\<in>X2. e2 \<le> p $ (fst x) + p $ (snd x) - 1"
    using finite_min_pos[where X = X2 and f = "\<lambda>x. p $ (fst x) + p $ (snd x) - 1"]
    by (auto simp: X2_def)
  define e where "e = min e1 (e2 / 2)"
  have epos: "0 < e" using e1 e2 by (simp add: e_def)
  have ele1: "e \<le> e1" by (simp add: e_def)
  have ele2: "2 * e \<le> e2" by (simp add: e_def)
  have tight: "\<And>u v. p $ u + p $ v = 1 \<Longrightarrow> w u + w v = 0"
    using c by (auto simp: w_def)
  have feas: "\<And>s. \<bar>s\<bar> \<le> e \<Longrightarrow> fcover E (\<chi> v. p $ v + s * w v)"
  proof -
    fix s assume s: "\<bar>s\<bar> \<le> e"
    show "fcover E (\<chi> v. p $ v + s * w v)"
      unfolding fcover_def
    proof (intro conjI allI impI)
      fix v
      have "\<bar>s * w v\<bar> \<le> e" using s wb[of v] by auto
      then have "- e \<le> s * w v" by linarith
      moreover have "e \<le> p $ v" using ele1 e1 by (meson order_trans)
      ultimately show "0 \<le> (\<chi> v. p $ v + s * w v) $ v" by simp
    next
      fix u v assume E: "E u v"
      have ge1: "1 \<le> p $ u + p $ v" using m E by (simp add: minimal_def fcover_def)
      show "1 \<le> (\<chi> v. p $ v + s * w v) $ u + (\<chi> v. p $ v + s * w v) $ v"
      proof (cases "p $ u + p $ v = 1")
        case True
        then have "w u + w v = 0" by (rule tight)
        have z: "s * w u + s * w v = 0"
        proof -
          have "s * w u + s * w v = s * (w u + w v)" by (simp add: algebra_simps)
          also have "\<dots> = 0" using \<open>w u + w v = 0\<close> by simp
          finally show ?thesis .
        qed
        show ?thesis using True z by simp
      next
        case False
        then have gt: "1 < p $ u + p $ v" using ge1 by simp
        then have "(u, v) \<in> X2" using E by (simp add: X2_def)
        then have "e2 \<le> p $ u + p $ v - 1" using e2 by auto
        moreover have "\<bar>s * (w u + w v)\<bar> \<le> 2 * e"
        proof -
          have "\<bar>w u + w v\<bar> \<le> 2" using wb[of u] wb[of v] by auto
          then have "\<bar>s\<bar> * \<bar>w u + w v\<bar> \<le> e * 2"
            using s by (intro mult_mono) auto
          then show ?thesis by (simp add: abs_mult)
        qed
        ultimately show ?thesis using ele2 by (simp add: algebra_simps abs_le_iff)
      qed
    qed
  qed
  define T where "T = (\<Sum>v\<in>UNIV. p $ v * w v)"
  have nonneg: "\<And>s. \<bar>s\<bar> \<le> e \<Longrightarrow> 0 \<le> s * T"
  proof -
    fix s assume s: "\<bar>s\<bar> \<le> e"
    have "0 \<le> (\<Sum>v\<in>UNIV. p $ v * ((\<chi> v. p $ v + s * w v) $ v - p $ v))"
      by (rule variational[OF m feas[OF s]])
    also have "\<dots> = s * T" by (simp add: T_def sum_distrib_left algebra_simps)
    finally show "0 \<le> s * T" .
  qed
  have "0 \<le> e * T" using nonneg[of e] epos by simp
  moreover have "0 \<le> (-e) * T" using nonneg[of "-e"] epos by simp
  ultimately have T0: "T = 0" using epos by (auto simp: mult_le_0_iff zero_le_mult_iff)
  have pt: "\<And>v. p $ v * w v =
      (if p $ v - 1/2 = c then 1/2 + c else 0) - (if p $ v - 1/2 = -c then 1/2 - c else 0)"
    using c by (auto simp: w_def)
  have "T = real (card {v. p $ v - 1/2 = c}) * (1/2 + c)
      - real (card {v. p $ v - 1/2 = -c}) * (1/2 - c)"
    by (simp add: T_def pt sum_subtractf sum_ind)
  then show ?thesis using T0 by simp
qed

lemma deviation_lower:
  fixes p :: "real^'n::finite"
  assumes m: "minimal E p" and ne: "\<exists>v. p $ v \<noteq> 1/2"
  shows "1 / (4 * real CARD('n)) \<le> (\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2)"
proof -
  have kpos: "(1::real) \<le> real CARD('n)" using card_pos[where 'n = 'n] by simp
  have kinv: "1 / (4 * real CARD('n)) \<le> 1 / 4"
    using kpos by (simp add: field_simps)
  show ?thesis
  proof (cases "\<exists>v. 1/2 \<le> \<bar>p $ v - 1/2\<bar>")
    case True
    then obtain v where v: "1/2 \<le> \<bar>p $ v - 1/2\<bar>" by blast
    have "(1/2::real)\<^sup>2 \<le> \<bar>p $ v - 1/2\<bar>\<^sup>2"
      using v by (intro power_mono) auto
    then have "1/4 \<le> (p $ v - 1/2)\<^sup>2" by (simp add: power2_eq_square)
    moreover have "(p $ v - 1/2)\<^sup>2 \<le> (\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2)"
      by (rule member_le_sum) auto
    ultimately show ?thesis using kinv by linarith
  next
    case False
    then have lt: "\<And>v. \<bar>p $ v - 1/2\<bar> < 1/2" by (simp add: not_le)
    have pos: "\<forall>v. 0 < p $ v"
    proof
      fix v
      have "\<bar>p $ v - 1/2\<bar> < 1/2" by (rule lt)
      then show "0 < p $ v" unfolding abs_less_iff by linarith
    qed
    obtain v0 where v0: "p $ v0 \<noteq> 1/2" using ne by blast
    define c where "c = \<bar>p $ v0 - 1/2\<bar>"
    have c: "0 < c" using v0 by (simp add: c_def)
    define H where "H = {v. p $ v - 1/2 = c}"
    define L where "L = {v. p $ v - 1/2 = -c}"
    have bal: "real (card H) * (1/2 + c) = real (card L) * (1/2 - c)"
      using level_balance[OF m pos c] by (simp add: H_def L_def)
    have disj: "H \<inter> L = {}" using c by (auto simp: H_def L_def)
    have hl: "card H + card L = card (H \<union> L)"
      using disj by (simp add: card_Un_disjoint)
    have hlk: "card H + card L \<le> CARD('n)"
      using hl card_mono[of UNIV "H \<union> L"] by simp
    have v0HL: "v0 \<in> H \<union> L" using c_def by (auto simp: H_def L_def abs_if split: if_splits)
    have ne: "H \<union> L \<noteq> {}" using v0HL by auto
    have mpos: "0 < card H + card L"
      using hl ne by (simp add: card_gt_0_iff)
    define h where "h = real (card H)"
    define l where "l = real (card L)"
    have mh: "0 < h + l" unfolding h_def l_def using mpos by (metis of_nat_add of_nat_0_less_iff)
    have key: "2 * c * (h + l) = l - h" using bal by (simp add: h_def l_def algebra_simps)
    have lh: "h + 1 \<le> l"
    proof -
      have "0 < 2 * c * (h + l)" using c mh by (intro mult_pos_pos) auto
      then have "h < l" using key by linarith
      then have "card H < card L" unfolding h_def l_def by simp
      then have "card H + 1 \<le> card L" by simp
      then show ?thesis by (simp add: h_def l_def)
    qed
    have mk: "h + l \<le> real CARD('n)" using hlk by (simp add: h_def l_def)
    have lower: "(h + l) * c\<^sup>2 \<le> (\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2)"
    proof -
      have "(\<Sum>v\<in>UNIV. (if p $ v - 1/2 = c then c\<^sup>2 else 0)
            + (if p $ v - 1/2 = -c then c\<^sup>2 else 0)) \<le> (\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2)"
        by (rule sum_mono) (use c in \<open>auto simp: power2_eq_square\<close>)
      moreover have "(\<Sum>v\<in>UNIV. (if p $ v - 1/2 = c then c\<^sup>2 else 0)
            + (if p $ v - 1/2 = -c then c\<^sup>2 else 0)) = (h + l) * c\<^sup>2"
        by (simp add: sum.distrib sum_ind h_def l_def H_def L_def algebra_simps)
      ultimately show ?thesis by simp
    qed
    have one: "1 \<le> 2 * c * (h + l)" using key lh by linarith
    have sq: "1 \<le> (2 * c * (h + l))\<^sup>2" using one by (intro one_le_power) auto
    have hh: "(h + l) * (h + l) \<le> real CARD('n) * (h + l)"
      using mk mh by (intro mult_right_mono) auto
    have "1 \<le> 4 * real CARD('n) * ((h + l) * c\<^sup>2)"
    proof -
      have "(2 * c * (h + l))\<^sup>2 = 4 * c\<^sup>2 * ((h + l) * (h + l))"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> \<le> 4 * c\<^sup>2 * (real CARD('n) * (h + l))"
        using hh by (intro mult_left_mono) auto
      finally show ?thesis using sq by (simp add: algebra_simps)
    qed
    then have "1 / (4 * real CARD('n)) \<le> (h + l) * c\<^sup>2"
      using kpos by (simp add: divide_le_eq algebra_simps)
    then show ?thesis using lower by linarith
  qed
qed

section \<open>Arithmetic of the bound\<close>

lemma div4_odd: "(4 * (y::nat) + 1) div 4 = y"
  by arith

lemma bound_form:
  fixes k :: nat
  assumes "0 < k"
  shows "real (k\<^sup>2 div 4) / real k = real k / 4 - real (k mod 2) / (4 * real k)"
proof -
  have eq: "4 * (k\<^sup>2 div 4) + k mod 2 = k\<^sup>2"
  proof -
    have h: "k = 2 * (k div 2) \<or> k = 2 * (k div 2) + 1" by arith
    then obtain m where "k = 2 * m \<or> k = 2 * m + 1" by blast
    then show ?thesis
    proof
      assume "k = 2 * m"
      then have "k\<^sup>2 = 4 * (m * m)" by (simp add: power2_eq_square algebra_simps)
      then show ?thesis using \<open>k = 2 * m\<close> by auto
    next
      assume "k = 2 * m + 1"
      then have "k\<^sup>2 = 4 * (m * m + m) + 1" by (simp add: power2_eq_square algebra_simps)
      have d: "k\<^sup>2 div 4 = m * m + m" using \<open>k\<^sup>2 = 4 * (m * m + m) + 1\<close> by (simp add: div4_odd)
      have md: "k mod 2 = 1" using \<open>k = 2 * m + 1\<close> by arith
      show ?thesis using d md \<open>k\<^sup>2 = 4 * (m * m + m) + 1\<close> by simp
    qed
  qed
  have "4 * real (k\<^sup>2 div 4) + real (k mod 2) = (real k)\<^sup>2"
    by (metis eq of_nat_add of_nat_mult of_nat_numeral of_nat_power)
  then have "real (k\<^sup>2 div 4) = ((real k)\<^sup>2 - real (k mod 2)) / 4" by simp
  moreover have "real k \<noteq> 0" using assms by simp
  ultimately show ?thesis by (simp add: field_simps power2_eq_square)
qed

lemma prod_parts:
  fixes k :: nat
  shows "((k + 1) div 2) * (k div 2) = k\<^sup>2 div 4"
proof -
  have h: "k = 2 * (k div 2) \<or> k = 2 * (k div 2) + 1" by arith
  then obtain m where "k = 2 * m \<or> k = 2 * m + 1" by blast
  then show ?thesis
  proof
    assume "k = 2 * m"
    then have "k\<^sup>2 = 4 * (m * m)" by (simp add: power2_eq_square algebra_simps)
    then show ?thesis using \<open>k = 2 * m\<close> by auto
  next
    assume "k = 2 * m + 1"
    then have "k\<^sup>2 = 4 * (m * m + m) + 1" by (simp add: power2_eq_square algebra_simps)
    then have "k\<^sup>2 div 4 = m * m + m" by (simp add: div4_odd)
    moreover have "(k + 1) div 2 = m + 1" and "k div 2 = m" using \<open>k = 2 * m + 1\<close> by arith+
    ultimately show ?thesis by (simp add: algebra_simps)
  qed
qed

section \<open>The main theorem\<close>

theorem graph_threshold_bound:
  fixes E :: "'n::finite \<Rightarrow> 'n \<Rightarrow> bool"
  shows "\<exists>p::real^'n. fcover E p \<and>
      (\<forall>I. indep E I \<longrightarrow> (\<Sum>v\<in>I. p $ v) \<le> real (CARD('n)\<^sup>2 div 4) / real CARD('n))"
proof -
  obtain p :: "real^'n" where m: "minimal E p" using exists_minimal by blast
  have cov: "fcover E p" using m by (simp add: minimal_def)
  have kpos: "0 < CARD('n)" by (rule card_pos)
  have kr: "(1::real) \<le> real CARD('n)" using kpos by simp
  have bf: "real (CARD('n)\<^sup>2 div 4) / real CARD('n)
      = real CARD('n) / 4 - real (CARD('n) mod 2) / (4 * real CARD('n))"
    by (rule bound_form[OF kpos])
  have D0: "0 \<le> (\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2)" by (simp add: sum_nonneg)
  have inv4: "1 / (4 * real CARD('n)) \<le> 1 / 4" using kr by (simp add: field_simps)
  have all: "\<forall>I. indep E I \<longrightarrow> (\<Sum>v\<in>I. p $ v) \<le> real (CARD('n)\<^sup>2 div 4) / real CARD('n)"
  proof (intro allI impI)
    fix I assume I: "indep E I"
    have core: "(\<Sum>v\<in>I. p $ v) \<le> real CARD('n) / 4 - (\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2)"
      by (rule indep_bound[OF m I])
    show "(\<Sum>v\<in>I. p $ v) \<le> real (CARD('n)\<^sup>2 div 4) / real CARD('n)"
    proof (cases "CARD('n) mod 2 = 0")
      case True
      have tgt: "real (CARD('n)\<^sup>2 div 4) / real CARD('n) = real CARD('n) / 4"
        using bf True by simp
      then show ?thesis using core D0 by linarith
    next
      case odd: False
      then have one: "CARD('n) mod 2 = 1" by arith
      show ?thesis
      proof (cases "\<exists>v. p $ v \<noteq> 1/2")
        case True
        have dl: "1 / (4 * real CARD('n)) \<le> (\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2)"
          by (rule deviation_lower[OF m True])
        have tgt: "real (CARD('n)\<^sup>2 div 4) / real CARD('n)
            = real CARD('n) / 4 - 1 / (4 * real CARD('n))"
          using bf one by simp
        then show ?thesis using core dl by linarith
      next
        case False
        then have half: "\<And>v. p $ v = 1/2" by blast
        have s: "(\<Sum>v\<in>I. p $ v) = real (card I) / 2" by (simp add: half)
        have dz: "(\<Sum>v\<in>UNIV. (p $ v - 1/2)\<^sup>2) = 0" by (simp add: half)
        have "real (card I) / 2 \<le> real CARD('n) / 4" using core s dz by simp
        then have "real (2 * card I) \<le> real CARD('n)" by simp
        then have "2 * card I \<le> CARD('n)" by (simp only: of_nat_le_iff)
        then have "2 * card I + 1 \<le> CARD('n)" using one by arith
        then have "real (2 * card I + 1) \<le> real CARD('n)" by (simp only: of_nat_le_iff)
        then have "2 * real (card I) + 1 \<le> real CARD('n)" by simp
        have tgt: "real (CARD('n)\<^sup>2 div 4) / real CARD('n)
            = real CARD('n) / 4 - 1 / (4 * real CARD('n))"
          using bf one by simp
        then show ?thesis using s inv4 \<open>2 * real (card I) + 1 \<le> real CARD('n)\<close> by linarith
      qed
    qed
  qed
  show ?thesis using cov all by blast
qed

text \<open>The same bound in the form with the parity written out.\<close>

corollary graph_threshold_bound_parity:
  fixes E :: "'n::finite \<Rightarrow> 'n \<Rightarrow> bool"
  shows "\<exists>p::real^'n. fcover E p \<and>
      (\<forall>I. indep E I \<longrightarrow> (\<Sum>v\<in>I. p $ v)
          \<le> ((real CARD('n))\<^sup>2 - real (CARD('n) mod 2)) / (4 * real CARD('n)))"
proof -
  have kpos: "0 < CARD('n)" by (rule card_pos)
  have "real (CARD('n)\<^sup>2 div 4) / real CARD('n)
      = ((real CARD('n))\<^sup>2 - real (CARD('n) mod 2)) / (4 * real CARD('n))"
    using bound_form[OF kpos] kpos by (simp add: field_simps power2_eq_square)
  then show ?thesis using graph_threshold_bound[of E] by simp
qed

section \<open>The bound is attained by the balanced complete bipartite graph\<close>

definition kbip :: "'n set \<Rightarrow> 'n set \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool" where
  "kbip X Y u v \<longleftrightarrow> (u \<in> X \<and> v \<in> Y) \<or> (u \<in> Y \<and> v \<in> X)"

theorem bound_attained:
  fixes X Y :: "'n::finite set" and p :: "real^'n"
  assumes disj: "X \<inter> Y = {}" and cover: "X \<union> Y = UNIV"
    and cx: "card X = (CARD('n) + 1) div 2" and cy: "card Y = CARD('n) div 2"
    and p: "fcover (kbip X Y) p"
  shows "\<exists>I. indep (kbip X Y) I \<and>
      real (CARD('n)\<^sup>2 div 4) / real CARD('n) \<le> (\<Sum>v\<in>I. p $ v)"
proof -
  have indX: "indep (kbip X Y) X" and indY: "indep (kbip X Y) Y"
    using disj by (auto simp: indep_def kbip_def)
  define a where "a = real (card X)"
  define b where "b = real (card Y)"
  have ab: "a * b = real (CARD('n)\<^sup>2 div 4)"
    using prod_parts[of "CARD('n)"] cx cy by (simp add: a_def b_def flip: of_nat_mult)
  have sum_k: "a + b = real CARD('n)"
  proof -
    have "card X + card Y = card (X \<union> Y)" using disj by (simp add: card_Un_disjoint)
    then show ?thesis using cover by (simp add: a_def b_def flip: of_nat_add)
  qed
  have kpos: "0 < CARD('n)" by (rule card_pos)
  define pX where "pX = (\<Sum>v\<in>X. p $ v)"
  define pY where "pY = (\<Sum>v\<in>Y. p $ v)"
  have lower: "a * b \<le> b * pX + a * pY"
  proof -
    have "(\<Sum>x\<in>X. \<Sum>y\<in>Y. (1::real)) \<le> (\<Sum>x\<in>X. \<Sum>y\<in>Y. p $ x + p $ y)"
    proof (intro sum_mono)
      fix x y assume "x \<in> X" "y \<in> Y"
      then have "kbip X Y x y" by (simp add: kbip_def)
      then show "(1::real) \<le> p $ x + p $ y" using p by (simp add: fcover_def)
    qed
    moreover have "(\<Sum>x\<in>X. \<Sum>y\<in>Y. (1::real)) = a * b" by (simp add: a_def b_def)
    moreover have "(\<Sum>x\<in>X. \<Sum>y\<in>Y. p $ x + p $ y) = b * pX + a * pY"
      by (simp add: sum.distrib sum_distrib_left pX_def pY_def a_def b_def mult.commute)
    ultimately show ?thesis by simp
  qed
  have a0: "0 \<le> a" and b0: "0 \<le> b" by (simp_all add: a_def b_def)
  have ab0: "0 < a + b" using sum_k kpos by simp
  show ?thesis
  proof (cases "pY \<le> pX")
    case True
    have "(a + b) * pX \<ge> b * pX + a * pY"
      using True a0 by (simp add: algebra_simps mult_left_mono)
    then have "a * b \<le> (a + b) * pX" using lower by linarith
    then have "real (CARD('n)\<^sup>2 div 4) / real CARD('n) \<le> pX"
      using ab sum_k ab0 by (simp add: divide_le_eq algebra_simps)
    then show ?thesis using indX by (auto simp: pX_def)
  next
    case False
    then have "pX \<le> pY" by simp
    have "(a + b) * pY \<ge> b * pX + a * pY"
      using \<open>pX \<le> pY\<close> b0 by (simp add: algebra_simps mult_left_mono)
    then have "a * b \<le> (a + b) * pY" using lower by linarith
    then have "real (CARD('n)\<^sup>2 div 4) / real CARD('n) \<le> pY"
      using ab sum_k ab0 by (simp add: divide_le_eq algebra_simps)
    then show ?thesis using indY by (auto simp: pY_def)
  qed
qed

end
