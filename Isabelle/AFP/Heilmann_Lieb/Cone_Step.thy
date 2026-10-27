(*  Title:      Cone_Step.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The cone step

    The analytic core of the Heilmann--Lieb theorem: subtracting an element of the cone of interlacing polynomials from
    x times a product of real linear factors gives again a product of real linear factors, which interlaces the first
    one. Plan: PLAN_cone_step.md.

    Main results:
    * cone_step.
*)

theory Cone_Step
  imports Interlacing
begin

section \<open>Lists with one element left out\<close>

lemma lin_prod_append: "lin_prod (qs @ ts) = lin_prod qs * lin_prod ts"
proof (induction qs)
  case Nil
  then show ?case by simp
next
  case (Cons a qs)
  have "lin_prod ((a # qs) @ ts) = [:-a, 1:] * lin_prod (qs @ ts)" by (simp only: append_Cons lin_prod_Cons)
  also have "\<dots> = [:-a, 1:] * (lin_prod qs * lin_prod ts)" by (simp only: Cons.IH)
  also have "\<dots> = ([:-a, 1:] * lin_prod qs) * lin_prod ts" by (simp only: mult.assoc)
  also have "\<dots> = lin_prod (a # qs) * lin_prod ts" by (simp only: lin_prod_Cons)
  finally show ?case .
qed

lemma omit_append: "omit (length qs + i) (qs @ ts) = qs @ omit i ts"
  by (simp add: omit_def)

lemma length_omit: "l < length ts \<Longrightarrow> length (omit l ts) = length ts - 1"
  by (simp add: omit_def)

lemma nth_omit: "k < length ts - 1 \<Longrightarrow> l < length ts \<Longrightarrow> omit l ts ! k = (if k < l then ts ! k else ts ! Suc k)"
  by (simp add: omit_def nth_append)

lemma mem_omit:
  assumes "distinct ts" "l < length ts" "j < length ts"
  shows "ts ! j \<in> set (omit l ts) \<longleftrightarrow> j \<noteq> l"
proof
  assume "ts ! j \<in> set (omit l ts)"
  then obtain k where k: "k < length ts - 1" "omit l ts ! k = ts ! j"
    using assms(2) by (auto simp: in_set_conv_nth length_omit)
  show "j \<noteq> l"
  proof
    assume "j = l"
    with k assms show False
      by (auto simp: nth_omit nth_eq_iff_index_eq split: if_splits)
  qed
next
  assume "j \<noteq> l"
  show "ts ! j \<in> set (omit l ts)"
  proof (cases "j < l")
    case True
    then show ?thesis using assms(2) by (auto simp: in_set_conv_nth length_omit nth_omit intro!: exI[of _ j])
  next
    case False
    with \<open>j \<noteq> l\<close> have "l < j" by simp
    then show ?thesis using assms(3)
      by (auto simp: in_set_conv_nth length_omit nth_omit assms(2) intro!: exI[of _ "j - 1"])
  qed
qed

lemma poly_omit_zero:
  assumes "distinct ts" "l < length ts" "j < length ts"
  shows "poly (lin_prod (omit l ts)) (ts ! j) = 0 \<longleftrightarrow> j \<noteq> l"
proof -
  have e1: "poly (lin_prod (omit l ts)) (ts ! j) = prod_list (map (\<lambda>r. ts ! j - r) (omit l ts))"
    by (simp add: poly_lin_prod)
  have e2: "(0 \<in> set (map (\<lambda>r. ts ! j - r) (omit l ts))) = (ts ! j \<in> set (omit l ts))"
    by auto
  have "(poly (lin_prod (omit l ts)) (ts ! j) = 0) = (0 \<in> set (map (\<lambda>r. ts ! j - r) (omit l ts)))"
    by (simp only: e1 prod_list_zero_iff)
  also have "\<dots> = (ts ! j \<in> set (omit l ts))" by (rule e2)
  also have "\<dots> = (j \<noteq> l)" by (rule mem_omit[OF assms])
  finally show ?thesis .
qed

section \<open>Multiplying by common factors\<close>

lemma in_cone_prepend: "in_cone p ts \<Longrightarrow> in_cone (lin_prod qs * p) (qs @ ts)"
proof -
  assume "in_cone p ts"
  then obtain c where c: "\<forall>i<length ts. 0 \<le> c i"
    and p: "p = (\<Sum>i<length ts. smult (c i) (lin_prod (omit i ts)))"
    unfolding in_cone_def by blast
  let ?m = "length qs" and ?n = "length ts"
  let ?c = "\<lambda>i. if i < ?m then 0 else c (i - ?m)"
  let ?g = "\<lambda>i. smult (?c i) (lin_prod (omit i (qs @ ts)))"
  have "(\<Sum>i<?m + ?n. ?g i) = (\<Sum>i\<in>{0..<?m}. ?g i) + (\<Sum>i\<in>{?m..<?m + ?n}. ?g i)"
    unfolding lessThan_atLeast0 by (rule sum.atLeastLessThan_concat[symmetric]) simp_all
  also have "(\<Sum>i\<in>{0..<?m}. ?g i) = 0" by simp
  also have "(\<Sum>i\<in>{?m..<?m + ?n}. ?g i) = (\<Sum>i\<in>{0..<?n}. ?g (?m + i))"
    using sum.shift_bounds_nat_ivl[of ?g 0 ?m ?n] by (simp add: add.commute)
  also have "\<dots> = (\<Sum>i<?n. smult (c i) (lin_prod qs * lin_prod (omit i ts)))"
    by (simp add: lessThan_atLeast0 omit_append lin_prod_append)
  also have "\<dots> = lin_prod qs * p"
    by (simp add: p sum_distrib_left mult_smult_right)
  finally have A: "lin_prod qs * p = (\<Sum>i<length (qs @ ts). ?g i)" by simp
  have B: "\<forall>i<length (qs @ ts). 0 \<le> ?c i"
  proof (intro allI impI)
    fix i assume i: "i < length (qs @ ts)"
    show "0 \<le> ?c i"
    proof (cases "i < ?m")
      case True then show ?thesis by simp
    next
      case False
      with i have "i - ?m < ?n" by simp
      then show ?thesis using c False by simp
    qed
  qed
  show ?thesis unfolding in_cone_def
    by (rule exI[of _ ?c], rule conjI, rule B, rule A)
qed

section \<open>Multisets of roots\<close>

lemma mset_omit_aux: "i < length xs \<Longrightarrow> mset (omit i xs) = mset xs - {#xs ! i#}"
proof -
  assume h: "i < length xs"
  have e: "mset xs = mset (take i xs @ xs ! i # drop (Suc i) xs)"
    by (rule arg_cong[where f = mset, OF id_take_nth_drop[OF h]])
  have "mset xs = mset (omit i xs) + {#xs ! i#}"
    unfolding omit_def by (subst e) simp
  then show ?thesis by simp
qed

lemma lin_prod_append_aux: "lin_prod (as @ bs) = lin_prod as * lin_prod bs"
  by (simp add: lin_prod_def)

lemma lin_prod_omit_remove1_aux:
  assumes "i < length rs"
  shows "lin_prod (omit i rs) = lin_prod (remove1 (rs ! i) rs)"
proof (rule lin_prod_perm)
  show "mset (omit i rs) = mset (remove1 (rs ! i) rs)"
    using mset_omit_aux[OF assms] by (simp add: mset_remove1)
qed

lemma lin_prod_remove1_split_aux:
  assumes "mset rs = mset qs + mset ss" and "j < length ss"
  shows "lin_prod (remove1 (ss ! j) rs) = lin_prod qs * lin_prod (omit j ss)"
proof -
  have mem: "ss ! j \<in># mset ss" using assms(2) by simp
  have cr: "0 < count (mset ss) (ss ! j)" using mem by simp
  have "mset (remove1 (ss ! j) rs) = mset (qs @ omit j ss)"
    unfolding mset_remove1 mset_append mset_omit_aux[OF assms(2)] assms(1)
  proof (rule multiset_eqI)
    fix a
    show "count (mset qs + mset ss - {#ss ! j#}) a = count (mset qs + (mset ss - {#ss ! j#})) a"
      using cr by (cases "a = ss ! j") (auto simp: )
  qed
  then have "lin_prod (remove1 (ss ! j) rs) = lin_prod (qs @ omit j ss)"
    by (rule lin_prod_perm)
  then show ?thesis by (simp only: lin_prod_append_aux)
qed

section \<open>Grouping repeated roots\<close>

text \<open>Every element of the cone of \<open>rs\<close> can be written with a common factor \<open>R\<close> taken out, over a strictly
  increasing list of distinct roots with strictly positive weights.\<close>

lemma group_roots:
  assumes "in_cone S rs"
  shows "\<exists>qs ss C. sorted_wrt (<) ss \<and> (\<forall>j<length ss. 0 < C j) \<and>
           length qs + length ss = length rs \<and>
           lin_prod rs = lin_prod qs * lin_prod ss \<and>
           S = lin_prod qs * (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss)))"
proof -
  obtain c where hc: "\<forall>i<length rs. 0 \<le> c i"
    and hS: "S = (\<Sum>i<length rs. smult (c i) (lin_prod (omit i rs)))"
    using assms unfolding in_cone_def by blast
  define n where "n = length rs"
  define W where "W r = (\<Sum>i\<in>{i. i < n \<and> rs ! i = r}. c i)" for r
  have Wnn: "\<And>r. 0 \<le> W r"
    unfolding W_def using hc n_def by (intro sum_nonneg) auto
  define ss where "ss = sorted_list_of_set {r \<in> set rs. 0 < W r}"
  have fin: "finite {r \<in> set rs. 0 < W r}" by simp
  have setss: "set ss = {r \<in> set rs. 0 < W r}" unfolding ss_def using fin by simp
  have dist: "distinct ss" unfolding ss_def by simp
  have srt: "sorted_wrt (<) ss" unfolding ss_def
    by (simp add: strict_sorted_iff)
  have sub: "mset ss \<le># mset rs"
  proof (subst subseteq_mset_def, intro allI)
    fix a
    show "count (mset ss) a \<le> count (mset rs) a"
    proof (cases "a \<in> set ss")
      case True
      then have "a \<in> set rs" using setss by simp
      then have "0 < count (mset rs) a" by simp
      moreover have "count (mset ss) a = 1" using dist True by (simp add: distinct_count_atmost_1)
      ultimately show ?thesis by simp
    next
      case False
      have z: "count (mset ss) a = 0" using False by (simp add: count_eq_zero_iff)
      show ?thesis by (subst z) (rule zero_le)
    qed
  qed
  obtain qs where mq: "mset qs = mset rs - mset ss" using ex_mset by blast
  have mrs: "mset rs = mset qs + mset ss" using sub mq by simp
  have len: "length qs + length ss = length rs"
  proof -
    have "size (mset rs) = size (mset qs) + size (mset ss)" using mrs by (simp only:) simp
    then show ?thesis by simp
  qed
  have lp: "lin_prod rs = lin_prod qs * lin_prod ss"
  proof -
    have "lin_prod rs = lin_prod (qs @ ss)" by (rule lin_prod_perm) (simp add: mrs)
    then show ?thesis by (simp only: lin_prod_append_aux)
  qed
  have Cpos: "\<forall>j<length ss. 0 < W (ss ! j)"
  proof (intro allI impI)
    fix j assume "j < length ss"
    then have "ss ! j \<in> set ss" by simp
    then show "0 < W (ss ! j)" using setss by simp
  qed
  (* regroup the sum by the value of the root *)
  have step1: "S = (\<Sum>i<n. smult (c i) (lin_prod (remove1 (rs ! i) rs)))"
    unfolding hS n_def using lin_prod_omit_remove1_aux by (intro sum.cong) auto
  have step2: "(\<Sum>i<n. smult (c i) (lin_prod (remove1 (rs ! i) rs)))
      = (\<Sum>r\<in>set rs. smult (W r) (lin_prod (remove1 r rs)))"
  proof -
    have g: "(\<Sum>r\<in>set rs. \<Sum>i\<in>{i \<in> {..<n}. rs ! i = r}. smult (c i) (lin_prod (remove1 (rs ! i) rs)))
        = (\<Sum>i<n. smult (c i) (lin_prod (remove1 (rs ! i) rs)))"
      by (rule sum.group) (use n_def in auto)
    have pw: "\<And>r. r \<in> set rs \<Longrightarrow>
        (\<Sum>i\<in>{i \<in> {..<n}. rs ! i = r}. smult (c i) (lin_prod (remove1 (rs ! i) rs)))
        = smult (W r) (lin_prod (remove1 r rs))"
    proof -
      fix r assume "r \<in> set rs"
      have "(\<Sum>i\<in>{i \<in> {..<n}. rs ! i = r}. smult (c i) (lin_prod (remove1 (rs ! i) rs)))
          = (\<Sum>i\<in>{i. i < n \<and> rs ! i = r}. smult (c i) (lin_prod (remove1 r rs)))"
        by (intro sum.cong) auto
      also have "\<dots> = smult (W r) (lin_prod (remove1 r rs))"
        unfolding W_def by (simp add: smult_sum)
      finally show "(\<Sum>i\<in>{i \<in> {..<n}. rs ! i = r}. smult (c i) (lin_prod (remove1 (rs ! i) rs)))
          = smult (W r) (lin_prod (remove1 r rs))" .
    qed
    have "(\<Sum>r\<in>set rs. \<Sum>i\<in>{i \<in> {..<n}. rs ! i = r}. smult (c i) (lin_prod (remove1 (rs ! i) rs)))
        = (\<Sum>r\<in>set rs. smult (W r) (lin_prod (remove1 r rs)))"
      by (rule sum.cong[OF refl]) (rule pw)
    with g show ?thesis by simp
  qed
  have step3: "(\<Sum>r\<in>set rs. smult (W r) (lin_prod (remove1 r rs)))
      = (\<Sum>r\<in>set ss. smult (W r) (lin_prod (remove1 r rs)))"
  proof (rule sum.mono_neutral_right)
    show "finite (set rs)" by simp
    show "set ss \<subseteq> set rs" using setss by auto
    show "\<forall>r\<in>set rs - set ss. smult (W r) (lin_prod (remove1 r rs)) = 0"
    proof
      fix r assume "r \<in> set rs - set ss"
      then have "\<not> 0 < W r" using setss by auto
      with Wnn[of r] have "W r = 0" by simp
      then show "smult (W r) (lin_prod (remove1 r rs)) = 0" by simp
    qed
  qed
  have bij: "bij_betw (nth ss) {..<length ss} (set ss)"
    unfolding bij_betw_def
  proof
    show "inj_on (nth ss) {..<length ss}"
      using dist by (auto simp: inj_on_def nth_eq_iff_index_eq)
    show "nth ss ` {..<length ss} = set ss" by (auto simp: set_conv_nth)
  qed
  have step4: "(\<Sum>r\<in>set ss. smult (W r) (lin_prod (remove1 r rs)))
      = (\<Sum>j<length ss. smult (W (ss ! j)) (lin_prod (remove1 (ss ! j) rs)))"
    by (rule sum.reindex_bij_betw[OF bij, symmetric])
  have step5: "(\<Sum>j<length ss. smult (W (ss ! j)) (lin_prod (remove1 (ss ! j) rs)))
      = lin_prod qs * (\<Sum>j<length ss. smult (W (ss ! j)) (lin_prod (omit j ss)))"
  proof -
    have "(\<Sum>j<length ss. smult (W (ss ! j)) (lin_prod (remove1 (ss ! j) rs)))
        = (\<Sum>j<length ss. lin_prod qs * smult (W (ss ! j)) (lin_prod (omit j ss)))"
    proof (rule sum.cong[OF refl])
      fix j assume "j \<in> {..<length ss}"
      then have "j < length ss" by simp
      then show "smult (W (ss ! j)) (lin_prod (remove1 (ss ! j) rs))
          = lin_prod qs * smult (W (ss ! j)) (lin_prod (omit j ss))"
        by (simp add: lin_prod_remove1_split_aux[OF mrs])
    qed
    then show ?thesis by (simp add: sum_distrib_left)
  qed
  show ?thesis
    apply (rule exI[where x = qs], rule exI[where x = ss], rule exI[where x = "\<lambda>j. W (ss ! j)"])
    using srt Cpos len lp step1 step2 step3 step4 step5 by simp
qed

section \<open>The simple case\<close>

text \<open>The sign of a product of linear factors at a point that is not a root: one minus sign for every root
  above the point.\<close>

lemma sign_lin_prod:
  assumes "x \<notin> set ss"
  shows "sgn (poly (lin_prod ss) x) = (-1) ^ length (filter (\<lambda>s. x < s) ss)"
  using assms
proof (induction ss)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  have ne: "x \<noteq> s" using Cons.prems by simp
  have xs: "x \<notin> set ss" using Cons.prems by simp
  have IH: "sgn (poly (lin_prod ss) x) = (-1) ^ length (filter (\<lambda>s. x < s) ss)" by (rule Cons.IH[OF xs])
  have pe: "poly (lin_prod (s # ss)) x = (x - s) * poly (lin_prod ss) x"
    by (simp add: algebra_simps)
  show ?case
  proof (cases "x < s")
    case True
    then have "sgn (x - s) = -1" by simp
    then show ?thesis using True IH by (simp add: pe sgn_mult del: lin_prod_Cons)
  next
    case False
    with ne have "0 < x - s" by simp
    then have "sgn (x - s) = 1" by simp
    then show ?thesis using False IH by (simp add: pe sgn_mult del: lin_prod_Cons)
  qed
qed

section \<open>Auxiliary lemmas for the simple case\<close>

lemma hl_lin_prod_root_zero: "x \<in> set xs \<Longrightarrow> poly (lin_prod xs) x = 0"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons a xs) then show ?case by (cases "x = a") (auto simp: lin_prod_Cons)
qed

lemma hl_omit_mem:
  assumes "j < length ss" and "i \<noteq> j"
  shows "ss ! j \<in> set (omit i ss)"
proof (cases "j < i")
  case True
  then have e: "ss ! j = take i ss ! j" using assms(1) by simp
  have "j < length (take i ss)" using True assms(1) by simp
  then have "take i ss ! j \<in> set (take i ss)" by (rule nth_mem)
  then show ?thesis unfolding omit_def e by (simp only: set_append Un_iff) simp
next
  case False
  with assms(2) have ij: "i < j" by simp
  have e: "ss ! j = drop (Suc i) ss ! (j - Suc i)" using ij assms(1) by simp
  have "j - Suc i < length (drop (Suc i) ss)" using ij assms(1) by simp
  then have "drop (Suc i) ss ! (j - Suc i) \<in> set (drop (Suc i) ss)" by (rule nth_mem)
  then show ?thesis unfolding omit_def e by (simp only: set_append Un_iff) simp
qed

definition simple_Q :: "real list \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real poly" where
  "simple_Q ss C = [:0, 1:] * lin_prod ss - (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss)))"

lemma hl_simple_Q_deg: "degree (simple_Q ss C) = Suc (length ss) \<and> lead_coeff (simple_Q ss C) = 1"
proof -
  let ?A = "[:0, 1:] * lin_prod ss"
  let ?B = "(\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss)))"
  have dA: "degree ?A = Suc (length ss)"
    by (subst degree_mult_eq) (simp_all add: lin_prod_ne_0)
  have lA: "lead_coeff ?A = 1" by (subst lead_coeff_mult, subst lead_coeff_lin_prod) simp
  have dB: "degree ?B \<le> length ss"
  proof (rule degree_sum_le)
    show "finite {..<length ss}" by simp
    fix j assume "j \<in> {..<length ss}"
    have "degree (smult (C j) (lin_prod (omit j ss))) \<le> degree (lin_prod (omit j ss))"
      by (rule degree_smult_le)
    also have "\<dots> = length (omit j ss)" by simp
    also have "\<dots> \<le> length ss" unfolding omit_def by simp
    finally show "degree (smult (C j) (lin_prod (omit j ss))) \<le> length ss" .
  qed
  have dmB: "degree (- ?B) < degree ?A" using dB dA by simp
  have eq: "simple_Q ss C = - ?B + ?A" unfolding simple_Q_def by simp
  show ?thesis unfolding eq
    using degree_add_eq_left[OF dmB] lead_coeff_add_le[OF dmB] dA lA by simp
qed

lemma hl_poly_Q_at:
  assumes "j < length ss"
  shows "poly (simple_Q ss C) (ss ! j) = - (C j * poly (lin_prod (omit j ss)) (ss ! j))"
proof -
  have mem: "ss ! j \<in> set ss" using assms by simp
  have z: "\<And>i. i \<in> {..<length ss} - {j} \<Longrightarrow> C i * poly (lin_prod (omit i ss)) (ss ! j) = 0"
  proof -
    fix i assume "i \<in> {..<length ss} - {j}"
    then have "i \<noteq> j" by simp
    from hl_omit_mem[OF assms this] hl_lin_prod_root_zero show "C i * poly (lin_prod (omit i ss)) (ss ! j) = 0"
      by simp
  qed
  have "(\<Sum>i<length ss. C i * poly (lin_prod (omit i ss)) (ss ! j))
        = C j * poly (lin_prod (omit j ss)) (ss ! j)"
  proof -
    have "(\<Sum>i<length ss. C i * poly (lin_prod (omit i ss)) (ss ! j))
        = C j * poly (lin_prod (omit j ss)) (ss ! j)
          + (\<Sum>i\<in>{..<length ss} - {j}. C i * poly (lin_prod (omit i ss)) (ss ! j))"
      by (rule sum.remove) (use assms in simp_all)
    also have "(\<Sum>i\<in>{..<length ss} - {j}. C i * poly (lin_prod (omit i ss)) (ss ! j)) = 0"
      by (rule sum.neutral) (use z in auto)
    finally show ?thesis by simp
  qed
  moreover have "poly ([:0, 1:] * lin_prod ss) (ss ! j) = 0"
    using hl_lin_prod_root_zero[OF mem] by simp
  ultimately show ?thesis unfolding simple_Q_def by (simp add: poly_sum)
qed

lemma hl_sgn_omit:
  assumes "sorted_wrt (<) ss" and "j < length ss"
  shows "sgn (poly (lin_prod (omit j ss)) (ss ! j)) = (-1) ^ (length ss - Suc j)"
proof -
  have A: "\<forall>x\<in>set (take j ss). x < ss ! j"
  proof
    fix x assume "x \<in> set (take j ss)"
    then obtain i where i: "i < length (take j ss)" "x = take j ss ! i" by (auto simp: in_set_conv_nth)
    then have "i < j" "i < length ss" using assms(2) by auto
    moreover have "x = ss ! i" using i by simp
    ultimately show "x < ss ! j" using sorted_wrt_nth_less[OF assms(1) _ assms(2)] by simp
  qed
  have B: "\<forall>x\<in>set (drop (Suc j) ss). ss ! j < x"
  proof
    fix x assume "x \<in> set (drop (Suc j) ss)"
    then obtain i where i: "i < length (drop (Suc j) ss)" "x = drop (Suc j) ss ! i" by (auto simp: in_set_conv_nth)
    then have il: "Suc j + i < length ss" by simp
    have "x = ss ! (Suc j + i)" using i by simp
    moreover have "ss ! j < ss ! (Suc j + i)" using sorted_wrt_nth_less[OF assms(1) _ il] by simp
    ultimately show "ss ! j < x" by simp
  qed
  have ni: "ss ! j \<notin> set (omit j ss)" unfolding omit_def using A B by force
  have f: "filter (\<lambda>s. ss ! j < s) (omit j ss) = drop (Suc j) ss"
  proof -
    have f1: "filter (\<lambda>s. ss ! j < s) (take j ss) = []" using A by (simp add: filter_empty_conv) force
    have f2: "filter (\<lambda>s. ss ! j < s) (drop (Suc j) ss) = drop (Suc j) ss"
      using B by (simp add: filter_id_conv)
    show ?thesis unfolding omit_def using f1 f2 by simp
  qed
  show ?thesis using sign_lin_prod[OF ni] f by simp
qed

lemma hl_sgn_Q_at:
  assumes "sorted_wrt (<) ss" and "\<forall>j<length ss. 0 < C j" and "j < length ss"
  shows "sgn (poly (simple_Q ss C) (ss ! j)) = (-1) ^ (length ss - j)"
proof -
  have c: "0 < C j" using assms(2,3) by simp
  have s: "sgn (poly (lin_prod (omit j ss)) (ss ! j)) = (-1) ^ (length ss - Suc j)"
    using hl_sgn_omit[OF assms(1,3)] .
  have "sgn (poly (simple_Q ss C) (ss ! j)) = - (sgn (C j) * sgn (poly (lin_prod (omit j ss)) (ss ! j)))"
    using hl_poly_Q_at[OF assms(3), of C] by (simp add: sgn_minus sgn_mult)
  also have "\<dots> = - ((-1) ^ (length ss - Suc j))" using c s by simp
  also have "\<dots> = (-1) ^ (length ss - j)"
  proof -
    have "length ss - j = Suc (length ss - Suc j)" using assms(3) by simp
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma hl_sgn_minfty:
  assumes "degree p = n" and "lead_coeff p = (1::real)"
  shows "\<exists>a. \<forall>x\<le>a. sgn (poly p x) = (-1) ^ n"
proof -
  define q where "q = smult ((-1) ^ n) (pcompose p [:0, -1:])"
  have d1: "degree [:0, -1::real:] = 1" by simp
  have lq: "lead_coeff q = 1"
  proof -
    have "lead_coeff (pcompose p [:0, -1::real:]) = lead_coeff p * (-1) ^ degree p"
      using lead_coeff_comp[of "[:0, -1::real:]" p] d1 by simp
    then show ?thesis unfolding q_def using assms
      by (cases "even n") (simp_all add: lead_coeff_smult)
  qed
  have posq: "0 < lead_coeff q" using lq by simp
  obtain N where N0: "\<forall>x\<ge>N. lead_coeff q \<le> poly q x"
    using poly_pinfty_gt_lc[OF posq] by blast
  have N: "\<forall>x\<ge>N. 1 \<le> poly q x" using N0 by (simp only: lq)
  show ?thesis
  proof (rule exI[where x = "- N"], intro allI impI)
    fix x :: real assume x: "x \<le> - N"
    have "1 \<le> poly q (- x)" using N x by simp
    then have pos: "0 < (-1) ^ n * poly p x" unfolding q_def
      by (simp add: poly_pcompose)
    show "sgn (poly p x) = (-1) ^ n"
    proof (cases "even n")
      case True
      with pos have "0 < poly p x" by simp
      then show ?thesis using True by simp
    next
      case False
      with pos have "poly p x < 0" by simp
      then show ?thesis using False by simp
    qed
  qed
qed

lemma hl_sgn_pinfty:
  assumes "lead_coeff p = (1::real)"
  shows "\<exists>b. \<forall>x\<ge>b. sgn (poly p x) = 1"
proof -
  obtain N where "\<forall>x\<ge>N. 1 \<le> poly p x" using poly_pinfty_gt_lc[of p] assms by auto
  then show ?thesis by (intro exI[where x = N]) auto
qed

lemma hl_opp_sgn_neg: "sgn (x::real) = - sgn y \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x * y < 0"
  by (auto simp: sgn_real_def mult_less_0_iff split: if_splits)

lemma hl_strict_steps:
  assumes "\<forall>l\<le>k. (u :: nat \<Rightarrow> real) l < u (Suc l)"
  shows "\<forall>j\<le>Suc k. \<forall>i<j. u i < u j"
proof (intro allI)
  fix j show "j \<le> Suc k \<longrightarrow> (\<forall>i<j. u i < u j)"
  proof (induction j)
    case 0 then show ?case by simp
  next
    case (Suc m)
    show ?case
    proof (intro impI allI)
      assume sk: "Suc m \<le> Suc k"
      have step: "u m < u (Suc m)" using assms sk by simp
      fix i assume "i < Suc m"
      then show "u i < u (Suc m)"
      proof (cases "i = m")
        case True then show ?thesis using step by simp
      next
        case False
        with \<open>i < Suc m\<close> have "i < m" by simp
        then have "u i < u m" using Suc.IH sk by simp
        then show ?thesis using step by simp
      qed
    qed
  qed
qed


text \<open>With distinct roots \<open>s_1 < \<dots> < s_k\<close> and positive weights, \<open>x \<cdot> P_1 - S_1\<close> has \<open>k + 1\<close> real roots
  \<open>t_0 < s_1 < t_1 < \<dots> < s_k < t_k\<close>.\<close>

lemma simple_case_roots:
  assumes "sorted_wrt (<) ss" and "\<forall>j<length ss. 0 < C j"
  shows "\<exists>ts. sorted_wrt (<) ts \<and> length ts = Suc (length ss) \<and>
           (\<forall>j<length ss. ts ! j < ss ! j \<and> ss ! j < ts ! Suc j) \<and>
           [:0, 1:] * lin_prod ss - (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss))) = lin_prod ts"
proof (cases "ss = []")
  case True
  then show ?thesis by (intro exI[where x = "[0]"]) simp
next
  case False
  define k where "k = length ss"
  have kpos: "0 < k" using False k_def by simp
  define Q where "Q = simple_Q ss C"
  have QE: "Q = [:0, 1:] * lin_prod ss - (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss)))"
    unfolding Q_def simple_Q_def by simp
  have hQ: "degree Q = Suc k \<and> lead_coeff Q = 1"
    unfolding Q_def k_def by (rule hl_simple_Q_deg)
  have dQ: "degree Q = Suc k" using hQ by (rule conjunct1)
  have lQ: "lead_coeff Q = 1" using hQ by (rule conjunct2)
  obtain a where a: "\<forall>x\<le>a. sgn (poly Q x) = (-1) ^ Suc k" using hl_sgn_minfty[OF dQ lQ] by blast
  obtain b where b: "\<forall>x\<ge>b. sgn (poly Q x) = 1" using hl_sgn_pinfty[OF lQ] by blast
  have s0: "0 < length ss" using kpos k_def by simp
  have sk1: "k - 1 < length ss" using kpos k_def by simp
  define a' where "a' = min a (ss ! 0 - 1)"
  define b' where "b' = max b (ss ! (k - 1) + 1)"
  define u :: "nat \<Rightarrow> real" where "u l = (if l = 0 then a' else if l \<le> k then ss ! (l - 1) else b')" for l
  have u0: "u 0 = a'" unfolding u_def by simp
  have uj: "\<And>j. j < k \<Longrightarrow> u (Suc j) = ss ! j" unfolding u_def by simp
  have uk1: "u (Suc k) = b'" unfolding u_def by simp
  have step: "\<forall>l\<le>k. u l < u (Suc l)"
  proof (intro allI impI)
    fix l assume l: "l \<le> k"
    show "u l < u (Suc l)"
    proof (cases "l = 0")
      case True
      have "a' \<le> ss ! 0 - 1" unfolding a'_def by simp
      then show ?thesis using True u0 uj[of 0] kpos by simp
    next
      case lz: False
      show ?thesis
      proof (cases "l = k")
        case True
        have "u k = ss ! (k - 1)" unfolding u_def using kpos by simp
        moreover have "ss ! (k - 1) < b'" unfolding b'_def by simp
        ultimately show ?thesis using True uk1 by simp
      next
        case False
        with l lz have lk: "l < k" and lp: "0 < l" by simp_all
        obtain m where m: "l = Suc m" using lp by (cases l) auto
        then have mk: "m < k" using lk by simp
        have "u (Suc m) = ss ! m" using uj[OF mk] .
        moreover have "u (Suc l) = ss ! l" using uj[OF lk] by simp
        moreover have "ss ! m < ss ! l"
          using sorted_wrt_nth_less[OF assms(1), of m l] m lk k_def by simp
        ultimately show ?thesis using m by simp
      qed
    qed
  qed
  have sgnu: "\<forall>l\<le>Suc k. sgn (poly Q (u l)) = (-1) ^ (Suc k - l)"
  proof (intro allI impI)
    fix l assume l: "l \<le> Suc k"
    show "sgn (poly Q (u l)) = (-1) ^ (Suc k - l)"
    proof (cases "l = 0")
      case True
      have "a' \<le> a" unfolding a'_def by simp
      then show ?thesis using a True u0 by simp
    next
      case lz: False
      show ?thesis
      proof (cases "l = Suc k")
        case True
        have "b \<le> b'" unfolding b'_def by simp
        then show ?thesis using b True uk1 by simp
      next
        case False
        with l lz obtain j where j: "l = Suc j" "j < k" by (cases l) auto
        have "sgn (poly Q (ss ! j)) = (-1) ^ (length ss - j)"
          unfolding Q_def using hl_sgn_Q_at[OF assms(1,2)] j(2) k_def by simp
        then show ?thesis using j uj k_def by simp
      qed
    qed
  qed
  have roots: "\<forall>l\<in>{..k}. \<exists>t. u l < t \<and> t < u (Suc l) \<and> poly Q t = 0"
  proof
    fix l assume "l \<in> {..k}"
    then have l: "l \<le> k" by simp
    have s1: "sgn (poly Q (u l)) = (-1) ^ Suc (k - l)"
      using sgnu l by (simp add: Suc_diff_le)
    have s2: "sgn (poly Q (u (Suc l))) = (-1) ^ (k - l)"
      using sgnu l by simp
    have ne: "poly Q (u (Suc l)) \<noteq> 0"
    proof
      assume "poly Q (u (Suc l)) = 0"
      then have "sgn (poly Q (u (Suc l))) = 0" by simp
      with s2 show False by simp
    qed
    have "poly Q (u l) * poly Q (u (Suc l)) < 0"
      by (rule hl_opp_sgn_neg[OF _ ne]) (simp add: s1 s2)
    from poly_IVT[OF _ this] step l show "\<exists>t. u l < t \<and> t < u (Suc l) \<and> poly Q t = 0" by auto
  qed
  obtain f where f: "\<forall>l\<in>{..k}. u l < f l \<and> f l < u (Suc l) \<and> poly Q (f l) = 0"
    using bchoice[OF roots] by blast
  define ts where "ts = map f [0..<Suc k]"
  have lts: "length ts = Suc k" unfolding ts_def by simp
  have tsn: "\<And>l. l \<le> k \<Longrightarrow> ts ! l = f l"
  proof -
    fix l assume l: "l \<le> k"
    have l2: "l < Suc k - 0" using l by simp
    show "ts ! l = f l" unfolding ts_def using nth_map_upt[OF l2, of f] by simp
  qed
  have mono: "\<forall>j\<le>Suc k. \<forall>i<j. u i < u j" by (rule hl_strict_steps[OF step])
  have fmono: "\<And>i j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> f i < f j"
  proof -
    fix i j assume ij: "i < j" "j \<le> k"
    have "f i < u (Suc i)" using f ij by simp
    also have "u (Suc i) \<le> u j"
    proof (cases "Suc i = j")
      case True then show ?thesis by simp
      next
      case False
      with ij have "Suc i < j" by simp
      then show ?thesis using mono ij(2) by (simp add: less_imp_le)
    qed
    also have "u j < f j" using f ij by simp
    finally show "f i < f j" .
  qed
  have sorted_ts: "sorted_wrt (<) ts"
    unfolding sorted_wrt_iff_nth_less
  proof (intro allI impI)
    fix i j assume "i < j" "j < length ts"
    then show "ts ! i < ts ! j" using fmono tsn lts by simp
  qed
  have dist: "distinct ts" using sorted_ts by (simp add: strict_sorted_iff)
  have inter: "\<forall>j<length ss. ts ! j < ss ! j \<and> ss ! j < ts ! Suc j"
  proof (intro allI impI)
    fix j assume j: "j < length ss"
    then have jk: "j < k" using k_def by simp
    have "ts ! j = f j" using tsn jk by simp
    moreover have "ts ! Suc j = f (Suc j)" using tsn jk by simp
    moreover have "f j < u (Suc j)" using f jk by simp
    moreover have "u (Suc j) < f (Suc j)"
    proof -
      have mem: "Suc j \<in> {..k}" using jk by simp
      show ?thesis using bspec[OF f mem] by simp
    qed
    ultimately show "ts ! j < ss ! j \<and> ss ! j < ts ! Suc j" using uj[OF jk] by simp
  qed
  have eq: "Q = lin_prod ts"
  proof (rule poly_eqI_degree_lead_coeff[where n = "Suc k" and A = "set ts"])
    show "poly.coeff Q (Suc k) = poly.coeff (lin_prod ts) (Suc k)"
    proof -
      have a1: "poly.coeff Q (Suc k) = lead_coeff Q" by (simp add: dQ)
      have dl: "degree (lin_prod ts) = Suc k" using lts by simp
      have a2: "poly.coeff (lin_prod ts) (Suc k) = lead_coeff (lin_prod ts)"
        by (simp add: dl lts)
      have a3: "lead_coeff (lin_prod ts) = 1" by (rule lead_coeff_lin_prod)
      show ?thesis using a1 a2 a3 lQ by simp
    qed
    show "Suc k \<le> card (set ts)" using dist lts by (simp add: distinct_card)
    show "degree Q \<le> Suc k" using dQ by simp
    show "degree (lin_prod ts) \<le> Suc k" using lts by simp
    fix z assume "z \<in> set ts"
    then obtain l where l: "l < Suc k" "z = ts ! l" by (auto simp: in_set_conv_nth lts)
    have "poly Q z = 0" using f l tsn by auto
    moreover have "poly (lin_prod ts) z = 0" using hl_lin_prod_root_zero \<open>z \<in> set ts\<close> by simp
    ultimately show "poly Q z = poly (lin_prod ts) z" by simp
  qed
  show ?thesis
    apply (rule exI[where x = ts])
    using sorted_ts lts inter eq QE k_def by simp
qed


text \<open>Lagrange interpolation at distinct nodes.\<close>

lemma lagrange_cone:
  assumes "distinct ts" and "degree p < length ts"
  shows "p = (\<Sum>l<length ts. smult (poly p (ts ! l) / poly (lin_prod (omit l ts)) (ts ! l)) (lin_prod (omit l ts)))"
proof -
  let ?n = "length ts"
  let ?R = "\<Sum>l<?n. smult (poly p (ts ! l) / poly (lin_prod (omit l ts)) (ts ! l)) (lin_prod (omit l ts))"
  have npos: "0 < ?n" using assms(2) by linarith
  have degR: "degree ?R < ?n"
  proof -
    have "degree ?R \<le> ?n - 1"
      by (rule degree_sum_le) (auto intro!: order_trans[OF degree_smult_le] simp: length_omit)
    with npos show ?thesis by arith
  qed
  have card: "card (set ts) = ?n" using assms(1) by (simp add: distinct_card)
  have "poly p x = poly ?R x" if "x \<in> set ts" for x
  proof -
    from that obtain j where j: "j < ?n" "x = ts ! j" by (auto simp: in_set_conv_nth)
    have "poly ?R x = (\<Sum>l<?n. poly p (ts ! l) / poly (lin_prod (omit l ts)) (ts ! l) * poly (lin_prod (omit l ts)) x)"
      by (simp add: poly_sum)
    also have "\<dots> = (\<Sum>l\<in>{j}. poly p (ts ! l) / poly (lin_prod (omit l ts)) (ts ! l) * poly (lin_prod (omit l ts)) x)"
      using j assms(1) by (intro sum.mono_neutral_right) (auto simp: poly_omit_zero)
    also have "\<dots> = poly p x"
      using poly_omit_zero[OF assms(1) j(1) j(1)] j by simp
    finally show ?thesis by simp
  qed
  then show ?thesis
    by (intro poly_eqI_degree[of "set ts"]) (use card assms(2) degR in auto)
qed

lemma filter_split_aux:
  assumes "\<forall>x\<in>set A. \<not> P x" and "\<forall>x\<in>set B. P x"
  shows "filter P (A @ B) = B"
  using assms by (simp add: filter_empty_conv)

lemma sorted_wrt_nth_le_aux:
  assumes "sorted_wrt (<) (xs :: real list)" and "i \<le> j" and "j < length xs"
  shows "xs ! i \<le> xs ! j"
proof (cases "i = j")
  case True then show ?thesis by simp
next
  case False
  with assms have "i < j" by simp
  from sorted_wrt_nth_less[OF assms(1) this assms(3)] show ?thesis by simp
qed

lemma cone_sign_pos_aux:
  assumes "a \<noteq> 0" and "b \<noteq> 0" and "sgn a = sgn (b::real)"
  shows "0 < a / b"
proof -
  have "0 < a * b"
    using assms by (auto simp: sgn_real_def mult_pos_pos mult_neg_neg split: if_splits)
  moreover have "0 < b * b"
    using assms(2) by (simp add: power2_eq_square[symmetric])
  ultimately have "0 < a * b / (b * b)" by (rule divide_pos_pos)
  moreover have "a * b / (b * b) = a / b" using assms(2) by simp
  ultimately show ?thesis by simp
qed

lemma simple_case_cone:
  assumes "sorted_wrt (<) ss" and "sorted_wrt (<) ts" and "length ts = Suc (length ss)"
    and "\<forall>j<length ss. ts ! j < ss ! j \<and> ss ! j < ts ! Suc j"
  shows "in_cone (lin_prod ss) ts"
proof -
  define n where "n = length ss"
  have dist: "distinct ts" using assms(2) by (simp add: strict_sorted_iff)
  have deg: "degree (lin_prod ss) < length ts" using assms(3) by simp
  note lag = lagrange_cone[OF dist deg]
  have pos: "\<forall>l<length ts. 0 < poly (lin_prod ss) (ts ! l) / poly (lin_prod (omit l ts)) (ts ! l)"
  proof (intro allI impI)
    fix l assume l: "l < length ts"
    then have ln: "l \<le> n" using assms(3) n_def by simp
    have A: "\<forall>x\<in>set (take l ss). x < ts ! l"
    proof
      fix x assume "x \<in> set (take l ss)"
      then obtain j where j: "j < length (take l ss)" "x = take l ss ! j" by (auto simp: in_set_conv_nth)
      then have jl: "j < l" and jn: "j < length ss" using ln n_def by auto
      have "x = ss ! j" using j by simp
      also have "\<dots> < ts ! Suc j" using assms(4) jn by simp
      also have "\<dots> \<le> ts ! l" using sorted_wrt_nth_le_aux[OF assms(2) _ l] jl by simp
      finally show "x < ts ! l" .
    qed
    have B: "\<forall>x\<in>set (drop l ss). ts ! l < x"
    proof
      fix x assume "x \<in> set (drop l ss)"
      then obtain i where i: "i < length (drop l ss)" "x = drop l ss ! i" by (auto simp: in_set_conv_nth)
      then have il: "l + i < length ss" by simp
      have xe: "x = ss ! (l + i)" using i by simp
      have "ts ! l \<le> ts ! (l + i)"
        using sorted_wrt_nth_le_aux[OF assms(2) _ ] il assms(3) by simp
      also have "\<dots> < ss ! (l + i)" using assms(4) il by simp
      finally show "ts ! l < x" using xe by simp
    qed
    have C: "\<forall>x\<in>set (take l ts). x < ts ! l"
    proof
      fix x assume "x \<in> set (take l ts)"
      then obtain j where j: "j < length (take l ts)" "x = take l ts ! j" by (auto simp: in_set_conv_nth)
      then have "j < l" using l by auto
      then show "x < ts ! l" using j sorted_wrt_nth_less[OF assms(2) _ l] by simp
    qed
    have D: "\<forall>x\<in>set (drop (Suc l) ts). ts ! l < x"
    proof
      fix x assume "x \<in> set (drop (Suc l) ts)"
      then obtain i where i: "i < length (drop (Suc l) ts)" "x = drop (Suc l) ts ! i"
        by (auto simp: in_set_conv_nth)
      then have il: "Suc l + i < length ts" by simp
      have "x = ts ! (Suc l + i)" using i by simp
      moreover have "ts ! l < ts ! (Suc l + i)"
        using sorted_wrt_nth_less[OF assms(2) _ il] by simp
      ultimately show "ts ! l < x" by simp
    qed
    have s1: "ts ! l \<notin> set ss"
    proof -
      have "set ss = set (take l ss) \<union> set (drop l ss)"
        by (metis append_take_drop_id set_append)
      then show ?thesis using A B by force
    qed
    have s2: "ts ! l \<notin> set (omit l ts)"
      unfolding omit_def using C D by force
    have f1: "filter (\<lambda>s. ts ! l < s) ss = drop l ss"
    proof -
      have "filter (\<lambda>s. ts ! l < s) (take l ss @ drop l ss) = drop l ss"
        by (rule filter_split_aux) (use A B in auto)
      then show ?thesis by simp
    qed
    have f2: "filter (\<lambda>s. ts ! l < s) (omit l ts) = drop (Suc l) ts"
      unfolding omit_def
      by (rule filter_split_aux) (use C D in auto)
    have e1: "sgn (poly (lin_prod ss) (ts ! l)) = (-1) ^ (n - l)"
      using sign_lin_prod[OF s1] f1 n_def by simp
    have e2: "sgn (poly (lin_prod (omit l ts)) (ts ! l)) = (-1) ^ (n - l)"
      using sign_lin_prod[OF s2] f2 assms(3) n_def by simp
    have nz1: "poly (lin_prod ss) (ts ! l) \<noteq> 0"
    proof
      assume "poly (lin_prod ss) (ts ! l) = 0"
      then have "sgn (poly (lin_prod ss) (ts ! l)) = 0" by simp
      with e1 show False by simp
    qed
    have nz2: "poly (lin_prod (omit l ts)) (ts ! l) \<noteq> 0"
    proof
      assume "poly (lin_prod (omit l ts)) (ts ! l) = 0"
      then have "sgn (poly (lin_prod (omit l ts)) (ts ! l)) = 0" by simp
      with e2 show False by simp
    qed
    show "0 < poly (lin_prod ss) (ts ! l) / poly (lin_prod (omit l ts)) (ts ! l)"
      by (rule cone_sign_pos_aux[OF nz1 nz2]) (simp add: e1 e2)
  qed
  show ?thesis
    unfolding in_cone_def
    apply (rule exI[where x = "\<lambda>l. poly (lin_prod ss) (ts ! l) / poly (lin_prod (omit l ts)) (ts ! l)"])
    using pos lag by (auto simp: less_imp_le)
qed

section \<open>The cone step\<close>

theorem cone_step:
  assumes "in_cone S rs"
  shows "\<exists>ts. length ts = Suc (length rs) \<and> [:0, 1:] * lin_prod rs - S = lin_prod ts \<and> in_cone (lin_prod rs) ts"
proof -
  obtain qs ss C where ss: "sorted_wrt (<) ss" and Cpos: "\<forall>j<length ss. 0 < C j"
    and len: "length qs + length ss = length rs"
    and P: "lin_prod rs = lin_prod qs * lin_prod ss"
    and S: "S = lin_prod qs * (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss)))"
    using group_roots[OF assms] by blast
  obtain ts1 where ts1s: "sorted_wrt (<) ts1" and ts1l: "length ts1 = Suc (length ss)"
    and ts1i: "\<forall>j<length ss. ts1 ! j < ss ! j \<and> ss ! j < ts1 ! Suc j"
    and ts1q: "[:0, 1:] * lin_prod ss - (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss))) = lin_prod ts1"
    using simple_case_roots[OF ss Cpos] by blast
  have cone1: "in_cone (lin_prod ss) ts1" by (rule simple_case_cone[OF ss ts1s ts1l ts1i])
  have cone2: "in_cone (lin_prod qs * lin_prod ss) (qs @ ts1)" by (rule in_cone_prepend[OF cone1])
  have eq: "[:0, 1:] * lin_prod rs - S = lin_prod (qs @ ts1)"
  proof -
    have "[:0, 1:] * lin_prod rs - S
        = lin_prod qs * ([:0, 1:] * lin_prod ss - (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss))))"
      unfolding P S by (simp add: algebra_simps)
    also have "\<dots> = lin_prod qs * lin_prod ts1" by (simp only: ts1q)
    also have "\<dots> = lin_prod (qs @ ts1)" by (simp only: lin_prod_append)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule exI[where x = "qs @ ts1"]) (use len ts1l eq cone2 P in simp)
qed

end
