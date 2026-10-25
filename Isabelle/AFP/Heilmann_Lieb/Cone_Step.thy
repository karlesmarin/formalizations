(*  Title:      Cone_Step.thy
    Author:     Carles Marín

The analytic core of the Heilmann--Lieb theorem: subtracting an element of the cone from x times a product of
real linear factors gives again a product of real linear factors, which interlaces the first one.
Plan: PLAN_cone_step.md.
*)

theory Cone_Step
  imports Interlacing
begin

section \<open>Multiplying by common factors\<close>

lemma in_cone_prepend: "in_cone p ts \<Longrightarrow> in_cone (lin_prod qs * p) (qs @ ts)"
  sorry

section \<open>Grouping repeated roots\<close>

text \<open>Every element of the cone of \<open>rs\<close> can be written with a common factor \<open>R\<close> taken out, over a strictly
  increasing list of distinct roots with strictly positive weights.\<close>

lemma group_roots:
  assumes "in_cone S rs"
  shows "\<exists>qs ss C. sorted_wrt (<) ss \<and> (\<forall>j<length ss. 0 < C j) \<and>
           length qs + length ss = length rs \<and>
           lin_prod rs = lin_prod qs * lin_prod ss \<and>
           S = lin_prod qs * (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss)))"
  sorry

section \<open>The simple case\<close>

text \<open>The sign of a product of linear factors at a point that is not a root: one minus sign for every root
  above the point.\<close>

lemma sign_lin_prod:
  assumes "x \<notin> set ss"
  shows "sgn (poly (lin_prod ss) x) = (-1) ^ length (filter (\<lambda>s. x < s) ss)"
  sorry

text \<open>With distinct roots \<open>s_1 < \<dots> < s_k\<close> and positive weights, \<open>x \<cdot> P_1 - S_1\<close> has \<open>k + 1\<close> real roots
  \<open>t_0 < s_1 < t_1 < \<dots> < s_k < t_k\<close>.\<close>

lemma simple_case_roots:
  assumes "sorted_wrt (<) ss" and "\<forall>j<length ss. 0 < C j"
  shows "\<exists>ts. sorted_wrt (<) ts \<and> length ts = Suc (length ss) \<and>
           (\<forall>j<length ss. ts ! j < ss ! j \<and> ss ! j < ts ! Suc j) \<and>
           [:0, 1:] * lin_prod ss - (\<Sum>j<length ss. smult (C j) (lin_prod (omit j ss))) = lin_prod ts"
  sorry

text \<open>Lagrange interpolation at distinct nodes.\<close>

lemma lagrange_cone:
  assumes "distinct ts" and "degree p < length ts"
  shows "p = (\<Sum>l<length ts. smult (poly p (ts ! l) / poly (lin_prod (omit l ts)) (ts ! l)) (lin_prod (omit l ts)))"
  sorry

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
  sorry

end
