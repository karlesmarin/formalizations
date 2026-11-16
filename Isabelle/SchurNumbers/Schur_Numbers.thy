(*  Title:      Schur_Numbers.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Schur numbers S(2) = 4 and S(3) = 13 (statements as in atlas-lean)
*)

theory Schur_Numbers
  imports Main
begin

section \<open>Definitions\<close>

text \<open>A $k$-colouring is a function \<open>c :: nat \<Rightarrow> nat\<close> with \<open>c n < k\<close> for all \<open>n\<close>
  (the analogue of \<open>c : \<nat> \<rightarrow> Fin k\<close>).  The number @{term "schur_forces k N"} says that every
  such colouring has a monochromatic solution of \<open>x + y = z\<close> with \<open>x, y, z \<in> [1, N]\<close>
  (\<open>x = y\<close> is allowed).\<close>

definition schur_forces :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "schur_forces k N \<longleftrightarrow>
    (\<forall>c :: nat \<Rightarrow> nat. (\<forall>n. c n < k) \<longrightarrow>
      (\<exists>x y z. 1 \<le> x \<and> x \<le> N \<and> 1 \<le> y \<and> y \<le> N \<and> 1 \<le> z \<and> z \<le> N \<and>
         x + y = z \<and> c x = c y \<and> c y = c z))"

definition schur_number :: "nat \<Rightarrow> nat" where
  "schur_number k = (if k < 1 then 0 else Inf {N. schur_forces k N} - 1)"

lemma schur_forces_mono: "schur_forces k N \<Longrightarrow> N \<le> N' \<Longrightarrow> schur_forces k N'"
  unfolding schur_forces_def
proof (intro allI impI)
  fix c :: "nat \<Rightarrow> nat"
  assume H: "\<forall>c :: nat \<Rightarrow> nat. (\<forall>n. c n < k) \<longrightarrow>
      (\<exists>x y z. 1 \<le> x \<and> x \<le> N \<and> 1 \<le> y \<and> y \<le> N \<and> 1 \<le> z \<and> z \<le> N \<and>
         x + y = z \<and> c x = c y \<and> c y = c z)"
  assume NN: "N \<le> N'" and ck: "\<forall>n. c n < k"
  from H ck obtain x y z where "1 \<le> x" "x \<le> N" "1 \<le> y" "y \<le> N" "1 \<le> z" "z \<le> N"
    "x + y = z" "c x = c y" "c y = c z" by blast
  with NN show "\<exists>x y z. 1 \<le> x \<and> x \<le> N' \<and> 1 \<le> y \<and> y \<le> N' \<and> 1 \<le> z \<and> z \<le> N' \<and>
         x + y = z \<and> c x = c y \<and> c y = c z"
    by (intro exI[of _ x] exI[of _ y] exI[of _ z]) auto
qed

text \<open>If \<open>N+1\<close> forces but \<open>N\<close> does not, then the Schur number is \<open>N\<close>.\<close>

lemma schur_number_eq:
  assumes k: "1 \<le> k" and up: "schur_forces k (Suc N)" and low: "\<not> schur_forces k N"
  shows "schur_number k = N"
proof -
  let ?S = "{M. schur_forces k M}"
  have ne: "?S \<noteq> {}" using up by auto
  have le: "Inf ?S \<le> Suc N" using up by (intro cInf_lower) auto
  have mem: "Inf ?S \<in> ?S" using Inf_nat_def1[OF ne] .
  have "\<not> Inf ?S \<le> N"
  proof
    assume "Inf ?S \<le> N"
    with mem have "schur_forces k N" using schur_forces_mono by auto
    with low show False by contradiction
  qed
  with le have "Inf ?S = Suc N" by simp
  with k show ?thesis unfolding schur_number_def by simp
qed

section \<open>Executable search with pruning\<close>

text \<open>\<open>viol c z\<close>: there is a monochromatic \<open>x + y = z\<close> with \<open>z\<close> the largest element.\<close>

definition viol :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "viol c z = list_ex (\<lambda>x. c x = c (z - x) \<and> c (z - x) = c z) [1..<z]"

text \<open>\<open>ext k m c n\<close>: the colouring \<open>c\<close> on \<open>[1, n]\<close> (assumed sum-free so far) extends to
  \<open>[1, n+m]\<close> without a monochromatic solution.  Colours of \<open>n+1, n+2, \<dots>\<close> are tried in
  order; a branch is cut as soon as the newest element closes a monochromatic solution.\<close>

primrec ext :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "ext k 0 c n = True"
| "ext k (Suc m) c n =
    list_ex (\<lambda>a. \<not> viol (c(n + 1 := a)) (n + 1) \<and> ext k m (c(n + 1 := a)) (n + 1)) [0..<k]"

lemma viol_cong:
  assumes "\<forall>i. 1 \<le> i \<longrightarrow> i \<le> z \<longrightarrow> c i = d i"
  shows "viol c z = viol d z"
proof -
  have "\<And>x. x \<in> set [1..<z] \<Longrightarrow> c x = d x \<and> c (z - x) = d (z - x)"
    using assms by auto
  moreover have "c z = d z" if "1 \<le> z" using assms that by auto
  ultimately show ?thesis
    unfolding viol_def list_ex_iff
    by (cases "z = 0") auto
qed

lemma viol_imp:
  assumes "viol d z"
  shows "\<exists>x y. 1 \<le> x \<and> 1 \<le> y \<and> x + y = z \<and> d x = d y \<and> d y = d z"
proof -
  from assms obtain x where x: "x \<in> set [1..<z]" "d x = d (z - x)" "d (z - x) = d z"
    unfolding viol_def list_ex_iff by blast
  then have "1 \<le> x" "x < z" by auto
  then show ?thesis using x by (intro exI[of _ x] exI[of _ "z - x"]) auto
qed

lemma ext_sound:
  "\<not> ext k m c n \<Longrightarrow> (\<forall>i. d i < k) \<Longrightarrow> (\<forall>i. 1 \<le> i \<longrightarrow> i \<le> n \<longrightarrow> d i = c i) \<Longrightarrow>
    (\<exists>z. z \<le> n + m \<and> viol d z)"
proof (induction m arbitrary: c n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  let ?a = "d (n + 1)"
  have a: "?a \<in> set [0..<k]" using Suc.prems(2) by auto
  from Suc.prems(1) have no:
    "\<forall>a\<in>set [0..<k]. viol (c(n + 1 := a)) (n + 1) \<or> \<not> ext k m (c(n + 1 := a)) (n + 1)"
    by (simp add: list_ex_iff)
  from no a have cases:
    "viol (c(n + 1 := ?a)) (n + 1) \<or> \<not> ext k m (c(n + 1 := ?a)) (n + 1)" by blast
  have agree: "\<forall>i. 1 \<le> i \<longrightarrow> i \<le> n + 1 \<longrightarrow> d i = (c(n + 1 := ?a)) i"
    using Suc.prems(3) by auto
  show ?case
  proof (rule disjE[OF cases])
    assume vc: "viol (c(n + 1 := ?a)) (n + 1)"
    have agree': "\<forall>i. 1 \<le> i \<longrightarrow> i \<le> n + 1 \<longrightarrow> (c(n + 1 := ?a)) i = d i"
      using agree by metis
    have e: "viol (c(n + 1 := ?a)) (n + 1) = viol d (n + 1)" by (rule viol_cong[OF agree'])
    from e vc have "viol d (n + 1)" by simp
    then show ?thesis by (intro exI[of _ "n + 1"]) auto
  next
    assume "\<not> ext k m (c(n + 1 := ?a)) (n + 1)"
    from Suc.IH[OF this Suc.prems(2) agree] show ?thesis by auto
  qed
qed

lemma forces_of_ext:
  assumes "\<not> ext k N (\<lambda>_. 0) 0"
  shows "schur_forces k N"
  unfolding schur_forces_def
proof (intro allI impI)
  fix d :: "nat \<Rightarrow> nat"
  assume dk: "\<forall>n. d n < k"
  from ext_sound[OF assms dk] obtain z where z: "z \<le> 0 + N" "viol d z" by auto
  from viol_imp[OF z(2)] obtain x y where "1 \<le> x" "1 \<le> y" "x + y = z" "d x = d y" "d y = d z"
    by blast
  with z(1) show "\<exists>x y z. 1 \<le> x \<and> x \<le> N \<and> 1 \<le> y \<and> y \<le> N \<and> 1 \<le> z \<and> z \<le> N \<and>
         x + y = z \<and> d x = d y \<and> d y = d z"
    by (intro exI[of _ x] exI[of _ y] exI[of _ z]) auto
qed

section \<open>Lower bounds: explicit sum-free colourings\<close>

text \<open>A colouring that is sum-free on \<open>[1, N]\<close> (checked by evaluation) refutes forcing at \<open>N\<close>.\<close>

lemma not_forces_of_free:
  assumes "\<forall>n. c n < k"
    and "\<forall>x\<in>set [1..<N+1]. \<forall>y\<in>set [1..<N+1]. x + y \<le> N \<longrightarrow> \<not> (c x = c y \<and> c y = c (x + y))"
  shows "\<not> schur_forces k N"
proof
  assume "schur_forces k N"
  then obtain x y z where
    "1 \<le> x" "x \<le> N" "1 \<le> y" "y \<le> N" "1 \<le> z" "z \<le> N" "x + y = z" "c x = c y" "c y = c z"
    using assms(1) unfolding schur_forces_def by blast
  then have xm: "x \<in> set [1..<N+1]" and ym: "y \<in> set [1..<N+1]"
    and xy: "x + y \<le> N" and eq: "c x = c y \<and> c y = c (x + y)" by auto
  from assms(2) xm ym xy eq show False by blast
qed

definition col2 :: "nat \<Rightarrow> nat" where
  "col2 n = (if n \<in> {1, 4} then 0 else 1)"

definition col3 :: "nat \<Rightarrow> nat" where
  "col3 n = (if n \<in> {1, 4, 10, 13} then 0 else if n \<in> {2, 3, 11, 12} then 1 else 2)"

lemma col2_lt: "col2 n < 2" unfolding col2_def by simp
lemma col3_lt: "col3 n < 3" unfolding col3_def by simp

lemma free2: "\<not> schur_forces 2 4"
proof (rule not_forces_of_free[where c = col2])
  show "\<forall>n. col2 n < 2" using col2_lt by blast
  show "\<forall>x\<in>set [1..<4+1]. \<forall>y\<in>set [1..<4+1]. x + y \<le> 4 \<longrightarrow>
      \<not> (col2 x = col2 y \<and> col2 y = col2 (x + y))"
    unfolding col2_def by eval
qed

lemma free3: "\<not> schur_forces 3 13"
proof (rule not_forces_of_free[where c = col3])
  show "\<forall>n. col3 n < 3" using col3_lt by blast
  show "\<forall>x\<in>set [1..<13+1]. \<forall>y\<in>set [1..<13+1]. x + y \<le> 13 \<longrightarrow>
      \<not> (col3 x = col3 y \<and> col3 y = col3 (x + y))"
    unfolding col3_def by eval
qed

section \<open>The theorems\<close>

lemma forces2: "schur_forces 2 5"
  by (rule forces_of_ext) eval

lemma forces3: "schur_forces 3 14"
  by (rule forces_of_ext) eval

theorem schur_two: "schur_number 2 = 4"
  by (rule schur_number_eq) (use forces2 free2 in simp_all)

theorem schur_three: "schur_number 3 = 13"
  by (rule schur_number_eq) (use forces3 free3 in simp_all)

end
