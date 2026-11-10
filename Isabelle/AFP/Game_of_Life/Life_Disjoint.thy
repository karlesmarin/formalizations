(*  Title:      Game_of_Life/Life_Disjoint.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Life_Disjoint
  imports Life_Base
begin

section \<open>Disjoint evolution\<close>

text \<open>Two patterns whose 1-thickenings are disjoint evolve independently for one generation;
  iterated, two patterns whose \<open>t\<close>-thickenings are disjoint (Chebyshev distance at least
  \<open>2t + 1\<close>: the gap must shrink by at most 2 per generation) evolve independently for \<open>t\<close>
  generations.\<close>

lemma dil_mono: "A \<subseteq> B \<Longrightarrow> dil r A \<subseteq> dil r B"
  unfolding dil_def by blast

lemma dil_le:
  assumes "r \<le> s"
  shows "dil r A \<subseteq> dil s A"
proof
  fix d assume "d \<in> dil r A"
  then obtain c where c: "c \<in> A" "\<bar>fst d - fst c\<bar> \<le> int r" "\<bar>snd d - snd c\<bar> \<le> int r"
    unfolding dil_def by blast
  have "int r \<le> int s" using assms by simp
  then show "d \<in> dil s A" unfolding dil_def using c by (intro CollectI bexI[of _ c]) auto
qed

lemma dil_dil: "dil a (dil b R) \<subseteq> dil (a + b) R"
proof
  fix d assume "d \<in> dil a (dil b R)"
  then obtain e c where "c \<in> R" "\<bar>fst d - fst e\<bar> \<le> int a" "\<bar>snd d - snd e\<bar> \<le> int a"
    "\<bar>fst e - fst c\<bar> \<le> int b" "\<bar>snd e - snd c\<bar> \<le> int b"
    by (auto simp: dil_def)
  then show "d \<in> dil (a + b) R"
    unfolding dil_def by (intro CollectI bexI[of _ c]) auto
qed

lemma steps_subset_dil: "(step ^^ k) S \<subseteq> dil k S"
proof (induction k)
  case 0
  show ?case by (simp add: subset_dil)
next
  case (Suc k)
  have "(step ^^ Suc k) S \<subseteq> dil 1 ((step ^^ k) S)"
    using step_subset_dil by simp
  also have "\<dots> \<subseteq> dil 1 (dil k S)"
    by (rule dil_mono[OF Suc.IH])
  also have "\<dots> \<subseteq> dil (1 + k) S"
    by (rule dil_dil)
  finally show ?case by simp
qed

lemma outside_dil1: "c \<notin> dil 1 S \<Longrightarrow> S \<inter> nbhd c = {} \<and> c \<notin> S"
  using subset_dil[of S 1] nbhd_subset_dil1[of _ S] nbhd_sym by blast

lemma step_union_local:
  assumes "S' \<inter> nbhd c = {}" "c \<notin> S'"
  shows "c \<in> step (S \<union> S') \<longleftrightarrow> c \<in> step S"
proof -
  have "(S \<union> S') \<inter> nbhd c = S \<inter> nbhd c" using assms(1) by blast
  then show ?thesis using assms(2) by (simp add: mem_step nbrs_def)
qed

theorem disjoint_step:
  assumes "dil 1 S \<inter> dil 1 S' = {}"
  shows "step (S \<union> S') = step S \<union> step S'"
proof (intro set_eqI)
  fix c
  show "c \<in> step (S \<union> S') \<longleftrightarrow> c \<in> step S \<union> step S'"
  proof (cases "c \<in> dil 1 S'")
    case True
    then have out: "c \<notin> dil 1 S" using assms by blast
    then have o: "S \<inter> nbhd c = {}" "c \<notin> S" using outside_dil1 by blast+
    have "c \<in> step (S' \<union> S) \<longleftrightarrow> c \<in> step S'"
      by (rule step_union_local[OF o])
    then have "c \<in> step (S \<union> S') \<longleftrightarrow> c \<in> step S'"
      by (simp only: Un_commute[of S' S])
    moreover have "c \<notin> step S" using out step_subset_dil by blast
    ultimately show ?thesis by blast
  next
    case False
    then have o: "S' \<inter> nbhd c = {}" "c \<notin> S'" using outside_dil1 by blast+
    have "c \<in> step (S \<union> S') \<longleftrightarrow> c \<in> step S"
      by (rule step_union_local[OF o])
    moreover have "c \<notin> step S'" using False step_subset_dil by blast
    ultimately show ?thesis by blast
  qed
qed

theorem disjoint_steps:
  assumes "\<forall>k<t. dil 1 ((step ^^ k) S) \<inter> dil 1 ((step ^^ k) S') = {}"
  shows "(step ^^ t) (S \<union> S') = (step ^^ t) S \<union> (step ^^ t) S'"
  using assms
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have ih: "(step ^^ t) (S \<union> S') = (step ^^ t) S \<union> (step ^^ t) S'"
    using Suc.prems by (intro Suc.IH) auto
  have "dil 1 ((step ^^ t) S) \<inter> dil 1 ((step ^^ t) S') = {}"
    using Suc.prems by simp
  then have "step ((step ^^ t) S \<union> (step ^^ t) S') = step ((step ^^ t) S) \<union> step ((step ^^ t) S')"
    by (rule disjoint_step)
  then show ?case using ih by simp
qed

corollary disjoint_steps_regions:
  assumes "\<forall>k<t. (step ^^ k) S \<subseteq> A k \<and> (step ^^ k) S' \<subseteq> B k \<and> dil 1 (A k) \<inter> dil 1 (B k) = {}"
  shows "(step ^^ t) (S \<union> S') = (step ^^ t) S \<union> (step ^^ t) S'"
proof (rule disjoint_steps, intro allI impI)
  fix k assume "k < t"
  then have h: "(step ^^ k) S \<subseteq> A k" "(step ^^ k) S' \<subseteq> B k" "dil 1 (A k) \<inter> dil 1 (B k) = {}"
    using assms by auto
  have "dil 1 ((step ^^ k) S) \<subseteq> dil 1 (A k)" "dil 1 ((step ^^ k) S') \<subseteq> dil 1 (B k)"
    using dil_mono[OF h(1)] dil_mono[OF h(2)] .
  then show "dil 1 ((step ^^ k) S) \<inter> dil 1 ((step ^^ k) S') = {}" using h(3) by blast
qed

lemma dil1_steps_le:
  assumes "k < t"
  shows "dil 1 ((step ^^ k) S) \<subseteq> dil t S"
proof -
  have "dil 1 ((step ^^ k) S) \<subseteq> dil 1 (dil k S)" by (rule dil_mono[OF steps_subset_dil])
  also have "\<dots> \<subseteq> dil (1 + k) S" by (rule dil_dil)
  also have "\<dots> \<subseteq> dil t S" using assms by (intro dil_le) simp
  finally show ?thesis .
qed

corollary disjoint_steps_dist:
  assumes "dil t S \<inter> dil t S' = {}"
  shows "(step ^^ t) (S \<union> S') = (step ^^ t) S \<union> (step ^^ t) S'"
proof (rule disjoint_steps, intro allI impI)
  fix k assume "k < t"
  then have "dil 1 ((step ^^ k) S) \<subseteq> dil t S" "dil 1 ((step ^^ k) S') \<subseteq> dil t S'"
    by (rule dil1_steps_le)+
  then show "dil 1 ((step ^^ k) S) \<inter> dil 1 ((step ^^ k) S') = {}" using assms by blast
qed

text \<open>An executable sufficient condition: every pair of cells is more than \<open>2r\<close> apart.\<close>

definition far :: "nat \<Rightarrow> cell list \<Rightarrow> cell list \<Rightarrow> bool" where
  "far r xs ys = list_all (\<lambda>a. list_all (\<lambda>b.
     int (2 * r) < \<bar>fst a - fst b\<bar> \<or> int (2 * r) < \<bar>snd a - snd b\<bar>) ys) xs"

lemma far_correct:
  assumes "far r xs ys"
  shows "dil r (set xs) \<inter> dil r (set ys) = {}"
proof (rule ccontr)
  assume "dil r (set xs) \<inter> dil r (set ys) \<noteq> {}"
  then obtain d a b where ab: "a \<in> set xs" "b \<in> set ys"
    and da: "\<bar>fst d - fst a\<bar> \<le> int r" "\<bar>snd d - snd a\<bar> \<le> int r"
    and db: "\<bar>fst d - fst b\<bar> \<le> int r" "\<bar>snd d - snd b\<bar> \<le> int r"
    unfolding dil_def by blast
  have "int (2 * r) < \<bar>fst a - fst b\<bar> \<or> int (2 * r) < \<bar>snd a - snd b\<bar>"
    using assms ab by (auto simp: far_def list_all_iff)
  then show False using da db by auto
qed

section \<open>Intermediate generations of a trace\<close>

lemma trace_ok_nth:
  "trace_ok xs yss \<Longrightarrow> k < length yss \<Longrightarrow> (step ^^ Suc k) (set xs) = set (yss ! k)"
proof (induction yss arbitrary: xs k)
  case Nil
  then show ?case by simp
next
  case (Cons ys yss)
  then have s: "step (set xs) = set ys" and t: "trace_ok ys yss"
    by (simp_all add: same_set_correct sim_step_correct)
  show ?case
  proof (cases k)
    case 0
    then show ?thesis using s by simp
  next
    case (Suc j)
    then have "j < length yss" using Cons.prems by simp
    then have "(step ^^ Suc j) (set ys) = set (yss ! j)" using Cons.IH[OF t] by blast
    then show ?thesis using s Suc by (simp add: funpow_Suc_right del: funpow.simps)
  qed
qed

end
