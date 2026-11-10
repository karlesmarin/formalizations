(*  Title:      Game_of_Life/Life_Base.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Life_Base
  imports Main
begin

section \<open>Conway's Game of Life on \<open>\<int>\<^sup>2\<close>\<close>

text \<open>
  A generation is an arbitrary (possibly infinite) set of live cells in \<open>\<int> \<times> \<int>\<close>.
  The Moore neighbourhood of a cell consists of the eight cells at Chebyshev distance one.
  The rule is B3/S23: a dead cell is born with exactly three live neighbours, a live cell
  survives with two or three.  Since every neighbourhood is finite, \<open>card\<close> counts correctly
  also when the generation is infinite.
\<close>

type_synonym cell = "int \<times> int"
type_synonym gen = "cell set"

definition nbhd :: "cell \<Rightarrow> cell set" where
  "nbhd c = {d. d \<noteq> c \<and> \<bar>fst d - fst c\<bar> \<le> 1 \<and> \<bar>snd d - snd c\<bar> \<le> 1}"

definition nbrs :: "gen \<Rightarrow> cell \<Rightarrow> nat" where
  "nbrs S c = card (S \<inter> nbhd c)"

definition step :: "gen \<Rightarrow> gen" where
  "step S = {c. if c \<in> S then nbrs S c = 2 \<or> nbrs S c = 3 else nbrs S c = 3}"

lemma mem_step: "c \<in> step S \<longleftrightarrow> (if c \<in> S then nbrs S c = 2 \<or> nbrs S c = 3 else nbrs S c = 3)"
  by (simp add: step_def)

lemma nbhd_sym: "d \<in> nbhd c \<longleftrightarrow> c \<in> nbhd d"
  by (auto simp: nbhd_def abs_minus_commute)

subsection \<open>Translations and an executable neighbourhood\<close>

definition tr :: "cell \<Rightarrow> cell \<Rightarrow> cell" where
  "tr v c = (fst c + fst v, snd c + snd v)"

definition transl :: "cell \<Rightarrow> gen \<Rightarrow> gen" where
  "transl v S = tr v ` S"

definition moore :: "cell list" where
  "moore = [(-1,-1), (-1,0), (-1,1), (0,-1), (0,1), (1,-1), (1,0), (1,1)]"

definition nbhd_list :: "cell \<Rightarrow> cell list" where
  "nbhd_list c = map (\<lambda>v. tr v c) moore"

lemma abs_le1_int: "\<bar>i::int\<bar> \<le> 1 \<longleftrightarrow> i = -1 \<or> i = 0 \<or> i = 1"
  by arith

lemma set_nbhd_list: "set (nbhd_list c) = nbhd c"
proof (cases c)
  case (Pair a b)
  have "d \<in> set (nbhd_list (a, b)) \<longleftrightarrow> d \<in> nbhd (a, b)" for d
  proof (cases d)
    case (Pair x y)
    have "(x, y) \<in> nbhd (a, b) \<longleftrightarrow> (x - a, y - b) \<noteq> (0, 0) \<and> \<bar>x - a\<bar> \<le> 1 \<and> \<bar>y - b\<bar> \<le> 1"
      by (auto simp: nbhd_def)
    also have "\<dots> \<longleftrightarrow> (x - a, y - b) \<in> set moore"
      unfolding abs_le1_int by (auto simp: moore_def)
    also have "\<dots> \<longleftrightarrow> (x, y) \<in> set (nbhd_list (a, b))"
      by (force simp: nbhd_list_def tr_def)
    finally show ?thesis using Pair by simp
  qed
  then show ?thesis using Pair by blast
qed

lemma finite_nbhd [simp]: "finite (nbhd c)"
  by (metis List.finite_set set_nbhd_list)

lemma distinct_nbhd_list: "distinct (nbhd_list c)"
  by (cases c) (simp add: nbhd_list_def moore_def tr_def)

section \<open>Equivariance\<close>

text \<open>Every bijection of the plane that preserves the neighbourhood relation commutes with \<open>step\<close>.\<close>

theorem step_equivariant:
  assumes "bij f" and nb: "\<And>c d. f d \<in> nbhd (f c) \<longleftrightarrow> d \<in> nbhd c"
  shows "step (f ` S) = f ` step S"
proof -
  have inj: "inj f" using assms(1) by (rule bij_is_inj)
  have card: "nbrs (f ` S) (f c) = nbrs S c" for c
  proof -
    have "f ` S \<inter> nbhd (f c) = f ` (S \<inter> nbhd c)"
      using inj by (auto simp: nb)
    then show ?thesis
      unfolding nbrs_def by (metis card_image inj inj_on_subset top_greatest)
  qed
  have mem: "f c \<in> step (f ` S) \<longleftrightarrow> c \<in> step S" for c
    using card[of c] inj by (simp add: mem_step inj_image_mem_iff)
  show ?thesis
  proof (intro set_eqI iffI)
    fix x assume x: "x \<in> step (f ` S)"
    obtain c where "x = f c" using assms(1) by (metis bij_pointE)
    then show "x \<in> f ` step S" using x mem by blast
  next
    fix x assume "x \<in> f ` step S"
    then show "x \<in> step (f ` S)" using mem by blast
  qed
qed

corollary steps_equivariant:
  assumes "bij f" "\<And>c d. f d \<in> nbhd (f c) \<longleftrightarrow> d \<in> nbhd c"
  shows "(step ^^ n) (f ` S) = f ` (step ^^ n) S"
  by (induction n) (simp_all add: step_equivariant[OF assms])

lemma bij_tr: "bij (tr v)"
  by (rule o_bij[of "tr (- fst v, - snd v)"]) (auto simp: tr_def fun_eq_iff)

lemma nbhd_tr: "tr v d \<in> nbhd (tr v c) \<longleftrightarrow> d \<in> nbhd c"
  by (auto simp: nbhd_def tr_def prod_eq_iff)

theorem step_transl: "step (transl v S) = transl v (step S)"
  unfolding transl_def by (rule step_equivariant[OF bij_tr nbhd_tr])

theorem steps_transl: "(step ^^ n) (transl v S) = transl v ((step ^^ n) S)"
  unfolding transl_def by (rule steps_equivariant[OF bij_tr nbhd_tr])

text \<open>The two generators of the symmetry group \<open>D\<^sub>4\<close> of the square: the quarter turn and the
  reflection in the diagonal.  Every element of \<open>D\<^sub>4\<close> is a composition of these, and
  \<open>step_equivariant\<close> applies to each composition (its hypotheses are closed under composition).\<close>

definition rot :: "cell \<Rightarrow> cell" where "rot c = (- snd c, fst c)"
definition flip :: "cell \<Rightarrow> cell" where "flip c = (snd c, fst c)"

lemma bij_rot: "bij rot"
  by (rule o_bij[of "\<lambda>c. (snd c, - fst c)"]) (auto simp: rot_def fun_eq_iff)

lemma bij_flip: "bij flip"
  by (rule o_bij[of flip]) (auto simp: flip_def fun_eq_iff)

lemma nbhd_rot: "rot d \<in> nbhd (rot c) \<longleftrightarrow> d \<in> nbhd c"
  by (auto simp: nbhd_def rot_def prod_eq_iff abs_minus_commute)

lemma nbhd_flip: "flip d \<in> nbhd (flip c) \<longleftrightarrow> d \<in> nbhd c"
  by (auto simp: nbhd_def flip_def prod_eq_iff)

theorem step_rot: "step (rot ` S) = rot ` step S"
  by (rule step_equivariant[OF bij_rot nbhd_rot])

theorem step_flip: "step (flip ` S) = flip ` step S"
  by (rule step_equivariant[OF bij_flip nbhd_flip])

lemma nbhd_comp:
  assumes "\<And>c d. f d \<in> nbhd (f c) \<longleftrightarrow> d \<in> nbhd c" "\<And>c d. g d \<in> nbhd (g c) \<longleftrightarrow> d \<in> nbhd c"
  shows "(f \<circ> g) d \<in> nbhd ((f \<circ> g) c) \<longleftrightarrow> d \<in> nbhd c"
  using assms by simp

section \<open>Locality (finite speed of light) and finiteness\<close>

text \<open>\<open>dil r R\<close>: the region \<open>R\<close> thickened by \<open>r\<close> cells in the Chebyshev (max) norm.\<close>

definition dil :: "nat \<Rightarrow> cell set \<Rightarrow> cell set" where
  "dil r R = {d. \<exists>c\<in>R. \<bar>fst d - fst c\<bar> \<le> int r \<and> \<bar>snd d - snd c\<bar> \<le> int r}"

lemma subset_dil: "R \<subseteq> dil r R"
proof
  fix d assume "d \<in> R"
  then show "d \<in> dil r R" unfolding dil_def by (intro CollectI bexI[of _ d]) auto
qed

lemma nbhd_subset_dil1: "c \<in> R \<Longrightarrow> nbhd c \<subseteq> dil 1 R"
  by (auto simp: dil_def nbhd_def)

lemma dil_dil1: "dil t (dil 1 R) \<subseteq> dil (Suc t) R"
proof
  fix d assume "d \<in> dil t (dil 1 R)"
  then obtain e c where "c \<in> R" "\<bar>fst d - fst e\<bar> \<le> int t" "\<bar>snd d - snd e\<bar> \<le> int t"
    "\<bar>fst e - fst c\<bar> \<le> 1" "\<bar>snd e - snd c\<bar> \<le> 1"
    by (auto simp: dil_def)
  then show "d \<in> dil (Suc t) R"
    unfolding dil_def by (intro CollectI bexI[of _ c]) auto
qed

lemma agree_mono: "A \<subseteq> B \<Longrightarrow> S \<inter> B = S' \<inter> B \<Longrightarrow> S \<inter> A = S' \<inter> A"
  by blast

lemma locality_step:
  assumes "S \<inter> dil 1 R = S' \<inter> dil 1 R"
  shows "step S \<inter> R = step S' \<inter> R"
proof -
  have "c \<in> step S \<longleftrightarrow> c \<in> step S'" if "c \<in> R" for c
  proof -
    have "S \<inter> nbhd c = S' \<inter> nbhd c"
      using agree_mono[OF nbhd_subset_dil1[OF that] assms] .
    moreover have "c \<in> S \<longleftrightarrow> c \<in> S'"
      using assms subset_dil[of R 1] that by blast
    ultimately show ?thesis by (simp add: mem_step nbrs_def)
  qed
  then show ?thesis by blast
qed

text \<open>The cone lemma: after \<open>t\<close> generations, the state on \<open>R\<close> depends only on the initial state
  on \<open>R\<close> thickened by \<open>t\<close>.\<close>

theorem locality:
  assumes "S \<inter> dil t R = S' \<inter> dil t R"
  shows "(step ^^ t) S \<inter> R = (step ^^ t) S' \<inter> R"
  using assms
proof (induction t arbitrary: R)
  case 0
  then show ?case using agree_mono[OF subset_dil[of R 0] "0.prems"] by simp
next
  case (Suc t)
  have "S \<inter> dil t (dil 1 R) = S' \<inter> dil t (dil 1 R)"
    using agree_mono[OF dil_dil1 Suc.prems] .
  then have "(step ^^ t) S \<inter> dil 1 R = (step ^^ t) S' \<inter> dil 1 R"
    by (rule Suc.IH)
  then have "step ((step ^^ t) S) \<inter> R = step ((step ^^ t) S') \<inter> R"
    by (rule locality_step)
  then show ?case by simp
qed

corollary locality_restrict: "(step ^^ t) S \<inter> R = (step ^^ t) (S \<inter> dil t R) \<inter> R"
  by (rule locality) blast

lemma step_empty [simp]: "step {} = {}"
  by (simp add: step_def nbrs_def)

lemma steps_empty [simp]: "(step ^^ n) {} = {}"
  by (induction n) simp_all

lemma step_subset: "step S \<subseteq> S \<union> \<Union> (nbhd ` S)"
proof
  fix c assume c: "c \<in> step S"
  show "c \<in> S \<union> \<Union> (nbhd ` S)"
  proof (cases "c \<in> S")
    case False
    then have "card (S \<inter> nbhd c) = 3" using c by (simp add: mem_step nbrs_def)
    then obtain d where "d \<in> S" "d \<in> nbhd c" by (metis card.empty disjoint_iff zero_neq_numeral)
    then show ?thesis using nbhd_sym by blast
  qed simp
qed

lemma step_subset_dil: "step S \<subseteq> dil 1 S"
  using step_subset subset_dil[of S 1] nbhd_subset_dil1[of _ S] by blast

theorem finite_step: "finite S \<Longrightarrow> finite (step S)"
  by (rule finite_subset[OF step_subset]) auto

corollary finite_steps: "finite S \<Longrightarrow> finite ((step ^^ n) S)"
  by (induction n) (simp_all add: finite_step)

section \<open>An executable simulator and certified trace replay\<close>

text \<open>A finite generation is represented by a list of its live cells (repetitions allowed).
  The candidate cells of the next generation are the live cells and their neighbours.\<close>

definition cnt :: "cell list \<Rightarrow> cell \<Rightarrow> nat" where
  "cnt xs c = length (filter (\<lambda>d. d \<in> set xs) (nbhd_list c))"

definition alive :: "cell list \<Rightarrow> cell \<Rightarrow> bool" where
  "alive xs c = (if c \<in> set xs then cnt xs c = 2 \<or> cnt xs c = 3 else cnt xs c = 3)"

definition sim_step :: "cell list \<Rightarrow> cell list" where
  "sim_step xs = filter (alive xs) (remdups (xs @ concat (map nbhd_list xs)))"

lemma cnt_correct: "cnt xs c = nbrs (set xs) c"
proof -
  have "cnt xs c = card ({d. d \<in> set xs} \<inter> set (nbhd_list c))"
    unfolding cnt_def by (rule distinct_length_filter[OF distinct_nbhd_list])
  also have "{d. d \<in> set xs} \<inter> set (nbhd_list c) = set xs \<inter> nbhd c"
    by (auto simp: set_nbhd_list)
  finally show ?thesis by (simp add: nbrs_def)
qed

theorem sim_step_correct: "set (sim_step xs) = step (set xs)"
proof -
  have "set (sim_step xs) = {c \<in> set xs \<union> \<Union> (nbhd ` set xs). c \<in> step (set xs)}"
    by (auto simp: sim_step_def alive_def cnt_correct mem_step set_nbhd_list)
  also have "\<dots> = step (set xs)"
    using step_subset[of "set xs"] by blast
  finally show ?thesis .
qed

theorem sim_steps_correct: "set ((sim_step ^^ n) xs) = (step ^^ n) (set xs)"
  by (induction n) (simp_all add: sim_step_correct)

definition same_set :: "cell list \<Rightarrow> cell list \<Rightarrow> bool" where
  "same_set xs ys = (list_all (\<lambda>x. x \<in> set ys) xs \<and> list_all (\<lambda>y. y \<in> set xs) ys)"

lemma same_set_correct: "same_set xs ys \<longleftrightarrow> set xs = set ys"
  by (auto simp: same_set_def list_all_iff)

text \<open>Trace replay: an untrusted simulator proposes each intermediate generation; the checker
  verifies every single transition.\<close>

fun trace_ok :: "cell list \<Rightarrow> cell list list \<Rightarrow> bool" where
  "trace_ok xs [] = True"
| "trace_ok xs (ys # yss) = (same_set (sim_step xs) ys \<and> trace_ok ys yss)"

theorem trace_ok_correct:
  "trace_ok xs yss \<Longrightarrow> (step ^^ length yss) (set xs) = set (last (xs # yss))"
proof (induction yss arbitrary: xs)
  case (Cons ys yss)
  then have "step (set xs) = set ys" "(step ^^ length yss) (set ys) = set (last (ys # yss))"
    by (simp_all add: same_set_correct sim_step_correct)
  then show ?case by (simp add: funpow_Suc_right del: funpow.simps)
qed simp

lemma transl_set: "transl v (set xs) = set (map (tr v) xs)"
  by (simp add: transl_def)

section \<open>A translation invariant: the difference set\<close>

definition diffs :: "gen \<Rightarrow> cell set" where
  "diffs S = {(fst a - fst b, snd a - snd b) | a b. a \<in> S \<and> b \<in> S}"

lemma diffs_transl: "diffs (transl v S) = diffs S"
proof (intro set_eqI iffI)
  fix d assume "d \<in> diffs (transl v S)"
  then obtain a b where ab: "a \<in> S" "b \<in> S"
    "d = (fst (tr v a) - fst (tr v b), snd (tr v a) - snd (tr v b))"
    unfolding diffs_def transl_def by blast
  then have "d = (fst a - fst b, snd a - snd b)" by (simp add: tr_def)
  then show "d \<in> diffs S" using ab(1,2) unfolding diffs_def by blast
next
  fix d assume "d \<in> diffs S"
  then obtain a b where ab: "a \<in> S" "b \<in> S" "d = (fst a - fst b, snd a - snd b)"
    unfolding diffs_def by blast
  then have "d = (fst (tr v a) - fst (tr v b), snd (tr v a) - snd (tr v b))" by (simp add: tr_def)
  moreover have "tr v a \<in> transl v S" "tr v b \<in> transl v S" using ab(1,2) by (simp_all add: transl_def)
  ultimately show "d \<in> diffs (transl v S)" unfolding diffs_def by blast
qed

definition diffs_list :: "cell list \<Rightarrow> cell list" where
  "diffs_list xs = concat (map (\<lambda>a. map (\<lambda>b. (fst a - fst b, snd a - snd b)) xs) xs)"

lemma set_diffs_list: "set (diffs_list xs) = diffs (set xs)"
proof (intro set_eqI iffI)
  fix d assume "d \<in> set (diffs_list xs)"
  then obtain a b where "a \<in> set xs" "b \<in> set xs" "d = (fst a - fst b, snd a - snd b)"
    unfolding diffs_list_def by auto
  then show "d \<in> diffs (set xs)" unfolding diffs_def by blast
next
  fix d assume "d \<in> diffs (set xs)"
  then obtain a b where "a \<in> set xs" "b \<in> set xs" "d = (fst a - fst b, snd a - snd b)"
    unfolding diffs_def by blast
  then show "d \<in> set (diffs_list xs)" unfolding diffs_list_def by auto
qed

lemma not_transl_by_diffs:
  "\<not> same_set (diffs_list xs) (diffs_list ys) \<Longrightarrow> set ys \<noteq> transl v (set xs)"
  by (metis diffs_transl same_set_correct set_diffs_list)

end
