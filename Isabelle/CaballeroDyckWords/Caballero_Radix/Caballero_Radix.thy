(*  Title:      Caballero_Radix.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
*)

section \<open>Mixed radix and the maximal refinement: combinatorial core\<close>

theory Caballero_Radix
  imports Complex_Main "HOL-Library.Multiset"
begin

text \<open>
  Combinatorial core of the maximal-refinement theorem (Section 3 of the note on Rodríguez Caballero's
  parenthesis languages): the classical mixed-radix lemma, and the fact that the word \<open>w\<^sub>f(x)\<close> defined by
  the comparisons \<open>u\<^sub>a(x) < 1 + u\<^sub>b(x)\<close> is unchanged when the first coordinate \<open>x\<^sub>1\<close>, with index range
  \<open>{0..F}\<close>, \<open>F = (u+1)(v+1) - 1\<close>, is replaced by the two coordinates \<open>(x\<^sub>1, (u+1) x\<^sub>1)\<close> with index ranges
  \<open>{0..u}\<close> and \<open>{0..v}\<close>.

  The remaining indices \<open>a\<^sub>2, \<dots>, a\<^sub>s\<close> contribute a fixed real offset \<open>\<rho>(r)\<close> (index set \<open>R\<close>), so the
  statements hold for every \<open>s\<close> at once.

  \<^bold>\<open>Out of scope:\<close> the realisation of the word by an integer \<open>n\<close> (Lemma on realisation, via Bertrand's
  postulate and perturbation of \<open>y\<close>) is not formalised here. Neither is the characterisation of the arrangement
  of hyperplanes; only the transfer ``no two positions differ by exactly 1'' is proved.
\<close>

subsection \<open>The mixed-radix bijection\<close>

definition radix :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat" where
  "radix u = (\<lambda>(i, j). i + (u + 1) * j)"

lemma radix_mod: "(i::nat) \<le> u \<Longrightarrow> (i + (u + 1) * j) mod (u + 1) = i"
proof -
  assume "i \<le> u"
  hence lt: "i < u + 1" by simp
  have "(i + (u + 1) * j) mod (u + 1) = i mod (u + 1)" by (rule mod_mult_self2)
  also have "\<dots> = i" by (rule mod_less[OF lt])
  finally show ?thesis .
qed

lemma radix_div: "(i::nat) \<le> u \<Longrightarrow> (i + (u + 1) * j) div (u + 1) = j"
proof -
  assume iu: "i \<le> u"
  let ?N = "i + (u + 1) * j"
  have m: "?N mod (u + 1) = i" by (rule radix_mod[OF iu])
  have e: "?N mod (u + 1) + (u + 1) * (?N div (u + 1)) = ?N"
    using mult_div_mod_eq[of "u + 1" ?N] by linarith
  hence "(u + 1) * (?N div (u + 1)) = (u + 1) * j" using m by linarith
  thus ?thesis by (simp only: mult_cancel_left) simp
qed

lemma radix_le: "(i::nat) \<le> u \<Longrightarrow> j \<le> v \<Longrightarrow> i + (u + 1) * j \<le> (u + 1) * (v + 1) - 1"
proof -
  assume i: "i \<le> u" and j: "j \<le> v"
  have "(u + 1) * j \<le> (u + 1) * v" using j by (rule mult_left_mono) simp
  hence "i + (u + 1) * j \<le> u + (u + 1) * v" using i by linarith
  also have "\<dots> = (u + 1) * (v + 1) - 1" by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma radix_digits: "(N::nat) \<le> (u + 1) * (v + 1) - 1 \<Longrightarrow> N mod (u + 1) \<le> u \<and> N div (u + 1) \<le> v"
proof -
  assume N: "N \<le> (u + 1) * (v + 1) - 1"
  have pos: "(u + 1) * (v + 1) > (0::nat)" by simp
  have "N < (u + 1) * (v + 1)" using N pos by (cases "(u + 1) * (v + 1)") auto
  hence "N div (u + 1) < v + 1" by (simp add: less_mult_imp_div_less ac_simps)
  moreover have "N mod (u + 1) < u + 1" by simp
  ultimately show ?thesis by simp
qed

lemma radix_recompose: "((N::nat) mod (u + 1)) + (u + 1) * (N div (u + 1)) = N"
  using mult_div_mod_eq[of "u + 1" N] by linarith

theorem radix_bij:
  "bij_betw (radix u) ({0..u} \<times> {0..v}) {0..(u + 1) * (v + 1) - 1}"
proof (rule bij_betw_byWitness[where f' = "\<lambda>N. (N mod (u + 1), N div (u + 1))"])
  show "\<forall>p\<in>{0..u} \<times> {0..v}. (\<lambda>N. (N mod (u + 1), N div (u + 1))) (radix u p) = p"
  proof
    fix p assume p: "p \<in> {0..u} \<times> {0..v}"
    obtain i j where ij: "p = (i, j)" by (cases p)
    hence iu: "i \<le> u" using p by simp
    show "(\<lambda>N. (N mod (u + 1), N div (u + 1))) (radix u p) = p"
      unfolding ij radix_def prod.case by (simp only: radix_mod[OF iu] radix_div[OF iu])
  qed
next
  show "\<forall>N\<in>{0..(u + 1) * (v + 1) - 1}. radix u ((\<lambda>N. (N mod (u + 1), N div (u + 1))) N) = N"
    by (simp only: radix_def prod.case radix_recompose simp_thms ball_triv)
next
  show "radix u ` ({0..u} \<times> {0..v}) \<subseteq> {0..(u + 1) * (v + 1) - 1}"
  proof (rule image_subsetI)
    fix p assume p: "p \<in> {0..u} \<times> {0..v}"
    obtain i j where ij: "p = (i, j)" by (cases p)
    hence iu: "i \<le> u" and jv: "j \<le> v" using p by simp_all
    show "radix u p \<in> {0..(u + 1) * (v + 1) - 1}"
      unfolding ij radix_def prod.case atLeastAtMost_iff
      by (intro conjI le0 radix_le[OF iu jv])
  qed
next
  show "(\<lambda>N. (N mod (u + 1), N div (u + 1))) ` {0..(u + 1) * (v + 1) - 1} \<subseteq> {0..u} \<times> {0..v}"
  proof (rule image_subsetI)
    fix N assume N: "N \<in> {0..(u + 1) * (v + 1) - 1}"
    hence "N \<le> (u + 1) * (v + 1) - 1" by simp
    from radix_digits[OF this] show "(N mod (u + 1), N div (u + 1)) \<in> {0..u} \<times> {0..v}"
      by (simp add: atLeastAtMost_iff)
  qed
qed

subsection \<open>Positions, counts and words\<close>

text \<open>Generic: an index set \<open>I\<close> and positions \<open>p : I \<rightarrow> real\<close>. The count of \<open>b\<close> is the number of \<open>a\<close> with
  \<open>p a < 1 + p b\<close> (the paper's \<open>c\<^sub>b(x)\<close>).\<close>

definition cnt :: "'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> 'i \<Rightarrow> nat" where
  "cnt I p b = card {a \<in> I. p a < 1 + p b}"

fun wordaux :: "nat \<Rightarrow> nat list \<Rightarrow> bool list" where
  "wordaux prev [] = []"
| "wordaux prev (c # cs) = replicate (c - prev) True @ [False] @ wordaux c cs"

text \<open>The word of the paper: sort the counts increasingly, then write \<open>c\<^sub>(1)\<close> openings (\<open>True\<close>), a closing
  (\<open>False\<close>), \<open>c\<^sub>(2) - c\<^sub>(1)\<close> openings, a closing, and so on.\<close>

definition wordF :: "'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> bool list" where
  "wordF I p = wordaux 0 (sorted_list_of_multiset (image_mset (cnt I p) (mset_set I)))"

lemma cnt_transfer:
  assumes bij: "bij_betw \<phi> I' I" and pp: "\<And>a. a \<in> I' \<Longrightarrow> p' a = p (\<phi> a)" and b: "b \<in> I'"
  shows "cnt I' p' b = cnt I p (\<phi> b)"
proof -
  have inj: "inj_on \<phi> I'" using bij by (simp add: bij_betw_def)
  have img: "\<phi> ` {a \<in> I'. p' a < 1 + p' b} = {a \<in> I. p a < 1 + p (\<phi> b)}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> \<phi> ` {a \<in> I'. p' a < 1 + p' b}"
    then obtain a where a: "a \<in> I'" "p' a < 1 + p' b" "y = \<phi> a" by auto
    from bij a(1) have "\<phi> a \<in> I" by (auto simp: bij_betw_def)
    thus "y \<in> {a \<in> I. p a < 1 + p (\<phi> b)}" using a pp b by auto
  next
    fix y assume y: "y \<in> {a \<in> I. p a < 1 + p (\<phi> b)}"
    then obtain a where a: "a \<in> I'" "y = \<phi> a" using bij by (auto simp: bij_betw_def)
    thus "y \<in> \<phi> ` {a \<in> I'. p' a < 1 + p' b}" using y pp b by auto
  qed
  have "cnt I' p' b = card (\<phi> ` {a \<in> I'. p' a < 1 + p' b})"
    unfolding cnt_def by (rule card_image[symmetric]) (use inj in \<open>auto intro: inj_on_subset\<close>)
  also have "\<dots> = cnt I p (\<phi> b)" using img by (simp add: cnt_def)
  finally show ?thesis .
qed

theorem word_transfer:
  assumes "finite I'" and bij: "bij_betw \<phi> I' I" and pp: "\<And>a. a \<in> I' \<Longrightarrow> p' a = p (\<phi> a)"
  shows "wordF I' p' = wordF I p"
proof -
  have inj: "inj_on \<phi> I'" using bij by (simp add: bij_betw_def)
  have I: "I = \<phi> ` I'" using bij by (simp add: bij_betw_def)
  have "image_mset (cnt I' p') (mset_set I') = image_mset (\<lambda>a. cnt I p (\<phi> a)) (mset_set I')"
  proof (rule multiset.map_cong0)
      fix a assume "a \<in># mset_set I'"
      hence aI: "a \<in> I'" using assms(1) by simp
      show "cnt I' p' a = cnt I p (\<phi> a)" using cnt_transfer[of \<phi> I' I p' p a] bij pp aI by blast
    qed
  also have "\<dots> = image_mset (cnt I p) (image_mset \<phi> (mset_set I'))"
    by (simp add: multiset.map_comp o_def)
  also have "image_mset \<phi> (mset_set I') = mset_set I"
    using image_mset_mset_set[OF inj] I by simp
  finally show ?thesis by (simp add: wordF_def)
qed

subsection \<open>The first coordinate: \<open>{0..F}\<close> versus \<open>{0..u} \<times> {0..v}\<close>\<close>

text \<open>Pattern \<open>f\<close>: first index \<open>N \<in> {0..F}\<close>, rest \<open>r \<in> R\<close> with offset \<open>\<rho> r\<close>. Pattern \<open>f'\<close>: indices
  \<open>(i, j, r)\<close>. Coordinates \<open>(x, (u+1)x)\<close> against \<open>x\<close>.\<close>

definition idxF :: "nat \<Rightarrow> 'r set \<Rightarrow> (nat \<times> 'r) set" where
  "idxF F R = {0..F} \<times> R"

definition posF :: "real \<Rightarrow> ('r \<Rightarrow> real) \<Rightarrow> nat \<times> 'r \<Rightarrow> real" where
  "posF x \<rho> = (\<lambda>(N, r). real N * x + \<rho> r)"

definition idxS :: "nat \<Rightarrow> nat \<Rightarrow> 'r set \<Rightarrow> (nat \<times> nat \<times> 'r) set" where
  "idxS u v R = {0..u} \<times> {0..v} \<times> R"

definition posS :: "real \<Rightarrow> nat \<Rightarrow> ('r \<Rightarrow> real) \<Rightarrow> nat \<times> nat \<times> 'r \<Rightarrow> real" where
  "posS x u \<rho> = (\<lambda>(i, j, r). real i * x + real j * (real (u + 1) * x) + \<rho> r)"

definition phi :: "nat \<Rightarrow> nat \<times> nat \<times> 'r \<Rightarrow> nat \<times> 'r" where
  "phi u = (\<lambda>(i, j, r). (i + (u + 1) * j, r))"

lemma phi_bij:
  "bij_betw (phi u) (idxS u v R) (idxF ((u + 1) * (v + 1) - 1) R)"
proof (rule bij_betw_byWitness[where f' = "\<lambda>(N, r). (N mod (u + 1), N div (u + 1), r)"])
  show "\<forall>t\<in>idxS u v R. (case phi u t of (N, r) \<Rightarrow> (N mod (u + 1), N div (u + 1), r)) = t"
  proof
    fix t assume t: "t \<in> idxS u v R"
    obtain i j r where ijr: "t = (i, j, r)" by (cases t) auto
    hence iu: "i \<le> u" using t by (simp add: idxS_def)
    show "(case phi u t of (N, r) \<Rightarrow> (N mod (u + 1), N div (u + 1), r)) = t"
      unfolding ijr phi_def by (simp only: prod.case radix_mod[OF iu] radix_div[OF iu])
  qed
next
  show "\<forall>t\<in>idxF ((u + 1) * (v + 1) - 1) R.
      phi u (case t of (N, r) \<Rightarrow> (N mod (u + 1), N div (u + 1), r)) = t"
  proof
    fix t assume "t \<in> idxF ((u + 1) * (v + 1) - 1) R"
    obtain N r where Nr: "t = (N, r)" by (cases t) auto
    show "phi u (case t of (N, r) \<Rightarrow> (N mod (u + 1), N div (u + 1), r)) = t"
      unfolding Nr phi_def by (simp only: prod.case radix_recompose)
  qed
next
  show "phi u ` idxS u v R \<subseteq> idxF ((u + 1) * (v + 1) - 1) R"
  proof (rule image_subsetI)
    fix t assume t: "t \<in> idxS u v R"
    obtain i j r where ijr: "t = (i, j, r)" by (cases t) auto
    hence iu: "i \<le> u" and jv: "j \<le> v" and rR: "r \<in> R" using t by (simp_all add: idxS_def)
    show "phi u t \<in> idxF ((u + 1) * (v + 1) - 1) R"
      unfolding ijr phi_def idxF_def prod.case
      using radix_le[OF iu jv] rR by (simp only: mem_Times_iff atLeastAtMost_iff le0 simp_thms fst_conv snd_conv)
  qed
next
  show "(\<lambda>(N, r). (N mod (u + 1), N div (u + 1), r)) ` idxF ((u + 1) * (v + 1) - 1) R \<subseteq> idxS u v R"
  proof (rule image_subsetI)
    fix t assume t: "t \<in> idxF ((u + 1) * (v + 1) - 1) R"
    obtain N r where Nr: "t = (N, r)" by (cases t) auto
    hence N: "N \<le> (u + 1) * (v + 1) - 1" and rR: "r \<in> R" using t by (simp_all add: idxF_def)
    from radix_digits[OF N] rR show "(case t of (N, r) \<Rightarrow> (N mod (u + 1), N div (u + 1), r)) \<in> idxS u v R"
      unfolding Nr idxS_def by (simp add: atLeastAtMost_iff)
  qed
qed

lemma pos_phi:
  assumes "t \<in> idxS u v R"
  shows "posS x u \<rho> t = posF x \<rho> (phi u t)"
proof -
  obtain i j r where t: "t = (i, j, r)" by (cases t) auto
  show ?thesis by (simp add: t posS_def posF_def phi_def algebra_simps)
qed

text \<open>(ii) of the task: the comparison of the signature in the coordinate \<open>x\<close> coincides with the
  comparison of the signature \<open>(u, v)\<close> in \<open>(x, (u+1)x)\<close>.\<close>

theorem comparison_transfer:
  assumes "t \<in> idxS u v R" "t' \<in> idxS u v R"
  shows "posS x u \<rho> t < 1 + posS x u \<rho> t' \<longleftrightarrow> posF x \<rho> (phi u t) < 1 + posF x \<rho> (phi u t')"
  using pos_phi[OF assms(1)] pos_phi[OF assms(2)] by simp

theorem no_unit_difference_transfer:
  assumes "\<And>a b. a \<in> idxF ((u + 1) * (v + 1) - 1) R \<Longrightarrow> b \<in> idxF ((u + 1) * (v + 1) - 1) R \<Longrightarrow>
      posF x \<rho> a - posF x \<rho> b \<noteq> 1"
    and "a \<in> idxS u v R" "b \<in> idxS u v R"
  shows "posS x u \<rho> a - posS x u \<rho> b \<noteq> 1"
proof -
  have "phi u a \<in> idxF ((u + 1) * (v + 1) - 1) R" "phi u b \<in> idxF ((u + 1) * (v + 1) - 1) R"
    using bij_betwE[OF phi_bij[of u v R]] assms(2,3) by blast+
  from assms(1)[OF this] show ?thesis using pos_phi[OF assms(2)] pos_phi[OF assms(3)] by simp
qed

text \<open>The general statement: the word \<open>w\<^sub>f(x)\<close> equals the word \<open>w\<^sub>{f'}(y)\<close>.\<close>

theorem word_refinement:
  assumes "finite R"
  shows "wordF (idxS u v R) (posS x u \<rho>) = wordF (idxF ((u + 1) * (v + 1) - 1) R) (posF x \<rho>)"
proof (rule word_transfer[OF _ phi_bij])
  show "finite (idxS u v R)" using assms by (simp add: idxS_def)
  show "\<And>a. a \<in> idxS u v R \<Longrightarrow> posS x u \<rho> a = posF x \<rho> (phi u a)" by (rule pos_phi)
qed

end
