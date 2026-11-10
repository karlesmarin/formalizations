(*  Title:      Game_of_Life/Life_Flight.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Life_Flight
  imports Life_Disjoint Life_Objects
begin

section \<open>Families of patterns and free flight of salvos\<close>

text \<open>The disjoint-evolution theorem for an arbitrary family: if the 1-thickenings of the members
  are pairwise disjoint, one generation of the union is the union of the generations.  For a
  spaceship (a pattern that reappears translated after \<open>p\<close> generations) the condition only has to
  be checked during one period, which gives the free flight of a salvo: any family of translated
  copies of the spaceship, in arbitrary phases, that stay apart for one period fly independently
  for ever.\<close>

lemma dil_transl: "dil r (transl v A) = transl v (dil r A)"
proof (intro set_eqI iffI)
  fix c assume "c \<in> dil r (transl v A)"
  then obtain a where a: "a \<in> A" "\<bar>fst c - (fst a + fst v)\<bar> \<le> int r"
    "\<bar>snd c - (snd a + snd v)\<bar> \<le> int r"
    by (auto simp: dil_def transl_def tr_def)
  let ?e = "(fst c - fst v, snd c - snd v)"
  have "?e \<in> dil r A"
    unfolding dil_def using a by (intro CollectI bexI[of _ a]) (auto simp: algebra_simps)
  moreover have "c = tr v ?e" by (simp add: tr_def)
  ultimately show "c \<in> transl v (dil r A)" unfolding transl_def by blast
next
  fix c assume "c \<in> transl v (dil r A)"
  then obtain e a where e: "c = tr v e" "a \<in> A" "\<bar>fst e - fst a\<bar> \<le> int r"
    "\<bar>snd e - snd a\<bar> \<le> int r"
    by (auto simp: dil_def transl_def)
  then show "c \<in> dil r (transl v A)"
    unfolding dil_def transl_def by (intro CollectI bexI[of _ "tr v a"]) (auto simp: tr_def)
qed

lemma transl_comm: "transl a (transl b S) = transl b (transl a S)"
  by (simp add: transl_transl add.commute)

lemma transl_inter: "transl u (C \<inter> D) = transl u C \<inter> transl u D"
  unfolding transl_def by (rule image_Int) (rule bij_is_inj[OF bij_tr])

lemma transl_disjoint:
  assumes "dil 1 C \<inter> dil 1 D = {}"
  shows "dil 1 (transl u C) \<inter> dil 1 (transl u D) = {}"
proof -
  have "dil 1 (transl u C) \<inter> dil 1 (transl u D) = transl u (dil 1 C \<inter> dil 1 D)"
    by (simp only: dil_transl transl_inter[symmetric])
  also have "\<dots> = {}" using assms by (simp add: transl_def)
  finally show ?thesis .
qed

lemma dil_UN: "dil r (\<Union>i\<in>J. A i) = (\<Union>i\<in>J. dil r (A i))"
  unfolding dil_def by blast

lemma step_family_split:
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> dil 1 (A i) \<inter> dil 1 (A j) = {}"
    and "i \<in> I"
  shows "step (\<Union>j\<in>I. A j) = step (A i) \<union> step (\<Union>j\<in>I - {i}. A j)"
    and "step (\<Union>j\<in>I - {i}. A j) \<inter> dil 1 (A i) = {}"
proof -
  let ?R = "\<Union>j\<in>I - {i}. A j"
  have dis: "dil 1 (A i) \<inter> dil 1 ?R = {}"
    using assms by (auto simp: dil_UN)
  have un: "(\<Union>j\<in>I. A j) = A i \<union> ?R" using assms(2) by auto
  show "step (\<Union>j\<in>I. A j) = step (A i) \<union> step ?R"
    unfolding un by (rule disjoint_step[OF dis])
  show "step ?R \<inter> dil 1 (A i) = {}"
    using step_subset_dil dis by blast
qed

theorem disjoint_step_family:
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> dil 1 (A i) \<inter> dil 1 (A j) = {}"
  shows "step (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. step (A i))"
proof (intro set_eqI iffI)
  fix c assume c: "c \<in> step (\<Union>i\<in>I. A i)"
  then have "c \<in> dil 1 (\<Union>i\<in>I. A i)" using step_subset_dil by blast
  then obtain i where i: "i \<in> I" "c \<in> dil 1 (A i)" by (auto simp: dil_UN)
  have split: "step (\<Union>j\<in>I. A j) = step (A i) \<union> step (\<Union>j\<in>I - {i}. A j)"
    and apart: "step (\<Union>j\<in>I - {i}. A j) \<inter> dil 1 (A i) = {}"
    using step_family_split[of I A i] assms i(1) by blast+
  have "c \<in> step (A i)" using c i(2) apart unfolding split by blast
  then show "c \<in> (\<Union>i\<in>I. step (A i))" using i(1) by blast
next
  fix c assume "c \<in> (\<Union>i\<in>I. step (A i))"
  then obtain i where i: "i \<in> I" "c \<in> step (A i)" by blast
  have "step (\<Union>j\<in>I. A j) = step (A i) \<union> step (\<Union>j\<in>I - {i}. A j)"
    using step_family_split[of I A i] assms i(1) by blast
  then show "c \<in> step (\<Union>i\<in>I. A i)" using i(2) by blast
qed

theorem disjoint_steps_family:
  assumes "\<And>k i j. k < t \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow>
    dil 1 ((step ^^ k) (A i)) \<inter> dil 1 ((step ^^ k) (A j)) = {}"
  shows "(step ^^ t) (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. (step ^^ t) (A i))"
  using assms
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have ih: "(step ^^ t) (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. (step ^^ t) (A i))"
    using Suc.prems by (intro Suc.IH) auto
  have "step (\<Union>i\<in>I. (step ^^ t) (A i)) = (\<Union>i\<in>I. step ((step ^^ t) (A i)))"
    by (rule disjoint_step_family) (use Suc.prems in blast)
  then show ?case using ih by simp
qed

subsection \<open>Spaceships\<close>

lemma flight_mult:
  assumes "(step ^^ p) X = transl v X"
  shows "(step ^^ (p * k)) X = transl (int k * fst v, int k * snd v) X"
proof (induction k)
  case 0
  then show ?case by (simp add: transl_def tr_def)
next
  case (Suc k)
  have e: "p * Suc k = p + p * k" by simp
  have "(step ^^ (p * Suc k)) X = (step ^^ p) ((step ^^ (p * k)) X)"
    by (simp only: e funpow_add comp_apply)
  also have "\<dots> = transl (int k * fst v, int k * snd v) ((step ^^ p) X)"
    by (simp add: Suc.IH steps_transl)
  also have "\<dots> = transl (int k * fst v + fst v, int k * snd v + snd v) X"
    by (simp add: assms transl_transl)
  also have "\<dots> = transl (int (Suc k) * fst v, int (Suc k) * snd v) X"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma flight_shift:
  assumes "0 < p" and "(step ^^ p) X = transl v X"
  shows "(step ^^ (k + m)) X
    = transl (int (k div p) * fst v, int (k div p) * snd v) ((step ^^ (k mod p + m)) X)"
proof -
  have e: "k + m = (k mod p + m) + p * (k div p)" using mod_mult_div_eq[of k p] by arith
  have "(step ^^ (k + m)) X = (step ^^ (k mod p + m)) ((step ^^ (p * (k div p))) X)"
    by (simp only: e funpow_add comp_apply)
  also have "\<dots> = (step ^^ (k mod p + m))
      (transl (int (k div p) * fst v, int (k div p) * snd v) X)"
    by (simp only: flight_mult[OF assms(2)])
  finally show ?thesis by (simp only: steps_transl)
qed

lemma flight_decomp:
  assumes "0 < p" and "(step ^^ p) X = transl v X"
  shows "(step ^^ n) X = transl (int (n div p) * fst v, int (n div p) * snd v) ((step ^^ (n mod p)) X)"
  using flight_shift[OF assms, of n 0] by simp

theorem salvo_flight:
  assumes "0 < p" and "(step ^^ p) X = transl v X"
    and "\<And>k i j. k < p \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow>
      dil 1 (transl (w i) ((step ^^ (k + ph i)) X)) \<inter> dil 1 (transl (w j) ((step ^^ (k + ph j)) X)) = {}"
  shows "(step ^^ n) (\<Union>i\<in>I. transl (w i) ((step ^^ ph i) X))
       = (\<Union>i\<in>I. transl (w i) ((step ^^ (n + ph i)) X))"
proof -
  have A_step: "(step ^^ k) (transl (w i) ((step ^^ ph i) X))
      = transl (w i) ((step ^^ (k + ph i)) X)" for k i
    by (simp add: steps_transl funpow_add)
  have fam: "dil 1 ((step ^^ k) (transl (w i) ((step ^^ ph i) X)))
      \<inter> dil 1 ((step ^^ k) (transl (w j) ((step ^^ ph j) X))) = {}"
    if ij: "i \<in> I" "j \<in> I" "i \<noteq> j" for k i j
  proof -
    define u where "u = (int (k div p) * fst v, int (k div p) * snd v)"
    have form: "(step ^^ k) (transl (w l) ((step ^^ ph l) X))
        = transl u (transl (w l) ((step ^^ (k mod p + ph l)) X))" for l
    proof -
      have "(step ^^ k) (transl (w l) ((step ^^ ph l) X)) = transl (w l) ((step ^^ (k + ph l)) X)"
        by (rule A_step)
      also have "(step ^^ (k + ph l)) X = transl u ((step ^^ (k mod p + ph l)) X)"
        unfolding u_def by (rule flight_shift[OF assms(1,2)])
      finally show ?thesis by (simp only: transl_comm[of "w l" u])
    qed
    have "k mod p < p" using assms(1) by simp
    from assms(3)[OF this ij] show ?thesis
      unfolding form by (rule transl_disjoint)
  qed
  have "(step ^^ n) (\<Union>i\<in>I. transl (w i) ((step ^^ ph i) X))
    = (\<Union>i\<in>I. (step ^^ n) (transl (w i) ((step ^^ ph i) X)))"
    by (rule disjoint_steps_family) (use fam in blast)
  then show ?thesis by (simp only: A_step)
qed

subsection \<open>Glider salvos\<close>

definition gbox :: "cell set" where
  "gbox = {c. 0 \<le> fst c \<and> fst c \<le> 3 \<and> 0 \<le> snd c \<and> snd c \<le> 3}"

lemma glider_phase_gbox: "k < 4 \<Longrightarrow> (step ^^ k) glider \<subseteq> gbox"
proof -
  assume "k < 4"
  then have "k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3" by arith
  then show ?thesis
    using glider_steps_1_to_4 by (auto simp: glider_def gbox_def g1_def g2_def g3_def)
qed

lemma glider_envelope: "(step ^^ n) glider \<subseteq> transl (int (n div 4), int (n div 4)) gbox"
proof -
  have "(step ^^ n) glider = transl (int (n div 4), int (n div 4)) ((step ^^ (n mod 4)) glider)"
    using flight_decomp[OF _ glider_moves, of n] by simp
  moreover have "(step ^^ (n mod 4)) glider \<subseteq> gbox"
    by (rule glider_phase_gbox) simp
  ultimately show ?thesis unfolding transl_def by (simp add: image_mono)
qed

lemma glider_phase_box3:
  assumes "k < 4"
  shows "\<exists>x0 y0. (step ^^ k) glider
    \<subseteq> {c. x0 \<le> fst c \<and> fst c \<le> x0 + 2 \<and> y0 \<le> snd c \<and> snd c \<le> y0 + 2}"
proof -
  have "k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3" using assms by arith
  then show ?thesis
  proof (elim disjE)
    assume "k = 0"
    then show ?thesis by (intro exI[of _ 0] exI[of _ 0]) (auto simp: glider_def)
  next
    assume "k = 1"
    then show ?thesis
      using glider_steps_1_to_4(1) by (intro exI[of _ 0] exI[of _ 1]) (auto simp: g1_def)
  next
    assume "k = 2"
    then show ?thesis
      using glider_steps_1_to_4(2) by (intro exI[of _ 0] exI[of _ 1]) (auto simp: g2_def)
  next
    assume "k = 3"
    then show ?thesis
      using glider_steps_1_to_4(3) by (intro exI[of _ 1] exI[of _ 1]) (auto simp: g3_def)
  qed
qed

lemma box3_apart:
  assumes "B \<subseteq> {c. x0 \<le> fst c \<and> fst c \<le> x0 + 2 \<and> y0 \<le> snd c \<and> snd c \<le> y0 + 2}"
    and "5 \<le> \<bar>fst u - fst u'\<bar> \<or> 5 \<le> \<bar>snd u - snd u'\<bar>"
  shows "dil 1 (transl u B) \<inter> dil 1 (transl u' B) = {}"
proof (rule ccontr)
  assume "dil 1 (transl u B) \<inter> dil 1 (transl u' B) \<noteq> {}"
  then obtain c where "c \<in> dil 1 (transl u B)" "c \<in> dil 1 (transl u' B)" by blast
  then obtain b b' where b: "b \<in> B" "\<bar>fst c - (fst b + fst u)\<bar> \<le> 1"
    "\<bar>snd c - (snd b + snd u)\<bar> \<le> 1"
    and b': "b' \<in> B" "\<bar>fst c - (fst b' + fst u')\<bar> \<le> 1" "\<bar>snd c - (snd b' + snd u')\<bar> \<le> 1"
    by (auto simp: dil_def transl_def tr_def)
  have "x0 \<le> fst b" "fst b \<le> x0 + 2" "y0 \<le> snd b" "snd b \<le> y0 + 2"
    "x0 \<le> fst b'" "fst b' \<le> x0 + 2" "y0 \<le> snd b'" "snd b' \<le> y0 + 2"
    using assms(1) b(1) b'(1) by auto
  then show False using assms(2) b b' by arith
qed

theorem glider_salvo:
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow>
     5 \<le> \<bar>fst (w i) - fst (w j)\<bar> \<or> 5 \<le> \<bar>snd (w i) - snd (w j)\<bar>"
  shows "(step ^^ n) (\<Union>i\<in>I. transl (w i) glider) = (\<Union>i\<in>I. transl (w i) ((step ^^ n) glider))"
proof -
  have "(step ^^ n) (\<Union>i\<in>I. transl (w i) ((step ^^ 0) glider))
      = (\<Union>i\<in>I. transl (w i) ((step ^^ (n + 0)) glider))"
  proof (rule salvo_flight[OF _ glider_moves])
    show "0 < (4::nat)" by simp
    fix k :: nat and i j assume k: "k < 4" and ij: "i \<in> I" "j \<in> I" "i \<noteq> j"
    obtain x0 y0 where "(step ^^ k) glider
      \<subseteq> {c. x0 \<le> fst c \<and> fst c \<le> x0 + 2 \<and> y0 \<le> snd c \<and> snd c \<le> y0 + 2}"
      using glider_phase_box3[OF k] by blast
    from box3_apart[OF this assms[OF ij]]
    show "dil 1 (transl (w i) ((step ^^ (k + 0)) glider))
        \<inter> dil 1 (transl (w j) ((step ^^ (k + 0)) glider)) = {}"
      by simp
  qed
  then show ?thesis by simp
qed

corollary glider_salvo_flight:
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow>
     5 \<le> \<bar>fst (w i) - fst (w j)\<bar> \<or> 5 \<le> \<bar>snd (w i) - snd (w j)\<bar>"
  shows "(step ^^ (4 * k)) (\<Union>i\<in>I. transl (w i) glider) = transl (int k, int k) (\<Union>i\<in>I. transl (w i) glider)"
proof -
  have "(step ^^ (4 * k)) (\<Union>i\<in>I. transl (w i) glider)
      = (\<Union>i\<in>I. transl (w i) ((step ^^ (4 * k)) glider))"
    by (rule glider_salvo[OF assms])
  also have "\<dots> = (\<Union>i\<in>I. transl (int k, int k) (transl (w i) glider))"
  proof (rule SUP_cong[OF refl])
    fix i assume "i \<in> I"
    show "transl (w i) ((step ^^ (4 * k)) glider) = transl (int k, int k) (transl (w i) glider)"
      unfolding glider_flight by (rule transl_comm)
  qed
  also have "\<dots> = transl (int k, int k) (\<Union>i\<in>I. transl (w i) glider)"
    unfolding transl_def by (simp add: image_UN)
  finally show ?thesis .
qed

end
