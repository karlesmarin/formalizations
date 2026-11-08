(*  Title:      Rung_Recursion.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: su7-certified-gap, Proposition prop:rec (the rung recursion), as a counting identity: contents with or
   without the generator 7(+,+), whose moments (8D, 2A4) = (-6, 0) are eight_generator_moments of SU7WeightChannels *)
theory Rung_Recursion
  imports Complex_Main
begin

text \<open>Proposition \<open>prop:rec\<close> of the note on the certified gap of SU(7) gauge-Higgs unification. A content is
  a non-negative combination of eight generators. One of them, $\mathbf 7(+,+)$, has $A_4=0$ and moves $8D$ by $-6$;
  the other seven form the contents $x\in X$ with weight $w(x)=(A_4,8D)$. Writing $N(a,q)$ for the number of contents
  of weight $(a,q)$ and $P(a,q)$ for those without $\mathbf 7(+,+)$,
  \[ N(a,q) = P(a,q) + N(a,q+6), \qquad\text{that is}\qquad N(a,q+6) = N(a,q) - P(a,q): \]
  a content of weight $(a,q)$ either has no copy of $\mathbf 7(+,+)$, or removing one copy gives a content of weight
  $(a,q+6)$. First the identity for any generator $(0,-c)$ and any set of contents (\<open>rung_recursion\<close>), then the
  finiteness of a cell for the actual data (\<open>su7_cell_finite\<close>) and the recursion for it (\<open>su7_rung_recursion\<close>).

  Attribution: the recursion is CLASSICAL, the standard recursion of a vector partition function in one generator
  (M. Beck, S. Robins, \emph{Computing the Continuous Discretely}; B. Sturmfels, \emph{On vector partition
  functions}, J. Combin. Theory Ser. A); the note says so. What is ours is this formalization, the finiteness of a cell
  for the SU(7) data, and, in the note, the measurement of how small the correction term is.\<close>

section \<open>The counting identity\<close>

definition cell :: "'x set \<Rightarrow> ('x \<Rightarrow> int \<times> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (nat \<times> 'x) set" where
  "cell X w c a q = {(k, x). x \<in> X \<and> w x = (a, q + int k * c)}"

definition Ncount :: "'x set \<Rightarrow> ('x \<Rightarrow> int \<times> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat" where
  "Ncount X w c a q = card (cell X w c a q)"

definition Pcount :: "'x set \<Rightarrow> ('x \<Rightarrow> int \<times> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat" where
  "Pcount X w a q = card {x \<in> X. w x = (a, q)}"

lemma cell_split:
  "cell X w c a q = (\<lambda>x. (0, x)) ` {x \<in> X. w x = (a, q)} \<union> (\<lambda>(k, x). (Suc k, x)) ` cell X w c a (q + c)"
proof (intro equalityI subsetI)
  fix p assume p: "p \<in> cell X w c a q"
  obtain k x where kx: "p = (k, x)" by (cases p)
  show "p \<in> (\<lambda>x. (0, x)) ` {x \<in> X. w x = (a, q)} \<union> (\<lambda>(k, x). (Suc k, x)) ` cell X w c a (q + c)"
  proof (cases k)
    case 0
    then show ?thesis using p kx unfolding cell_def by auto
  next
    case (Suc j)
    have "(j, x) \<in> cell X w c a (q + c)" using p kx Suc unfolding cell_def by (auto simp: algebra_simps)
    then show ?thesis using kx Suc by force
  qed
next
  fix p assume "p \<in> (\<lambda>x. (0, x)) ` {x \<in> X. w x = (a, q)} \<union> (\<lambda>(k, x). (Suc k, x)) ` cell X w c a (q + c)"
  then show "p \<in> cell X w c a q" unfolding cell_def by (auto simp: algebra_simps)
qed

theorem rung_recursion:
  assumes fin: "finite (cell X w c a q)"
  shows "Ncount X w c a q = Pcount X w a q + Ncount X w c a (q + c)"
proof -
  let ?A = "(\<lambda>x. (0::nat, x)) ` {x \<in> X. w x = (a, q)}"
  let ?B = "(\<lambda>(k, x). (Suc k, x)) ` cell X w c a (q + c)"
  have fA: "finite ?A" and fB: "finite ?B" using fin cell_split[of X w c a q] by (metis finite_Un)+
  have inj: "inj_on (\<lambda>(k, x). (Suc k, x)) (cell X w c a (q + c))" by (auto simp: inj_on_def)
  have fC: "finite (cell X w c a (q + c))" using fB finite_image_iff[OF inj] by simp
  have dis: "?A \<inter> ?B = {}" by auto
  have "card (?A \<union> ?B) = card ?A + card ?B" using card_Un_disjoint[OF fA fB dis] .
  moreover have "card ?A = card {x \<in> X. w x = (a, q)}" by (rule card_image) (auto simp: inj_on_def)
  moreover have "card ?B = card (cell X w c a (q + c))" by (rule card_image[OF inj])
  ultimately show ?thesis unfolding Ncount_def Pcount_def by (simp add: cell_split[of X w c a q])
qed

section \<open>The SU(7) data: finiteness of a cell and the recursion\<close>

text \<open>Moments $(A_4,8D)$ of the seven generators other than $\mathbf 7(+,+)$, from \<open>eight_generator_moments\<close>
  (Lean, \<open>GaugeHiggsUnification.SU7WeightChannels\<close>), which lists $(8D,2A_4)$:
  $(8,2),(16,34),(2,8),(0,36),(28,16),(10,136),(80,218)$. To stay in the integers we use $2A_4$; every generator
  has $2A_4\ge 2$. The generator $\mathbf 7(+,+)$ is $(8D,2A_4)=(-6,0)$, so $c=6$.\<close>

definition gA :: "int list" where "gA = [2, 34, 8, 36, 16, 136, 218]"   (* 2 A4 *)
definition gD :: "int list" where "gD = [8, 16, 2, 0, 28, 10, 80]"       (* 8 D *)

definition contents :: "nat list set" where "contents = {n. length n = 7}"

definition su7w :: "nat list \<Rightarrow> int \<times> int" where
  "su7w n = ((\<Sum>j<7. int (n ! j) * gA ! j), (\<Sum>j<7. int (n ! j) * gD ! j))"

lemma gA_pos: "j < 7 \<Longrightarrow> 1 \<le> gA ! j"
  by (auto simp: gA_def less_Suc_eq numeral_eq_Suc)

lemma entry_le: "n \<in> contents \<Longrightarrow> j < 7 \<Longrightarrow> int (n ! j) \<le> fst (su7w n)"
proof -
  assume n: "n \<in> contents" and j: "j < 7"
  have nonneg: "\<And>i. i < 7 \<Longrightarrow> 0 \<le> int (n ! i) * gA ! i" using gA_pos by (simp add: order.trans[OF _ gA_pos])
  have "int (n ! j) \<le> int (n ! j) * gA ! j" using gA_pos[OF j] by (simp add: mult_le_cancel_left1)
  also have "\<dots> \<le> (\<Sum>i<7. int (n ! i) * gA ! i)"
    using j nonneg by (intro member_le_sum) auto
  finally show ?thesis by (simp add: su7w_def)
qed

text \<open>Observation \<open>obs:fin\<close>: a cell is finite. Every entry is bounded by $2A_4$ of the target, so the contents
  of a given $2A_4$ are finitely many, and $k$ is determined by $8D$.\<close>
theorem su7_cell_finite: "finite (cell contents su7w 6 a q)"
proof -
  let ?L = "{n. set n \<subseteq> {0..nat a} \<and> length n = 7}"
  have fL: "finite ?L" by (rule finite_lists_length_eq) simp
  have sub: "snd ` cell contents su7w 6 a q \<subseteq> ?L"
  proof
    fix n assume "n \<in> snd ` cell contents su7w 6 a q"
    then obtain k where kn: "(k, n) \<in> cell contents su7w 6 a q" by force
    then have n: "n \<in> contents" and A: "fst (su7w n) = a" unfolding cell_def by auto
    have "\<forall>x\<in>set n. x \<le> nat a"
    proof
      fix x assume "x \<in> set n"
      then obtain j where j: "j < length n" "n ! j = x" by (auto simp: in_set_conv_nth)
      then have "j < 7" using n by (simp add: contents_def)
      then show "x \<le> nat a" using entry_le[OF n] A j by fastforce
    qed
    then show "n \<in> ?L" using n by (auto simp: contents_def)
  qed
  have fN: "finite (snd ` cell contents su7w 6 a q)" using finite_subset[OF sub fL] .
  have fK: "finite (fst ` cell contents su7w 6 a q)"
  proof (rule finite_subset)
    show "fst ` cell contents su7w 6 a q \<subseteq> (\<lambda>n. nat ((snd (su7w n) - q) div 6)) ` snd ` cell contents su7w 6 a q"
    proof
      fix k assume "k \<in> fst ` cell contents su7w 6 a q"
      then obtain n where kn: "(k, n) \<in> cell contents su7w 6 a q" by force
      then have "snd (su7w n) = q + int k * 6" unfolding cell_def by auto
      then have "k = nat ((snd (su7w n) - q) div 6)" by simp
      then show "k \<in> (\<lambda>n. nat ((snd (su7w n) - q) div 6)) ` snd ` cell contents su7w 6 a q" using kn by force
    qed
    show "finite ((\<lambda>n. nat ((snd (su7w n) - q) div 6)) ` snd ` cell contents su7w 6 a q)" using fN by simp
  qed
  have "cell contents su7w 6 a q \<subseteq> fst ` cell contents su7w 6 a q \<times> snd ` cell contents su7w 6 a q"
    by (auto simp: image_iff) (metis fst_conv snd_conv)+
  then show ?thesis using finite_subset fK fN by blast
qed

text \<open>Proposition \<open>prop:rec\<close>: raising $8D$ by six removes exactly the contents without $\mathbf 7(+,+)$.\<close>
corollary su7_rung_recursion:
  "Ncount contents su7w 6 a (q + 6) = Ncount contents su7w 6 a q - Pcount contents su7w a q"
  using rung_recursion[OF su7_cell_finite[of a q]] by simp

end
