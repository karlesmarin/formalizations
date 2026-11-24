(*  Title:      IL_Formula.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Integer length formula: the least number of integer squares is n + P + (z mod 2) for the graph model (lengths paper)
*)

theory IL_Formula
  imports IL_Iso
begin

section \<open>The integer length formula\<close>

text \<open>With \<open>n\<close> the number of vertices, \<open>P\<close> the number of path components with at least two vertices and \<open>z\<close>
the number of isolated vertices, the least number of squares is \<open>n + P + (z mod 2)\<close>: it is attained,
and \<open>nnz T + (n + P + z mod 2) \<le> 2 n\<close> for every integer representation \<open>T\<close>.\<close>

theorem integer_length:
  assumes ok: "okc cs"
  shows "(\<exists>T. rep (Vc cs) (Ec cs) T \<and>
      nnz T + (card (Vc cs) + card (Cp cs) + card (Cz cs) mod 2) = 2 * card (Vc cs))"
    and "\<And>T. rep (Vc cs) (Ec cs) T \<Longrightarrow>
      nnz T + (card (Vc cs) + card (Cp cs) + card (Cz cs) mod 2) \<le> 2 * card (Vc cs)"
proof -
  interpret g: lgraph "Vc cs" "Ec cs" by (rule lgraph_Vc[OF ok])
  have sup: "\<And>i j. T0 cs i j \<noteq> 0 \<Longrightarrow> Ec cs i j" unfolding Ec_def by blast
  have M1: "\<exists>T. rep (Vc cs) (Ec cs) T \<and> nnz T = nnz (T0 cs) + 2 * (g.nz div 2)"
    by (rule g.max_nnz(1)[OF T0_rep[OF ok] sup])
  have M2: "\<And>T. rep (Vc cs) (Ec cs) T \<Longrightarrow> nnz T \<le> nnz (T0 cs) + 2 * (g.nz div 2)"
    by (rule g.max_nnz(2)[OF T0_rep[OF ok] sup])
  have nzz: "g.nz = card (Cz cs)" by (rule nz_Cz[OF ok])
  have s1: "nnz (T0 cs) + card (Cn cs) = card (Vc cs)" by (rule n_split[OF ok])
  have s2: "card (Cn cs) = card (Cp cs) + card (Cz cs)" by (rule Cn_split[OF ok])
  show "\<exists>T. rep (Vc cs) (Ec cs) T \<and>
      nnz T + (card (Vc cs) + card (Cp cs) + card (Cz cs) mod 2) = 2 * card (Vc cs)"
    proof -
    obtain T where T: "rep (Vc cs) (Ec cs) T" "nnz T = nnz (T0 cs) + 2 * (g.nz div 2)" using M1 by blast
    have "nnz T + (card (Vc cs) + card (Cp cs) + card (Cz cs) mod 2) = 2 * card (Vc cs)"
      by (rule nat_fin_eq[OF _ s1 s2]) (simp add: T(2) nzz)
    thus ?thesis using T(1) by blast
  qed
  fix T assume rT: "rep (Vc cs) (Ec cs) T"
  have b: "nnz T \<le> nnz (T0 cs) + 2 * (card (Cz cs) div 2)" using M2[OF rT] nzz by simp
  show "nnz T + (card (Vc cs) + card (Cp cs) + card (Cz cs) mod 2) \<le> 2 * card (Vc cs)"
    by (rule nat_fin_le[OF b s1 s2])
qed

end
