(*  Title:      ZL_Counts.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Admissibility as a distance condition, the endpoint bound for maximum bases with m >= n(n-1)/2,
    and the arithmetic of the weak gap in three columns.
*)
theory ZL_Counts
  imports ZL_Labels
begin

section \<open>Admissibility as a distance condition\<close>

text \<open>Two cells are adjacent in \<open>R_O\<close> when they are opposite corners of a rectangle whose four corners are
  occupied. (C2) says the two cells of a pair are not adjacent; (C3) says they have no common neighbour.\<close>

definition adj :: "(nat \<times> nat) set \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "adj Oc c d \<longleftrightarrow> c \<in> Oc \<and> d \<in> Oc \<and> fst c \<noteq> fst d \<and> snd c \<noteq> snd d \<and>
     (fst c, snd d) \<in> Oc \<and> (fst d, snd c) \<in> Oc"

lemma C2_iff_not_adj:
  assumes "c \<in> Oc" "d \<in> Oc"
  shows "C2 Oc c d \<longleftrightarrow> \<not> adj Oc c d"
  using assms unfolding C2_def adj_def by blast

lemma C3_iff_no_common_neighbour:
  assumes "c \<in> Oc" "d \<in> Oc"
  shows "C3 Oc c d \<longleftrightarrow> \<not> (\<exists>w. adj Oc c w \<and> adj Oc w d)"
proof
  assume h: "C3 Oc c d"
  show "\<not> (\<exists>w. adj Oc c w \<and> adj Oc w d)"
  proof
    assume "\<exists>w. adj Oc c w \<and> adj Oc w d"
    then obtain k l where "adj Oc c (k, l)" "adj Oc (k, l) d" by auto
    then show False using h unfolding C3_def adj_def by (metis fst_conv snd_conv)
  qed
next
  assume h: "\<not> (\<exists>w. adj Oc c w \<and> adj Oc w d)"
  show "C3 Oc c d"
    unfolding C3_def
  proof (rule notI)
    assume "\<exists>k l. k \<noteq> fst c \<and> k \<noteq> fst d \<and> l \<noteq> snd c \<and> l \<noteq> snd d \<and>
      (k, l) \<in> Oc \<and> (k, snd c) \<in> Oc \<and> (k, snd d) \<in> Oc \<and> (fst c, l) \<in> Oc \<and> (fst d, l) \<in> Oc"
    then obtain k l where "adj Oc c (k, l) \<and> adj Oc (k, l) d"
      using assms unfolding adj_def by auto
    then show False using h by blast
  qed
qed

section \<open>The endpoint bound in the regime \<open>m \<ge> n(n-1)/2\<close>\<close>

text \<open>Rows are \<open>< m\<close>, columns \<open>< n\<close>, and the base is maximum: \<open>|E\<^sub>1| = m + n(n-1)/2\<close>. Then the
  number of endpoints (occupied cells outside the base), which is twice the number of pairs, is at most
  \<open>(n-2) m - n(n-1)/2 + 1\<close>.\<close>

locale max_base_count = max_base_regime +
  fixes m :: nat
  assumes rows: "\<And>c. c \<in> Occ \<Longrightarrow> fst c < m"
    and occ_cols: "\<And>c. c \<in> Occ \<Longrightarrow> snd c < n"
    and card_E1: "card E1 = m + n * (n - 1) div 2"
begin

theorem endpoint_bound:
  "card (Occ - E1) + n * (n - 1) div 2 \<le> (n - 2) * m + 1"
proof -
  let ?S = "{..<m} \<times> {..<n}"
  have occS: "Occ \<subseteq> ?S" using rows occ_cols by (auto simp: mem_Times_iff)
  have finS: "finite ?S" by simp
  have finO: "finite Occ" by (rule finite_subset[OF occS finS])
  have E1O: "E1 \<subseteq> Occ" using E1_in_Occ by blast
  have cOE: "card (Occ - E1) = card Occ - card E1"
    by (rule card_Diff_subset[OF finite_subset[OF E1O finO] E1O])
  have eO: "card E1 \<le> card Occ" by (rule card_mono[OF finO E1O])
  let ?R = "{r. r < m \<and> \<not> full r}"
  let ?FR = "{r. r < m \<and> full r}"
  have finm: "finite {..<m}" by simp
  have finFR: "finite ?FR" by (rule finite_subset[OF _ finm]) auto
  have FR1: "card ?FR \<le> 1"
  proof -
    have "\<forall>a\<in>?FR. \<forall>b\<in>?FR. a = b" using at_most_one_full_row by blast
    then show ?thesis using card_le_Suc0_iff_eq[OF finFR] by simp
  qed
  have split: "{..<m} = ?R \<union> ?FR" by auto
  have "m = card ({..<m})" by simp
  also have "\<dots> \<le> card ?R + card ?FR" unfolding split by (rule card_Un_le)
  finally have mR: "m \<le> card ?R + 1" using FR1 by simp
  have RS: "?R \<subseteq> fst ` (?S - Occ)"
  proof
    fix r assume r: "r \<in> ?R"
    then have "\<not> full r" "r < m" by auto
    then obtain j where "j < n" "(r, j) \<notin> Occ" unfolding full_def by auto
    then show "r \<in> fst ` (?S - Occ)" using r by (force intro: image_eqI[of _ _ "(r, j)"])
  qed
  have finSO: "finite (?S - Occ)" by simp
  have "card ?R \<le> card (fst ` (?S - Occ))" by (rule card_mono[OF finite_imageI[OF finSO] RS])
  also have "\<dots> \<le> card (?S - Occ)" by (rule card_image_le[OF finSO])
  also have "\<dots> = card ?S - card Occ" by (rule card_Diff_subset[OF finO occS])
  finally have Rb: "card ?R \<le> m * n - card Occ" by simp
  have cS: "card Occ \<le> m * n" using card_mono[OF finS occS] by simp
  have nk: "n = (n - 2) + 2" using n3 by simp
  obtain k where kk: "k = n - 2" by blast
  then have nk: "n = k + 2" using n3 by simp
  have mn: "m * n = m * k + 2 * m" using nk by (simp add: algebra_simps)
  have nm: "(n - 2) * m = m * k" using nk by simp
  show ?thesis
    using card_E1 cOE eO mR Rb cS unfolding mn nm by arith
qed

end

section \<open>The weak gap in three columns\<close>

text \<open>With \<open>z_wL(m,3) = m + 3 + \<lfloor>(2m-4)/3\<rfloor>\<close> (Qi, Löfberg and Chen, Thm. 26, for \<open>m \<ge> 16\<close>) and
  \<open>z_L(m,3) = m + 3 + \<lfloor>(m-2)/2\<rfloor>\<close> (Theorem A), the gap is \<open>\<lfloor>(2m-4)/3\<rfloor> - \<lfloor>(m-2)/2\<rfloor>\<close>, and six times it
  differs from \<open>m - 2\<close> by less than six.\<close>

lemma weak_gap_arith:
  fixes m :: int
  assumes "2 \<le> m"
  shows "m - 8 < 6 * ((2 * m - 4) div 3 - (m - 2) div 2) \<and> 6 * ((2 * m - 4) div 3 - (m - 2) div 2) < m + 4"
  using assms by presburger

end
