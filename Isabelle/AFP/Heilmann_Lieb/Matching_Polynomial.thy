(*  Title:      Matching_Polynomial.thy
    Author:     Carles Marín

The matching polynomial of a finite simple graph and its vertex recurrence.
*)

theory Matching_Polynomial
  imports "HOL-Computational_Algebra.Polynomial"
begin

section \<open>Graphs and matchings\<close>

text \<open>A finite simple graph is given by a finite vertex set \<open>V\<close> and a set \<open>E\<close> of two-element subsets of
  \<open>V\<close>. A matching is a set of pairwise disjoint edges.\<close>

definition graph :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "graph V E \<longleftrightarrow> finite V \<and> (\<forall>e\<in>E. card e = 2 \<and> e \<subseteq> V)"

definition matching :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "matching E M \<longleftrightarrow> M \<subseteq> E \<and> pairwise disjnt M"

definition matchings :: "'a set set \<Rightarrow> 'a set set set" where
  "matchings E = {M. matching E M}"

lemma graph_finite_E: "graph V E \<Longrightarrow> finite E"
  unfolding graph_def by (meson Pow_iff finite_Pow_iff finite_subset subsetI)

lemma finite_matchings: "finite E \<Longrightarrow> finite (matchings E)"
  by (rule finite_subset[of _ "Pow E"]) (auto simp: matchings_def matching_def)

lemma matching_finite: "graph V E \<Longrightarrow> matching E M \<Longrightarrow> finite M"
  using graph_finite_E finite_subset unfolding matching_def by blast

lemma card_Union_matching:
  assumes G: "graph V E" and M: "matching E M"
  shows "card (\<Union>M) = 2 * card M"
proof -
  have fin: "finite M" using matching_finite[OF G M] .
  have two: "\<And>e. e \<in> M \<Longrightarrow> card e = 2" using G M unfolding graph_def matching_def by blast
  have fe: "\<And>e. e \<in> M \<Longrightarrow> finite e" using two by (metis card.infinite zero_neq_numeral)
  have "card (\<Union>M) = sum card M"
    using M fin fe unfolding matching_def by (intro card_Union_disjoint) auto
  also have "\<dots> = sum (\<lambda>_. 2) M" using two by (rule sum.cong[OF refl])
  finally show ?thesis by simp
qed

lemma matching_card_le:
  assumes G: "graph V E" and M: "matching E M" and S: "\<Union>M \<subseteq> S" and fS: "finite S"
  shows "2 * card M \<le> card S"
  using card_mono[OF fS S] card_Union_matching[OF G M] by simp

section \<open>The matching polynomial\<close>

text \<open>Multiplication by \<open>x\<close> (stated here so as not to depend on the name of the library lemma, which changed
  between Isabelle versions).\<close>

lemma x_mult: "[:0, 1:] * p = pCons 0 (p :: 'a :: comm_semiring_1 poly)"
  by (simp add: mult_pCons_left)

definition mu :: "'a set \<Rightarrow> 'a set set \<Rightarrow> real poly" where
  "mu V E = (\<Sum>M\<in>matchings E. (-1) ^ card M * monom 1 (card V - 2 * card M))"

text \<open>Deleting a vertex, and deleting two vertices.\<close>

definition del1 :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set set" where
  "del1 E v = {e\<in>E. v \<notin> e}"

definition del2 :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set set" where
  "del2 E u v = {e\<in>E. u \<notin> e \<and> v \<notin> e}"

definition nbrs :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "nbrs E v = {u. {v, u} \<in> E}"

lemma graph_del1: "graph V E \<Longrightarrow> graph (V - {v}) (del1 E v)"
  unfolding graph_def del1_def by blast

lemma graph_del2: "graph V E \<Longrightarrow> graph (V - {u, v}) (del2 E u v)"
  unfolding graph_def del2_def by blast

lemma nbrs_sub:
  assumes G: "graph V E" and v: "v \<in> V"
  shows "nbrs E v \<subseteq> V - {v}"
proof
  fix u assume u: "u \<in> nbrs E v"
  then have e: "{v, u} \<in> E" by (simp add: nbrs_def)
  then have "card {v, u} = 2" "{v, u} \<subseteq> V" using G unfolding graph_def by blast+
  then show "u \<in> V - {v}" by (cases "u = v") auto
qed

subsection \<open>Splitting the matchings at a vertex\<close>

lemma matchings_avoid:
  "{M \<in> matchings E. v \<notin> \<Union>M} = matchings (del1 E v)"
  unfolding matchings_def matching_def del1_def by blast

lemma matchings_cover:
  assumes G: "graph V E" and v: "v \<in> V"
  shows "{M \<in> matchings E. v \<in> \<Union>M} = (\<Union>u\<in>nbrs E v. insert {v, u} ` matchings (del2 E u v))"
    (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix M assume "M \<in> ?L"
    then have M: "matching E M" and vM: "v \<in> \<Union>M" by (auto simp: matchings_def)
    obtain e where e: "e \<in> M" "v \<in> e" using vM by blast
    have eE: "e \<in> E" using M e unfolding matching_def by blast
    then have ce: "card e = 2" using G unfolding graph_def by blast
    obtain u where eu: "e = {v, u}" "u \<noteq> v"
    proof -
      obtain a b where ab: "e = {a, b}" "a \<noteq> b" using ce by (metis card_2_iff)
      show ?thesis
        using that ab e(2) by (metis doubleton_eq_iff insertE singletonD)
    qed
    have un: "u \<in> nbrs E v" using eE eu by (simp add: nbrs_def)
    have rest: "M - {e} \<in> matchings (del2 E u v)"
    proof -
      have avoid: "u \<notin> f \<and> v \<notin> f" if f: "f \<in> M - {e}" for f
      proof -
        have "disjnt f e" using M e(1) f unfolding matching_def pairwise_def by auto
        then show ?thesis using eu(1) unfolding disjnt_def by auto
      qed
      have sub: "M - {e} \<subseteq> del2 E u v" using M avoid unfolding matching_def del2_def by auto
      have pw: "pairwise disjnt (M - {e})" using M unfolding matching_def by (meson Diff_subset pairwise_subset)
      show ?thesis using sub pw by (simp add: matchings_def matching_def)
    qed
    have "M = insert {v, u} (M - {e})" using e eu by blast
    then show "M \<in> ?R" using un rest by blast
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix M assume "M \<in> ?R"
    then obtain u M' where u: "u \<in> nbrs E v" and M': "M' \<in> matchings (del2 E u v)" and MM: "M = insert {v, u} M'"
      by blast
    have eE: "{v, u} \<in> E" using u by (simp add: nbrs_def)
    have m': "matching (del2 E u v) M'" using M' by (simp add: matchings_def)
    have "matching E M"
      using m' eE unfolding MM matching_def del2_def pairwise_def disjnt_def by blast
    then show "M \<in> ?L" using MM by (auto simp: matchings_def)
  qed
qed

lemma insert_edge_disjoint:
  assumes "u \<noteq> u'" "u \<in> nbrs E v" "u' \<in> nbrs E v"
  shows "insert {v, u} ` matchings (del2 E u v) \<inter> insert {v, u'} ` matchings (del2 E u' v) = {}"
proof -
  { fix M' M'' assume M': "M' \<in> matchings (del2 E u v)" and M'': "M'' \<in> matchings (del2 E u' v)"
      and eq: "insert {v, u} M' = insert {v, u'} M''"
    have "{v, u'} \<in> insert {v, u'} M''" by simp
    then have "{v, u'} \<in> insert {v, u} M'" by (simp only: eq)
    moreover have "{v, u'} \<noteq> {v, u}" using assms(1) by (metis doubleton_eq_iff)
    ultimately have "{v, u'} \<in> M'" by blast
    then have False using M' unfolding matchings_def matching_def del2_def by blast }
  then show ?thesis by blast
qed

lemma inj_insert_edge: "inj_on (insert {v, u}) (matchings (del2 E u v))"
proof (rule inj_onI)
  fix M' M'' assume "M' \<in> matchings (del2 E u v)" "M'' \<in> matchings (del2 E u v)"
    and "insert {v, u} M' = insert {v, u} M''"
  moreover have "{v, u} \<notin> M'" "{v, u} \<notin> M''"
    using calculation(1,2) unfolding matchings_def matching_def del2_def by blast+
  ultimately show "M' = M''" by (metis insert_ident)
qed

subsection \<open>The vertex recurrence\<close>

theorem mu_recurrence:
  assumes G: "graph V E" and v: "v \<in> V"
  shows "mu V E = [:0, 1:] * mu (V - {v}) (del1 E v)
                 - (\<Sum>u\<in>nbrs E v. mu (V - {u, v}) (del2 E u v))"
proof -
  let ?n = "card V"
  let ?f = "\<lambda>M. (-1) ^ card M * monom (1::real) (?n - 2 * card M)"
  have fV: "finite V" using G by (simp add: graph_def)
  have fE: "finite E" using graph_finite_E[OF G] .
  have fM: "finite (matchings E)" using finite_matchings[OF fE] .
  have split: "matchings E = {M \<in> matchings E. v \<notin> \<Union>M} \<union> {M \<in> matchings E. v \<in> \<Union>M}" by blast
  have "mu V E = sum ?f {M \<in> matchings E. v \<notin> \<Union>M} + sum ?f {M \<in> matchings E. v \<in> \<Union>M}"
    unfolding mu_def by (subst split, rule sum.union_disjoint) (use fM in auto)
  moreover have A: "sum ?f {M \<in> matchings E. v \<notin> \<Union>M} = [:0, 1:] * mu (V - {v}) (del1 E v)"
  proof -
    have "sum ?f (matchings (del1 E v)) = [:0, 1:] * mu (V - {v}) (del1 E v)"
      unfolding mu_def sum_distrib_left
    proof (rule sum.cong[OF refl])
      fix M assume "M \<in> matchings (del1 E v)"
      then have Md: "matching (del1 E v) M" by (simp add: matchings_def)
      have sub: "\<Union>M \<subseteq> V - {v}" using Md G unfolding matching_def del1_def graph_def by auto
      have le: "2 * card M \<le> card (V - {v})" using matching_card_le[OF graph_del1[OF G] Md sub] fV by simp
      have n1: "card (V - {v}) = ?n - 1" using v fV by (simp add: card_Diff_singleton)
      have pos: "0 < ?n" using v fV card_gt_0_iff by blast
      have k: "?n - 2 * card M = Suc (card (V - {v}) - 2 * card M)" using le n1 pos by linarith
      show "?f M = [:0, 1:] * ((-1) ^ card M * monom 1 (card (V - {v}) - 2 * card M))"
        unfolding k by (simp add: monom_Suc x_mult algebra_simps)
    qed
    then show ?thesis using matchings_avoid by metis
  qed
  moreover have B: "sum ?f {M \<in> matchings E. v \<in> \<Union>M} = (\<Sum>u\<in>nbrs E v. - mu (V - {u, v}) (del2 E u v))"
  proof -
    have fN: "finite (nbrs E v)" using nbrs_sub[OF G v] fV finite_subset by blast
    have "sum ?f {M \<in> matchings E. v \<in> \<Union>M}
        = (\<Sum>u\<in>nbrs E v. sum ?f (insert {v, u} ` matchings (del2 E u v)))"
    proof -
      have finA: "\<forall>i\<in>nbrs E v. finite (insert {v, i} ` matchings (del2 E i v))"
        using fE by (simp add: finite_matchings del2_def)
      have disj: "\<forall>i\<in>nbrs E v. \<forall>j\<in>nbrs E v. i \<noteq> j \<longrightarrow>
          insert {v, i} ` matchings (del2 E i v) \<inter> insert {v, j} ` matchings (del2 E j v) = {}"
      proof (intro ballI impI)
        fix i j assume ij: "i \<in> nbrs E v" "j \<in> nbrs E v" "i \<noteq> j"
        show "insert {v, i} ` matchings (del2 E i v) \<inter> insert {v, j} ` matchings (del2 E j v) = {}"
          using ij(3) ij(1) ij(2) by (rule insert_edge_disjoint)
      qed
      show ?thesis unfolding matchings_cover[OF G v] by (rule sum.UNION_disjoint[OF fN finA disj])
    qed
    also have "\<dots> = (\<Sum>u\<in>nbrs E v. - mu (V - {u, v}) (del2 E u v))"
    proof (rule sum.cong[OF refl])
      fix u assume u: "u \<in> nbrs E v"
      have uV: "u \<in> V" "u \<noteq> v" using nbrs_sub[OF G v] u by blast+
      have cuv: "card (V - {u, v}) = ?n - 2" using uV v fV by (simp add: card_Diff_subset)
      have "sum ?f (insert {v, u} ` matchings (del2 E u v)) = sum (?f \<circ> insert {v, u}) (matchings (del2 E u v))"
        by (rule sum.reindex[OF inj_insert_edge])
      also have "\<dots> = (\<Sum>M\<in>matchings (del2 E u v). - ((-1) ^ card M * monom 1 (card (V - {u, v}) - 2 * card M)))"
      proof (rule sum.cong[OF refl])
        fix M assume M: "M \<in> matchings (del2 E u v)"
        then have Md: "matching (del2 E u v) M" by (simp add: matchings_def)
        have fMM: "finite M" using matching_finite[OF graph_del2[OF G] Md] .
        have nin: "{v, u} \<notin> M" using M unfolding matchings_def matching_def del2_def by blast
        have ci: "card (insert {v, u} M) = Suc (card M)" using fMM nin by simp
        have sub2: "\<Union>M \<subseteq> V - {u, v}" using Md G unfolding matching_def del2_def graph_def by auto
        have "2 * card M \<le> card (V - {u, v})" using matching_card_le[OF graph_del2[OF G] Md sub2] fV by simp
        then have e: "?n - 2 * Suc (card M) = card (V - {u, v}) - 2 * card M" using cuv by simp
        show "(?f \<circ> insert {v, u}) M = - ((-1) ^ card M * monom 1 (card (V - {u, v}) - 2 * card M))"
          unfolding comp_def ci e by simp
      qed
      also have "\<dots> = - mu (V - {u, v}) (del2 E u v)" unfolding mu_def by (simp add: sum_negf)
      finally show "sum ?f (insert {v, u} ` matchings (del2 E u v)) = - mu (V - {u, v}) (del2 E u v)" .
    qed
    finally show ?thesis .
  qed
  ultimately show ?thesis by (simp add: sum_negf)
qed

end
