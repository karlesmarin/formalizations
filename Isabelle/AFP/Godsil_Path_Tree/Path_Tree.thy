(*  Title:      Path_Tree.thy
    Author:     Carles Marín

Godsil's path tree: the matching polynomial of a graph and of its path tree are related by
mu (G - u) * mu T = mu G * mu (T - root).
*)

theory Path_Tree
  imports Heilmann_Lieb.Matching_Polynomial
begin

section \<open>The path tree\<close>

text \<open>The vertices of the path tree of \<open>G\<close> at \<open>u\<close> are the simple paths of \<open>G\<close> that start at \<open>u\<close>, as lists of
  vertices; a path is joined to each of its one-step extensions.\<close>

definition is_path :: "'a set set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_path E p \<longleftrightarrow> p \<noteq> [] \<and> distinct p \<and> (\<forall>i. Suc i < length p \<longrightarrow> {p ! i, p ! Suc i} \<in> E)"

definition pt_V :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a list set" where
  "pt_V V E u = {p. is_path E p \<and> hd p = u \<and> set p \<subseteq> V}"

definition pt_E :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a list set set" where
  "pt_E V E u = {{p, p @ [w]} | p w. p \<in> pt_V V E u \<and> p @ [w] \<in> pt_V V E u}"

lemma pt_root: "u \<in> V \<Longrightarrow> [u] \<in> pt_V V E u"
  by (simp add: pt_V_def is_path_def)

lemma graph_pt: "graph V E \<Longrightarrow> u \<in> V \<Longrightarrow> graph (pt_V V E u) (pt_E V E u)"
proof -
  assume G: "graph V E" and u: "u \<in> V"
  have fV: "finite V" using G by (simp add: graph_def)
  have sub: "pt_V V E u \<subseteq> {xs. set xs \<subseteq> V \<and> length xs \<le> card V}"
  proof
    fix p assume p: "p \<in> pt_V V E u"
    then have d: "distinct p" and s: "set p \<subseteq> V" by (auto simp: pt_V_def is_path_def)
    have "length p = card (set p)" using d by (simp add: distinct_card)
    also have "\<dots> \<le> card V" using card_mono[OF fV s] .
    finally show "p \<in> {xs. set xs \<subseteq> V \<and> length xs \<le> card V}" using s by simp
  qed
  have fin: "finite (pt_V V E u)"
    by (rule finite_subset[OF sub finite_lists_length_le[OF fV]])
  have edges: "\<forall>e\<in>pt_E V E u. card e = 2 \<and> e \<subseteq> pt_V V E u"
  proof
    fix e assume "e \<in> pt_E V E u"
    then obtain p w where e: "e = {p, p @ [w]}" and p: "p \<in> pt_V V E u" and pw: "p @ [w] \<in> pt_V V E u"
      by (auto simp: pt_E_def)
    have ne: "p \<noteq> p @ [w]" by simp
    show "card e = 2 \<and> e \<subseteq> pt_V V E u" using e p pw ne by simp
  qed
  show ?thesis unfolding graph_def using fin edges by blast
qed

section \<open>Matchings under renaming and unions\<close>

lemma matching_image:
  assumes inj: "inj_on f V" and sub: "\<forall>e\<in>E. e \<subseteq> V" and m: "matching E M"
  shows "matching ((`) f ` E) ((`) f ` M)"
proof -
  have s: "(`) f ` M \<subseteq> (`) f ` E" using m unfolding matching_def by blast
  have "pairwise disjnt ((`) f ` M)"
  proof (rule pairwiseI)
    fix a b assume a: "a \<in> (`) f ` M" and b: "b \<in> (`) f ` M" and ne: "a \<noteq> b"
    obtain e where e: "e \<in> M" "a = f ` e" using a by blast
    obtain d where d: "d \<in> M" "b = f ` d" using b by blast
    have ed: "e \<noteq> d" using ne e d by blast
    have pm: "pairwise disjnt M" using m unfolding matching_def by simp
    have "disjnt e d" by (rule pairwiseD[OF pm e(1) d(1) ed])
    then have i0: "e \<inter> d = {}" by (simp add: disjnt_def)
    have eV: "e \<subseteq> V" and dV: "d \<subseteq> V" using m e(1) d(1) sub unfolding matching_def by blast+
    have "f ` e \<inter> f ` d = f ` (e \<inter> d)" using inj_on_image_Int[OF inj eV dV] by simp
    then show "disjnt a b" using i0 e(2) d(2) by (simp add: disjnt_def)
  qed
  then show ?thesis using s unfolding matching_def by blast
qed

lemma matching_preimage:
  assumes inj: "inj_on f V" and sub: "\<forall>e\<in>E. e \<subseteq> V" and m: "matching ((`) f ` E) M'"
  shows "\<exists>M. matching E M \<and> M' = (`) f ` M"
proof -
  let ?M = "{e\<in>E. f ` e \<in> M'}"
  have eq: "M' = (`) f ` ?M"
  proof
    show "M' \<subseteq> (`) f ` ?M" using m unfolding matching_def by blast
    show "(`) f ` ?M \<subseteq> M'" by blast
  qed
  have "pairwise disjnt ?M"
  proof (rule pairwiseI)
    fix e d assume e: "e \<in> ?M" and d: "d \<in> ?M" and ed: "e \<noteq> d"
    have eV: "e \<subseteq> V" and dV: "d \<subseteq> V" using e d sub by blast+
    have ne: "f ` e \<noteq> f ` d" using inj_on_image_eq_iff[OF inj eV dV] ed by simp
    have pm: "pairwise disjnt M'" using m unfolding matching_def by simp
    have em: "f ` e \<in> M'" and dm: "f ` d \<in> M'" using e d by simp_all
    have "disjnt (f ` e) (f ` d)" by (rule pairwiseD[OF pm em dm ne])
    then have "f ` (e \<inter> d) = {}"
      using inj_on_image_Int[OF inj eV dV] by (simp add: disjnt_def)
    then show "disjnt e d" by (simp add: disjnt_def)
  qed
  moreover have "?M \<subseteq> E" by blast
  ultimately show ?thesis using eq unfolding matching_def by blast
qed

lemma mu_empty: "mu {} {} = 1"
proof -
  have "matchings ({} :: 'a set set) = {{}}" by (auto simp: matchings_def matching_def)
  then show ?thesis by (simp add: mu_def)
qed

lemma graph_UNION:
  assumes "finite I" and "\<forall>i\<in>I. graph (Vs i) (Es i)"
  shows "graph (\<Union>i\<in>I. Vs i) (\<Union>i\<in>I. Es i)"
  using assms unfolding graph_def by auto

section \<open>Renaming vertices and disjoint unions\<close>

lemma mu_bij:
  assumes G: "graph V E" and B: "bij_betw f V W"
  shows "mu W ((`) f ` E) = mu V E"
proof -
  have injV: "inj_on f V" using B by (simp add: bij_betw_def)
  have sub: "\<forall>e\<in>E. e \<subseteq> V" using G unfolding graph_def by blast
  have injE: "inj_on ((`) f) E"
  proof (rule inj_onI)
    fix a b assume a: "a \<in> E" and b: "b \<in> E" and "f ` a = f ` b"
    then show "a = b" using inj_on_image_eq_iff[OF injV] sub by blast
  qed
  have mt: "matchings ((`) f ` E) = (\<lambda>M. (`) f ` M) ` matchings E"
  proof
    show "matchings ((`) f ` E) \<subseteq> (\<lambda>M. (`) f ` M) ` matchings E"
    proof
      fix M' assume "M' \<in> matchings ((`) f ` E)"
      then have mm: "matching ((`) f ` E) M'" by (simp add: matchings_def)
      obtain M where "matching E M" "M' = (`) f ` M"
        using matching_preimage[OF injV sub mm] by blast
      then show "M' \<in> (\<lambda>M. (`) f ` M) ` matchings E" by (auto simp: matchings_def)
    qed
    show "(\<lambda>M. (`) f ` M) ` matchings E \<subseteq> matchings ((`) f ` E)"
      using matching_image[OF injV sub] by (auto simp: matchings_def)
  qed
  have injh: "inj_on (\<lambda>M. (`) f ` M) (matchings E)"
  proof (rule inj_onI)
    fix M N assume M: "M \<in> matchings E" and N: "N \<in> matchings E" and eq: "(`) f ` M = (`) f ` N"
    have "M \<subseteq> E" "N \<subseteq> E" using M N by (auto simp: matchings_def matching_def)
    then show "M = N" using inj_on_image_eq_iff[OF injE] eq by simp
  qed
  have cW: "card W = card V" using bij_betw_same_card[OF B] by simp
  have "mu W ((`) f ` E) = (\<Sum>M'\<in>(\<lambda>M. (`) f ` M) ` matchings E. (-1) ^ card M' * monom 1 (card W - 2 * card M'))"
    unfolding mu_def mt by simp
  also have "\<dots> = (\<Sum>M\<in>matchings E. (-1) ^ card ((`) f ` M) * monom 1 (card W - 2 * card ((`) f ` M)))"
    by (rule sum.reindex[OF injh, unfolded comp_def])
  also have "\<dots> = mu V E" unfolding mu_def
  proof (rule sum.cong[OF refl])
    fix M assume M: "M \<in> matchings E"
    then have "M \<subseteq> E" by (auto simp: matchings_def matching_def)
    then have "card ((`) f ` M) = card M" using card_image[OF inj_on_subset[OF injE]] by simp
    then show "(-1) ^ card ((`) f ` M) * monom 1 (card W - 2 * card ((`) f ` M)) =
        (-1) ^ card M * monom 1 (card V - 2 * card M)" using cW by simp
  qed
  finally show ?thesis .
qed

lemma mu_disjoint_union:
  assumes G1: "graph V1 E1" and G2: "graph V2 E2" and dj: "V1 \<inter> V2 = {}"
  shows "mu (V1 \<union> V2) (E1 \<union> E2) = mu V1 E1 * mu V2 E2"
proof -
  have f1: "finite V1" and f2: "finite V2" using G1 G2 by (simp_all add: graph_def)
  have s1: "\<forall>e\<in>E1. e \<subseteq> V1" and s2: "\<forall>e\<in>E2. e \<subseteq> V2" using G1 G2 unfolding graph_def by blast+
  have E12: "E1 \<inter> E2 = {}"
  proof (rule ccontr)
    assume "E1 \<inter> E2 \<noteq> {}"
    then obtain e where e1: "e \<in> E1" and e2: "e \<in> E2" by blast
    have "e \<subseteq> V1 \<inter> V2" using s1 s2 e1 e2 by blast
    then have "e = {}" using dj by blast
    moreover have "card e = 2" using G1 e1 unfolding graph_def by blast
    ultimately show False by simp
  qed
  have cross: "\<And>e d. e \<in> E1 \<Longrightarrow> d \<in> E2 \<Longrightarrow> disjnt e d"
  proof -
    fix e d assume "e \<in> E1" "d \<in> E2"
    then have "e \<subseteq> V1" "d \<subseteq> V2" using s1 s2 by blast+
    then show "disjnt e d" using dj unfolding disjnt_def by blast
  qed
  let ?A = "matchings E1" and ?B = "matchings E2"
  let ?u = "\<lambda>z :: 'a set set \<times> 'a set set. fst z \<union> snd z"
  have mt: "matchings (E1 \<union> E2) = ?u ` (?A \<times> ?B)"
  proof
    show "?u ` (?A \<times> ?B) \<subseteq> matchings (E1 \<union> E2)"
    proof
      fix M assume "M \<in> ?u ` (?A \<times> ?B)"
      then obtain M1 M2 where M: "M = M1 \<union> M2" and m1: "matching E1 M1" and m2: "matching E2 M2"
        by (auto simp: matchings_def)
      have "pairwise disjnt M"
      proof (rule pairwiseI)
        fix x y assume x: "x \<in> M" and y: "y \<in> M" and xy: "x \<noteq> y"
        have p1: "pairwise disjnt M1" and p2: "pairwise disjnt M2" using m1 m2 unfolding matching_def by blast+
        have M1E: "M1 \<subseteq> E1" and M2E: "M2 \<subseteq> E2" using m1 m2 unfolding matching_def by blast+
        show "disjnt x y"
        proof (cases "x \<in> M1")
          case True
          show ?thesis
          proof (cases "y \<in> M1")
            case True
            then show ?thesis using \<open>x \<in> M1\<close> p1 xy unfolding pairwise_def by blast
          next
            case False
            then have "y \<in> M2" using y M by blast
            then show ?thesis using cross \<open>x \<in> M1\<close> M1E M2E by blast
          qed
        next
          case False
          then have xM2: "x \<in> M2" using x M by blast
          show ?thesis
          proof (cases "y \<in> M1")
            case True
            then show ?thesis using cross xM2 M1E M2E by (metis disjnt_sym subsetD)
          next
            case False
            then have "y \<in> M2" using y M by blast
            then show ?thesis using xM2 p2 xy unfolding pairwise_def by blast
          qed
        qed
      qed
      moreover have "M \<subseteq> E1 \<union> E2" using m1 m2 M unfolding matching_def by blast
      ultimately show "M \<in> matchings (E1 \<union> E2)" by (simp add: matchings_def matching_def)
    qed
    show "matchings (E1 \<union> E2) \<subseteq> ?u ` (?A \<times> ?B)"
    proof
      fix M assume "M \<in> matchings (E1 \<union> E2)"
      then have m: "matching (E1 \<union> E2) M" by (simp add: matchings_def)
      then have sM: "M \<subseteq> E1 \<union> E2" and pM: "pairwise disjnt M" unfolding matching_def by blast+
      have p1: "pairwise disjnt (M \<inter> E1)" by (rule pairwise_subset[OF pM Int_lower1])
      have p2: "pairwise disjnt (M \<inter> E2)" by (rule pairwise_subset[OF pM Int_lower1])
      have m1: "M \<inter> E1 \<in> ?A" unfolding matchings_def matching_def using p1 by simp
      have m2: "M \<inter> E2 \<in> ?B" unfolding matchings_def matching_def using p2 by simp
      have eq: "M = (M \<inter> E1) \<union> (M \<inter> E2)" using sM by blast
      have mem: "(M \<inter> E1, M \<inter> E2) \<in> ?A \<times> ?B" using m1 m2 by simp
      show "M \<in> ?u ` (?A \<times> ?B)"
        by (rule image_eqI[OF _ mem]) (simp add: eq[symmetric])
    qed
  qed
  have inj: "inj_on ?u (?A \<times> ?B)"
  proof (rule inj_onI)
    fix z w assume z: "z \<in> ?A \<times> ?B" and w: "w \<in> ?A \<times> ?B" and eq: "?u z = ?u w"
    have zs: "fst z \<subseteq> E1" "snd z \<subseteq> E2" and ws: "fst w \<subseteq> E1" "snd w \<subseteq> E2"
      using z w by (auto simp: matchings_def matching_def)
    have "fst z = fst w"
      using eq zs ws E12 by (auto simp: set_eq_iff) blast+
    moreover have "snd z = snd w"
      using eq zs ws E12 by (auto simp: set_eq_iff) blast+
    ultimately show "z = w" by (simp add: prod_eq_iff)
  qed
  have cV: "card (V1 \<union> V2) = card V1 + card V2" using card_Un_disjoint[OF f1 f2 dj] .
  have le1: "\<And>M. M \<in> ?A \<Longrightarrow> 2 * card M \<le> card V1"
  proof -
    fix M assume M: "M \<in> ?A"
    then have m: "matching E1 M" by (simp add: matchings_def)
    have "\<Union>M \<subseteq> V1" using m s1 unfolding matching_def by blast
    then show "2 * card M \<le> card V1" using matching_card_le[OF G1 m _ f1] by blast
  qed
  have le2: "\<And>M. M \<in> ?B \<Longrightarrow> 2 * card M \<le> card V2"
  proof -
    fix M assume M: "M \<in> ?B"
    then have m: "matching E2 M" by (simp add: matchings_def)
    have "\<Union>M \<subseteq> V2" using m s2 unfolding matching_def by blast
    then show "2 * card M \<le> card V2" using matching_card_le[OF G2 m _ f2] by blast
  qed
  have "mu V1 E1 * mu V2 E2 =
      (\<Sum>M1\<in>?A. \<Sum>M2\<in>?B. ((-1) ^ card M1 * monom 1 (card V1 - 2 * card M1)) *
                          ((-1) ^ card M2 * monom 1 (card V2 - 2 * card M2)))"
    unfolding mu_def by (rule sum_product)
  also have "\<dots> = (\<Sum>z\<in>?A \<times> ?B. ((-1) ^ card (fst z) * monom 1 (card V1 - 2 * card (fst z))) *
                          ((-1) ^ card (snd z) * monom 1 (card V2 - 2 * card (snd z))))"
    by (simp add: sum.cartesian_product case_prod_beta)
  also have "\<dots> = (\<Sum>z\<in>?A \<times> ?B. (-1) ^ card (?u z) * monom 1 (card (V1 \<union> V2) - 2 * card (?u z)))"
  proof (rule sum.cong[OF refl])
    fix z assume z: "z \<in> ?A \<times> ?B"
    then have zA: "fst z \<in> ?A" and zB: "snd z \<in> ?B" by auto
    have fa: "finite (fst z)" and fb: "finite (snd z)"
      using zA zB graph_finite_E[OF G1] graph_finite_E[OF G2]
      by (auto simp: matchings_def matching_def intro: finite_subset)
    have dd: "fst z \<inter> snd z = {}"
      using zA zB E12 by (auto simp: matchings_def matching_def)
    have cc: "card (?u z) = card (fst z) + card (snd z)" using card_Un_disjoint[OF fa fb dd] by simp
    have ex: "card (V1 \<union> V2) - 2 * (card (fst z) + card (snd z)) = (card V1 - 2 * card (fst z)) + (card V2 - 2 * card (snd z))"
      using le1[OF zA] le2[OF zB] cV by simp
    show "(-1) ^ card (fst z) * monom 1 (card V1 - 2 * card (fst z)) *
          ((-1) ^ card (snd z) * monom 1 (card V2 - 2 * card (snd z))) =
          (-1) ^ card (?u z) * monom 1 (card (V1 \<union> V2) - 2 * card (?u z))"
      unfolding cc ex by (simp add: power_add mult_monom mult_ac)
  qed
  also have "\<dots> = (\<Sum>M\<in>?u ` (?A \<times> ?B). (-1) ^ card M * monom 1 (card (V1 \<union> V2) - 2 * card M))"
    by (rule sum.reindex[OF inj, unfolded comp_def, symmetric])
  also have "\<dots> = mu (V1 \<union> V2) (E1 \<union> E2)" unfolding mu_def mt by simp
  finally show ?thesis by simp
qed

lemma mu_UNION:
  assumes "finite I" and "\<forall>i\<in>I. graph (Vs i) (Es i)" and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> Vs i \<inter> Vs j = {}"
  shows "mu (\<Union>i\<in>I. Vs i) (\<Union>i\<in>I. Es i) = (\<Prod>i\<in>I. mu (Vs i) (Es i))"
  using assms
proof (induct I rule: finite_induct)
  case empty
  then show ?case by (simp add: mu_empty)
next
  case (insert i I)
  have gi: "graph (Vs i) (Es i)" using insert.prems(1) by simp
  have gI: "\<forall>j\<in>I. graph (Vs j) (Es j)" using insert.prems(1) by simp
  have dI: "\<forall>j\<in>I. \<forall>k\<in>I. j \<noteq> k \<longrightarrow> Vs j \<inter> Vs k = {}" using insert.prems(2) by simp
  have gU: "graph (\<Union>j\<in>I. Vs j) (\<Union>j\<in>I. Es j)" by (rule graph_UNION[OF insert.hyps(1) gI])
  have dj: "Vs i \<inter> (\<Union>j\<in>I. Vs j) = {}"
    using insert.prems(2) insert.hyps(2) by auto
  have "mu (\<Union>j\<in>insert i I. Vs j) (\<Union>j\<in>insert i I. Es j)
      = mu (Vs i \<union> (\<Union>j\<in>I. Vs j)) (Es i \<union> (\<Union>j\<in>I. Es j))" by simp
  also have "\<dots> = mu (Vs i) (Es i) * mu (\<Union>j\<in>I. Vs j) (\<Union>j\<in>I. Es j)"
    by (rule mu_disjoint_union[OF gi gU dj])
  also have "\<dots> = mu (Vs i) (Es i) * (\<Prod>j\<in>I. mu (Vs j) (Es j))"
    using insert.hyps(3)[OF gI dI] by simp
  also have "\<dots> = (\<Prod>j\<in>insert i I. mu (Vs j) (Es j))"
    using insert.hyps by simp
  finally show ?case .
qed

section \<open>Paths\<close>

lemma is_path_Cons:
  assumes "q \<noteq> []"
  shows "is_path E (a # q) \<longleftrightarrow> {a, hd q} \<in> E \<and> a \<notin> set q \<and> is_path E q"
proof
  assume H: "is_path E (a # q)"
  have d: "distinct (a # q)" and e: "\<forall>i. Suc i < length (a # q) \<longrightarrow> {(a # q) ! i, (a # q) ! Suc i} \<in> E"
    using H unfolding is_path_def by auto
  have "{a, hd q} \<in> E" using e[rule_format, of 0] assms by (cases q) auto
  moreover have "a \<notin> set q" using d by simp
  moreover have "is_path E q"
    unfolding is_path_def
  proof (intro conjI allI impI)
    show "q \<noteq> []" by fact
    show "distinct q" using d by simp
    fix i assume "Suc i < length q"
    then show "{q ! i, q ! Suc i} \<in> E" using e[rule_format, of "Suc i"] by simp
  qed
  ultimately show "{a, hd q} \<in> E \<and> a \<notin> set q \<and> is_path E q" by blast
next
  assume H: "{a, hd q} \<in> E \<and> a \<notin> set q \<and> is_path E q"
  then have ha: "{a, hd q} \<in> E" and an: "a \<notin> set q" and pq: "is_path E q" by blast+
  have d: "distinct q" and e: "\<forall>i. Suc i < length q \<longrightarrow> {q ! i, q ! Suc i} \<in> E"
    using pq unfolding is_path_def by auto
  show "is_path E (a # q)"
    unfolding is_path_def
  proof (intro conjI allI impI)
    show "a # q \<noteq> []" by simp
    show "distinct (a # q)" using d an by simp
    fix i assume i: "Suc i < length (a # q)"
    show "{(a # q) ! i, (a # q) ! Suc i} \<in> E"
    proof (cases i)
      case 0
      then show ?thesis using ha assms by (cases q) auto
    next
      case (Suc j)
      then show ?thesis using e[rule_format, of j] i by simp
    qed
  qed
qed

lemma pt_E_I:
  "p \<in> pt_V V E u \<Longrightarrow> p @ [w] \<in> pt_V V E u \<Longrightarrow> {p, p @ [w]} \<in> pt_E V E u"
  unfolding pt_E_def by (intro CollectI exI[of _ p] exI[of _ w] conjI refl) assumption+

lemma is_path_del1:
  "is_path (del1 E u) q \<Longrightarrow> is_path E q"
  unfolding is_path_def del1_def by auto

lemma is_path_del1_rev:
  "is_path E q \<Longrightarrow> u \<notin> set q \<Longrightarrow> is_path (del1 E u) q"
  unfolding is_path_def del1_def by (auto simp: nth_mem)

section \<open>The path tree below its root\<close>

text \<open>Below the root, the path tree of \<open>G\<close> at \<open>u\<close> is the disjoint union, over the neighbours \<open>v\<close> of \<open>u\<close>, of
  copies of the path tree of \<open>G - u\<close> at \<open>v\<close> (each path prefixed by \<open>u\<close>).\<close>

lemma pt_V_minus_root:
  assumes "graph V E" and "u \<in> V"
  shows "pt_V V E u - {[u]} = (\<Union>v\<in>nbrs E u. (#) u ` pt_V (V - {u}) (del1 E u) v)"
proof (rule set_eqI)
  fix p
  show "p \<in> pt_V V E u - {[u]} \<longleftrightarrow> p \<in> (\<Union>v\<in>nbrs E u. (#) u ` pt_V (V - {u}) (del1 E u) v)"
  proof
    assume P: "p \<in> pt_V V E u - {[u]}"
    then have ip: "is_path E p" and hp: "hd p = u" and sp: "set p \<subseteq> V" and ne: "p \<noteq> [u]"
      unfolding pt_V_def by auto
    from ip have "p \<noteq> []" unfolding is_path_def by simp
    then obtain q where pq: "p = u # q" using hp by (cases p) auto
    have qne: "q \<noteq> []" using ne pq by auto
    have ic: "is_path E (u # q)" using ip pq by simp
    have c0: "{u, hd q} \<in> E \<and> u \<notin> set q \<and> is_path E q"
      using ic is_path_Cons[OF qne, of E u] by blast
    then have c: "{u, hd q} \<in> E" "u \<notin> set q" "is_path E q" by blast+
    have "hd q \<in> nbrs E u" using c(1) by (simp add: nbrs_def)
    moreover have "q \<in> pt_V (V - {u}) (del1 E u) (hd q)"
      unfolding pt_V_def using is_path_del1_rev[OF c(3) c(2)] c(2) sp pq by auto
    ultimately show "p \<in> (\<Union>v\<in>nbrs E u. (#) u ` pt_V (V - {u}) (del1 E u) v)"
      using pq by auto
  next
    assume "p \<in> (\<Union>v\<in>nbrs E u. (#) u ` pt_V (V - {u}) (del1 E u) v)"
    then obtain v q where v: "v \<in> nbrs E u" and q: "q \<in> pt_V (V - {u}) (del1 E u) v" and pq: "p = u # q"
      by auto
    from q have iq: "is_path (del1 E u) q" and hq: "hd q = v" and sq: "set q \<subseteq> V - {u}"
      unfolding pt_V_def by auto
    have qne: "q \<noteq> []" using iq unfolding is_path_def by simp
    have "is_path E (u # q)"
      using is_path_Cons[OF qne] v hq sq is_path_del1[OF iq] by (auto simp: nbrs_def)
    then show "p \<in> pt_V V E u - {[u]}"
      using pq qne sq assms(2) unfolding pt_V_def by auto
  qed
qed

lemma pt_E_minus_root:
  assumes "graph V E" and "u \<in> V"
  shows "del1 (pt_E V E u) [u] = (\<Union>v\<in>nbrs E u. (`) ((#) u) ` pt_E (V - {u}) (del1 E u) v)"
proof (rule set_eqI)
  fix e
  show "e \<in> del1 (pt_E V E u) [u] \<longleftrightarrow> e \<in> (\<Union>v\<in>nbrs E u. (`) ((#) u) ` pt_E (V - {u}) (del1 E u) v)"
  proof
    assume "e \<in> del1 (pt_E V E u) [u]"
    then have eE: "e \<in> pt_E V E u" and nu: "[u] \<notin> e" unfolding del1_def by auto
    from eE obtain p w where e: "e = {p, p @ [w]}" and p: "p \<in> pt_V V E u" and pw: "p @ [w] \<in> pt_V V E u"
      unfolding pt_E_def by auto
    have p1: "p \<in> pt_V V E u - {[u]}" using p nu e by auto
    have p2: "p @ [w] \<in> pt_V V E u - {[u]}" using pw nu e by auto
    from p1 pt_V_minus_root[OF assms] obtain v q where v: "v \<in> nbrs E u"
      and q: "q \<in> pt_V (V - {u}) (del1 E u) v" and pq: "p = u # q" by auto
    from p2 pt_V_minus_root[OF assms] obtain v' q' where v': "v' \<in> nbrs E u"
      and q': "q' \<in> pt_V (V - {u}) (del1 E u) v'" and pq': "p @ [w] = u # q'" by auto
    have qq': "q' = q @ [w]" using pq pq' by simp
    have qne: "q \<noteq> []" using q unfolding pt_V_def is_path_def by auto
    have "v' = v" using q q' qq' qne unfolding pt_V_def by (auto simp: hd_append)
    then have "q @ [w] \<in> pt_V (V - {u}) (del1 E u) v" using q' qq' by simp
    then have "{q, q @ [w]} \<in> pt_E (V - {u}) (del1 E u) v"
      by (rule pt_E_I[OF q])
    moreover have "e = (`) ((#) u) {q, q @ [w]}" using e pq by simp
    ultimately show "e \<in> (\<Union>v\<in>nbrs E u. (`) ((#) u) ` pt_E (V - {u}) (del1 E u) v)"
      by (intro UN_I[OF v] image_eqI)
  next
    assume "e \<in> (\<Union>v\<in>nbrs E u. (`) ((#) u) ` pt_E (V - {u}) (del1 E u) v)"
    then obtain v f where v: "v \<in> nbrs E u" and f: "f \<in> pt_E (V - {u}) (del1 E u) v" and ef: "e = (`) ((#) u) f"
      by auto
    from f obtain q w where fe: "f = {q, q @ [w]}" and q: "q \<in> pt_V (V - {u}) (del1 E u) v"
      and qw: "q @ [w] \<in> pt_V (V - {u}) (del1 E u) v" unfolding pt_E_def by auto
    have a: "u # q \<in> pt_V V E u - {[u]}"
      using q v pt_V_minus_root[OF assms] by auto
    have b: "u # (q @ [w]) \<in> pt_V V E u - {[u]}"
      using qw v pt_V_minus_root[OF assms] by auto
    have "e = {u # q, (u # q) @ [w]}" using ef fe by simp
    moreover have "{u # q, (u # q) @ [w]} \<in> pt_E V E u"
      by (rule pt_E_I) (use a b in auto)
    ultimately show "e \<in> del1 (pt_E V E u) [u]"
      using a b unfolding del1_def by auto
  qed
qed

lemma nbrs_pt_root:
  assumes "graph V E" and "u \<in> V"
  shows "nbrs (pt_E V E u) [u] = (\<lambda>v. [u, v]) ` nbrs E u"
proof (rule set_eqI)
  fix p
  show "p \<in> nbrs (pt_E V E u) [u] \<longleftrightarrow> p \<in> (\<lambda>v. [u, v]) ` nbrs E u"
  proof
    assume "p \<in> nbrs (pt_E V E u) [u]"
    then have "{[u], p} \<in> pt_E V E u" by (simp add: nbrs_def)
    then obtain r w where e: "{[u], p} = {r, r @ [w]}" and r: "r \<in> pt_V V E u"
      and rw: "r @ [w] \<in> pt_V V E u" unfolding pt_E_def by auto
    have rne: "r \<noteq> []" using r unfolding pt_V_def is_path_def by auto
    have ru: "r = [u]"
    proof -
      have "[u] = r \<or> [u] = r @ [w]" using e by (auto simp: doubleton_eq_iff)
      then show ?thesis using rne by (auto simp: Cons_eq_append_conv)
    qed
    have pe: "p = [u] @ [w]"
    proof -
      have "r @ [w] \<in> {[u], p}" using e by blast
      then show ?thesis using ru by auto
    qed
    have "is_path E [u, w]" using rw ru unfolding pt_V_def by simp
    then have "{u, w} \<in> E" unfolding is_path_def using allE[where x=0] by force
    then have "w \<in> nbrs E u" by (simp add: nbrs_def)
    then show "p \<in> (\<lambda>v. [u, v]) ` nbrs E u" using pe by auto
  next
    assume "p \<in> (\<lambda>v. [u, v]) ` nbrs E u"
    then obtain v where v: "v \<in> nbrs E u" and p: "p = [u, v]" by auto
    have vV: "v \<in> V - {u}" using nbrs_sub[OF assms] v by blast
    have eE: "{u, v} \<in> E" using v by (simp add: nbrs_def)
    have r: "[u] \<in> pt_V V E u" by (rule pt_root[OF assms(2)])
    have rw: "[u] @ [v] \<in> pt_V V E u"
    proof -
      have "u \<noteq> v" using vV by blast
      moreover have "v \<in> V" using vV by blast
      moreover have "\<And>i. Suc i < Suc (Suc 0) \<Longrightarrow> {[u, v] ! i, [u, v] ! Suc i} \<in> E"
        using eE by (case_tac i) auto
      ultimately show ?thesis using assms(2) unfolding pt_V_def is_path_def by auto
    qed
    have "{[u], [u] @ [v]} \<in> pt_E V E u" by (rule pt_E_I[OF r rw])
    then show "p \<in> nbrs (pt_E V E u) [u]" using p by (simp add: nbrs_def)
  qed
qed

section \<open>Branches of the path tree\<close>

definition brV :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set" where
  "brV E V u v = (#) u ` pt_V (V - {u}) (del1 E u) v"

definition brE :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set set" where
  "brE E V u v = (`) ((#) u) ` pt_E (V - {u}) (del1 E u) v"

lemma graph_image:
  assumes "graph V E" and "inj_on f V"
  shows "graph (f ` V) ((`) f ` E)"
  unfolding graph_def
proof (rule conjI)
  show "finite (f ` V)" using assms(1) by (simp add: graph_def)
next
  show "\<forall>e'\<in>(`) f ` E. card e' = 2 \<and> e' \<subseteq> f ` V"
  proof (intro ballI)
    fix e' assume "e' \<in> (`) f ` E"
    then obtain e where e: "e \<in> E" "e' = f ` e" by blast
    have ce: "card e = 2" "e \<subseteq> V" using assms(1) e(1) unfolding graph_def by blast+
    have "inj_on f e" using assms(2) ce(2) by (rule inj_on_subset)
    then show "card e' = 2 \<and> e' \<subseteq> f ` V" using e ce by (simp add: card_image image_mono)
  qed
qed

lemma inj_cons: "inj_on ((#) u) A" by (simp add: inj_on_def)

lemma graph_br:
  assumes G: "graph V E" and u: "u \<in> V" and v: "v \<in> nbrs E u"
  shows "graph (brV E V u v) (brE E V u v)"
proof -
  have "v \<in> V - {u}" using nbrs_sub[OF G u] v by blast
  then have "graph (pt_V (V - {u}) (del1 E u) v) (pt_E (V - {u}) (del1 E u) v)"
    by (rule graph_pt[OF graph_del1[OF G]])
  then show ?thesis unfolding brV_def brE_def by (rule graph_image[OF _ inj_cons])
qed

lemma mu_br:
  assumes G: "graph V E" and u: "u \<in> V" and v: "v \<in> nbrs E u"
  shows "mu (brV E V u v) (brE E V u v) = mu (pt_V (V - {u}) (del1 E u) v) (pt_E (V - {u}) (del1 E u) v)"
proof -
  have vv: "v \<in> V - {u}" using nbrs_sub[OF G u] v by blast
  have g: "graph (pt_V (V - {u}) (del1 E u) v) (pt_E (V - {u}) (del1 E u) v)"
    by (rule graph_pt[OF graph_del1[OF G] vv])
  have b: "bij_betw ((#) u) (pt_V (V - {u}) (del1 E u) v) (brV E V u v)"
    unfolding bij_betw_def brV_def by (simp add: inj_cons)
  show ?thesis using mu_bij[OF g b] unfolding brE_def brV_def by simp
qed

lemma br_cons:
  assumes "x \<in> brV E V u v"
  shows "\<exists>q. x = u # q \<and> hd q = v"
  using assms unfolding brV_def pt_V_def by auto

lemma br_disj:
  assumes "v \<noteq> w"
  shows "brV E V u v \<inter> brV E V u w = {}"
proof (rule equals0I)
  fix x assume "x \<in> brV E V u v \<inter> brV E V u w"
  then have xv: "x \<in> brV E V u v" and xw: "x \<in> brV E V u w" by simp_all
  obtain q where q: "x = u # q" "hd q = v" using br_cons[OF xv] by blast
  obtain q' where q': "x = u # q'" "hd q' = w" using br_cons[OF xw] by blast
  from q q' have "q = q'" by simp
  then show False using q(2) q'(2) assms by simp
qed

lemma br_edges_sub:
  assumes G: "graph V E" and u: "u \<in> V" and v: "v \<in> nbrs E u" and e: "e \<in> brE E V u v"
  shows "e \<subseteq> brV E V u v"
  using graph_br[OF G u v] e unfolding graph_def by blast

lemma br_root:
  assumes G: "graph V E" and u: "u \<in> V" and v: "v \<in> nbrs E u"
  shows "[u, v] \<in> brV E V u v"
proof -
  have "v \<in> V - {u}" using nbrs_sub[OF G u] v by blast
  then have "[v] \<in> pt_V (V - {u}) (del1 E u) v" by (rule pt_root)
  then show ?thesis unfolding brV_def by force
qed

lemma finite_nbrs:
  assumes "graph V E" and "u \<in> V" shows "finite (nbrs E u)"
  using nbrs_sub[OF assms] assms(1) finite_subset unfolding graph_def by blast

lemma mu_root_rest:
  assumes G: "graph V E" and u: "u \<in> V"
  shows "mu (pt_V V E u - {[u]}) (del1 (pt_E V E u) [u])
       = (\<Prod>v\<in>nbrs E u. mu (pt_V (V - {u}) (del1 E u) v) (pt_E (V - {u}) (del1 E u) v))"
proof -
  have "mu (pt_V V E u - {[u]}) (del1 (pt_E V E u) [u])
      = mu (\<Union>v\<in>nbrs E u. brV E V u v) (\<Union>v\<in>nbrs E u. brE E V u v)"
    using pt_V_minus_root[OF G u] pt_E_minus_root[OF G u] by (simp add: brV_def brE_def)
  also have "\<dots> = (\<Prod>v\<in>nbrs E u. mu (brV E V u v) (brE E V u v))"
  proof (rule mu_UNION[OF finite_nbrs[OF G u]])
      show "\<forall>i\<in>nbrs E u. graph (brV E V u i) (brE E V u i)" by (intro ballI graph_br[OF G u])
      show "\<forall>i\<in>nbrs E u. \<forall>j\<in>nbrs E u. i \<noteq> j \<longrightarrow> brV E V u i \<inter> brV E V u j = {}"
        by (intro ballI impI, rule br_disj, assumption)
    qed
  also have "\<dots> = (\<Prod>v\<in>nbrs E u. mu (pt_V (V - {u}) (del1 E u) v) (pt_E (V - {u}) (del1 E u) v))"
    by (rule prod.cong[OF refl]) (rule mu_br[OF G u])
  finally show ?thesis .
qed

lemma mu_root_rest_minus:
  assumes G: "graph V E" and u: "u \<in> V" and v: "v \<in> nbrs E u"
  shows "mu (pt_V V E u - {[u]} - {[u, v]}) (del1 (del1 (pt_E V E u) [u]) [u, v])
       = mu (pt_V (V - {u}) (del1 E u) v - {[v]}) (del1 (pt_E (V - {u}) (del1 E u) v) [v])
         * (\<Prod>w\<in>nbrs E u - {v}. mu (pt_V (V - {u}) (del1 E u) w) (pt_E (V - {u}) (del1 E u) w))"
proof -
  let ?N = "nbrs E u"
  let ?W = "\<lambda>w. pt_V (V - {u}) (del1 E u) w"
  let ?F = "\<lambda>w. pt_E (V - {u}) (del1 E u) w"
  let ?Vs = "\<lambda>w. if w = v then (#) u ` (?W v - {[v]}) else brV E V u w"
  let ?Es = "\<lambda>w. if w = v then (`) ((#) u) ` del1 (?F v) [v] else brE E V u w"
  have vV: "v \<in> V - {u}" using nbrs_sub[OF G u] v by blast
  have gv: "graph (?W v) (?F v)" by (rule graph_pt[OF graph_del1[OF G] vV])
  have notin: "[u, v] \<notin> brV E V u w" if "w \<in> ?N" "w \<noteq> v" for w
    using br_root[OF G u v] br_disj[of v w E V u] that(2) by blast
  have VA: "pt_V V E u - {[u]} - {[u, v]} = (\<Union>w\<in>?N. ?Vs w)"
  proof (rule set_eqI)
    fix x
    have "x \<in> pt_V V E u - {[u]} - {[u, v]} \<longleftrightarrow> x \<in> (\<Union>w\<in>?N. brV E V u w) \<and> x \<noteq> [u, v]"
      using pt_V_minus_root[OF G u] unfolding brV_def by blast
    also have "\<dots> \<longleftrightarrow> x \<in> (\<Union>w\<in>?N. ?Vs w)"
    proof
      assume h: "x \<in> (\<Union>w\<in>?N. brV E V u w) \<and> x \<noteq> [u, v]"
      then obtain w where w: "w \<in> ?N" "x \<in> brV E V u w" "x \<noteq> [u, v]" by blast
      show "x \<in> (\<Union>w\<in>?N. ?Vs w)"
      proof (cases "w = v")
        case True
        then obtain y where y: "y \<in> ?W v" "x = u # y" using w(2) unfolding brV_def by blast
        have "y \<noteq> [v]" using y w(3) by auto
        then show ?thesis using v y True by force
      next
        case False
        then show ?thesis using w by auto
      qed
    next
      assume h: "x \<in> (\<Union>w\<in>?N. ?Vs w)"
      then obtain w where w: "w \<in> ?N" "x \<in> ?Vs w" by blast
      show "x \<in> (\<Union>w\<in>?N. brV E V u w) \<and> x \<noteq> [u, v]"
      proof (cases "w = v")
        case True
        then obtain y where y: "y \<in> ?W v" "y \<noteq> [v]" "x = u # y" using w(2) by auto
        then show ?thesis using w True unfolding brV_def by force
      next
        case False
        then show ?thesis using w notin by auto
      qed
    qed
    finally show "x \<in> pt_V V E u - {[u]} - {[u, v]} \<longleftrightarrow> x \<in> (\<Union>w\<in>?N. ?Vs w)" .
  qed
  have EA: "del1 (del1 (pt_E V E u) [u]) [u, v] = (\<Union>w\<in>?N. ?Es w)"
  proof (rule set_eqI)
    fix e
    have "e \<in> del1 (del1 (pt_E V E u) [u]) [u, v]
          \<longleftrightarrow> e \<in> (\<Union>w\<in>?N. brE E V u w) \<and> [u, v] \<notin> e"
      using pt_E_minus_root[OF G u] unfolding del1_def brE_def by blast
    also have "\<dots> \<longleftrightarrow> e \<in> (\<Union>w\<in>?N. ?Es w)"
    proof
      assume h: "e \<in> (\<Union>w\<in>?N. brE E V u w) \<and> [u, v] \<notin> e"
      then obtain w where w: "w \<in> ?N" "e \<in> brE E V u w" "[u, v] \<notin> e" by blast
      show "e \<in> (\<Union>w\<in>?N. ?Es w)"
      proof (cases "w = v")
        case True
        then obtain e0 where e0: "e0 \<in> ?F v" "e = (#) u ` e0" using w(2) unfolding brE_def by blast
        have "[v] \<notin> e0" using e0 w(3) by force
        then have "e0 \<in> del1 (?F v) [v]" using e0 unfolding del1_def by simp
        then show ?thesis using v True e0 by force
      next
        case False
        then show ?thesis using w by auto
      qed
    next
      assume h: "e \<in> (\<Union>w\<in>?N. ?Es w)"
      then obtain w where w: "w \<in> ?N" "e \<in> ?Es w" by blast
      show "e \<in> (\<Union>w\<in>?N. brE E V u w) \<and> [u, v] \<notin> e"
      proof (cases "w = v")
        case True
        then obtain e0 where e0: "e0 \<in> ?F v" "[v] \<notin> e0" "e = (#) u ` e0" using w(2) unfolding del1_def by auto
        have "[u, v] \<notin> e"
        proof
          assume "[u, v] \<in> e"
          then obtain y where "y \<in> e0" "u # y = [u, v]" using e0(3) by blast
          then show False using e0(2) by auto
        qed
        have mem: "e \<in> brE E V u w"
          unfolding brE_def True using imageI[OF e0(1), of "(`) ((#) u)"] e0(3) by simp
        have "e \<in> (\<Union>w\<in>?N. brE E V u w)" by (simp only: UN_iff, rule bexI[of "\<lambda>z. e \<in> brE E V u z" w, OF mem w(1)])
        then show ?thesis using \<open>[u, v] \<notin> e\<close> by simp
      next
        case False
        have "[u, v] \<notin> e"
        proof
          assume "[u, v] \<in> e"
          then have "[u, v] \<in> brV E V u w" using br_edges_sub[OF G u w(1)] w(2) False by auto
          then show False using notin[OF w(1) False] by blast
        qed
        then show ?thesis using w False by auto
      qed
    qed
    finally show "e \<in> del1 (del1 (pt_E V E u) [u]) [u, v] \<longleftrightarrow> e \<in> (\<Union>w\<in>?N. ?Es w)" .
  qed
  have gs: "\<forall>w\<in>?N. graph (?Vs w) (?Es w)"
  proof
    fix w assume w: "w \<in> ?N"
    show "graph (?Vs w) (?Es w)"
    proof (cases "w = v")
      case True
      have "graph (?W v - {[v]}) (del1 (?F v) [v])" by (rule graph_del1[OF gv])
      then show ?thesis using True graph_image[OF _ inj_cons] by simp
    next
      case False
      then show ?thesis using graph_br[OF G u w] by simp
    qed
  qed
  have ds: "\<forall>w\<in>?N. \<forall>w'\<in>?N. w \<noteq> w' \<longrightarrow> ?Vs w \<inter> ?Vs w' = {}"
  proof (intro ballI impI)
    fix w w' assume "w \<in> ?N" "w' \<in> ?N" "w \<noteq> w'"
    have sub: "?Vs z \<subseteq> brV E V u z" for z unfolding brV_def by auto
    show "?Vs w \<inter> ?Vs w' = {}" using br_disj[OF \<open>w \<noteq> w'\<close>, of E V u] sub by blast
  qed
  have "mu (pt_V V E u - {[u]} - {[u, v]}) (del1 (del1 (pt_E V E u) [u]) [u, v])
      = (\<Prod>w\<in>?N. mu (?Vs w) (?Es w))"
    unfolding VA EA by (rule mu_UNION[OF finite_nbrs[OF G u] gs ds])
  also have "\<dots> = mu (?Vs v) (?Es v) * (\<Prod>w\<in>?N - {v}. mu (?Vs w) (?Es w))"
    by (rule prod.remove[OF finite_nbrs[OF G u] v])
  also have "\<dots> = mu (?W v - {[v]}) (del1 (?F v) [v]) * (\<Prod>w\<in>?N - {v}. mu (?W w) (?F w))"
  proof -
    have "mu (?Vs v) (?Es v) = mu (?W v - {[v]}) (del1 (?F v) [v])"
    proof -
      have b: "bij_betw ((#) u) (?W v - {[v]}) ((#) u ` (?W v - {[v]}))"
        using inj_cons by (simp add: bij_betw_def)
      show ?thesis using mu_bij[OF graph_del1[OF gv] b] by simp
    qed
    moreover have "(\<Prod>w\<in>?N - {v}. mu (?Vs w) (?Es w)) = (\<Prod>w\<in>?N - {v}. mu (?W w) (?F w))"
      by (rule prod.cong[OF refl]) (use mu_br[OF G u] in auto)
    ultimately show ?thesis by simp
  qed
  finally show ?thesis .
qed

section \<open>Godsil's identity\<close>

theorem godsil_ratio:
  assumes "graph V E" and "u \<in> V"
  shows "mu (V - {u}) (del1 E u) * mu (pt_V V E u) (pt_E V E u)
       = mu V E * mu (pt_V V E u - {[u]}) (del1 (pt_E V E u) [u])"
  using assms
proof (induction "card V" arbitrary: V E u rule: less_induct)
  case less
  note G = less.prems(1) and u = less.prems(2)
  let ?N = "nbrs E u"
  let ?W = "\<lambda>w. pt_V (V - {u}) (del1 E u) w"
  let ?F = "\<lambda>w. pt_E (V - {u}) (del1 E u) w"
  let ?x = "[:0, 1:] :: real poly"
  let ?A = "mu (V - {u}) (del1 E u)"
  let ?T = "\<lambda>w. mu (?W w) (?F w)"
  let ?P = "\<Prod>w\<in>?N. ?T w"
  let ?C = "\<lambda>w. mu (V - {w, u}) (del2 E w u)"
  let ?D = "\<lambda>w. mu (?W w - {[w]}) (del1 (?F w) [w])"
  have fN: "finite ?N" by (rule finite_nbrs[OF G u])
  have gT: "graph (pt_V V E u) (pt_E V E u)" by (rule graph_pt[OF G u])
  have r: "[u] \<in> pt_V V E u" by (rule pt_root[OF u])
  have fV: "finite V" using G by (simp add: graph_def)
  have IH: "?C w * ?T w = ?A * ?D w" if w: "w \<in> ?N" for w
  proof -
    have wV: "w \<in> V - {u}" using nbrs_sub[OF G u] w by blast
    have lt: "card (V - {u}) < card V" by (rule card_Diff1_less[OF fV u])
    have ih: "mu (V - {u} - {w}) (del1 (del1 E u) w) * mu (?W w) (?F w)
            = mu (V - {u}) (del1 E u) * mu (?W w - {[w]}) (del1 (?F w) [w])"
      by (rule less.hyps[OF lt graph_del1[OF G] wV])
    have e1: "V - {u} - {w} = V - {w, u}" by auto
    have e2: "del1 (del1 E u) w = del2 E w u" unfolding del1_def del2_def by auto
    show ?thesis using ih unfolding e1 e2 by simp
  qed
  have s1: "mu (pt_V V E u) (pt_E V E u)
      = ?x * ?P - (\<Sum>v\<in>?N. ?D v * (\<Prod>w\<in>?N - {v}. ?T w))"
  proof -
    have rec: "mu (pt_V V E u) (pt_E V E u)
      = ?x * mu (pt_V V E u - {[u]}) (del1 (pt_E V E u) [u])
        - (\<Sum>p\<in>nbrs (pt_E V E u) [u]. mu (pt_V V E u - {p, [u]}) (del2 (pt_E V E u) p [u]))"
      by (rule mu_recurrence[OF gT r])
    have inj: "inj_on (\<lambda>v. [u, v]) ?N" by (simp add: inj_on_def)
    have "(\<Sum>p\<in>nbrs (pt_E V E u) [u]. mu (pt_V V E u - {p, [u]}) (del2 (pt_E V E u) p [u]))
        = (\<Sum>v\<in>?N. mu (pt_V V E u - {[u, v], [u]}) (del2 (pt_E V E u) [u, v] [u]))"
      unfolding nbrs_pt_root[OF G u] by (rule sum.reindex[OF inj, unfolded comp_def])
    also have "\<dots> = (\<Sum>v\<in>?N. ?D v * (\<Prod>w\<in>?N - {v}. ?T w))"
    proof (rule sum.cong[OF refl])
      fix v assume v: "v \<in> ?N"
      have e1: "pt_V V E u - {[u, v], [u]} = pt_V V E u - {[u]} - {[u, v]}" by auto
      have e2: "del2 (pt_E V E u) [u, v] [u] = del1 (del1 (pt_E V E u) [u]) [u, v]"
        unfolding del1_def del2_def by auto
      show "mu (pt_V V E u - {[u, v], [u]}) (del2 (pt_E V E u) [u, v] [u]) = ?D v * (\<Prod>w\<in>?N - {v}. ?T w)"
        unfolding e1 e2 by (rule mu_root_rest_minus[OF G u v])
    qed
    finally have "(\<Sum>p\<in>nbrs (pt_E V E u) [u]. mu (pt_V V E u - {p, [u]}) (del2 (pt_E V E u) p [u]))
        = (\<Sum>v\<in>?N. ?D v * (\<Prod>w\<in>?N - {v}. ?T w))" .
    then show ?thesis using rec mu_root_rest[OF G u] by simp
  qed
  have mG: "mu V E = ?x * ?A - (\<Sum>w\<in>?N. ?C w)"
    using mu_recurrence[OF G u] by simp
  have "mu V E * ?P = ?x * ?A * ?P - (\<Sum>w\<in>?N. ?C w * ?P)"
    unfolding mG by (simp add: algebra_simps sum_distrib_right)
  also have "(\<Sum>w\<in>?N. ?C w * ?P) = (\<Sum>w\<in>?N. ?A * (?D w * (\<Prod>v\<in>?N - {w}. ?T v)))"
  proof (rule sum.cong[OF refl])
    fix w assume w: "w \<in> ?N"
    have "?P = ?T w * (\<Prod>v\<in>?N - {w}. ?T v)" by (rule prod.remove[OF fN w])
    then have "?C w * ?P = (?C w * ?T w) * (\<Prod>v\<in>?N - {w}. ?T v)" by simp
    also have "\<dots> = ?A * ?D w * (\<Prod>v\<in>?N - {w}. ?T v)" using IH[OF w] by simp
    finally show "?C w * ?P = ?A * (?D w * (\<Prod>v\<in>?N - {w}. ?T v))" by simp
  qed
  finally have "mu V E * ?P = ?A * (?x * ?P - (\<Sum>v\<in>?N. ?D v * (\<Prod>w\<in>?N - {v}. ?T w)))"
    by (simp add: algebra_simps sum_distrib_left)
  then show ?case using s1 mu_root_rest[OF G u] by simp
qed

end
