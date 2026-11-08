(*  Title:      Chvatal_Tree_Ramsey.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Chvatal_Tree_Ramsey
  imports "Ramsey_Bounds.Ramsey_Bounds" "Tree_Enumeration.Tree_Graph"
begin

section \<open>Chv\'atal's theorem: the Ramsey number of a triangle versus a tree\<close>

text \<open>The host graphs and Ramsey numbers follow the AFP entry \<open>Ramsey_Bounds\<close>: a graph on a finite
  set \<open>W\<close> is a set of edges, cliques and independent sets are those of \<open>HOL-Library.Ramsey\<close>, and
  the definition below has the shape of \<open>is_clique_RN\<close>.  Trees are those of the AFP entry
  \<open>Tree_Enumeration\<close> (locale \<open>tree\<close>: a finite connected undirected graph without cycles).  A copy of
  a tree $(V_T, E_T)$ in the complement of a graph is an injective map of $V_T$ into \<open>W\<close> sending
  every edge of the tree to a non-edge of the graph.\<close>

definition compl_copy :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> bool" where
  "compl_copy VT ET W E \<longleftrightarrow>
     (\<exists>f. inj_on f VT \<and> f ` VT \<subseteq> W \<and> (\<forall>u v. {u, v} \<in> ET \<longrightarrow> {f u, f v} \<notin> E))"

definition is_triangle_tree_RN where
  "is_triangle_tree_RN \<equiv> \<lambda>U::'b itself. \<lambda>VT ET r.
     (\<forall>W::'b set. \<forall>E. finite W \<longrightarrow> card W \<ge> r \<longrightarrow>
        (\<exists>K\<subseteq>W. card K = 3 \<and> clique K E) \<or> compl_copy VT ET W E)"

text \<open>The Ramsey number $R(K_3, T)$, with vertex sets of natural numbers as in \<open>RN\<close>.\<close>

definition triangle_tree_RN :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat" where
  "triangle_tree_RN VT ET = (LEAST r. is_triangle_tree_RN TYPE(nat) VT ET r)"

lemma is_triangle_tree_RN_mono:
  assumes "is_triangle_tree_RN U VT ET r" and "r \<le> s"
  shows "is_triangle_tree_RN U VT ET s"
  using assms unfolding is_triangle_tree_RN_def by (meson order_trans)

section \<open>The upper bound\<close>

text \<open>Induction on the tree, adding a leaf \<open>l\<close> at \<open>v\<close>.  Let \<open>R\<close> be the part of \<open>W\<close> not used by the
  copy of the smaller tree.  If some vertex of \<open>R\<close> is not adjacent to the image of \<open>v\<close>, it receives
  \<open>l\<close>.  Otherwise \<open>R\<close> lies in the neighbourhood of that image, so it is independent because there is
  no triangle, and it is large enough to hold the whole tree.\<close>

lemma chvatal_upper_aux:
  fixes W :: "'b set" and H :: "'b set set"
  assumes tr: "tree VT ET" and finW: "finite W"
    and noK: "\<not> (\<exists>K\<subseteq>W. card K = 3 \<and> clique K H)" and big: "2 * card VT - 1 \<le> card W"
  shows "compl_copy VT ET W H"
proof -
  have "2 * card VT - 1 \<le> card W \<longrightarrow> compl_copy VT ET W H"
  proof (rule tree_induct[where P = "\<lambda>V E. 2 * card V - 1 \<le> card W \<longrightarrow> compl_copy V E W H", OF tr])
    fix v :: 'a
    show "2 * card {v} - 1 \<le> card W \<longrightarrow> compl_copy {v} {} W H"
    proof
      assume "2 * card {v} - 1 \<le> card W"
      then have "W \<noteq> {}" by auto
      then obtain w where "w \<in> W" by blast
      then show "compl_copy {v} {} W H"
        unfolding compl_copy_def by (intro exI[where x = "\<lambda>_. w"]) auto
    qed
  next
    fix l v :: 'a and V' :: "'a set" and E' :: "'a set set"
    assume tr': "tree V' E'" and IH: "2 * card V' - 1 \<le> card W \<longrightarrow> compl_copy V' E' W H"
      and lV: "l \<notin> V'" and vV: "v \<in> V'"
    show "2 * card (insert l V') - 1 \<le> card W \<longrightarrow> compl_copy (insert l V') (insert {l, v} E') W H"
    proof
      assume big': "2 * card (insert l V') - 1 \<le> card W"
      interpret t: tree V' E' by (rule tr')
      have finV: "finite V'" by (rule t.finV)
      have c: "card (insert l V') = Suc (card V')" using finV lV by simp
      have "2 * card V' - 1 \<le> card W" using big' c by arith
      with IH have "compl_copy V' E' W H" by blast
      then obtain f where fi: "inj_on f V'" and fW: "f ` V' \<subseteq> W"
        and fe: "\<forall>a b. {a, b} \<in> E' \<longrightarrow> {f a, f b} \<notin> H"
        unfolding compl_copy_def by blast
      let ?R = "W - f ` V'"
      have finR: "finite ?R" using finW by simp
      have cfV: "card (f ` V') = card V'" by (rule card_image[OF fi])
      have cR: "card ?R = card W - card V'"
        using card_Diff_subset[OF finite_imageI[OF finV] fW] cfV by simp
      have cRge: "card (insert l V') \<le> card ?R" using cR big' c by arith
      show "compl_copy (insert l V') (insert {l, v} E') W H"
      proof (cases "\<exists>w\<in>?R. {f v, w} \<notin> H")
        case True
        then obtain w where wR: "w \<in> ?R" and nw: "{f v, w} \<notin> H" by blast
        have nw': "{w, f v} \<notin> H" using nw by (simp add: insert_commute)
        define g where "g = (\<lambda>x. if x = l then w else f x)"
        have gV: "\<And>x. x \<in> V' \<Longrightarrow> g x = f x" using lV by (auto simp: g_def)
        have gl: "g l = w" by (simp add: g_def)
        have giV: "inj_on g V'" by (rule iffD2[OF inj_on_cong[OF gV] fi])
        have wn: "g l \<notin> g ` V'" using wR gl gV by force
        have VV: "V' - {l} = V'" using lV by blast
        have inj: "inj_on g (insert l V')"
          unfolding inj_on_insert VV using giV wn by blast
        have gW: "g ` insert l V' \<subseteq> W"
        proof (rule image_subsetI)
          fix x assume "x \<in> insert l V'"
          then have "x = l \<or> x \<in> V'" by blast
          then show "g x \<in> W" using gl wR gV fW by auto
        qed
        have ge: "\<forall>a b. {a, b} \<in> insert {l, v} E' \<longrightarrow> {g a, g b} \<notin> H"
        proof (intro allI impI)
          fix a b assume ab: "{a, b} \<in> insert {l, v} E'"
          show "{g a, g b} \<notin> H"
          proof (cases "{a, b} = {l, v}")
            case True
            then have "(a = l \<and> b = v) \<or> (a = v \<and> b = l)" by (auto simp: doubleton_eq_iff)
            then show ?thesis using nw nw' gl gV[OF vV] by auto
          next
            case False
            with ab have e: "{a, b} \<in> E'" by blast
            have "{a, b} \<subseteq> V'" by (rule t.wellformed[OF e])
            then have "a \<in> V'" "b \<in> V'" by auto
            then show ?thesis using fe e gV by simp
          qed
        qed
        show ?thesis
          unfolding compl_copy_def by (rule exI[where x = g]) (use inj gW ge in blast)
      next
        case False
        then have allH: "\<And>w. w \<in> ?R \<Longrightarrow> {f v, w} \<in> H" by blast
        have fvW: "f v \<in> W" using fW vV by blast
        have fvR: "f v \<notin> ?R" using vV by blast
        have ind: "\<And>x y. x \<in> ?R \<Longrightarrow> y \<in> ?R \<Longrightarrow> x \<noteq> y \<Longrightarrow> {x, y} \<notin> H"
        proof (rule notI)
          fix x y assume x: "x \<in> ?R" and y: "y \<in> ?R" and xy: "x \<noteq> y" and e: "{x, y} \<in> H"
          have nx: "f v \<noteq> x" using x fvR by blast
          have ny: "f v \<noteq> y" using y fvR by blast
          have cK: "card {f v, x, y} = 3" using nx ny xy by (simp add: card_insert_if)
          have KW: "{f v, x, y} \<subseteq> W" using fvW x y by blast
          have "clique {f v, x, y} H"
            using allH[OF x] allH[OF y] e by (auto simp: clique_def insert_commute)
          then show False using noK cK KW by blast
        qed
        have finI: "finite (insert l V')" using finV by simp
        obtain h where h1: "h ` insert l V' \<subseteq> ?R" and h2: "inj_on h (insert l V')"
          using card_le_inj[OF finI finR cRge] by blast
        have he: "\<forall>a b. {a, b} \<in> insert {l, v} E' \<longrightarrow> {h a, h b} \<notin> H"
        proof (intro allI impI)
          fix a b assume ab: "{a, b} \<in> insert {l, v} E'"
          have mem: "a \<in> insert l V' \<and> b \<in> insert l V' \<and> a \<noteq> b"
          proof (cases "{a, b} = {l, v}")
            case True
            then have "(a = l \<and> b = v) \<or> (a = v \<and> b = l)" by (auto simp: doubleton_eq_iff)
            then show ?thesis using vV lV by auto
          next
            case False
            with ab have e: "{a, b} \<in> E'" by blast
            have "{a, b} \<subseteq> V'" by (rule t.wellformed[OF e])
            moreover have "card {a, b} = 2" by (rule t.two_edges[OF e])
            ultimately show ?thesis by auto
          qed
          have ha: "h a \<in> ?R" using mem h1 by blast
          have hb: "h b \<in> ?R" using mem h1 by blast
          have hn: "h a \<noteq> h b" using mem h2 by (meson inj_onD)
          show "{h a, h b} \<notin> H" by (rule ind[OF ha hb hn])
        qed
        have hW: "h ` insert l V' \<subseteq> W" using h1 by blast
        show ?thesis
          unfolding compl_copy_def by (rule exI[where x = h]) (use h2 hW he in blast)
      qed
    qed
  qed
  then show ?thesis using big by blast
qed

theorem chvatal_upper:
  assumes "tree VT ET"
  shows "is_triangle_tree_RN U VT ET (2 * card VT - 1)"
  unfolding is_triangle_tree_RN_def using chvatal_upper_aux[OF assms] by blast

section \<open>The lower bound\<close>

lemma tree_constant_on_edges:
  assumes tr: "tree V E" and h: "\<And>a b. {a, b} \<in> E \<Longrightarrow> Q a = Q b"
    and x: "x \<in> V" and y: "y \<in> V"
  shows "Q x = Q y"
proof -
  have "(\<forall>a b. {a, b} \<in> E \<longrightarrow> Q a = Q b) \<longrightarrow> (\<forall>x\<in>V. \<forall>y\<in>V. Q x = Q y)"
  proof (rule tree_induct[where P =
        "\<lambda>V E. (\<forall>a b. {a, b} \<in> E \<longrightarrow> Q a = Q b) \<longrightarrow> (\<forall>x\<in>V. \<forall>y\<in>V. Q x = Q y)", OF tr])
    fix v :: 'a
    show "(\<forall>a b. {a, b} \<in> {} \<longrightarrow> Q a = Q b) \<longrightarrow> (\<forall>x\<in>{v}. \<forall>y\<in>{v}. Q x = Q y)" by simp
  next
    fix l v :: 'a and V' :: "'a set" and E' :: "'a set set"
    assume IH: "(\<forall>a b. {a, b} \<in> E' \<longrightarrow> Q a = Q b) \<longrightarrow> (\<forall>x\<in>V'. \<forall>y\<in>V'. Q x = Q y)"
      and vV: "v \<in> V'"
    show "(\<forall>a b. {a, b} \<in> insert {l, v} E' \<longrightarrow> Q a = Q b) \<longrightarrow>
        (\<forall>x\<in>insert l V'. \<forall>y\<in>insert l V'. Q x = Q y)"
    proof
      assume hi: "\<forall>a b. {a, b} \<in> insert {l, v} E' \<longrightarrow> Q a = Q b"
      then have "\<forall>x\<in>V'. \<forall>y\<in>V'. Q x = Q y" using IH by blast
      with vV have hv: "\<forall>x\<in>V'. Q x = Q v" by blast
      have hl: "Q l = Q v" using hi by blast
      from hv hl have all: "\<forall>x\<in>insert l V'. Q x = Q v" by blast
      show "\<forall>x\<in>insert l V'. \<forall>y\<in>insert l V'. Q x = Q y"
      proof (intro ballI)
        fix x y assume x: "x \<in> insert l V'" and y: "y \<in> insert l V'"
        have "Q x = Q v" using all x by (rule bspec)
        moreover have "Q y = Q v" using all y by (rule bspec)
        ultimately show "Q x = Q y" by simp
      qed
    qed
  qed
  then show ?thesis using h x y by blast
qed

text \<open>The complete bipartite graph with two parts of size $n - 1$ has no triangle, and a connected
  graph in its complement stays inside one part.\<close>

theorem chvatal_lower:
  fixes U :: "'b itself"
  assumes tr: "tree VT ET" and inf: "infinite (UNIV :: 'b set)"
  shows "\<not> is_triangle_tree_RN U VT ET (2 * card VT - 2)"
proof
  assume RN: "is_triangle_tree_RN U VT ET (2 * card VT - 2)"
  interpret t: tree VT ET by (rule tr)
  have n1: "1 \<le> card VT" using t.finV t.not_empty by (simp add: Suc_le_eq card_gt_0_iff)
  obtain A :: "'b set" where finA: "finite A" and cA: "card A = card VT - 1"
    using infinite_arbitrarily_large[OF inf] by blast
  have "infinite (UNIV - A)" by (rule Diff_infinite_finite[OF finA inf])
  then obtain B :: "'b set" where finB: "finite B" and cB: "card B = card VT - 1"
    and BA: "B \<subseteq> UNIV - A"
    using infinite_arbitrarily_large by blast
  have disj: "A \<inter> B = {}" using BA by blast
  define W where "W = A \<union> B"
  define H where "H = {{a, b} | a b. a \<in> A \<and> b \<in> B}"
  have finW: "finite W" using finA finB by (simp add: W_def)
  have cW: "2 * card VT - 2 \<le> card W"
    unfolding W_def using card_Un_disjoint[OF finA finB disj] cA cB n1 by arith
  have sep: "\<And>x y. {x, y} \<in> H \<Longrightarrow> (x \<in> A) \<noteq> (y \<in> A)"
  proof -
    fix x y assume "{x, y} \<in> H"
    then obtain a b where e: "{x, y} = {a, b}" and a: "a \<in> A" and b: "b \<in> B"
      unfolding H_def by blast
    have nb: "b \<notin> A" using disj b by blast
    show "(x \<in> A) \<noteq> (y \<in> A)" using e a nb by (auto simp: doubleton_eq_iff)
  qed
  have notri: "\<not> (\<exists>K\<subseteq>W. card K = 3 \<and> clique K H)"
  proof
    assume "\<exists>K\<subseteq>W. card K = 3 \<and> clique K H"
    then obtain K where cK: "card K = 3" and qK: "clique K H" by blast
    then obtain x y z where K: "K = {x, y, z}" and xy: "x \<noteq> y" and yz: "y \<noteq> z" and xz: "x \<noteq> z"
      using card_3_iff[of K] by blast
    have e1: "{x, y} \<in> H" using qK K xy by (auto simp: clique_def)
    have e2: "{y, z} \<in> H" using qK K yz by (auto simp: clique_def)
    have e3: "{x, z} \<in> H" using qK K xz by (auto simp: clique_def)
    show False using sep[OF e1] sep[OF e2] sep[OF e3] by blast
  qed
  have "(\<exists>K\<subseteq>W. card K = 3 \<and> clique K H) \<or> compl_copy VT ET W H"
    using RN finW cW unfolding is_triangle_tree_RN_def by blast
  with notri have "compl_copy VT ET W H" by blast
  then obtain f where fi: "inj_on f VT" and fW: "f ` VT \<subseteq> W"
    and fe: "\<forall>a b. {a, b} \<in> ET \<longrightarrow> {f a, f b} \<notin> H"
    unfolding compl_copy_def by blast
  have side: "\<And>a b. {a, b} \<in> ET \<Longrightarrow> (f a \<in> A) = (f b \<in> A)"
  proof -
    fix a b assume ab: "{a, b} \<in> ET"
    have sub: "{a, b} \<subseteq> VT" by (rule t.wellformed[OF ab])
    have fa: "f a \<in> A \<union> B" "f b \<in> A \<union> B" using fW sub by (auto simp: W_def)
    have nH: "{f a, f b} \<notin> H" using fe ab by blast
    show "(f a \<in> A) = (f b \<in> A)"
    proof (rule ccontr)
      assume "(f a \<in> A) \<noteq> (f b \<in> A)"
      then have "(f a \<in> A \<and> f b \<in> B) \<or> (f b \<in> A \<and> f a \<in> B)" using fa by blast
      then have "{f a, f b} \<in> H \<or> {f b, f a} \<in> H" unfolding H_def by blast
      then show False using nH by (simp add: insert_commute)
    qed
  qed
  have same: "\<And>x y. x \<in> VT \<Longrightarrow> y \<in> VT \<Longrightarrow> (f x \<in> A) = (f y \<in> A)"
    using tree_constant_on_edges[where Q = "\<lambda>x. f x \<in> A", OF tr side] by blast
  obtain x0 where x0: "x0 \<in> VT" using t.not_empty by blast
  show False
  proof (cases "f x0 \<in> A")
    case True
    have "f ` VT \<subseteq> A" using True same x0 by blast
    from card_inj_on_le[OF fi this finA] cA n1 show False by arith
  next
    case False
    have "f ` VT \<subseteq> B"
    proof (rule image_subsetI)
      fix y assume y: "y \<in> VT"
      have "f y \<notin> A" using same[OF y x0] False by blast
      moreover have "f y \<in> A \<union> B" using fW y by (auto simp: W_def)
      ultimately show "f y \<in> B" by blast
    qed
    from card_inj_on_le[OF fi this finB] cB n1 show False by arith
  qed
qed

section \<open>Chv\'atal's theorem\<close>

theorem chvatal:
  assumes tr: "tree VT ET"
  shows "triangle_tree_RN VT ET = 2 * card VT - 1"
  unfolding triangle_tree_RN_def
proof (rule Least_equality)
  show "is_triangle_tree_RN TYPE(nat) VT ET (2 * card VT - 1)" by (rule chvatal_upper[OF tr])
next
  fix r assume r: "is_triangle_tree_RN TYPE(nat) VT ET r"
  interpret t: tree VT ET by (rule tr)
  have n1: "1 \<le> card VT" using t.finV t.not_empty by (simp add: Suc_le_eq card_gt_0_iff)
  show "2 * card VT - 1 \<le> r"
  proof (rule ccontr)
    assume "\<not> 2 * card VT - 1 \<le> r"
    then have "r \<le> 2 * card VT - 2" using n1 by arith
    with r have "is_triangle_tree_RN TYPE(nat) VT ET (2 * card VT - 2)"
      by (rule is_triangle_tree_RN_mono)
    with chvatal_lower[OF tr infinite_UNIV_nat] show False by blast
  qed
qed

text \<open>A connected graph with $n$ vertices and at most $n - 1$ edges is a tree.\<close>

corollary connected_few_edges_triangle_good:
  assumes g: "fin_connected_sgraph V E" and c: "card E + 1 \<le> card V"
  shows "triangle_tree_RN V E = 2 * card V - 1"
proof -
  interpret g: fin_connected_sgraph V E by (rule g)
  obtain T where T: "spanning_tree V E T" using g.has_spanning_tree by blast
  interpret s: spanning_tree V E T by (rule T)
  have "card T \<le> card E" by (intro card_mono g.fin_edges s.subgraph)
  moreover have "card V = Suc (card T)" by (rule s.T.card_V_card_E)
  ultimately have "card V = Suc (card E)" using c by arith
  then have "tree V E" using card_E_treeI g.fin_connected_ulgraph_axioms by blast
  then show ?thesis by (rule chvatal)
qed

section \<open>Agreement with \<open>RN\<close> of \<open>Ramsey_Bounds\<close>\<close>

text \<open>The tree $K_2$ is also a complete graph, so there the two notions of Ramsey number can be
  compared directly: a copy of $K_2$ in the complement is an independent pair.\<close>

lemma compl_copy_edge_iff:
  fixes W :: "'b set" and H :: "'b set set"
  assumes uv: "u \<noteq> v"
  shows "compl_copy {u, v} {{u, v}} W H \<longleftrightarrow> (\<exists>K\<subseteq>W. card K = 2 \<and> indep K H)"
proof
  assume "compl_copy {u, v} {{u, v}} W H"
  then obtain f where fi: "inj_on f {u, v}" and fW: "f ` {u, v} \<subseteq> W"
    and fe: "\<forall>a b. {a, b} \<in> {{u, v}} \<longrightarrow> {f a, f b} \<notin> H"
    unfolding compl_copy_def by blast
  have ne: "f u \<noteq> f v" using fi uv by (auto simp: inj_on_def)
  have nH: "{f u, f v} \<notin> H" using fe by blast
  have "indep {f u, f v} H" using nH by (auto simp: indep_def insert_commute)
  moreover have "card {f u, f v} = 2" using ne by simp
  moreover have "{f u, f v} \<subseteq> W" using fW by blast
  ultimately show "\<exists>K\<subseteq>W. card K = 2 \<and> indep K H" by blast
next
  assume "\<exists>K\<subseteq>W. card K = 2 \<and> indep K H"
  then obtain K where KW: "K \<subseteq> W" and cK: "card K = 2" and iK: "indep K H" by blast
  then obtain x y where K: "K = {x, y}" and xy: "x \<noteq> y" using card_2_iff[of K] by blast
  define f where "f = (\<lambda>z. if z = u then x else y)"
  have fu: "f u = x" and fv: "f v = y" using uv by (auto simp: f_def)
  have fi: "inj_on f {u, v}" using fu fv xy by (auto simp: inj_on_def)
  have fW: "f ` {u, v} \<subseteq> W" using fu fv KW K by auto
  have nH: "{x, y} \<notin> H" "{y, x} \<notin> H" using iK K xy by (auto simp: indep_def)
  have fe: "\<forall>a b. {a, b} \<in> {{u, v}} \<longrightarrow> {f a, f b} \<notin> H"
  proof (intro allI impI)
    fix a b assume "{a, b} \<in> {{u, v}}"
    then have "(a = u \<and> b = v) \<or> (a = v \<and> b = u)" by (auto simp: doubleton_eq_iff)
    then show "{f a, f b} \<notin> H" using fu fv nH by auto
  qed
  show "compl_copy {u, v} {{u, v}} W H"
    unfolding compl_copy_def by (rule exI[where x = f]) (use fi fW fe in blast)
qed

lemma ex_clique_indep_iff:
  "(\<exists>K\<subseteq>W. clique_indep m n K E) \<longleftrightarrow>
     (\<exists>K\<subseteq>W. card K = m \<and> clique K E) \<or> (\<exists>K\<subseteq>W. card K = n \<and> indep K E)"
  by (simp only: clique_indep_def conj_disj_distribL ex_disj_distrib)

lemma is_triangle_tree_RN_edge_iff:
  assumes "u \<noteq> v"
  shows "is_triangle_tree_RN U {u, v} {{u, v}} r \<longleftrightarrow> is_clique_RN U 3 2 r"
  unfolding is_triangle_tree_RN_def is_clique_RN_def compl_copy_edge_iff[OF assms] ex_clique_indep_iff
  by simp

corollary triangle_tree_RN_edge:
  assumes "u \<noteq> v"
  shows "triangle_tree_RN {u, v} {{u, v}} = RN 3 2"
  using chvatal[OF tree2[OF assms]] assms by simp

end
