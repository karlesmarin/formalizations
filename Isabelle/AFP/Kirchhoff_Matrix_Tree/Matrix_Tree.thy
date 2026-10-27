(*  Title:      Matrix_Tree.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Kirchhoff's matrix-tree theorem

    For a finite simple graph and a root r, the determinant of the reduced Laplacian (the row and the column of r
    deleted) is the number of spanning trees. The Laplacian factors as N N^T through the reduced oriented incidence
    matrix N; by Cauchy--Binet its determinant is the sum of the squared maximal minors of N, which are 0 or +-1 as the
    chosen edges do or do not form a spanning tree.
    Lean counterpart: Formalizations.Combinatorics.SimpleGraph.MatrixTree.

    Main results:
    * matrix_tree: det lap = card {T. spanning_tree V E T}.

    References:
    * G. Kirchhoff, Ueber die Aufloesung der Gleichungen, auf welche man bei der Untersuchung der linearen
      Vertheilung galvanischer Stroeme gefuehrt wird, Ann. Phys. Chem. 72 (1847) 497--508.
*)

theory Matrix_Tree
  imports
    "Smith_Normal_Form.Cauchy_Binet"
    "Tree_Enumeration.Tree_Graph"
begin

section \<open>Setting\<close>

text \<open>A finite simple graph on a linearly ordered vertex type, with a root @{term r}. The vertices other than
the root are numbered in increasing order, the edges in an arbitrary fixed order; an edge is oriented from its
smaller to its larger end.\<close>

locale matrix_tree = fin_sgraph V E for V :: "'a::linorder set" and E +
  fixes r :: 'a
  assumes root: "r \<in> V"
begin

definition vs :: "'a list" where "vs = sorted_list_of_set (V - {r})"

definition es :: "'a set list" where "es = (SOME l. distinct l \<and> set l = E)"

abbreviation nv :: nat where "nv \<equiv> length vs"
abbreviation ne :: nat where "ne \<equiv> length es"

definition ori :: "'a \<Rightarrow> 'a set \<Rightarrow> int" where
  "ori v e = (if v \<in> e then (if v = Min e then 1 else -1) else 0)"

text \<open>The reduced oriented incidence matrix (rows: vertices other than the root; columns: edges).\<close>
definition inc :: "int mat" where
  "inc = mat nv ne (\<lambda>(i, j). ori (vs ! i) (es ! j))"

text \<open>The reduced Laplacian.\<close>
definition lap :: "int mat" where
  "lap = mat nv nv (\<lambda>(i, j). if i = j then int (degree (vs ! i))
                             else if {vs ! i, vs ! j} \<in> E then -1 else 0)"

definition edges_of :: "nat set \<Rightarrow> 'a set set" where
  "edges_of I = (\<lambda>j. es ! j) ` I"

section \<open>Enumerations\<close>

lemma vs_distinct: "distinct vs" and set_vs: "set vs = V - {r}"
  using finV by (simp_all add: vs_def)

lemma es_props: "distinct es \<and> set es = E"
proof -
  obtain l where "distinct l \<and> set l = E" using finite_distinct_list[OF fin_edges] by blast
  then show ?thesis unfolding es_def by (rule someI)
qed

lemma es_distinct: "distinct es" and set_es: "set es = E"
  using es_props by simp_all

lemma nv_eq: "nv = card V - 1"
proof -
  have "nv = card (V - {r})" using vs_distinct set_vs distinct_card by metis
  then show ?thesis using root finV by simp
qed

lemma inc_carrier: "inc \<in> carrier_mat nv ne" and lap_carrier: "lap \<in> carrier_mat nv nv"
  by (simp_all add: inc_def lap_def)

section \<open>The Laplacian factors through the incidence matrix\<close>

lemma sum_es: "(\<Sum>k\<in>{0..<ne}. f (es ! k)) = (\<Sum>e\<in>E. f e)"
proof -
  have "(\<Sum>k\<in>{0..<ne}. f (es ! k)) = sum_list (map f es)"
    by (simp add: sum_list_sum_nth)
  also have "\<dots> = sum f (set es)"
    by (simp add: sum_list_distinct_conv_sum_set es_distinct)
  finally show ?thesis by (simp add: set_es)
qed

lemma ori_sq: "ori v e * ori v e = (if v \<in> e then 1 else 0)"
  by (simp add: ori_def)

lemma ori_mult:
  assumes e: "e \<in> E" and uw: "u \<noteq> w"
  shows "ori u e * ori w e = (if e = {u, w} then -1 else 0)"
proof (cases "u \<in> e \<and> w \<in> e")
  case True
  have fin: "finite e" using two_edges[OF e] card.infinite by fastforce
  have sub: "{u, w} \<subseteq> e" using True by blast
  have "card {u, w} = card e" using two_edges[OF e] uw by simp
  then have ee: "e = {u, w}" using card_subset_eq[OF fin sub] by simp
  have "Min e = u \<or> Min e = w" using ee by (metis Min_in empty_not_insert fin insert_iff singletonD)
  then show ?thesis using ee uw by (auto simp: ori_def)
next
  case False
  then show ?thesis by (auto simp: ori_def)
qed

lemma vs_in: "i < nv \<Longrightarrow> vs ! i \<in> V" and vs_ne_root: "i < nv \<Longrightarrow> vs ! i \<noteq> r"
  using set_vs nth_mem by fastforce+

lemma vs_inj: "i < nv \<Longrightarrow> j < nv \<Longrightarrow> vs ! i = vs ! j \<Longrightarrow> i = j"
  using vs_distinct nth_eq_iff_index_eq by blast

lemma degree_eq: "v \<in> V \<Longrightarrow> int (degree v) = (\<Sum>e\<in>E. if v \<in> e then 1 else 0)"
proof -
  assume "v \<in> V"
  have "\<not> has_loop v" using singleton_not_edge by (simp add: has_loop_def)
  then have "degree v = card (incident_edges v)" by simp
  also have "\<dots> = card {e \<in> E. v \<in> e}" by (simp add: incident_edges_def vincident_def)
  finally show ?thesis using fin_edges by (simp add: sum.If_cases Int_def)
qed

lemma lap_eq_inc_mult: "lap = inc * inc\<^sup>T"
proof (rule eq_matI)
  fix i j assume i: "i < dim_row (inc * inc\<^sup>T)" and j: "j < dim_col (inc * inc\<^sup>T)"
  then have i': "i < nv" and j': "j < nv" by (simp_all add: inc_def)
  have "(inc * inc\<^sup>T) $$ (i, j) = (\<Sum>k\<in>{0..<ne}. ori (vs ! i) (es ! k) * ori (vs ! j) (es ! k))"
    using i' j' by (simp add: inc_def scalar_prod_def)
  also have "\<dots> = (\<Sum>e\<in>E. ori (vs ! i) e * ori (vs ! j) e)"
    by (rule sum_es)
  also have "\<dots> = lap $$ (i, j)"
  proof (cases "i = j")
    case True
    then show ?thesis using i' vs_in degree_eq by (simp add: lap_def ori_sq)
  next
    case False
    then have ne: "vs ! i \<noteq> vs ! j" using vs_inj i' j' by blast
    have "(\<Sum>e\<in>E. ori (vs ! i) e * ori (vs ! j) e) = (\<Sum>e\<in>E. if e = {vs ! i, vs ! j} then -1 else 0)"
      by (rule sum.cong) (simp_all add: ori_mult ne)
    also have "\<dots> = (if {vs ! i, vs ! j} \<in> E then -1 else 0)"
      using fin_edges by (simp add: sum.delta')
    finally show ?thesis using False i' j' by (simp add: lap_def)
  qed
  finally show "lap $$ (i, j) = (inc * inc\<^sup>T) $$ (i, j)" by simp
qed (simp_all add: lap_def inc_def)

section \<open>Cauchy--Binet\<close>

lemma submatrix_transpose: "submatrix A\<^sup>T I UNIV = (submatrix A UNIV I)\<^sup>T"
proof (rule eq_matI)
  fix i j
  assume i: "i < dim_row (submatrix A UNIV I)\<^sup>T" and j: "j < dim_col (submatrix A UNIV I)\<^sup>T"
  have i': "i < card {a. a < dim_col A \<and> a \<in> I}"
    using i unfolding index_transpose_mat(2) dim_submatrix(2) by simp
  have j': "j < card {a. a < dim_row A \<and> a \<in> UNIV}"
    using j unfolding index_transpose_mat(3) dim_submatrix(1) by simp
  have pi: "pick I i < dim_col A" using pick_le[OF i'] .
  have pj: "j < dim_row A" using j' by simp
  have "submatrix A\<^sup>T I UNIV $$ (i, j) = A\<^sup>T $$ (pick I i, pick UNIV j)"
    by (rule submatrix_index) (use i' j' in simp_all)
  also have "\<dots> = A $$ (j, pick I i)"
    by (simp only: pick_UNIV, rule index_transpose_mat(1)) (use pi pj in simp_all)
  also have "\<dots> = submatrix A UNIV I $$ (j, i)"
    by (rule sym, rule submatrix_index[where A = A and I = UNIV and J = I, unfolded pick_UNIV])
       (use i' j' in simp_all)
  also have "\<dots> = (submatrix A UNIV I)\<^sup>T $$ (i, j)"
    by (rule sym, rule index_transpose_mat(1))
       (use i j in \<open>simp_all only: index_transpose_mat(2) index_transpose_mat(3)\<close>)
  finally show "submatrix A\<^sup>T I UNIV $$ (i, j) = (submatrix A UNIV I)\<^sup>T $$ (i, j)" .
next
  show "dim_row (submatrix A\<^sup>T I UNIV) = dim_row (submatrix A UNIV I)\<^sup>T"
    by (simp only: index_transpose_mat(2) dim_submatrix(1) dim_submatrix(2) index_transpose_mat(3) index_transpose_mat(2))
next
  show "dim_col (submatrix A\<^sup>T I UNIV) = dim_col (submatrix A UNIV I)\<^sup>T"
    by (simp only: index_transpose_mat(3) dim_submatrix(1) dim_submatrix(2) index_transpose_mat(2) index_transpose_mat(3))
qed

lemma minor_carrier:
  assumes "I \<subseteq> {0..<ne}" "card I = nv"
  shows "submatrix inc UNIV I \<in> carrier_mat nv nv"
proof -
  have r: "dim_row inc = nv" and c: "dim_col inc = ne" by (simp_all add: inc_def)
  have "{i. i < nv \<and> i \<in> UNIV} = {0..<nv}" by auto
  then have "card {i. i < nv \<and> i \<in> UNIV} = nv" by simp
  moreover have "{j. j < ne \<and> j \<in> I} = I" using assms(1) by auto
  ultimately show ?thesis
    using assms(2) by (simp only: carrier_mat_def mem_Collect_eq dim_submatrix r c)
qed

lemma det_lap_sum_squares:
  "det lap = (\<Sum>I\<in>{I. I \<subseteq> {0..<ne} \<and> card I = nv}. (det (submatrix inc UNIV I))\<^sup>2)"
proof -
  have incT: "inc\<^sup>T \<in> carrier_mat ne nv" using inc_carrier by (simp only: transpose_carrier_mat)
  have step: "\<And>I. I \<in> {I. I \<subseteq> {0..<ne} \<and> card I = nv} \<Longrightarrow>
      det (submatrix inc UNIV I) * det (submatrix inc\<^sup>T I UNIV) = (det (submatrix inc UNIV I))\<^sup>2"
  proof -
    fix I assume "I \<in> {I. I \<subseteq> {0..<ne} \<and> card I = nv}"
    then have sq: "submatrix inc UNIV I \<in> carrier_mat nv nv" using minor_carrier by blast
    show "det (submatrix inc UNIV I) * det (submatrix inc\<^sup>T I UNIV) = (det (submatrix inc UNIV I))\<^sup>2"
      by (simp only: submatrix_transpose det_transpose[OF sq] power2_eq_square)
  qed
  have "det lap = det (inc * inc\<^sup>T)" by (simp only: lap_eq_inc_mult)
  also have "\<dots> = (\<Sum>I\<in>{I. I \<subseteq> {0..<ne} \<and> card I = nv}.
                     det (submatrix inc UNIV I) * det (submatrix inc\<^sup>T I UNIV))"
    by (rule Cauchy_Binet[OF inc_carrier incT])
  also have "\<dots> = (\<Sum>I\<in>{I. I \<subseteq> {0..<ne} \<and> card I = nv}. (det (submatrix inc UNIV I))\<^sup>2)"
    by (rule sum.cong[OF refl step])
  finally show ?thesis .
qed

section \<open>The square of a maximal minor\<close>

subsection \<open>Disconnected edge sets: the minor vanishes\<close>

text \<open>If the chosen edges do not connect the graph, some component avoids the root, and the sum of the rows of
its vertices is zero.\<close>

lemma sum_vs: "(\<Sum>i\<in>{0..<nv}. f (vs ! i)) = (\<Sum>x\<in>V - {r}. f x)"
proof -
  have "(\<Sum>i\<in>{0..<nv}. f (vs ! i)) = sum_list (map f vs)"
    by (simp add: sum_list_sum_nth)
  also have "\<dots> = sum f (set vs)"
    by (simp add: sum_list_distinct_conv_sum_set vs_distinct)
  finally show ?thesis by (simp add: set_vs)
qed

lemma edges_of_sub: "edges_of I \<subseteq> E" if "I \<subseteq> {0..<ne}"
proof
  fix e assume "e \<in> edges_of I"
  then obtain j where j: "j \<in> I" "e = es ! j" by (auto simp: edges_of_def)
  then have "j < ne" using that by auto
  then show "e \<in> E" using j(2) set_es nth_mem by blast
qed

lemma ori_lt:
  assumes "a < b"
  shows "ori a {a, b} + ori b {a, b} = 0"
proof -
  have "Min {a, b} = a" by (rule Min_eqI) (use assms in auto)
  moreover have "b \<noteq> a" using assms by simp
  ultimately show ?thesis by (simp add: ori_def)
qed

lemma ori_pair: "e \<in> E \<Longrightarrow> (\<Sum>x\<in>e. ori x e) = 0"
proof -
  assume e: "e \<in> E"
  have c2: "card e = 2" by (rule two_edges[OF e])
  then obtain a b where ab: "a \<noteq> b" "e = {a, b}" by (auto simp: card_2_iff)
  have "(\<Sum>x\<in>{a, b}. ori x {a, b}) = ori a {a, b} + ori b {a, b}"
    using ab(1) by simp
  also have "\<dots> = 0"
  proof (cases "a < b")
    case True
    then show ?thesis by (rule ori_lt)
  next
    case False
    then have "b < a" using ab(1) by simp
    then show ?thesis using ori_lt[of b a] by (simp add: insert_commute add.commute)
  qed
  finally show ?thesis using ab(2) by simp
qed

lemma two_edge_eq:
  assumes e: "e \<in> E" and x: "x \<in> e" and y: "y \<in> e" and xy: "x \<noteq> y"
  shows "e = {x, y}"
proof -
  have fin: "finite e" using two_edges[OF e] card.infinite by fastforce
  have sub: "{x, y} \<subseteq> e" using x y by blast
  have "card {x, y} = card e" using two_edges[OF e] xy by simp
  then show ?thesis using card_subset_eq[OF fin sub] by simp
qed

lemma not_connected_component:
  assumes I: "I \<subseteq> {0..<ne}" and nc: "\<not> fin_connected_ulgraph V (edges_of I)"
  obtains C where "C \<subseteq> V" "r \<notin> C" "C \<noteq> {}" "\<And>e x y. e \<in> edges_of I \<Longrightarrow> x \<in> e \<Longrightarrow> y \<in> e \<Longrightarrow> x \<in> C \<Longrightarrow> y \<in> C"
proof -
  have sub: "edges_of I \<subseteq> E" using edges_of_sub[OF I] .
  interpret g: fin_ulgraph V "edges_of I"
    using sub two_edges finV wellformed by unfold_locales (auto simp: fin_edges finite_subset)
  have ncs: "\<not> g.is_connected_set V"
  proof
    assume c: "g.is_connected_set V"
    have "fin_connected_ulgraph V (edges_of I)"
      using c root by (unfold_locales) auto
    then show False using nc by blast
  qed
  then obtain u v where uv: "u \<in> V" "v \<in> V" "\<not> g.vert_connected u v"
    unfolding g.is_connected_set_def by blast
  obtain w where w: "w \<in> V" "\<not> g.vert_connected w r"
  proof (cases "g.vert_connected u r")
    case True
    then have "\<not> g.vert_connected v r" using uv(3) g.vert_connected_trans g.vert_connected_rev by blast
    then show ?thesis using uv(2) that by blast
  next
    case False
    then show ?thesis using uv(1) that by blast
  qed
  have adj: "g.vert_connected x y" if "e \<in> edges_of I" "x \<in> e" "y \<in> e" for e x y
  proof (cases "x = y")
    case True
    then show ?thesis using that sub g.vert_connected_id wellformed by blast
  next
    case False
    have ee: "e = {x, y}" using two_edge_eq[of e x y] that sub False by blast
    have "g.connecting_walk x y [x, y]"
      unfolding g.connecting_walk_def
      by (rule conjI, rule g.is_walkI) (use that ee wellformed sub in auto)
    then show ?thesis using g.connecting_walk_path g.vert_connected_def by blast
  qed
  show ?thesis
  proof (rule that[of "{x. g.vert_connected w x}"])
    show "{x. g.vert_connected w x} \<subseteq> V" using g.vert_connected_wf by blast
    show "r \<notin> {x. g.vert_connected w x}" using w(2) g.vert_connected_rev by blast
    show "{x. g.vert_connected w x} \<noteq> {}" using w(1) g.vert_connected_id by blast
    show "\<And>e x y. e \<in> edges_of I \<Longrightarrow> x \<in> e \<Longrightarrow> y \<in> e \<Longrightarrow> x \<in> {x. g.vert_connected w x} \<Longrightarrow>
      y \<in> {x. g.vert_connected w x}"
      using adj g.vert_connected_trans by blast
  qed
qed

lemma det_minor_zero_if_not_connected:
  assumes I: "I \<subseteq> {0..<ne}" "card I = nv" "\<not> fin_connected_ulgraph V (edges_of I)"
  shows "det (submatrix inc UNIV I) = 0"
proof -
  obtain C where C: "C \<subseteq> V" "r \<notin> C" "C \<noteq> {}"
    and cl: "\<And>e x y. e \<in> edges_of I \<Longrightarrow> x \<in> e \<Longrightarrow> y \<in> e \<Longrightarrow> x \<in> C \<Longrightarrow> y \<in> C"
    using not_connected_component[OF I(1) I(3)] by blast
  let ?A = "submatrix inc UNIV I"
  have finC: "finite C" using C(1) finV by (rule finite_subset)
  have Ac: "?A \<in> carrier_mat nv nv" using minor_carrier I(1,2) by blast
  have At: "?A\<^sup>T \<in> carrier_mat nv nv" using Ac by simp
  have fI: "finite I" using I(1) finite_subset by blast
  have entry: "?A $$ (i, j) = ori (vs ! i) (es ! pick I j)" if "i < nv" "j < nv" for i j
  proof -
    have r1: "{i. i < dim_row inc \<and> i \<in> UNIV} = {0..<nv}" by (auto simp: inc_def)
    have r2: "card {i. i < dim_row inc \<and> i \<in> UNIV} = nv" using r1 by simp
    have c1: "{j. j < dim_col inc \<and> j \<in> I} = I" using I(1) by (auto simp: inc_def)
    have c2: "card {j. j < dim_col inc \<and> j \<in> I} = nv" using c1 I(2) by simp
    have "pick I j \<in> I" using that(2) I(2) pick_in_set_le by simp
    then have pjn: "pick I j < ne" using I(1) by auto
    have "?A $$ (i, j) = inc $$ (pick UNIV i, pick I j)"
      by (rule submatrix_index) (use r2 c2 that in simp_all)
    then show ?thesis using that pjn by (simp add: pick_UNIV inc_def)
  qed
  have pj: "pick I j \<in> I" if "j < nv" for j using that I(2) pick_in_set_le by simp
  let ?v = "vec nv (\<lambda>i. if vs ! i \<in> C then (1::int) else 0)"
  have vc: "?v \<in> carrier_vec nv" by simp
  have "?A\<^sup>T *\<^sub>v ?v = 0\<^sub>v nv"
  proof (rule eq_vecI)
    fix j assume j: "j < dim_vec (0\<^sub>v nv)"
    then have j': "j < nv" by simp
    let ?e = "es ! pick I j"
    have eI: "?e \<in> edges_of I" using pj[OF j'] by (auto simp: edges_of_def)
    have eE: "?e \<in> E" using eI edges_of_sub[OF I(1)] by blast
    have dA: "dim_row (?A\<^sup>T) = nv" by (rule carrier_matD(1)[OF At])
    have dB: "dim_col (?A\<^sup>T) = nv" by (rule carrier_matD(2)[OF At])
    have s1: "(?A\<^sup>T *\<^sub>v ?v) $ j = (\<Sum>i\<in>{0..<nv}. ?A $$ (i, j) * (if vs ! i \<in> C then 1 else 0))"
    proof -
      have "j < dim_row (?A\<^sup>T)" using dA j' by simp
      then have "(?A\<^sup>T *\<^sub>v ?v) $ j = row (?A\<^sup>T) j \<bullet> ?v" by (rule index_mult_mat_vec)
      also have "\<dots> = (\<Sum>i\<in>{0..<nv}. ?A $$ (i, j) * (if vs ! i \<in> C then 1 else 0))"
        unfolding scalar_prod_def
      proof (rule sum.cong)
        show "{0..<dim_vec ?v} = {0..<nv}" by simp
      next
        fix i assume "i \<in> {0..<nv}"
        then have i: "i < nv" by simp
        have "row (?A\<^sup>T) j $ i = (?A\<^sup>T) $$ (j, i)"
          by (rule index_row(1)) (use i j' dA dB in simp_all)
        also have "\<dots> = ?A $$ (i, j)" using i j' dA dB by (simp add: index_transpose_mat)
        finally show "row (?A\<^sup>T) j $ i * ?v $ i = ?A $$ (i, j) * (if vs ! i \<in> C then 1 else 0)"
          using i by simp
      qed
      finally show ?thesis .
    qed
    have s2: "(\<Sum>i\<in>{0..<nv}. ?A $$ (i, j) * (if vs ! i \<in> C then (1::int) else 0))
        = (\<Sum>i\<in>{0..<nv}. ori (vs ! i) ?e * (if vs ! i \<in> C then 1 else 0))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {0..<nv}"
      then have "i < nv" by simp
      then show "?A $$ (i, j) * (if vs ! i \<in> C then (1::int) else 0)
          = ori (vs ! i) ?e * (if vs ! i \<in> C then 1 else 0)"
        using entry[OF _ j'] by simp
    qed
    have "(?A\<^sup>T *\<^sub>v ?v) $ j = (\<Sum>i\<in>{0..<nv}. ori (vs ! i) ?e * (if vs ! i \<in> C then 1 else 0))"
      using s1 s2 by simp
    also have "\<dots> = (\<Sum>x\<in>V - {r}. ori x ?e * (if x \<in> C then 1 else 0))"
      by (rule sum_vs)
    also have "\<dots> = (\<Sum>x\<in>C. ori x ?e)"
      by (rule sum.mono_neutral_cong_right) (use C finV finC in auto)
    also have "\<dots> = 0"
    proof (cases "?e \<inter> C = {}")
      case True
      then show ?thesis by (intro sum.neutral) (auto simp: ori_def)
    next
      case False
      then obtain x where x: "x \<in> ?e" "x \<in> C" by blast
      have "?e \<subseteq> C" using cl[OF eI x(1) _ x(2)] by blast
      have "(\<Sum>x\<in>C. ori x ?e) = (\<Sum>x\<in>?e. ori x ?e)"
        by (rule sum.mono_neutral_cong_right)
           (use finC \<open>?e \<subseteq> C\<close> in \<open>auto simp: ori_def\<close>)
      then show ?thesis using ori_pair[OF eE] by simp
    qed
    finally show "(?A\<^sup>T *\<^sub>v ?v) $ j = 0\<^sub>v nv $ j" using j' by simp
  next
    have "dim_vec (?A\<^sup>T *\<^sub>v ?v) = dim_row (?A\<^sup>T)" by (rule dim_mult_mat_vec)
    also have "\<dots> = nv" by (rule carrier_matD(1)[OF At])
    finally show "dim_vec (?A\<^sup>T *\<^sub>v ?v) = dim_vec (0\<^sub>v nv)" by (simp only: index_zero_vec(2))
  qed
  moreover have "?v \<noteq> 0\<^sub>v nv"
  proof -
    obtain x where "x \<in> C" using C(3) by blast
    then have "x \<in> set vs" using C set_vs by auto
    then obtain i where i: "i < nv" "vs ! i = x" using in_set_conv_nth by metis
    have "?v $ i = 1" using i \<open>x \<in> C\<close> by simp
    moreover have "(0\<^sub>v nv :: int vec) $ i = 0" using i by simp
    ultimately show ?thesis by (metis zero_neq_one)
  qed
  ultimately have ex: "\<exists>v. v \<in> carrier_vec nv \<and> v \<noteq> 0\<^sub>v nv \<and> ?A\<^sup>T *\<^sub>v v = 0\<^sub>v nv"
    using vc by blast
  have "det (?A\<^sup>T) = 0" by (rule iffD2[OF det_0_iff_vec_prod_zero[OF At] ex])
  then show ?thesis using det_transpose[OF Ac] by simp
qed

subsection \<open>Trees: squared minors are one\<close>

text \<open>If they form a tree, a leaf other than the root has a single nonzero entry in its row; expand along it
and remove the leaf (induction on the number of vertices).\<close>

definition ori0 :: "'a::linorder \<Rightarrow> 'a set \<Rightarrow> int" where
  "ori0 v e = (if v \<in> e then (if v = Min e then 1 else -1) else 0)"

definition Mx :: "'a::linorder list \<Rightarrow> 'a set list \<Rightarrow> int mat" where
  "Mx xs ys = mat (length xs) (length ys) (\<lambda>(i, j). ori0 (xs ! i) (ys ! j))"

definition del_nth :: "nat \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "del_nth k xs = take k xs @ drop (Suc k) xs"

lemma Mx_carrier: "Mx xs ys \<in> carrier_mat (length xs) (length ys)"
  by (simp add: Mx_def)

lemma Mx_index: "i < length xs \<Longrightarrow> j < length ys \<Longrightarrow> Mx xs ys $$ (i, j) = ori0 (xs ! i) (ys ! j)"
  by (simp add: Mx_def)

lemma ori0_sq: "v \<in> e \<Longrightarrow> ori0 v e * ori0 v e = 1"
  by (simp add: ori0_def)

lemma length_del_nth: "k < length xs \<Longrightarrow> length (del_nth k xs) = length xs - 1"
  by (simp add: del_nth_def)

lemma del_nth_index:
  assumes "k < length xs" "i < length xs - 1"
  shows "del_nth k xs ! i = xs ! (if i < k then i else Suc i)"
proof (cases "i < k")
  case True
  then show ?thesis using assms by (simp add: del_nth_def nth_append)
next
  case False
  then show ?thesis using assms by (simp add: del_nth_def nth_append)
qed

lemma mat_delete_Mx:
  assumes "i < length xs" "j < length ys"
  shows "mat_delete (Mx xs ys) i j = Mx (del_nth i xs) (del_nth j ys)"
proof (rule eq_matI)
  fix a b
  assume a: "a < dim_row (Mx (del_nth i xs) (del_nth j ys))"
    and b: "b < dim_col (Mx (del_nth i xs) (del_nth j ys))"
  then have a': "a < length xs - 1" and b': "b < length ys - 1"
    using assms by (simp_all add: Mx_def length_del_nth)
  have "mat_delete (Mx xs ys) i j $$ (a, b)
      = Mx xs ys $$ (if a < i then a else Suc a, if b < j then b else Suc b)"
    unfolding mat_delete_def using a' b' by (simp add: Mx_def)
  also have "\<dots> = ori0 (xs ! (if a < i then a else Suc a)) (ys ! (if b < j then b else Suc b))"
    using a' b' assms by (intro Mx_index) auto
  also have "\<dots> = Mx (del_nth i xs) (del_nth j ys) $$ (a, b)"
    using a' b' assms by (simp add: Mx_def length_del_nth del_nth_index)
  finally show "mat_delete (Mx xs ys) i j $$ (a, b) = Mx (del_nth i xs) (del_nth j ys) $$ (a, b)" .
next
  show "dim_row (mat_delete (Mx xs ys) i j) = dim_row (Mx (del_nth i xs) (del_nth j ys))"
    using assms by (simp add: Mx_def length_del_nth)
next
  show "dim_col (mat_delete (Mx xs ys) i j) = dim_col (Mx (del_nth i xs) (del_nth j ys))"
    using assms by (simp add: Mx_def length_del_nth)
qed

lemma del_nth_props:
  assumes "distinct xs" "k < length xs"
  shows "distinct (del_nth k xs)" "set (del_nth k xs) = set xs - {xs ! k}"
proof -
  have e: "take k xs @ xs ! k # drop (Suc k) xs = xs" by (rule id_take_nth_drop[OF assms(2), symmetric])
  have d: "distinct (take k xs @ xs ! k # drop (Suc k) xs)" using assms(1) by (simp only: e)
  have s: "set (take k xs @ xs ! k # drop (Suc k) xs) = set xs" by (simp only: e)
  from d show "distinct (del_nth k xs)" by (auto simp: del_nth_def)
  from d s show "set (del_nth k xs) = set xs - {xs ! k}" by (auto simp: del_nth_def)
qed

lemma sq_minus_one_pow: "(-1 :: int) ^ m * (-1) ^ m = 1"
  by (cases "even m") (simp_all add: minus_one_power_iff)

lemma det_sq_expand_row:
  assumes A: "A \<in> carrier_mat n n" and i: "i < n" and j0: "j0 < n"
    and z: "\<And>j. j < n \<Longrightarrow> j \<noteq> j0 \<Longrightarrow> A $$ (i, j) = 0"
    and u: "A $$ (i, j0) * A $$ (i, j0) = 1"
  shows "(det A)\<^sup>2 = (det (mat_delete A i j0))\<^sup>2"
proof -
  have "det A = (\<Sum>j<n. A $$ (i, j) * cofactor A i j)" by (rule laplace_expansion_row[OF A i])
  also have "\<dots> = (\<Sum>j\<in>{j0}. A $$ (i, j) * cofactor A i j)"
    by (rule sum.mono_neutral_right) (use j0 z in auto)
  finally have d: "det A = A $$ (i, j0) * cofactor A i j0" by simp
  have "(det A)\<^sup>2 = (A $$ (i, j0) * A $$ (i, j0)) * (cofactor A i j0 * cofactor A i j0)"
    by (simp add: d power2_eq_square algebra_simps)
  also have "cofactor A i j0 * cofactor A i j0
      = ((-1) ^ (i + j0) * (-1) ^ (i + j0)) * (det (mat_delete A i j0) * det (mat_delete A i j0))"
    by (simp add: cofactor_def algebra_simps)
  finally show ?thesis using u by (simp add: sq_minus_one_pow power2_eq_square)
qed

lemma det_sq_expand_col:
  assumes A: "A \<in> carrier_mat n n" and i0: "i0 < n" and j: "j < n"
    and z: "\<And>i. i < n \<Longrightarrow> i \<noteq> i0 \<Longrightarrow> A $$ (i, j) = 0"
    and u: "A $$ (i0, j) * A $$ (i0, j) = 1"
  shows "(det A)\<^sup>2 = (det (mat_delete A i0 j))\<^sup>2"
proof -
  have "det A = (\<Sum>i<n. A $$ (i, j) * cofactor A i j)" by (rule laplace_expansion_column[OF A j])
  also have "\<dots> = (\<Sum>i\<in>{i0}. A $$ (i, j) * cofactor A i j)"
    by (rule sum.mono_neutral_right) (use i0 z in auto)
  finally have d: "det A = A $$ (i0, j) * cofactor A i0 j" by simp
  have "(det A)\<^sup>2 = (A $$ (i0, j) * A $$ (i0, j)) * (cofactor A i0 j * cofactor A i0 j)"
    by (simp add: d power2_eq_square algebra_simps)
  also have "cofactor A i0 j * cofactor A i0 j
      = ((-1) ^ (i0 + j) * (-1) ^ (i0 + j)) * (det (mat_delete A i0 j) * det (mat_delete A i0 j))"
    by (simp add: cofactor_def algebra_simps)
  finally show ?thesis using u by (simp add: sq_minus_one_pow power2_eq_square)
qed

lemma tree_Mx_det_sq:
  assumes "tree W T"
  shows "\<forall>\<rho> xs ys. \<rho> \<in> W \<longrightarrow> distinct xs \<longrightarrow> distinct ys \<longrightarrow> set xs = W - {\<rho>} \<longrightarrow> set ys = T
           \<longrightarrow> length xs = length ys \<longrightarrow> (det (Mx xs ys))\<^sup>2 = 1"
  using assms
proof (induction rule: tree_induct)
  case (singolton v)
  show ?case
  proof (intro allI impI)
    fix \<rho> :: 'a and xs :: "'a list" and ys :: "'a set list"
    assume "\<rho> \<in> {v}" "distinct xs" "distinct ys" "set xs = {v} - {\<rho>}" "set ys = {}" "length xs = length ys"
    then have "xs = []" "ys = []" by auto
    then have "Mx xs ys \<in> carrier_mat 0 0" by (simp add: Mx_def)
    then show "(det (Mx xs ys))\<^sup>2 = 1" by simp
  qed
next
  case (insert l v V E)
  note tr = insert(1) and IH = insert.IH and lV = insert(2) and vV = insert(3) and lvE = insert(4)
  interpret t: tree V E by (rule tr)
  have E_sub: "\<And>e. e \<in> E \<Longrightarrow> e \<subseteq> V" using t.wellformed by blast
  have lnot: "\<And>e. e \<in> E \<Longrightarrow> l \<notin> e" using E_sub lV by blast
  have lv: "l \<noteq> v" using lV vV by auto
  show ?case
  proof (intro allI impI)
    fix \<rho> :: 'a and xs :: "'a list" and ys :: "'a set list"
    assume rho: "\<rho> \<in> insert l V" and dxs: "distinct xs" and dys: "distinct ys"
      and sxs: "set xs = insert l V - {\<rho>}" and sys: "set ys = insert {l, v} E"
      and len: "length xs = length ys"
    obtain j0 where j0: "j0 < length ys" "ys ! j0 = {l, v}" using sys by (metis in_set_conv_nth insertI1)
    have ysl: "\<And>j. j < length ys \<Longrightarrow> j \<noteq> j0 \<Longrightarrow> l \<notin> ys ! j"
    proof -
      fix j assume j: "j < length ys" "j \<noteq> j0"
      have mem: "ys ! j \<in> insert {l, v} E" using j(1) sys nth_mem by blast
      have "ys ! j \<noteq> {l, v}"
        using j j0 dys nth_eq_iff_index_eq by metis
      then have "ys ! j \<in> E" using mem by simp
      then show "l \<notin> ys ! j" by (rule lnot)
    qed
    show "(det (Mx xs ys))\<^sup>2 = 1"
    proof (cases "\<rho> = l")
      case False
      then have rV: "\<rho> \<in> V" using rho by simp
      have "l \<in> set xs" using sxs False by simp
      then obtain i0 where i0: "i0 < length xs" "xs ! i0 = l" by (auto simp: in_set_conv_nth)
      have n: "Mx xs ys \<in> carrier_mat (length xs) (length xs)" using Mx_carrier len by metis
      have z: "\<And>j. j < length xs \<Longrightarrow> j \<noteq> j0 \<Longrightarrow> Mx xs ys $$ (i0, j) = 0"
      proof -
        fix j assume j: "j < length xs" "j \<noteq> j0"
        have "l \<notin> ys ! j" using ysl j len by simp
        then show "Mx xs ys $$ (i0, j) = 0" using j i0 len by (simp add: Mx_index ori0_def)
      qed
      have u: "Mx xs ys $$ (i0, j0) * Mx xs ys $$ (i0, j0) = 1"
        using i0 j0 len by (simp add: Mx_index ori0_sq)
      have "(det (Mx xs ys))\<^sup>2 = (det (mat_delete (Mx xs ys) i0 j0))\<^sup>2"
        by (rule det_sq_expand_row[OF n i0(1) _ z u]) (use j0 len in auto)
      also have "mat_delete (Mx xs ys) i0 j0 = Mx (del_nth i0 xs) (del_nth j0 ys)"
        by (rule mat_delete_Mx) (use i0 j0 in auto)
      also have "(det \<dots>)\<^sup>2 = 1"
      proof -
        have s1: "set (del_nth i0 xs) = V - {\<rho>}"
          using del_nth_props(2)[OF dxs i0(1)] i0(2) sxs lV by auto
        have s2: "set (del_nth j0 ys) = E"
          using del_nth_props(2)[OF dys j0(1)] j0(2) sys lvE by auto
        have ll: "length (del_nth i0 xs) = length (del_nth j0 ys)"
          using length_del_nth[OF i0(1)] length_del_nth[OF j0(1)] len by simp
        show ?thesis
          using IH[rule_format, OF rV del_nth_props(1)[OF dxs i0(1)] del_nth_props(1)[OF dys j0(1)] s1 s2 ll] .
      qed
      finally show ?thesis .
    next
      case True
      then have sxs': "set xs = V" using sxs lV by auto
      then obtain i0 where i0: "i0 < length xs" "xs ! i0 = v" using vV by (auto simp: in_set_conv_nth)
      have n: "Mx xs ys \<in> carrier_mat (length xs) (length xs)" using Mx_carrier len by metis
      have z: "\<And>i. i < length xs \<Longrightarrow> i \<noteq> i0 \<Longrightarrow> Mx xs ys $$ (i, j0) = 0"
      proof -
        fix i assume i: "i < length xs" "i \<noteq> i0"
        have xi: "xs ! i \<in> V" using i sxs' nth_mem by blast
        have "xs ! i \<noteq> v" using i i0 dxs nth_eq_iff_index_eq by metis
        moreover have "xs ! i \<noteq> l" using xi lV by auto
        ultimately show "Mx xs ys $$ (i, j0) = 0" using i j0 len by (simp add: Mx_index ori0_def)
      qed
      have u: "Mx xs ys $$ (i0, j0) * Mx xs ys $$ (i0, j0) = 1"
        using i0 j0 len by (simp add: Mx_index ori0_sq)
      have "(det (Mx xs ys))\<^sup>2 = (det (mat_delete (Mx xs ys) i0 j0))\<^sup>2"
        by (rule det_sq_expand_col[OF n i0(1) _ z u]) (use j0 len in auto)
      also have "mat_delete (Mx xs ys) i0 j0 = Mx (del_nth i0 xs) (del_nth j0 ys)"
        by (rule mat_delete_Mx) (use i0 j0 in auto)
      also have "(det \<dots>)\<^sup>2 = 1"
      proof -
        have s1: "set (del_nth i0 xs) = V - {v}"
          using del_nth_props(2)[OF dxs i0(1)] i0(2) sxs' by auto
        have s2: "set (del_nth j0 ys) = E"
          using del_nth_props(2)[OF dys j0(1)] j0(2) sys lvE by auto
        have ll: "length (del_nth i0 xs) = length (del_nth j0 ys)"
          using length_del_nth[OF i0(1)] length_del_nth[OF j0(1)] len by simp
        show ?thesis
          using IH[rule_format, OF vV del_nth_props(1)[OF dxs i0(1)] del_nth_props(1)[OF dys j0(1)] s1 s2 ll] .
      qed
      finally show ?thesis .
    qed
  qed
qed

lemma ori_eq_ori0: "ori v e = ori0 v e"
  by (simp add: ori_def ori0_def)

lemma submatrix_inc_eq:
  assumes "I \<subseteq> {0..<ne}" "card I = nv"
  shows "submatrix inc UNIV I = Mx vs (map (\<lambda>k. es ! k) (sorted_list_of_set I))"
proof -
  have fin: "finite I" using assms(1) finite_subset by blast
  have lL: "length (sorted_list_of_set I) = nv" using assms(2) by simp
  have r: "{i. i < dim_row inc \<and> i \<in> UNIV} = {..<nv}" by (auto simp: inc_def)
  have c: "{j. j < dim_col inc \<and> j \<in> I} = I" using assms(1) by (auto simp: inc_def)
  show ?thesis
  proof (rule eq_matI)
    fix i j
    assume i: "i < dim_row (Mx vs (map (\<lambda>k. es ! k) (sorted_list_of_set I)))"
      and j: "j < dim_col (Mx vs (map (\<lambda>k. es ! k) (sorted_list_of_set I)))"
    then have i': "i < nv" and j': "j < nv" using lL by (simp_all add: Mx_def)
    have jL: "j < length (sorted_list_of_set I)" using j' lL by simp
    have pj: "pick I j = sorted_list_of_set I ! j" using sorted_list_of_set_eq_pick[OF jL] by simp
    have mem: "sorted_list_of_set I ! j \<in> I" using jL fin by (metis nth_mem set_sorted_list_of_set)
    then have lt: "sorted_list_of_set I ! j < ne" using assms(1) by auto
    have "submatrix inc UNIV I $$ (i, j) = inc $$ (pick UNIV i, pick I j)"
      by (rule submatrix_index) (use i' j' r c assms(2) in simp_all)
    also have "\<dots> = ori (vs ! i) (es ! (sorted_list_of_set I ! j))"
      using i' lt pj by (simp add: pick_UNIV inc_def)
    also have "\<dots> = Mx vs (map (\<lambda>k. es ! k) (sorted_list_of_set I)) $$ (i, j)"
      using i' jL lL by (simp add: Mx_index ori_eq_ori0)
    finally show "submatrix inc UNIV I $$ (i, j) = Mx vs (map (\<lambda>k. es ! k) (sorted_list_of_set I)) $$ (i, j)" .
  next
    show "dim_row (submatrix inc UNIV I) = dim_row (Mx vs (map (\<lambda>k. es ! k) (sorted_list_of_set I)))"
      using r by (simp add: dim_submatrix Mx_def)
  next
    show "dim_col (submatrix inc UNIV I) = dim_col (Mx vs (map (\<lambda>k. es ! k) (sorted_list_of_set I)))"
      using c lL assms(2) by (simp add: dim_submatrix Mx_def)
  qed
qed

lemma det_minor_unit_if_tree:
  assumes "I \<subseteq> {0..<ne}" "card I = nv" "tree V (edges_of I)"
  shows "(det (submatrix inc UNIV I))\<^sup>2 = 1"
proof -
  have fin: "finite I" using assms(1) finite_subset by blast
  let ?L = "sorted_list_of_set I"
  have lL: "length ?L = nv" using assms(2) by simp
  have inj: "inj_on (\<lambda>k. es ! k) (set ?L)"
  proof (rule inj_onI)
    fix a b assume "a \<in> set ?L" "b \<in> set ?L" "es ! a = es ! b"
    then have "a < ne" "b < ne" using assms(1) fin by auto
    then show "a = b" using \<open>es ! a = es ! b\<close> es_distinct nth_eq_iff_index_eq by blast
  qed
  have dys: "distinct (map (\<lambda>k. es ! k) ?L)" using inj by (simp add: distinct_map)
  have sys: "set (map (\<lambda>k. es ! k) ?L) = edges_of I" using fin by (simp add: edges_of_def)
  have "(det (Mx vs (map (\<lambda>k. es ! k) ?L)))\<^sup>2 = 1"
    using tree_Mx_det_sq[OF assms(3)] root vs_distinct dys set_vs sys lL by auto
  then show ?thesis using submatrix_inc_eq[OF assms(1,2)] by simp
qed

subsection \<open>Edge sets that are spanning trees\<close>

text \<open>A connected spanning subgraph with @{term "card V - 1"} edges is a tree.\<close>

lemma card_edges_of:
  assumes "I \<subseteq> {0..<ne}"
  shows "card (edges_of I) = card I"
proof -
  have "inj_on (\<lambda>j. es ! j) I"
  proof (rule inj_onI)
    fix x y assume "x \<in> I" "y \<in> I" "es ! x = es ! y"
    then have "x < ne" "y < ne" using assms by auto
    then show "x = y" using es_distinct \<open>es ! x = es ! y\<close> nth_eq_iff_index_eq by blast
  qed
  then show ?thesis unfolding edges_of_def by (rule card_image)
qed

lemma connected_card_tree:
  assumes "T \<subseteq> E" "card T = card V - 1" "fin_connected_ulgraph V T"
  shows "tree V T"
proof -
  have pos: "card V > 0" using finV root by (simp add: card_gt_0_iff) blast
  have "card V = Suc (card T)" using assms(2) pos by simp
  then show ?thesis using card_E_treeI[OF assms(3)] by simp
qed

lemma spanning_tree_iff:
  "spanning_tree V E T \<longleftrightarrow> T \<subseteq> E \<and> card T = card V - 1 \<and> fin_connected_ulgraph V T"
proof
  assume st: "spanning_tree V E T"
  interpret spanning_tree V E T using st .
  show "T \<subseteq> E \<and> card T = card V - 1 \<and> fin_connected_ulgraph V T"
    using subgraph T.card_V_card_E T.fin_connected_ulgraph_axioms by simp
next
  assume h: "T \<subseteq> E \<and> card T = card V - 1 \<and> fin_connected_ulgraph V T"
  then have tr: "tree V T" using connected_card_tree by blast
  show "spanning_tree V E T"
    unfolding spanning_tree_def spanning_tree_axioms_def using ulgraph_axioms tr h by simp
qed

lemma det_minor_sq:
  assumes I: "I \<subseteq> {0..<ne}" "card I = nv"
  shows "(det (submatrix inc UNIV I))\<^sup>2 = (if spanning_tree V E (edges_of I) then 1 else 0)"
proof (cases "spanning_tree V E (edges_of I)")
  case True
  then have "tree V (edges_of I)" using spanning_tree_def by (metis spanning_tree.axioms(2))
  then show ?thesis using True det_minor_unit_if_tree[OF I] by simp
next
  case False
  have "\<not> fin_connected_ulgraph V (edges_of I)"
  proof
    assume c: "fin_connected_ulgraph V (edges_of I)"
    have "spanning_tree V E (edges_of I)"
      using spanning_tree_iff c edges_of_sub[OF I(1)] card_edges_of[OF I(1)] I(2) nv_eq by simp
    then show False using False by simp
  qed
  then have "det (submatrix inc UNIV I) = 0" using det_minor_zero_if_not_connected[OF I] by blast
  then show ?thesis using False by simp
qed

section \<open>Counting\<close>

lemma edges_of_bij:
  "bij_betw edges_of {I. I \<subseteq> {0..<ne} \<and> card I = nv} {T. T \<subseteq> E \<and> card T = nv}"
proof (rule bij_betw_byWitness[where f' = "\<lambda>T. {k. k < ne \<and> es ! k \<in> T}"])
  have inj: "inj_on (\<lambda>j. es ! j) {0..<ne}"
  proof (rule inj_onI)
    fix x y assume "x \<in> {0..<ne}" "y \<in> {0..<ne}" "es ! x = es ! y"
    then have "x < ne" "y < ne" by simp_all
    then show "x = y" using es_distinct \<open>es ! x = es ! y\<close> nth_eq_iff_index_eq by blast
  qed
  have bk: "edges_of {k. k < ne \<and> es ! k \<in> T} = T" if T: "T \<subseteq> E" for T
  proof -
    show ?thesis
    proof
      show "edges_of {k. k < ne \<and> es ! k \<in> T} \<subseteq> T"
      proof (rule subsetI)
        fix t assume "t \<in> edges_of {k. k < ne \<and> es ! k \<in> T}"
        then obtain k where "k \<in> {k. k < ne \<and> es ! k \<in> T}" "t = es ! k" unfolding edges_of_def by blast
        then show "t \<in> T" by simp
      qed
      show "T \<subseteq> edges_of {k. k < ne \<and> es ! k \<in> T}"
      proof
        fix t assume t: "t \<in> T"
        have "t \<in> set es" using T t set_es by blast
        from iffD1[OF in_set_conv_nth this] obtain k where kk: "k < length es" "es ! k = t" by blast
        then have "k \<in> {k. k < ne \<and> es ! k \<in> T}" using t by simp
        then have "es ! k \<in> edges_of {k. k < ne \<and> es ! k \<in> T}" unfolding edges_of_def by (rule imageI)
        then show "t \<in> edges_of {k. k < ne \<and> es ! k \<in> T}" using kk(2) by simp
      qed
    qed
  qed
  show "\<forall>I\<in>{I. I \<subseteq> {0..<ne} \<and> card I = nv}. {k. k < ne \<and> es ! k \<in> edges_of I} = I"
  proof
    fix I assume "I \<in> {I. I \<subseteq> {0..<ne} \<and> card I = nv}"
    then have I: "I \<subseteq> {0..<ne}" by simp
    show "{k. k < ne \<and> es ! k \<in> edges_of I} = I"
    proof
      show "{k. k < ne \<and> es ! k \<in> edges_of I} \<subseteq> I"
      proof (rule subsetI)
        fix x assume "x \<in> {k. k < ne \<and> es ! k \<in> edges_of I}"
        then have x: "x < ne" "es ! x \<in> edges_of I" by simp_all
        then obtain j where j: "j \<in> I" "es ! x = es ! j" unfolding edges_of_def by blast
        have "x \<in> {0..<ne}" "j \<in> {0..<ne}" using x(1) j(1) I by auto
        then have "x = j" by (rule inj_onD[OF inj j(2)])
        then show "x \<in> I" using j(1) by simp
      qed
      show "I \<subseteq> {k. k < ne \<and> es ! k \<in> edges_of I}"
      proof (rule subsetI)
        fix j assume j: "j \<in> I"
        then have "j < ne" using I by auto
        moreover have "es ! j \<in> edges_of I" unfolding edges_of_def using j by (rule imageI)
        ultimately show "j \<in> {k. k < ne \<and> es ! k \<in> edges_of I}" by simp
      qed
    qed
  qed
  show "\<forall>T\<in>{T. T \<subseteq> E \<and> card T = nv}. edges_of {k. k < ne \<and> es ! k \<in> T} = T"
    using bk by blast
  show "edges_of ` {I. I \<subseteq> {0..<ne} \<and> card I = nv} \<subseteq> {T. T \<subseteq> E \<and> card T = nv}"
  proof (rule subsetI)
    fix T assume "T \<in> edges_of ` {I. I \<subseteq> {0..<ne} \<and> card I = nv}"
    then obtain I where I: "I \<subseteq> {0..<ne}" "card I = nv" and "T = edges_of I" by blast
    then show "T \<in> {T. T \<subseteq> E \<and> card T = nv}"
      using edges_of_sub[OF I(1)] card_edges_of[OF I(1)] I(2) by simp
  qed
  show "(\<lambda>T. {k. k < ne \<and> es ! k \<in> T}) ` {T. T \<subseteq> E \<and> card T = nv} \<subseteq> {I. I \<subseteq> {0..<ne} \<and> card I = nv}"
  proof (rule subsetI)
    fix J assume "J \<in> (\<lambda>T. {k. k < ne \<and> es ! k \<in> T}) ` {T. T \<subseteq> E \<and> card T = nv}"
    then obtain T where T: "T \<subseteq> E" "card T = nv" and J: "J = {k. k < ne \<and> es ! k \<in> T}" by blast
    have sub: "J \<subseteq> {0..<ne}" using J by (auto simp: atLeastLessThan_iff)
    have "card J = card (edges_of J)" using card_edges_of[OF sub] by simp
    moreover have "edges_of J = T" using bk[OF T(1)] J by simp
    ultimately have "card J = nv" using T(2) by simp
    then show "J \<in> {I. I \<subseteq> {0..<ne} \<and> card I = nv}" using sub by simp
  qed
qed

theorem matrix_tree: "det lap = int (card {T. spanning_tree V E T})"
proof -
  let ?A = "{I. I \<subseteq> {0..<ne} \<and> card I = nv}"
  let ?B = "{T. T \<subseteq> E \<and> card T = nv}"
  have finB: "finite ?B"
  proof (rule finite_subset[of _ "Pow E"])
    show "?B \<subseteq> Pow E" by auto
    show "finite (Pow E)" using fin_edges by simp
  qed
  have eq: "{T\<in>?B. spanning_tree V E T} = {T. spanning_tree V E T}"
  proof (rule equalityI)
    show "{T\<in>?B. spanning_tree V E T} \<subseteq> {T. spanning_tree V E T}" by (rule subsetI) simp
    show "{T. spanning_tree V E T} \<subseteq> {T\<in>?B. spanning_tree V E T}"
    proof (rule subsetI)
      fix T assume "T \<in> {T. spanning_tree V E T}"
      then have st: "spanning_tree V E T" by simp
      then have "T \<subseteq> E \<and> card T = card V - 1" using spanning_tree_iff by blast
      then show "T \<in> {T\<in>?B. spanning_tree V E T}" using nv_eq st by simp
    qed
  qed
  have "det lap = (\<Sum>I\<in>?A. if spanning_tree V E (edges_of I) then 1 else 0)"
    unfolding det_lap_sum_squares
  proof (rule sum.cong[OF refl])
    fix I assume "I \<in> ?A"
    then have "I \<subseteq> {0..<ne}" "card I = nv" by simp_all
    then show "(det (submatrix inc UNIV I))\<^sup>2 = (if spanning_tree V E (edges_of I) then 1 else 0)"
      by (rule det_minor_sq)
  qed
  also have "\<dots> = (\<Sum>T\<in>?B. if spanning_tree V E T then 1 else 0)"
    by (rule sum.reindex_bij_betw[OF edges_of_bij])
  also have "\<dots> = int (card {T\<in>?B. spanning_tree V E T})"
  proof -
    have "(\<Sum>T\<in>?B. if spanning_tree V E T then (1::int) else 0) = (\<Sum>T\<in>{T\<in>?B. spanning_tree V E T}. 1)"
      by (rule sum.inter_filter[OF finB, symmetric])
    then show ?thesis by simp
  qed
  finally show ?thesis using eq by simp
qed

end

end
