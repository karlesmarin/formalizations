(*  Title:      Path_Tree_Dvd.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Divisibility of the path tree's matching polynomial

    The matching polynomial of the connected component of u divides that of the path tree at u; for a connected graph,
    mu G divides mu T. For a disconnected graph mu G need not divide mu T, since T only sees the component of u.

    Main results:
    * godsil_dvd_comp: the matching polynomial of the component of u divides mu T.
    * godsil_dvd: for a connected graph, mu G divides mu T.

    References:
    * C. D. Godsil, Matchings and walks in graphs, J. Graph Theory 5 (1981) 285--297.
*)

theory Path_Tree_Dvd
  imports Path_Tree
begin

section \<open>Connected components\<close>

text \<open>The component of \<open>u\<close>: the last vertices of the paths that start at \<open>u\<close>. Restricting a graph to a set of
  vertices keeps the edges inside it.\<close>

definition comp :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "comp V E u = last ` pt_V V E u"

definition restr :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "restr C E = {e \<in> E. e \<subseteq> C}"

subsection \<open>Reachability\<close>

abbreviation adjr :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "adjr E a b \<equiv> {a, b} \<in> E"

lemma reach_symm: "(adjr E)\<^sup>*\<^sup>* a b \<Longrightarrow> (adjr E)\<^sup>*\<^sup>* b a"
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule rtranclp.rtrancl_refl)
next
  case (step b c)
  have "adjr E c b" using step(2) by (simp add: insert_commute)
  then have "(adjr E)\<^sup>*\<^sup>* c b" by (rule r_into_rtranclp)
  then show ?case using step(3) by (rule rtranclp_trans)
qed

lemma path_reach: "is_path E p \<Longrightarrow> \<forall>x\<in>set p. (adjr E)\<^sup>*\<^sup>* (hd p) x"
proof (induction p)
  case Nil
  then show ?case by (simp add: is_path_def)
next
  case (Cons a q)
  show ?case
  proof (cases "q = []")
    case True
    then show ?thesis by simp
  next
    case False
    have H: "adjr E a (hd q)" and pq: "is_path E q" using Cons.prems is_path_Cons[OF False] by blast+
    have IH: "\<forall>x\<in>set q. (adjr E)\<^sup>*\<^sup>* (hd q) x" using Cons.IH[OF pq] .
    have s: "(adjr E)\<^sup>*\<^sup>* a (hd q)" using H by (rule r_into_rtranclp)
    show ?thesis
    proof
      fix x assume x: "x \<in> set (a # q)"
      show "(adjr E)\<^sup>*\<^sup>* (hd (a # q)) x"
      proof (cases "x = a")
        case True
        then show ?thesis by simp
      next
        case False
        then have "x \<in> set q" using x by simp
        then have "(adjr E)\<^sup>*\<^sup>* (hd q) x" using IH by blast
        then show ?thesis using s by (simp add: rtranclp_trans)
      qed
    qed
  qed
qed

lemma is_path_prefix: "is_path E (q @ r) \<Longrightarrow> q \<noteq> [] \<Longrightarrow> is_path E q"
  unfolding is_path_def
proof (intro conjI allI impI)
  assume H: "(q @ r) \<noteq> [] \<and> distinct (q @ r) \<and> (\<forall>i. Suc i < length (q @ r) \<longrightarrow> {(q @ r) ! i, (q @ r) ! Suc i} \<in> E)"
    and q: "q \<noteq> []"
  show "q \<noteq> []" by fact
  show "distinct q" using H by simp
  fix i assume i: "Suc i < length q"
  have i0: "i < length q" using i by simp
  have "Suc i < length (q @ r)" using i by simp
  then have "{(q @ r) ! i, (q @ r) ! Suc i} \<in> E" using H by blast
  then show "{q ! i, q ! Suc i} \<in> E" using i i0 by (simp add: nth_append)
qed

lemma is_path_snoc:
  assumes "is_path E p" and "w \<notin> set p" and "{last p, w} \<in> E"
  shows "is_path E (p @ [w])"
proof -
  have p0: "p \<noteq> []" and d: "distinct p"
    and e: "\<forall>i. Suc i < length p \<longrightarrow> {p ! i, p ! Suc i} \<in> E" using assms(1) unfolding is_path_def by auto
  show ?thesis unfolding is_path_def
  proof (intro conjI allI impI)
    show "p @ [w] \<noteq> []" by simp
    show "distinct (p @ [w])" using d assms(2) by simp
    fix i assume i: "Suc i < length (p @ [w])"
    show "{(p @ [w]) ! i, (p @ [w]) ! Suc i} \<in> E"
    proof (cases "Suc i < length p")
      case True
      then show ?thesis using e by (simp add: nth_append)
    next
      case False
      then have ie: "Suc i = length p" using i by simp
      then have i0: "i < length p" by simp
      have il: "i = length p - 1" using ie by simp
      have "(p @ [w]) ! i = last p" using i0 p0 il by (simp add: nth_append last_conv_nth)
      moreover have "(p @ [w]) ! Suc i = w" using ie by simp
      ultimately show ?thesis using assms(3) by simp
    qed
  qed
qed

lemma is_path_mono: "is_path E' p \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> is_path E p"
  unfolding is_path_def by blast

lemma comp_eq:
  assumes G: "graph V E" and u: "u \<in> V"
  shows "comp V E u = {w \<in> V. (adjr E)\<^sup>*\<^sup>* u w}"
proof
  show "comp V E u \<subseteq> {w \<in> V. (adjr E)\<^sup>*\<^sup>* u w}"
  proof
    fix w assume "w \<in> comp V E u"
    then obtain p where p: "p \<in> pt_V V E u" and w: "w = last p" unfolding comp_def by blast
    have ip: "is_path E p" and hp: "hd p = u" and sp: "set p \<subseteq> V" using p unfolding pt_V_def by auto
    have p0: "p \<noteq> []" using ip unfolding is_path_def by blast
    have "w \<in> set p" using w p0 by simp
    then show "w \<in> {w \<in> V. (adjr E)\<^sup>*\<^sup>* u w}"
      using path_reach[OF ip] hp sp by blast
  qed
next
  show "{w \<in> V. (adjr E)\<^sup>*\<^sup>* u w} \<subseteq> comp V E u"
  proof
    fix w assume "w \<in> {w \<in> V. (adjr E)\<^sup>*\<^sup>* u w}"
    then have wV: "w \<in> V" and r: "(adjr E)\<^sup>*\<^sup>* u w" by blast+
    have "\<exists>p. p \<in> pt_V V E u \<and> last p = w" using r
    proof (induction rule: rtranclp_induct)
      case base
      show ?case using pt_root[OF u] by (intro exI[of _ "[u]"]) simp
    next
      case (step b c)
      obtain p where p: "p \<in> pt_V V E u" and lp: "last p = b" using step(3) by blast
      have ip: "is_path E p" and hp: "hd p = u" and sp: "set p \<subseteq> V" using p unfolding pt_V_def by auto
      have p0: "p \<noteq> []" using ip unfolding is_path_def by blast
      have cV: "c \<in> V" using step(2) G unfolding graph_def by blast
      show ?case
      proof (cases "c \<in> set p")
        case True
        then obtain xs ys where xy: "p = xs @ c # ys" by (blast dest: split_list)
        have pq: "p = (xs @ [c]) @ ys" using xy by simp
        have ipq: "is_path E (xs @ [c])" using ip pq is_path_prefix[of E "xs @ [c]" ys] by simp
        have "hd (xs @ [c]) = u" using hp xy by (cases xs) auto
        moreover have "set (xs @ [c]) \<subseteq> V" using sp xy by auto
        ultimately have "xs @ [c] \<in> pt_V V E u" using ipq unfolding pt_V_def by blast
        then show ?thesis by (intro exI[of _ "xs @ [c]"]) simp
      next
        case False
        have e: "{last p, c} \<in> E" using step(2) lp by simp
        have ipc: "is_path E (p @ [c])" by (rule is_path_snoc[OF ip False e])
        have "hd (p @ [c]) = u" using hp p0 by simp
        moreover have "set (p @ [c]) \<subseteq> V" using sp cV by auto
        ultimately have "p @ [c] \<in> pt_V V E u" using ipc unfolding pt_V_def by blast
        then show ?thesis by (intro exI[of _ "p @ [c]"]) simp
      qed
    qed
    then show "w \<in> comp V E u" unfolding comp_def by force
  qed
qed

lemma is_path_take:
  assumes "is_path E p" and "0 < n"
  shows "is_path E (take n p)"
  unfolding is_path_def
proof (intro conjI allI impI)
  have p: "p \<noteq> []" and d: "distinct p" and e: "\<forall>i. Suc i < length p \<longrightarrow> {p ! i, p ! Suc i} \<in> E"
    using assms(1) unfolding is_path_def by auto
  show "take n p \<noteq> []" using p assms(2) by simp
  show "distinct (take n p)" using d by simp
  fix i assume i: "Suc i < length (take n p)"
  then have "Suc i < n" "Suc i < length p" by simp_all
  then show "{take n p ! i, take n p ! Suc i} \<in> E" using e by simp
qed

lemma comp_edge_closed:
  assumes "graph V E" and "u \<in> V" and "{a, b} \<in> E" and "a \<in> comp V E u"
  shows "b \<in> comp V E u"
proof -
  obtain p where p: "p \<in> pt_V V E u" and a: "a = last p" using assms(4) unfolding comp_def by blast
  have ip: "is_path E p" and hp: "hd p = u" and sp: "set p \<subseteq> V" using p unfolding pt_V_def by auto
  have bV: "b \<in> V" using assms(1,3) unfolding graph_def by blast
  have pne: "p \<noteq> []" using ip unfolding is_path_def by simp
  show ?thesis
  proof (cases "b \<in> set p")
    case True
    then obtain i where i: "i < length p" and bi: "p ! i = b" by (auto simp: in_set_conv_nth)
    have t: "take (Suc i) p = take i p @ [p ! i]" using i by (simp add: take_Suc_conv_app_nth)
    have "take (Suc i) p \<in> pt_V V E u"
      unfolding pt_V_def using is_path_take[OF ip, of "Suc i"] hp pne sp
      by (auto simp: hd_take dest: in_set_takeD)
    moreover have "last (take (Suc i) p) = b" using t bi by simp
    ultimately show ?thesis unfolding comp_def by (metis image_eqI)
  next
    case False
    have "{last p, b} \<in> E" using assms(3) a by simp
    then have "is_path E (p @ [b])" using is_path_snoc[OF ip False] by simp
    then have "p @ [b] \<in> pt_V V E u" using hp pne sp bV unfolding pt_V_def by auto
    moreover have "last (p @ [b]) = b" by simp
    ultimately show ?thesis unfolding comp_def by (metis image_eqI)
  qed
qed

lemma comp_sub: "graph V E \<Longrightarrow> u \<in> V \<Longrightarrow> u \<in> comp V E u \<and> comp V E u \<subseteq> V"
  by (simp add: comp_eq)

lemma graph_restr: "graph V E \<Longrightarrow> C \<subseteq> V \<Longrightarrow> graph C (restr C E)"
  unfolding graph_def restr_def by (auto elim: finite_subset)

lemma pt_comp:
  assumes "graph V E" and "u \<in> V"
  shows "pt_V (comp V E u) (restr (comp V E u) E) u = pt_V V E u"
    and "pt_E (comp V E u) (restr (comp V E u) E) u = pt_E V E u"
proof -
  have eq: "pt_V (comp V E u) (restr (comp V E u) E) u = pt_V V E u"
  proof
    show "pt_V (comp V E u) (restr (comp V E u) E) u \<subseteq> pt_V V E u"
    proof
      fix p assume p: "p \<in> pt_V (comp V E u) (restr (comp V E u) E) u"
      then have a: "is_path (restr (comp V E u) E) p" and b: "hd p = u" and c: "set p \<subseteq> comp V E u"
        unfolding pt_V_def by auto
      have r: "restr (comp V E u) E \<subseteq> E" unfolding restr_def by blast
      have cv: "comp V E u \<subseteq> V" using comp_sub[OF assms] by blast
      show "p \<in> pt_V V E u" unfolding pt_V_def using is_path_mono[OF a r] b c cv by blast
    qed
  next
    show "pt_V V E u \<subseteq> pt_V (comp V E u) (restr (comp V E u) E) u"
    proof
      fix p assume p: "p \<in> pt_V V E u"
      then have ip: "is_path E p" and hp: "hd p = u" and sp: "set p \<subseteq> V" unfolding pt_V_def by auto
      have sc: "set p \<subseteq> comp V E u"
      proof
        fix x assume x: "x \<in> set p"
        have "(adjr E)\<^sup>*\<^sup>* u x" using path_reach[OF ip] hp x by blast
        moreover have "x \<in> V" using x sp by blast
        ultimately show "x \<in> comp V E u" by (simp add: comp_eq[OF assms])
      qed
      have "is_path (restr (comp V E u) E) p"
        unfolding is_path_def
      proof (intro conjI allI impI)
        show "p \<noteq> []" using ip unfolding is_path_def by blast
        show "distinct p" using ip unfolding is_path_def by blast
        fix i assume i: "Suc i < length p"
        have "{p ! i, p ! Suc i} \<in> E" using ip i unfolding is_path_def by blast
        moreover have "{p ! i, p ! Suc i} \<subseteq> comp V E u" using sc i by auto
        ultimately show "{p ! i, p ! Suc i} \<in> restr (comp V E u) E" unfolding restr_def by blast
      qed
      then show "p \<in> pt_V (comp V E u) (restr (comp V E u) E) u" using hp sc unfolding pt_V_def by blast
    qed
  qed
  show "pt_V (comp V E u) (restr (comp V E u) E) u = pt_V V E u" by (rule eq)
  show "pt_E (comp V E u) (restr (comp V E u) E) u = pt_E V E u" using eq unfolding pt_E_def by simp
qed

text \<open>No edge leaves a component, so the matching polynomial splits.\<close>

lemma mu_comp_split:
  assumes "graph V E" and "u \<in> V"
  shows "mu V E = mu (comp V E u) (restr (comp V E u) E) * mu (V - comp V E u) (restr (V - comp V E u) E)"
proof -
  let ?C = "comp V E u"
  have CV: "?C \<subseteq> V" using comp_sub[OF assms] by blast
  have g1: "graph ?C (restr ?C E)" by (rule graph_restr[OF assms(1) CV])
  have g2: "graph (V - ?C) (restr (V - ?C) E)" by (rule graph_restr[OF assms(1)]) blast
  have dj: "?C \<inter> (V - ?C) = {}" by blast
  have VU: "?C \<union> (V - ?C) = V" using CV by blast
  have EU: "restr ?C E \<union> restr (V - ?C) E = E"
  proof (rule set_eqI)
    fix e
    show "e \<in> restr ?C E \<union> restr (V - ?C) E \<longleftrightarrow> e \<in> E"
    proof
      assume "e \<in> restr ?C E \<union> restr (V - ?C) E"
      then show "e \<in> E" unfolding restr_def by blast
    next
      assume eE: "e \<in> E"
      then have c2: "card e = 2" and eV: "e \<subseteq> V" using assms(1) unfolding graph_def by blast+
      from c2 obtain a b where ab: "e = {a, b}" by (auto simp: card_2_iff)
      show "e \<in> restr ?C E \<union> restr (V - ?C) E"
      proof (cases "a \<in> ?C \<or> b \<in> ?C")
        case True
        have "{a, b} \<in> E" "{b, a} \<in> E" using eE ab by (auto simp: insert_commute)
        then have "a \<in> ?C \<and> b \<in> ?C"
          using True comp_edge_closed[OF assms] by blast
        then show ?thesis using eE ab unfolding restr_def by auto
      next
        case False
        then show ?thesis using eE ab eV unfolding restr_def by auto
      qed
    qed
  qed
  have "mu (?C \<union> (V - ?C)) (restr ?C E \<union> restr (V - ?C) E) = mu ?C (restr ?C E) * mu (V - ?C) (restr (V - ?C) E)"
    by (rule mu_disjoint_union[OF g1 g2 dj])
  then show ?thesis using VU EU by simp
qed

text \<open>Removing \<open>u\<close> from its component leaves the union of the components, in \<open>G - u\<close>, of its neighbours.\<close>

lemma comp_minus_root:
  assumes "graph V E" and "u \<in> V"
  shows "comp V E u - {u} = (\<Union>v\<in>nbrs E u. comp (V - {u}) (del1 E u) v)"
proof (rule set_eqI)
  fix w
  show "w \<in> comp V E u - {u} \<longleftrightarrow> w \<in> (\<Union>v\<in>nbrs E u. comp (V - {u}) (del1 E u) v)"
  proof
    assume W: "w \<in> comp V E u - {u}"
    then obtain p where p: "p \<in> pt_V V E u" and w: "w = last p" and wu: "w \<noteq> u"
      unfolding comp_def by blast
    have "p \<noteq> [u]" using w wu by auto
    then have "p \<in> pt_V V E u - {[u]}" using p by simp
    then obtain v q where v: "v \<in> nbrs E u" and q: "q \<in> pt_V (V - {u}) (del1 E u) v" and pq: "p = u # q"
      unfolding pt_V_minus_root[OF assms] by auto
    have qne: "q \<noteq> []" using q unfolding pt_V_def is_path_def by simp
    have "last q = w" using w pq qne by simp
    then show "w \<in> (\<Union>v\<in>nbrs E u. comp (V - {u}) (del1 E u) v)"
      using v q unfolding comp_def by blast
  next
    assume "w \<in> (\<Union>v\<in>nbrs E u. comp (V - {u}) (del1 E u) v)"
    then obtain v q where v: "v \<in> nbrs E u" and q: "q \<in> pt_V (V - {u}) (del1 E u) v" and w: "w = last q"
      unfolding comp_def by blast
    have qne: "q \<noteq> []" using q unfolding pt_V_def is_path_def by simp
    have sq: "set q \<subseteq> V - {u}" using q unfolding pt_V_def by simp
    have "u # q \<in> pt_V V E u - {[u]}"
      unfolding pt_V_minus_root[OF assms] using v q by blast
    then have "u # q \<in> pt_V V E u" by simp
    moreover have "last (u # q) = w" using w qne by simp
    ultimately have "w \<in> comp V E u" unfolding comp_def by (metis image_eqI)
    moreover have "w \<noteq> u" using w qne sq last_in_set by blast
    ultimately show "w \<in> comp V E u - {u}" by simp
  qed
qed


lemma comp_eq_or_disjoint:
  assumes "graph V E" and "v \<in> V" and "w \<in> V"
  shows "comp V E v = comp V E w \<or> comp V E v \<inter> comp V E w = {}"
proof (cases "comp V E v \<inter> comp V E w = {}")
  case True
  then show ?thesis by blast
next
  case False
  then obtain x where xv: "(adjr E)\<^sup>*\<^sup>* v x" and xw: "(adjr E)\<^sup>*\<^sup>* w x"
    using assms by (auto simp: comp_eq)
  have vw: "(adjr E)\<^sup>*\<^sup>* v w" using xv reach_symm[OF xw] by (rule rtranclp_trans)
  have wv: "(adjr E)\<^sup>*\<^sup>* w v" by (rule reach_symm[OF vw])
  have "comp V E v = comp V E w"
    unfolding comp_eq[OF assms(1,2)] comp_eq[OF assms(1,3)]
    using vw wv by (auto intro: rtranclp_trans)
  then show ?thesis ..
qed

lemma coeff_sign_mult: "coeff ((-1) ^ k * (p :: real poly)) n = (-1) ^ k * coeff p n"
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have "(-1) ^ Suc k * p = - ((-1) ^ k * p)" by simp
  then show ?case using Suc by simp
qed

lemma mu_ne_0:
  assumes G: "graph V E"
  shows "mu V E \<noteq> 0"
proof -
  have c: "\<forall>M\<in>matchings E. coeff ((-1) ^ card M * monom (1::real) (card V - 2 * card M)) (card V) = (if M = {} then 1 else 0)"
  proof
    fix M assume M: "M \<in> matchings E"
    have mm: "matching E M" using M unfolding matchings_def by simp
    have un: "\<Union>M \<subseteq> V" using mm G unfolding matching_def graph_def by blast
    have fV: "finite V" using G unfolding graph_def by blast
    have le: "2 * card M \<le> card V" using matching_card_le[OF G mm un fV] .
    show "coeff ((-1) ^ card M * monom (1::real) (card V - 2 * card M)) (card V) = (if M = {} then 1 else 0)"
    proof (cases "M = {}")
      case True
      then show ?thesis by (simp add: coeff_sign_mult)
    next
      case False
      then have "0 < card M" using matching_finite[OF G mm] by (simp add: card_gt_0_iff)
      then have n1: "card V - 2 * card M \<noteq> card V" using le by simp
      then have n2: "card V \<noteq> card V - 2 * card M" by (rule not_sym)
      show ?thesis
        by (subst coeff_sign_mult) (simp add: coeff_monom n1 n2 False)
    qed
  qed
  have "coeff (mu V E) (card V) = (\<Sum>M\<in>matchings E. if M = {} then (1::real) else 0)"
    unfolding mu_def coeff_sum by (rule sum.cong[OF refl]) (use c in blast)
  also have "\<dots> = 1"
    using sum.delta[OF finite_matchings[OF graph_finite_E[OF G]], of "{}" "\<lambda>_. (1::real)"]
    by (simp add: matchings_def matching_def)
  finally have "coeff (mu V E) (card V) = 1" .
  then show ?thesis by auto
qed

section \<open>Divisibility\<close>

text \<open>Auxiliary facts about components.\<close>

lemma comp_edge_end:
  assumes "graph W F" and "{a, b} \<in> F"
  shows "b \<in> comp W F a"
proof -
  have ab: "a \<noteq> b" using assms(2) assms(1) unfolding graph_def by (auto simp: card_2_iff)
  have aW: "a \<in> W" and bW: "b \<in> W" using assms unfolding graph_def by auto
  have "[a, b] \<in> pt_V W F a"
    unfolding pt_V_def is_path_def using assms(2) ab aW bW
    by (auto simp: nth_Cons' less_Suc_eq_0_disj)
  then have "last [a, b] \<in> comp W F a" unfolding comp_def by blast
  then show ?thesis by simp
qed

lemma comp_edge:
  assumes G: "graph W F" and e: "e \<in> F" and a: "a \<in> e" and v: "v \<in> W" and av: "a \<in> comp W F v"
  shows "e \<subseteq> comp W F v"
proof -
  have c2: "card e = 2" using e G unfolding graph_def by blast
  obtain x y where xy: "e = {x, y}"
    using c2 by (auto simp: card_2_iff)
  then obtain b where eab: "e = {a, b}"
  proof (cases "a = x")
    case True
    with xy that show ?thesis by blast
  next
    case False
    with a xy have "a = y" by blast
    with xy that[of x] show ?thesis by (simp add: insert_commute)
  qed
  have aW: "a \<in> W" using e a G unfolding graph_def by auto
  have b: "b \<in> comp W F a" using comp_edge_end[OF G] e eab by simp
  have aa: "a \<in> comp W F a" using comp_sub[OF G aW] by simp
  have "comp W F a = comp W F v"
    using comp_eq_or_disjoint[OF G aW v] aa av by blast
  with b av eab show ?thesis by auto
qed

lemma restr_union_comp:
  assumes G: "graph W F" and R: "R \<subseteq> W"
  shows "restr (\<Union>v\<in>R. comp W F v) F = (\<Union>v\<in>R. restr (comp W F v) F)"
proof
  show "restr (\<Union>v\<in>R. comp W F v) F \<subseteq> (\<Union>v\<in>R. restr (comp W F v) F)"
  proof
    fix e assume "e \<in> restr (\<Union>v\<in>R. comp W F v) F"
    then have eF: "e \<in> F" and es: "e \<subseteq> (\<Union>v\<in>R. comp W F v)" by (simp_all add: restr_def)
    have "e \<noteq> {}" using eF G unfolding graph_def by auto
    then obtain a where a: "a \<in> e" by blast
    with es obtain v where vR: "v \<in> R" and av: "a \<in> comp W F v" by blast
    have "e \<subseteq> comp W F v" by (rule comp_edge[OF G eF a _ av]) (use vR R in blast)
    then show "e \<in> (\<Union>v\<in>R. restr (comp W F v) F)" using vR eF by (auto simp: restr_def)
  qed
next
  show "(\<Union>v\<in>R. restr (comp W F v) F) \<subseteq> restr (\<Union>v\<in>R. comp W F v) F"
    by (auto simp: restr_def)
qed

lemma comp_family:
  assumes G: "graph W F" and fS: "finite S" and SW: "S \<subseteq> W"
  shows "\<exists>R\<subseteq>S. (\<forall>i\<in>R. \<forall>j\<in>R. i \<noteq> j \<longrightarrow> comp W F i \<inter> comp W F j = {})
            \<and> (\<Union>v\<in>R. comp W F v) = (\<Union>v\<in>S. comp W F v)"
  using fS SW
proof (induct S rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert s S)
  then have sW: "s \<in> W" and SW': "S \<subseteq> W" by auto
  obtain R where RS: "R \<subseteq> S" and dj: "\<forall>i\<in>R. \<forall>j\<in>R. i \<noteq> j \<longrightarrow> comp W F i \<inter> comp W F j = {}"
    and un: "(\<Union>v\<in>R. comp W F v) = (\<Union>v\<in>S. comp W F v)" using insert.hyps(3)[OF SW'] by blast
  show ?case
  proof (cases "comp W F s \<subseteq> (\<Union>v\<in>S. comp W F v)")
    case True
    show ?thesis
    proof (rule exI[of _ R], intro conjI)
      show "R \<subseteq> insert s S" using RS by blast
      show "\<forall>i\<in>R. \<forall>j\<in>R. i \<noteq> j \<longrightarrow> comp W F i \<inter> comp W F j = {}" by fact
      show "(\<Union>v\<in>R. comp W F v) = (\<Union>v\<in>insert s S. comp W F v)" using un True by auto
    qed
  next
    case False
    have disj: "\<forall>w\<in>S. comp W F s \<inter> comp W F w = {}"
    proof
      fix w assume w: "w \<in> S"
      then have wW: "w \<in> W" using SW' by blast
      show "comp W F s \<inter> comp W F w = {}"
      proof (rule ccontr)
        assume "comp W F s \<inter> comp W F w \<noteq> {}"
        then have "comp W F s = comp W F w" using comp_eq_or_disjoint[OF G sW wW] by blast
        then have "comp W F s \<subseteq> (\<Union>v\<in>S. comp W F v)" using w by blast
        with False show False by blast
      qed
    qed
    show ?thesis
    proof (rule exI[of _ "insert s R"], intro conjI)
      show "insert s R \<subseteq> insert s S" using RS by blast
      show "\<forall>i\<in>insert s R. \<forall>j\<in>insert s R. i \<noteq> j \<longrightarrow> comp W F i \<inter> comp W F j = {}"
      proof (intro ballI impI)
        fix i j assume i: "i \<in> insert s R" and j: "j \<in> insert s R" and ij: "i \<noteq> j"
        show "comp W F i \<inter> comp W F j = {}"
        proof (cases "i = s")
          case True
          with j ij have "j \<in> R" by blast
          then show ?thesis using True disj RS by blast
        next
          case False
          show ?thesis
          proof (cases "j = s")
            case True
            with i ij have "i \<in> R" by blast
            then show ?thesis using True disj RS by blast
          next
            case False2: False
            from i False have "i \<in> R" by blast
            moreover from j False2 have "j \<in> R" by blast
            ultimately show ?thesis using dj ij by blast
          qed
        qed
      qed
      show "(\<Union>v\<in>insert s R. comp W F v) = (\<Union>v\<in>insert s S. comp W F v)" using un by auto
    qed
  qed
qed

theorem godsil_dvd_comp:
  assumes "graph V E" and "u \<in> V"
  shows "mu (comp V E u) (restr (comp V E u) E) dvd mu (pt_V V E u) (pt_E V E u)"
  using assms
proof (induction "card V" arbitrary: V E u rule: less_induct)
  case less
  note G = less.prems(1) and u = less.prems(2)
  define C where "C = comp V E u"
  define W where "W = V - {u}"
  define F where "F = del1 E u"
  define N where "N = nbrs E u"
  have gC: "graph C (restr C E)"
    using graph_restr[OF G] comp_sub[OF G u] unfolding C_def by blast
  have uC: "u \<in> C" using comp_sub[OF G u] unfolding C_def by blast
  have gW: "graph W F" unfolding W_def F_def by (rule graph_del1[OF G])
  have fV: "finite V" using G unfolding graph_def by blast
  have cardW: "card W < card V" unfolding W_def by (rule card_Diff1_less[OF fV u])
  have NW: "N \<subseteq> W"
  proof
    fix v assume v: "v \<in> N"
    then have e: "{u, v} \<in> E" unfolding N_def nbrs_def by (simp add: insert_commute)
    have "card {u, v} = 2" "{u, v} \<subseteq> V" using e G unfolding graph_def by blast+
    then show "v \<in> W" unfolding W_def by (auto simp: card_2_iff)
  qed
  have fN: "finite N" using finite_subset[OF NW] gW unfolding graph_def by blast
  have hV: "pt_V C (restr C E) u = pt_V V E u" and hE: "pt_E C (restr C E) u = pt_E V E u"
    using pt_comp[OF G u] unfolding C_def by simp_all
  have ratio: "mu (C - {u}) (del1 (restr C E) u) * mu (pt_V V E u) (pt_E V E u)
      = mu C (restr C E) * mu (pt_V V E u - {[u]}) (del1 (pt_E V E u) [u])"
    using godsil_ratio[OF gC uC] unfolding hV hE .
  have root: "mu (pt_V V E u - {[u]}) (del1 (pt_E V E u) [u])
      = (\<Prod>v\<in>N. mu (pt_V W F v) (pt_E W F v))"
    using mu_root_rest[OF G u] unfolding N_def W_def F_def .
  obtain R where RN: "R \<subseteq> N"
    and dj: "\<forall>i\<in>R. \<forall>j\<in>R. i \<noteq> j \<longrightarrow> comp W F i \<inter> comp W F j = {}"
    and un: "(\<Union>v\<in>R. comp W F v) = (\<Union>v\<in>N. comp W F v)"
    using comp_family[OF gW fN NW] by blast
  have RW: "R \<subseteq> W" using RN NW by blast
  have CU: "C - {u} = (\<Union>v\<in>R. comp W F v)"
    using comp_minus_root[OF G u] un unfolding C_def W_def F_def N_def by simp
  have edges: "del1 (restr C E) u = (\<Union>v\<in>R. restr (comp W F v) F)"
  proof -
    have "del1 (restr C E) u = restr (C - {u}) F"
      unfolding del1_def restr_def F_def by auto
    also have "\<dots> = restr (\<Union>v\<in>R. comp W F v) F" using CU by simp
    also have "\<dots> = (\<Union>v\<in>R. restr (comp W F v) F)" by (rule restr_union_comp[OF gW RW])
    finally show ?thesis .
  qed
  have fR: "finite R" using finite_subset[OF RN fN] .
  have gD: "\<forall>v\<in>R. graph (comp W F v) (restr (comp W F v) F)"
    using graph_restr[OF gW] comp_sub[OF gW] RW by blast
  have P: "mu (C - {u}) (del1 (restr C E) u) = (\<Prod>v\<in>R. mu (comp W F v) (restr (comp W F v) F))"
    unfolding CU edges by (rule mu_UNION[OF fR gD]) (use dj in blast)
  have "(\<Prod>v\<in>R. mu (comp W F v) (restr (comp W F v) F)) dvd (\<Prod>v\<in>R. mu (pt_V W F v) (pt_E W F v))"
  proof (rule prod_dvd_prod)
    fix v assume "v \<in> R"
    then have "v \<in> W" using RW by blast
    from less.hyps[OF cardW gW this] show
      "mu (comp W F v) (restr (comp W F v) F) dvd mu (pt_V W F v) (pt_E W F v)" .
  qed
  moreover have "(\<Prod>v\<in>R. mu (pt_V W F v) (pt_E W F v)) dvd (\<Prod>v\<in>N. mu (pt_V W F v) (pt_E W F v))"
    by (rule prod_dvd_prod_subset[OF fN RN])
  ultimately have "mu (C - {u}) (del1 (restr C E) u) dvd (\<Prod>v\<in>N. mu (pt_V W F v) (pt_E W F v))"
    unfolding P by (rule dvd_trans)
  then obtain q where q: "(\<Prod>v\<in>N. mu (pt_V W F v) (pt_E W F v)) = mu (C - {u}) (del1 (restr C E) u) * q"
    by (auto simp: dvd_def)
  have ne: "mu (C - {u}) (del1 (restr C E) u) \<noteq> 0"
  proof -
    have "graph (C - {u}) (del1 (restr C E) u)" by (rule graph_del1[OF gC])
    then show ?thesis by (rule mu_ne_0)
  qed
  have "mu (C - {u}) (del1 (restr C E) u) * mu (pt_V V E u) (pt_E V E u)
      = mu (C - {u}) (del1 (restr C E) u) * (mu C (restr C E) * q)"
    using ratio root q by (simp add: mult.assoc mult.left_commute)
  then have "mu (pt_V V E u) (pt_E V E u) = mu C (restr C E) * q"
    using ne by simp
  then show ?case unfolding C_def by simp
qed

corollary godsil_dvd:
  assumes "graph V E" and "u \<in> V" and "comp V E u = V"
  shows "mu V E dvd mu (pt_V V E u) (pt_E V E u)"
proof -
  have "restr V E = E" using assms(1) unfolding restr_def graph_def by auto
  then show ?thesis using godsil_dvd_comp[OF assms(1,2)] assms(3) by simp
qed

end
