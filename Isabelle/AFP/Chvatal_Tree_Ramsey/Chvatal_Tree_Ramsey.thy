theory Chvatal_Tree_Ramsey
  imports Main "HOL-Library.FuncSet"
begin

section \<open>Chv\'atal's theorem: the Ramsey number of a triangle versus a tree\<close>

text \<open>Graphs on the vertex set $\{0,\dots,n-1\}$ are adjacency relations. This mirrors the statement
  the variant \<open>chvatal\<close> of Erdős problem 1182 in the formal-conjectures repository of
  google-deepmind (file ErdosProblems/1182.lean):
  for a tree $T$ on $n$ vertices, $R(K_3,T) = 2n-1$, where $R(G,H)$ is the least $N$ such that every
  graph on $N$ vertices contains $G$ or its complement contains $H$ (\<open>graphRamsey\<close>), and containment
  is an injective homomorphism (Mathlib's \<open>IsContained\<close>). A tree is a connected graph with $n-1$
  edges; Mathlib's \<open>SimpleGraph.isTree_iff_connected_and_card\<close> shows this agrees with
  connected and acyclic.\<close>

definition simple :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "simple n G \<longleftrightarrow> (\<forall>i<n. \<forall>j<n. G i j \<longleftrightarrow> G j i) \<and> (\<forall>i<n. \<not> G i i)"

definition compl :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "compl C i j \<longleftrightarrow> i \<noteq> j \<and> \<not> C i j"

text \<open>$G$ on $\{0..<n\}$ is contained in $C$ on $\{0..<N\}$.\<close>
definition contains :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "contains n G N C \<longleftrightarrow> (\<exists>f. inj_on f {..<n} \<and> f ` {..<n} \<subseteq> {..<N} \<and>
      (\<forall>i<n. \<forall>j<n. G i j \<longrightarrow> C (f i) (f j)))"

definition triangle :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "triangle i j \<longleftrightarrow> i < 3 \<and> j < 3 \<and> i \<noteq> j"

definition edges :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat set set" where
  "edges n G = {{i, j} | i j. i < n \<and> j < n \<and> G i j}"

definition connected :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "connected n G \<longleftrightarrow> 0 < n \<and>
     (\<forall>i<n. \<forall>j<n. (\<lambda>a b. a < n \<and> b < n \<and> G a b)\<^sup>*\<^sup>* i j)"

definition is_tree :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_tree n T \<longleftrightarrow> simple n T \<and> connected n T \<and> card (edges n T) + 1 = n"

text \<open>The Ramsey number $R(K_3, T)$, as \<open>graphRamsey (\<top> : SimpleGraph (Fin 3)) T\<close>.\<close>
definition ramsey_triangle :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "ramsey_triangle n T = Inf {N. \<forall>C. simple N C \<longrightarrow> contains 3 triangle N C \<or> contains n T N (compl C)}"

section \<open>Trees on an arbitrary finite vertex set\<close>

definition Eset :: "nat set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat set set" where
  "Eset S G = {{i, j} | i j. i \<in> S \<and> j \<in> S \<and> G i j}"

definition RS :: "nat set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "RS S G a b \<longleftrightarrow> a \<in> S \<and> b \<in> S \<and> G a b"

definition tree_on :: "nat set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "tree_on S T \<longleftrightarrow> finite S \<and> S \<noteq> {} \<and> (\<forall>i\<in>S. \<forall>j\<in>S. T i j = T j i) \<and> (\<forall>i\<in>S. \<not> T i i)
     \<and> (\<forall>i\<in>S. \<forall>j\<in>S. (RS S T)\<^sup>*\<^sup>* i j) \<and> card (Eset S T) + 1 = card S"

lemma finite_Eset: "finite S \<Longrightarrow> finite (Eset S G)"
  by (rule finite_subset[where B = "Pow S"]) (fastforce simp: Eset_def)+

lemma card_pos_tree: "tree_on S T \<Longrightarrow> 1 \<le> card S"
  unfolding tree_on_def by (auto simp: Suc_le_eq card_gt_0_iff)

text \<open>Degree sum: the number of ordered adjacent pairs is at most twice the number of edges.\<close>
lemma pairs_le_twice_edges:
  assumes fin: "finite S" and irr: "\<forall>i\<in>S. \<not> T i i"
  shows "card (Sigma S (\<lambda>v. {w \<in> S. T v w})) \<le> 2 * card (Eset S T)"
proof -
  let ?g = "\<lambda>p::nat \<times> nat. ({fst p, snd p}, fst p < snd p)"
  have "card (Sigma S (\<lambda>v. {w \<in> S. T v w})) \<le> card (Eset S T \<times> (UNIV :: bool set))"
  proof (rule card_inj_on_le)
    show "inj_on ?g (Sigma S (\<lambda>v. {w \<in> S. T v w}))"
    proof (rule inj_onI)
      fix p q assume "p \<in> Sigma S (\<lambda>v. {w \<in> S. T v w})" "q \<in> Sigma S (\<lambda>v. {w \<in> S. T v w})"
        and "?g p = ?g q"
      then obtain v w v' w' where pq: "p = (v, w)" "q = (v', w')" and "v \<in> S" "w \<in> S" "T v w"
        "v' \<in> S" "w' \<in> S" "T v' w'" by (cases p; cases q) auto
      with irr have ne: "v \<noteq> w" "v' \<noteq> w'" by auto
      from \<open>?g p = ?g q\<close> pq have e: "{v, w} = {v', w'}" and b: "(v < w) = (v' < w')" by auto
      from e have "(v = v' \<and> w = w') \<or> (v = w' \<and> w = v')" by (simp add: doubleton_eq_iff)
      then show "p = q"
      proof
        assume "v = v' \<and> w = w'" then show ?thesis using pq by simp
      next
        assume "v = w' \<and> w = v'"
        with b ne have False by auto
        then show ?thesis ..
      qed
    qed
    show "?g ` Sigma S (\<lambda>v. {w \<in> S. T v w}) \<subseteq> Eset S T \<times> (UNIV :: bool set)"
    proof
      fix y assume "y \<in> ?g ` Sigma S (\<lambda>v. {w \<in> S. T v w})"
      then obtain v w where "v \<in> S" "w \<in> S" "T v w" "y = ({v, w}, v < w)" by auto
      then show "y \<in> Eset S T \<times> (UNIV :: bool set)" unfolding Eset_def by blast
    qed
    show "finite (Eset S T \<times> (UNIV :: bool set))" using finite_Eset[OF fin] by simp
  qed
  also have "\<dots> = 2 * card (Eset S T)" by (simp add: card_cartesian_product)
  finally show ?thesis .
qed

lemma has_neighbour:
  assumes tr: "tree_on S T" and c2: "2 \<le> card S" and v: "v \<in> S"
  shows "\<exists>u\<in>S. T v u"
proof -
  have "\<not> S \<subseteq> {v}"
  proof
    assume sub: "S \<subseteq> {v}"
    have "card S \<le> card {v}" using card_mono[of "{v}" S] sub by simp
    with c2 show False by simp
  qed
  then obtain j where j: "j \<in> S" "j \<noteq> v" by auto
  from tr j v have "(RS S T)\<^sup>*\<^sup>* v j" unfolding tree_on_def by auto
  then show ?thesis
  proof (cases rule: converse_rtranclpE)
    case base then show ?thesis using j by simp
  next
    case (step y)
    then show ?thesis unfolding RS_def by auto
  qed
qed

lemma tree_has_leaf:
  assumes tr: "tree_on S T" and c2: "2 \<le> card S"
  shows "\<exists>v\<in>S. \<exists>u\<in>S. T v u \<and> (\<forall>w\<in>S. T v w \<longrightarrow> w = u)"
proof (rule ccontr)
  assume H: "\<not> ?thesis"
  have fin: "finite S" and irr: "\<forall>i\<in>S. \<not> T i i" and cE: "card (Eset S T) + 1 = card S"
    using tr unfolding tree_on_def by auto
  have deg2: "\<forall>v\<in>S. 2 \<le> card {w \<in> S. T v w}"
  proof
    fix v assume v: "v \<in> S"
    from has_neighbour[OF tr c2 v] obtain u where u: "u \<in> S" "T v u" by auto
    from H v u obtain w where w: "w \<in> S" "T v w" "w \<noteq> u" by blast
    have "card {u, w} \<le> card {w \<in> S. T v w}"
      by (rule card_mono) (use fin u w in auto)
    moreover have "card {u, w} = 2" using w by simp
    ultimately show "2 \<le> card {w \<in> S. T v w}" by simp
  qed
  have "card S * 2 = (\<Sum>v\<in>S. 2)" by simp
  also have "\<dots> \<le> (\<Sum>v\<in>S. card {w \<in> S. T v w})" by (rule sum_mono) (use deg2 in auto)
  also have "\<dots> = card (Sigma S (\<lambda>v. {w \<in> S. T v w}))"
    by (rule card_SigmaI[symmetric]) (use fin in auto)
  also have "\<dots> \<le> 2 * card (Eset S T)" using pairs_le_twice_edges[where S = S and T = T] fin irr by blast
  finally show False using cE c2 by simp
qed

lemma tree_remove_leaf:
  assumes tr: "tree_on S T" and c2: "2 \<le> card S" and vS: "v \<in> S" and uS: "u \<in> S" and vu: "T v u"
    and leaf: "\<forall>w\<in>S. T v w \<longrightarrow> w = u"
  shows "tree_on (S - {v}) T"
proof -
  have fin: "finite S" and sym: "\<forall>i\<in>S. \<forall>j\<in>S. T i j = T j i" and irr: "\<forall>i\<in>S. \<not> T i i"
    and con: "\<forall>i\<in>S. \<forall>j\<in>S. (RS S T)\<^sup>*\<^sup>* i j" and cE: "card (Eset S T) + 1 = card S"
    using tr unfolding tree_on_def by auto
  have uv: "u \<noteq> v" using irr vS vu by auto
  have cS': "card (S - {v}) = card S - 1" using vS fin by (simp add: card_Diff_singleton)
  have key: "\<And>i j. i \<in> S - {v} \<Longrightarrow> (RS S T)\<^sup>*\<^sup>* i j \<Longrightarrow>
      (j \<noteq> v \<longrightarrow> (RS (S - {v}) T)\<^sup>*\<^sup>* i j) \<and> (j = v \<longrightarrow> (RS (S - {v}) T)\<^sup>*\<^sup>* i u)"
  proof -
    fix i j assume i: "i \<in> S - {v}" and p: "(RS S T)\<^sup>*\<^sup>* i j"
    from p show "(j \<noteq> v \<longrightarrow> (RS (S - {v}) T)\<^sup>*\<^sup>* i j) \<and> (j = v \<longrightarrow> (RS (S - {v}) T)\<^sup>*\<^sup>* i u)"
    proof (induction rule: rtranclp_induct)
      case base then show ?case using i by auto
    next
      case (step b c)
      from step(2) have bS: "b \<in> S" and cS: "c \<in> S" and Tbc: "T b c" unfolding RS_def by auto
      show ?case
      proof (cases "b = v")
        case True
        with step(3) have R: "(RS (S - {v}) T)\<^sup>*\<^sup>* i u" by simp
        from True Tbc have "T v c" by simp
        with leaf cS have cu: "c = u" by simp
        with R uv show ?thesis by simp
      next
        case False
        with step(3) have R: "(RS (S - {v}) T)\<^sup>*\<^sup>* i b" by simp
        show ?thesis
        proof (cases "c = v")
          case True
          from Tbc True have "T b v" by simp
          with sym bS vS have "T v b" by blast
          with leaf bS have "b = u" by simp
          with R True show ?thesis by simp
        next
          case False2: False
          have "RS (S - {v}) T b c" using bS cS Tbc \<open>b \<noteq> v\<close> False2 unfolding RS_def by auto
          with R show ?thesis using False2 by (auto intro: rtranclp.rtrancl_into_rtrancl)
        qed
      qed
    qed
  qed
  have Eeq: "Eset S T = insert {v, u} (Eset (S - {v}) T)"
  proof (rule set_eqI)
    fix x
    show "x \<in> Eset S T \<longleftrightarrow> x \<in> insert {v, u} (Eset (S - {v}) T)"
    proof
      assume "x \<in> Eset S T"
      then obtain i j where x: "x = {i, j}" and ij: "i \<in> S" "j \<in> S" "T i j" unfolding Eset_def by auto
      show "x \<in> insert {v, u} (Eset (S - {v}) T)"
      proof (cases "i = v")
        case True
        with leaf ij have "j = u" by simp
        with True x show ?thesis by simp
      next
        case F1: False
        show ?thesis
        proof (cases "j = v")
          case True
          with ij sym vS have "T v i" by blast
          with leaf ij have "i = u" by simp
          with True x show ?thesis by (auto simp: insert_commute)
        next
          case F2: False
          have "x \<in> Eset (S - {v}) T" unfolding Eset_def using x ij F1 F2 by auto
          then show ?thesis by simp
        qed
      qed
    next
      assume "x \<in> insert {v, u} (Eset (S - {v}) T)"
      then show "x \<in> Eset S T"
      proof
        assume "x = {v, u}"
        then show ?thesis unfolding Eset_def using vS uS vu by auto
      next
        assume "x \<in> Eset (S - {v}) T"
        then show ?thesis unfolding Eset_def by auto
      qed
    qed
  qed
  have notin: "{v, u} \<notin> Eset (S - {v}) T"
  proof
    assume "{v, u} \<in> Eset (S - {v}) T"
    then obtain i j where "{v, u} = {i, j}" "i \<in> S - {v}" "j \<in> S - {v}" unfolding Eset_def by auto
    then show False by (auto simp: doubleton_eq_iff)
  qed
  have finE: "finite (Eset (S - {v}) T)" using finite_Eset[of "S - {v}"] fin by simp
  have "card (Eset S T) = Suc (card (Eset (S - {v}) T))" using Eeq notin finE by simp
  with cE cS' c2 have cE': "card (Eset (S - {v}) T) + 1 = card (S - {v})" by simp
  have "S - {v} \<noteq> {}"
  proof
    assume "S - {v} = {}"
    then have "card (S - {v}) = 0" by (simp only: card.empty)
    with cS' c2 show False by simp
  qed
  moreover have "\<forall>i\<in>S - {v}. \<forall>j\<in>S - {v}. (RS (S - {v}) T)\<^sup>*\<^sup>* i j"
  proof (intro ballI)
    fix i j assume i: "i \<in> S - {v}" and j: "j \<in> S - {v}"
    from con i j have "(RS S T)\<^sup>*\<^sup>* i j" by auto
    from key[OF i this] j show "(RS (S - {v}) T)\<^sup>*\<^sup>* i j" by auto
  qed
  ultimately show ?thesis using fin sym irr cE' unfolding tree_on_def by auto
qed

section \<open>The upper bound\<close>

lemma upper:
  fixes N :: nat and C :: "nat \<Rightarrow> nat \<Rightarrow> bool" and T :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes csym: "\<forall>i<N. \<forall>j<N. C i j = C j i"
    and notri: "\<forall>a<N. \<forall>b<N. \<forall>c<N. \<not> (C a b \<and> C b c \<and> C a c)"
  shows "\<forall>S. tree_on S T \<longrightarrow> card S = n \<longrightarrow> 2 * n - 1 \<le> N \<longrightarrow>
    (\<exists>f. inj_on f S \<and> f ` S \<subseteq> {..<N} \<and> (\<forall>i\<in>S. \<forall>j\<in>S. T i j \<longrightarrow> compl C (f i) (f j)))"
proof (induction n)
  case 0
  show ?case
  proof (intro allI impI)
    fix S assume "tree_on S T" "card S = 0"
    with card_pos_tree[of S T] show "\<exists>f. inj_on f S \<and> f ` S \<subseteq> {..<N} \<and>
      (\<forall>i\<in>S. \<forall>j\<in>S. T i j \<longrightarrow> compl C (f i) (f j))" by simp
  qed
next
  case (Suc n)
  show ?case
  proof (intro allI impI)
    fix S assume tr: "tree_on S T" and cn: "card S = Suc n" and Nb: "2 * Suc n - 1 \<le> N"
    have fin: "finite S" and sym: "\<forall>i\<in>S. \<forall>j\<in>S. T i j = T j i" and irr: "\<forall>i\<in>S. \<not> T i i"
      using tr unfolding tree_on_def by auto
    show "\<exists>f. inj_on f S \<and> f ` S \<subseteq> {..<N} \<and> (\<forall>i\<in>S. \<forall>j\<in>S. T i j \<longrightarrow> compl C (f i) (f j))"
    proof (cases "n = 0")
      case True
      with cn obtain s where S: "S = {s}" by (auto simp: card_1_singleton_iff)
      with irr have "\<not> T s s" by simp
      with S Nb True show ?thesis by (intro exI[where x = "\<lambda>_. 0"]) auto
    next
      case False
      with cn have c2: "2 \<le> card S" by simp
      from tree_has_leaf[OF tr c2] obtain v u where vS: "v \<in> S" and uS: "u \<in> S" and vu: "T v u"
        and leaf: "\<forall>w\<in>S. T v w \<longrightarrow> w = u" by blast
      have uv: "u \<noteq> v" using irr vS vu by auto
      let ?S' = "S - {v}"
      have tr': "tree_on ?S' T" by (rule tree_remove_leaf[OF tr c2 vS uS vu leaf])
      have cS': "card ?S' = n" using cn vS fin by (simp add: card_Diff_singleton)
      from Suc.IH tr' cS' Nb obtain f' where f1: "inj_on f' ?S'" and f2: "f' ` ?S' \<subseteq> {..<N}"
        and f3: "\<forall>i\<in>?S'. \<forall>j\<in>?S'. T i j \<longrightarrow> compl C (f' i) (f' j)" by fastforce
      have uS': "u \<in> ?S'" using uS uv by auto
      let ?R = "{..<N} - f' ` ?S'"
      have cR: "card ?R = N - n"
      proof -
        have h1: "card ?R = card {..<N} - card (f' ` ?S')"
          by (rule card_Diff_subset) (use f2 fin in \<open>auto intro: finite_imageI\<close>)
        have h2: "card (f' ` ?S') = n" using card_image[OF f1] cS' by simp
        show ?thesis using h1 h2 by simp
      qed
      have cRge: "Suc n \<le> card ?R" using cR Nb by simp
      show ?thesis
      proof (cases "\<exists>w\<in>?R. compl C (f' u) w")
        case True
        then obtain w where wR: "w \<in> ?R" and cw: "compl C (f' u) w" by auto
        let ?f = "\<lambda>x. if x = v then w else f' x"
        have wN: "w < N" and wnot: "w \<notin> f' ` ?S'" using wR by auto
        have fuN: "f' u < N" using f2 uS' by auto
        have cw': "compl C w (f' u)"
          using cw csym wN fuN unfolding compl_def by auto
        have inj: "inj_on ?f S"
        proof (rule inj_onI)
          fix x y assume xS: "x \<in> S" and yS: "y \<in> S" and e: "?f x = ?f y"
          show "x = y"
          proof (cases "x = v")
            case True
            show ?thesis
            proof (cases "y = v")
              case True with \<open>x = v\<close> show ?thesis by simp
            next
              case False
              with yS e True wnot show ?thesis by auto
            qed
          next
            case xv: False
            show ?thesis
            proof (cases "y = v")
              case True with xS e xv wnot show ?thesis by auto
            next
              case False
              with xv xS yS e f1 show ?thesis by (auto intro: inj_onD)
            qed
          qed
        qed
        have img: "?f ` S \<subseteq> {..<N}" using f2 wN by auto
        have ed: "\<forall>i\<in>S. \<forall>j\<in>S. T i j \<longrightarrow> compl C (?f i) (?f j)"
        proof (intro ballI impI)
          fix i j assume iS: "i \<in> S" and jS: "j \<in> S" and Tij: "T i j"
          show "compl C (?f i) (?f j)"
          proof (cases "i = v")
            case True
            with leaf jS Tij have "j = u" by simp
            with True cw' uv show ?thesis by simp
          next
            case iv: False
            show ?thesis
            proof (cases "j = v")
              case True
              from Tij True have "T i v" by simp
              with sym iS vS have "T v i" by blast
              with leaf iS have "i = u" by simp
              with True cw iv show ?thesis by simp
            next
              case jv: False
              with iv iS jS f3 Tij show ?thesis by auto
            qed
          qed
        qed
        from inj img ed show ?thesis by blast
      next
        case False
        then have allC: "\<forall>w\<in>?R. \<not> compl C (f' u) w" by simp
        have fuN: "f' u < N" using f2 uS' by auto
        have cfu: "\<forall>w\<in>?R. C (f' u) w"
        proof
          fix w assume wR: "w \<in> ?R"
          then have "w \<noteq> f' u" using uS' by auto
          have "\<not> compl C (f' u) w" using allC wR by blast
          with \<open>w \<noteq> f' u\<close> show "C (f' u) w" unfolding compl_def by auto
        qed
        have clique: "\<forall>w\<in>?R. \<forall>w'\<in>?R. w \<noteq> w' \<longrightarrow> compl C w w'"
        proof (intro ballI impI)
          fix w w' assume wR: "w \<in> ?R" and w'R: "w' \<in> ?R" and ne: "w \<noteq> w'"
          have wN: "w < N" and w'N: "w' < N" using wR w'R by auto
          show "compl C w w'"
          proof (rule ccontr)
            assume "\<not> compl C w w'"
            with ne have "C w w'" unfolding compl_def by simp
            with cfu wR w'R notri fuN wN w'N show False by blast
          qed
        qed
        have fR: "finite ?R" by simp
        from cn cRge have "card S \<le> card ?R" by simp
        from card_le_inj[OF fin fR this] obtain g where g1: "g ` S \<subseteq> ?R" and g2: "inj_on g S" by blast
        have "g ` S \<subseteq> {..<N}" using g1 by auto
        moreover have "\<forall>i\<in>S. \<forall>j\<in>S. T i j \<longrightarrow> compl C (g i) (g j)"
        proof (intro ballI impI)
          fix i j assume iS: "i \<in> S" and jS: "j \<in> S" and Tij: "T i j"
          from irr iS Tij have "i \<noteq> j" by auto
          with g2 iS jS have "g i \<noteq> g j" by (auto dest: inj_onD)
          with clique g1 iS jS show "compl C (g i) (g j)" by auto
        qed
        ultimately show ?thesis using g2 by blast
      qed
    qed
  qed
qed

section \<open>The lower bound\<close>

lemma lower:
  assumes tr: "is_tree n T" and N: "N < 2 * n - 1"
  shows "\<exists>C. simple N C \<and> \<not> contains 3 triangle N C \<and> \<not> contains n T N (compl C)"
proof -
  have n1: "1 \<le> n" using tr unfolding is_tree_def connected_def by auto
  have con: "\<forall>i<n. \<forall>j<n. (\<lambda>a b. a < n \<and> b < n \<and> T a b)\<^sup>*\<^sup>* i j"
    using tr unfolding is_tree_def connected_def by auto
  define a where "a = min N (n - 1)"
  define C where "C = (\<lambda>i j. i < N \<and> j < N \<and> ((i < a) \<noteq> (j < a)))"
  have simp1: "simple N C" unfolding simple_def C_def by auto
  have nt: "\<not> contains 3 triangle N C"
  proof
    assume "contains 3 triangle N C"
    then obtain f where "\<forall>i<3. \<forall>j<3. triangle i j \<longrightarrow> C (f i) (f j)" unfolding contains_def by auto
    then have "C (f 0) (f 1)" "C (f 1) (f 2)" "C (f 0) (f 2)" by (auto simp: triangle_def)
    then show False unfolding C_def by (cases "f 0 < a"; cases "f 1 < a"; cases "f 2 < a"; simp)
  qed
  have nT: "\<not> contains n T N (compl C)"
  proof
    assume "contains n T N (compl C)"
    then obtain f where fi: "inj_on f {..<n}" and fN: "f ` {..<n} \<subseteq> {..<N}"
      and fe: "\<forall>i<n. \<forall>j<n. T i j \<longrightarrow> compl C (f i) (f j)" unfolding contains_def by auto
    have side: "\<forall>i<n. \<forall>j<n. T i j \<longrightarrow> (f i < a) = (f j < a)"
    proof (intro allI impI)
      fix i j assume "i < n" "j < n" "T i j"
      with fe have "compl C (f i) (f j)" by auto
      moreover from fN \<open>i < n\<close> \<open>j < n\<close> have "f i < N" "f j < N" by auto
      ultimately show "(f i < a) = (f j < a)" unfolding compl_def C_def by auto
    qed
    have same: "\<And>j. j < n \<Longrightarrow> (f j < a) = (f 0 < a)"
    proof -
      fix j assume jn: "j < n"
      from con n1 jn have "(\<lambda>x y. x < n \<and> y < n \<and> T x y)\<^sup>*\<^sup>* 0 j" by auto
      then show "(f j < a) = (f 0 < a)"
      proof (induction rule: rtranclp_induct)
        case base then show ?case by simp
      next
        case (step b c)
        with side show ?case by auto
      qed
    qed
    show False
    proof (cases "f 0 < a")
      case True
      have "f ` {..<n} \<subseteq> {..<a}" using same True by auto
      from card_inj_on_le[OF fi this] have "n \<le> a" by simp
      with N n1 show False unfolding a_def by simp
    next
      case False
      have nl: "\<And>j. j < n \<Longrightarrow> \<not> f j < a" using same False by auto
      have "f ` {..<n} \<subseteq> {a..<N}"
      proof (rule image_subsetI)
        fix x assume x: "x \<in> {..<n}"
        then have "\<not> f x < a" using nl by simp
        moreover have "f x < N" using fN x by auto
        ultimately show "f x \<in> {a..<N}" by simp
      qed
      from card_inj_on_le[OF fi this] have "n \<le> N - a" by simp
      with N n1 show False unfolding a_def by simp
    qed
  qed
  from simp1 nt nT show ?thesis by blast
qed

section \<open>Chv\'atal's theorem\<close>

theorem chvatal:
  assumes "is_tree n T"
  shows "ramsey_triangle n T = 2 * n - 1"
proof -
  have n1: "1 \<le> n" using assms unfolding is_tree_def connected_def by auto
  have RSeq: "RS {..<n} T = (\<lambda>a b. a < n \<and> b < n \<and> T a b)" by (simp add: RS_def fun_eq_iff)
  have tr: "tree_on {..<n} T"
    using assms unfolding is_tree_def simple_def connected_def tree_on_def edges_def Eset_def RSeq
    by auto
  let ?S = "{N. \<forall>C. simple N C \<longrightarrow> contains 3 triangle N C \<or> contains n T N (compl C)}"
  have mem: "2 * n - 1 \<in> ?S"
    unfolding mem_Collect_eq
  proof (intro allI impI)
    fix C assume sC: "simple (2 * n - 1) C"
    show "contains 3 triangle (2 * n - 1) C \<or> contains n T (2 * n - 1) (compl C)"
    proof (cases "contains 3 triangle (2 * n - 1) C")
      case True then show ?thesis by simp
    next
      case False
      let ?N = "2 * n - 1"
      from sC have csym: "\<forall>i<?N. \<forall>j<?N. C i j = C j i" and cirr: "\<forall>i<?N. \<not> C i i"
        unfolding simple_def by auto
      have notri: "\<forall>a<?N. \<forall>b<?N. \<forall>c<?N. \<not> (C a b \<and> C b c \<and> C a c)"
      proof (intro allI impI notI)
        fix a b c assume aN: "a < ?N" and bN: "b < ?N" and cN: "c < ?N" and H: "C a b \<and> C b c \<and> C a c"
        then have Cab: "C a b" and Cbc: "C b c" and Cac: "C a c" by auto
        have Cba: "C b a" using csym aN bN Cab by auto
        have Ccb: "C c b" using csym bN cN Cbc by auto
        have Cca: "C c a" using csym aN cN Cac by auto
        have ab: "a \<noteq> b" and bc: "b \<noteq> c" and ac: "a \<noteq> c" using cirr aN bN cN Cab Cbc Cac by auto
        define f where "f = (\<lambda>i::nat. if i = 0 then a else if i = 1 then b else c)"
        have "contains 3 triangle ?N C"
          unfolding contains_def
        proof (intro exI[where x = f] conjI)
          show "inj_on f {..<3}" using ab bc ac unfolding f_def inj_on_def by (auto split: if_splits)
          show "f ` {..<3} \<subseteq> {..<?N}" using aN bN cN unfolding f_def by auto
          show "\<forall>i<3. \<forall>j<3. triangle i j \<longrightarrow> C (f i) (f j)"
          proof (intro allI impI)
            fix i j assume "i < 3" "j < 3" "triangle i j"
            then have ij: "i \<noteq> j" and i3: "i = 0 \<or> i = 1 \<or> i = 2" and j3: "j = 0 \<or> j = 1 \<or> j = 2"
              unfolding triangle_def by auto
            from i3 j3 ij show "C (f i) (f j)"
              using Cab Cba Cbc Ccb Cac Cca unfolding f_def by (elim disjE) auto
          qed
        qed
        with False show False by simp
      qed
      note U = upper[where n = n and T = T, OF csym notri, rule_format, of "{..<n}"]
      from U[OF tr card_lessThan order_refl] obtain f where
        "inj_on f {..<n}" "f ` {..<n} \<subseteq> {..<?N}"
        "\<forall>i\<in>{..<n}. \<forall>j\<in>{..<n}. T i j \<longrightarrow> compl C (f i) (f j)" by blast
      then have "contains n T ?N (compl C)" unfolding contains_def by (intro exI[where x = f]) auto
      then show ?thesis by simp
    qed
  qed
  have low: "\<And>N. N \<in> ?S \<Longrightarrow> 2 * n - 1 \<le> N"
  proof (rule ccontr)
    fix N assume "N \<in> ?S" and "\<not> 2 * n - 1 \<le> N"
    then have lt: "N < 2 * n - 1" by simp
    from lower[OF assms lt] obtain C where "simple N C" "\<not> contains 3 triangle N C"
      "\<not> contains n T N (compl C)" by blast
    with \<open>N \<in> ?S\<close> show False by blast
  qed
  have "ramsey_triangle n T = Inf ?S" unfolding ramsey_triangle_def by simp
  also have "\<dots> = 2 * n - 1"
  proof (rule antisym)
    show "Inf ?S \<le> 2 * n - 1" by (rule wellorder_Inf_le1[OF mem])
    show "2 * n - 1 \<le> Inf ?S" using Inf_nat_def1[of ?S] mem low by auto
  qed
  finally show ?thesis .
qed

section \<open>Connected graphs with at most $n-1$ edges\<close>

text \<open>Corollary \<open>erdos_1182.variants.F_ge_pred\<close>: a connected graph with at most $n-1$ edges is a
  tree, hence has Ramsey number $2n-1$ against the triangle. We first need that a connected graph
  on $n$ vertices has at least $n-1$ edges.\<close>

lemma exit_edge:
  assumes p: "(RS S G)\<^sup>*\<^sup>* x y" and x: "x \<in> X" and y: "y \<notin> X"
  shows "\<exists>a b. a \<in> X \<and> a \<in> S \<and> b \<in> S \<and> b \<notin> X \<and> G a b"
proof -
  have "y \<in> X \<or> (\<exists>a b. a \<in> X \<and> a \<in> S \<and> b \<in> S \<and> b \<notin> X \<and> G a b)"
    using p
  proof (induction rule: rtranclp_induct)
    case base then show ?case using x by simp
  next
    case (step p q)
    from step(2) have pS: "p \<in> S" and qS: "q \<in> S" and Gpq: "G p q" unfolding RS_def by auto
    from step(3) show ?case
    proof
      assume pX: "p \<in> X"
      show ?thesis
      proof (cases "q \<in> X")
        case True then show ?thesis by simp
      next
        case False
        with pX pS qS Gpq show ?thesis by blast
      qed
    next
      assume "\<exists>a b. a \<in> X \<and> a \<in> S \<and> b \<in> S \<and> b \<notin> X \<and> G a b"
      then show ?thesis by blast
    qed
  qed
  with y show ?thesis by blast
qed

lemma grow_edges:
  assumes fin: "finite S" and con: "\<forall>i\<in>S. \<forall>j\<in>S. (RS S G)\<^sup>*\<^sup>* i j"
  shows "\<forall>X. X \<subseteq> S \<longrightarrow> X \<noteq> {} \<longrightarrow> card (S - X) = k \<longrightarrow>
     card X \<le> card (Eset X G) + 1 \<longrightarrow> card S \<le> card (Eset S G) + 1"
proof (induction k)
  case 0
  show ?case
  proof (intro allI impI)
    fix X assume XS: "X \<subseteq> S" and "card (S - X) = 0" and h: "card X \<le> card (Eset X G) + 1"
    then have "S - X = {}" using fin by simp
    with XS have "X = S" by auto
    with h show "card S \<le> card (Eset S G) + 1" by simp
  qed
next
  case (Suc k)
  show ?case
  proof (intro allI impI)
    fix X assume XS: "X \<subseteq> S" and Xne: "X \<noteq> {}" and ck: "card (S - X) = Suc k"
      and h: "card X \<le> card (Eset X G) + 1"
    have finX: "finite X" by (rule finite_subset[OF XS fin])
    have "S - X \<noteq> {}"
    proof
      assume e: "S - X = {}"
      then have "card (S - X) = 0" by (simp only: card.empty)
      with ck show False by simp
    qed
    then obtain y where yS: "y \<in> S" and yX: "y \<notin> X" by auto
    from Xne obtain x where xX: "x \<in> X" by auto
    from con xX XS yS have "(RS S G)\<^sup>*\<^sup>* x y" by auto
    from exit_edge[OF this xX yX] obtain a b where aX: "a \<in> X" and aS: "a \<in> S" and bS: "b \<in> S"
      and bX: "b \<notin> X" and Gab: "G a b" by blast
    let ?X' = "insert b X"
    have X'S: "?X' \<subseteq> S" using XS bS by auto
    have cS: "card (S - ?X') = k"
    proof -
      have "S - ?X' = (S - X) - {b}" by auto
      then show ?thesis using ck bS bX fin by (simp add: card_Diff_singleton)
    qed
    have cX': "card ?X' = Suc (card X)" using finX bX by simp
    have finE: "finite (Eset X G)" by (rule finite_Eset[OF finX])
    have finE': "finite (Eset ?X' G)" by (rule finite_Eset) (use finX in simp)
    have notin: "{a, b} \<notin> Eset X G"
    proof
      assume "{a, b} \<in> Eset X G"
      then obtain i j where "{a, b} = {i, j}" "i \<in> X" "j \<in> X" unfolding Eset_def by auto
      then show False using bX by (auto simp: doubleton_eq_iff)
    qed
    have sub: "insert {a, b} (Eset X G) \<subseteq> Eset ?X' G"
      unfolding Eset_def using aX Gab by auto
    have "card (insert {a, b} (Eset X G)) \<le> card (Eset ?X' G)" by (rule card_mono[OF finE' sub])
    moreover have "card (insert {a, b} (Eset X G)) = Suc (card (Eset X G))" using notin finE by simp
    ultimately have "Suc (card (Eset X G)) \<le> card (Eset ?X' G)" by simp
    with h cX' have "card ?X' \<le> card (Eset ?X' G) + 1" by simp
    from Suc.IH[rule_format, OF X'S _ cS this] show "card S \<le> card (Eset S G) + 1" by simp
  qed
qed

lemma connected_edges_ge:
  assumes fin: "finite S" and ne: "S \<noteq> {}" and con: "\<forall>i\<in>S. \<forall>j\<in>S. (RS S G)\<^sup>*\<^sup>* i j"
  shows "card S \<le> card (Eset S G) + 1"
proof -
  from ne obtain r where r: "r \<in> S" by auto
  have "card {r} \<le> card (Eset {r} G) + 1" by simp
  from grow_edges[OF fin con, rule_format, of "{r}" "card (S - {r})"] r this show ?thesis by simp
qed

theorem connected_le_pred_edges_triangle_good:
  assumes sG: "simple n G" and cG: "connected n G" and le: "card (edges n G) \<le> n - 1"
  shows "ramsey_triangle n G = 2 * n - 1"
proof -
  have n1: "0 < n" using cG unfolding connected_def by auto
  have RSeq: "RS {..<n} G = (\<lambda>a b. a < n \<and> b < n \<and> G a b)" by (simp add: RS_def fun_eq_iff)
  have Eeq: "edges n G = Eset {..<n} G" unfolding edges_def Eset_def by auto
  have con: "\<forall>i\<in>{..<n}. \<forall>j\<in>{..<n}. (RS {..<n} G)\<^sup>*\<^sup>* i j"
    using cG unfolding connected_def RSeq by auto
  have ge: "n \<le> card (Eset {..<n} G) + 1"
  proof -
    have ne: "{..<n} \<noteq> {}" using n1 by auto
    from connected_edges_ge[OF finite_lessThan ne con] show ?thesis by simp
  qed
  have "card (edges n G) + 1 = n" using ge le Eeq n1 by simp
  then have "is_tree n G" unfolding is_tree_def using sG cG by simp
  then show ?thesis by (rule chvatal)
qed

end
