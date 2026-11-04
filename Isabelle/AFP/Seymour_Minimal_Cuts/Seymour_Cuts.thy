theory Seymour_Cuts
  imports Main "HOL-Library.FuncSet"
begin

section \<open>Definitions (faithful to formal-conjectures, Erdos 150)\<close>

text \<open>Graphs on vertex set @{term "{..<n}"}: a symmetric irreflexive edge relation inside it.\<close>
definition graph_on :: "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool" where
  "graph_on n E \<longleftrightarrow> E \<subseteq> {..<n} \<times> {..<n} \<and> sym E \<and> (\<forall>x. (x, x) \<notin> E)"

text \<open>Preconnected on a vertex set W: any two vertices of W joined by a path inside W
  (the induced subgraph has edges @{term "E \<inter> W \<times> W"}).\<close>
definition preconn :: "(nat \<times> nat) set \<Rightarrow> nat set \<Rightarrow> bool" where
  "preconn E W \<longleftrightarrow> (\<forall>x\<in>W. \<forall>y\<in>W. (x, y) \<in> (E \<inter> (W \<times> W))\<^sup>*)"

definition min_cut :: "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> nat set \<Rightarrow> bool" where
  "min_cut n E T \<longleftrightarrow> T \<subseteq> {..<n} \<and> \<not> preconn E ({..<n} - T)
      \<and> (\<forall>S. S \<subset> T \<longrightarrow> preconn E ({..<n} - S))"

definition cuts :: "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> nat set set" where
  "cuts n E = {T. min_cut n E T}"

definition max_minimal_cuts :: "nat \<Rightarrow> nat" where
  "max_minimal_cuts n = Sup {k. \<exists>E. graph_on n E \<and> card (cuts n E) = k}"

section \<open>Boundedness\<close>

lemma cuts_subset: "cuts n E \<subseteq> Pow {..<n}"
  by (auto simp: cuts_def min_cut_def)

lemma cuts_card_le: "card (cuts n E) \<le> 2 ^ n"
proof -
  have "card (cuts n E) \<le> card (Pow {..<n})"
    by (rule card_mono[OF _ cuts_subset]) simp
  also have "\<dots> = 2 ^ n" by (simp add: card_Pow)
  finally show ?thesis .
qed

lemma bdd_cut_counts: "bdd_above {k. \<exists>E. graph_on n E \<and> card (cuts n E) = k}"
  by (rule bdd_aboveI[where M = "2 ^ n"]) (auto intro: cuts_card_le)

section \<open>The construction\<close>

text \<open>Path k has positions 0..4: position 0 is s = 0, position 4 is t = 1, positions 1..3 are
  the internal vertices 3k+2, 3k+3, 3k+4.\<close>
definition vv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "vv k j = (if j = 0 then 0 else if j = 4 then 1 else 3 * k + j + 1)"

definition D :: "nat \<Rightarrow> (nat \<times> nat) set" where
  "D m = {(vv k j, vv k (Suc j)) | k j. k < m \<and> j < 4}"

definition Eg :: "nat \<Rightarrow> (nat \<times> nat) set" where
  "Eg m = D m \<union> (D m)\<inverse>"

definition Tf :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "Tf m f = {vv i (Suc (f i)) | i. i < m}"

lemma vv_range: "k < m \<Longrightarrow> j \<le> 4 \<Longrightarrow> vv k j < 3 * m + 2"
  unfolding vv_def by auto

lemma vv_eq:
  assumes "vv k j = vv k' j'" "j \<le> 4" "j' \<le> 4"
  shows "j = j' \<and> (j = 0 \<or> j = 4 \<or> k = k')"
  using assms unfolding vv_def by (auto split: if_splits; presburger)

lemma vv0: "vv k 0 = 0" and vv4: "vv k 4 = 1"
  by (simp_all add: vv_def)

lemma graph_Eg: "graph_on (3 * m + 2) (Eg m)"
  unfolding graph_on_def
proof (intro conjI allI)
  show "Eg m \<subseteq> {..<3 * m + 2} \<times> {..<3 * m + 2}"
    unfolding Eg_def D_def using vv_range by (auto simp: lessThan_iff)
  show "sym (Eg m)" unfolding Eg_def by (simp add: sym_Un_converse)
  fix x show "(x, x) \<notin> Eg m"
  proof
    assume "(x, x) \<in> Eg m"
    then obtain k j where kj: "k < m" "j < 4" "x = vv k j" "x = vv k (Suc j)"
      unfolding Eg_def D_def by auto
    from kj have "vv k j = vv k (Suc j)" by simp
    from vv_eq[OF this] kj(2) show False by simp
  qed
qed

lemma Eg_edge: "k < m \<Longrightarrow> j < 4 \<Longrightarrow> (vv k j, vv k (Suc j)) \<in> Eg m"
  unfolding Eg_def D_def by auto

lemma Eg_cases:
  assumes "(x, y) \<in> Eg m"
  obtains k j where "k < m" "j < 4" "x = vv k j" "y = vv k (Suc j)"
    | k j where "k < m" "j < 4" "y = vv k j" "x = vv k (Suc j)"
  using assms unfolding Eg_def D_def by auto

section \<open>Chains inside a vertex set\<close>

lemma chain:
  assumes "k < m"
  shows "j + d \<le> 4 \<Longrightarrow> (\<forall>q. j \<le> q \<longrightarrow> q \<le> j + d \<longrightarrow> vv k q \<in> W) \<Longrightarrow>
    (vv k j, vv k (j + d)) \<in> (Eg m \<inter> (W \<times> W))\<^sup>*"
proof (induction d)
  case 0 thus ?case by simp
next
  case (Suc d)
  have ih: "(vv k j, vv k (j + d)) \<in> (Eg m \<inter> (W \<times> W))\<^sup>*"
    using Suc.prems by (intro Suc.IH) auto
  have e: "(vv k (j + d), vv k (Suc (j + d))) \<in> Eg m \<inter> (W \<times> W)"
    using Suc.prems Eg_edge[OF assms, of "j + d"] by auto
  from rtrancl_into_rtrancl[OF ih e] show ?case by simp
qed

lemma sym_R: "sym (Eg m \<inter> (W \<times> W))"
proof -
  have "sym (Eg m)" using graph_Eg unfolding graph_on_def by blast
  thus ?thesis by (auto simp: sym_def)
qed

section \<open>The cuts\<close>

lemma f_facts:
  assumes "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat})" "i < m"
  shows "f i < 3"
  using assms by (auto simp: PiE_iff)

lemma Tf_not_special:
  assumes f: "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat})"
  shows "0 \<notin> Tf m f" "1 \<notin> Tf m f"
proof -
  have h: "i < m \<Longrightarrow> vv i (Suc (f i)) \<noteq> 0 \<and> vv i (Suc (f i)) \<noteq> 1" for i
    using f_facts[OF f, of i] unfolding vv_def by auto
  show "0 \<notin> Tf m f"
  proof
    assume "0 \<in> Tf m f"
    then obtain i where "i < m" "0 = vv i (Suc (f i))" unfolding Tf_def by auto
    with h show False by metis
  qed
  show "1 \<notin> Tf m f"
  proof
    assume "1 \<in> Tf m f"
    then obtain i where "i < m" "1 = vv i (Suc (f i))" unfolding Tf_def by auto
    with h show False by metis
  qed
qed

lemma Tf_mem:
  assumes f: "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat})" "k < m" "q \<le> 4"
  shows "vv k q \<in> Tf m f \<longleftrightarrow> q = Suc (f k)"
proof
  assume "vv k q \<in> Tf m f"
  then obtain i where i: "i < m" "vv k q = vv i (Suc (f i))" unfolding Tf_def by auto
  have fi: "f i < 3" using f_facts[OF f(1) i(1)] .
  from vv_eq[OF i(2)] f(3) fi have "q = Suc (f i) \<and> (q = 0 \<or> q = 4 \<or> k = i)" by auto
  with fi have "q = Suc (f i)" "k = i" by auto
  thus "q = Suc (f k)" by simp
next
  assume "q = Suc (f k)"
  thus "vv k q \<in> Tf m f" using f(2) unfolding Tf_def by auto
qed

lemma Tf_sub: "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat}) \<Longrightarrow> Tf m f \<subseteq> {..<3 * m + 2}"
proof
  fix x assume f: "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat})" "x \<in> Tf m f"
  then obtain i where i: "i < m" "x = vv i (Suc (f i))" unfolding Tf_def by auto
  have "f i < 3" using f_facts[OF f(1) i(1)] .
  with i vv_range show "x \<in> {..<3 * m + 2}" by (auto simp: lessThan_iff)
qed

lemma not_preconn:
  assumes f: "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat})"
  shows "\<not> preconn (Eg m) ({..<3 * m + 2} - Tf m f)"
proof
  assume pc: "preconn (Eg m) ({..<3 * m + 2} - Tf m f)"
  let ?W = "{..<3 * m + 2} - Tf m f"
  let ?A = "insert 0 {vv i q | i q. i < m \<and> 1 \<le> q \<and> q \<le> f i}"
  have s: "0 \<in> ?W" using Tf_not_special[OF f] by simp
  have t: "1 \<in> ?W" using Tf_not_special[OF f] by simp
  have closed: "(x, y) \<in> Eg m \<inter> (?W \<times> ?W) \<Longrightarrow> x \<in> ?A \<Longrightarrow> y \<in> ?A" for x y
  proof -
    assume xy: "(x, y) \<in> Eg m \<inter> (?W \<times> ?W)" and xA: "x \<in> ?A"
    hence e: "(x, y) \<in> Eg m" and yW: "y \<notin> Tf m f" by auto
    from xA have "x = 0 \<or> (\<exists>i q. x = vv i q \<and> i < m \<and> 1 \<le> q \<and> q \<le> f i)" by auto
    thus "y \<in> ?A"
    proof
      assume x0: "x = 0"
      from e show ?thesis
      proof (cases rule: Eg_cases)
        case (1 k j)
        have "vv k j = vv k 0" using 1 x0 by (simp add: vv0)
        from vv_eq[OF this] 1(2) have j0: "j = 0" by simp
        have "y = vv k 1" using 1 j0 by simp
        have "f k \<noteq> 0"
        proof
          assume "f k = 0"
          hence "vv k (Suc (f k)) = y" using \<open>y = vv k 1\<close> by simp
          with Tf_mem[OF f 1(1), of "Suc (f k)"] f_facts[OF f 1(1)] yW show False by auto
        qed
        hence fk1: "1 \<le> f k" by simp
        have "y \<in> {vv i q | i q. i < m \<and> 1 \<le> q \<and> q \<le> f i}"
          using \<open>y = vv k 1\<close> 1(1) fk1 by blast
        thus ?thesis by (rule insertI2)
      next
        case (2 k j)
        have "vv k (Suc j) = vv k 0" using 2 x0 by (simp add: vv0)
        from vv_eq[OF this] 2(2) show ?thesis by simp
      qed
    next
      assume "\<exists>i q. x = vv i q \<and> i < m \<and> 1 \<le> q \<and> q \<le> f i"
      then obtain i q where iq: "x = vv i q" "i < m" "1 \<le> q" "q \<le> f i" by auto
      have fi: "f i < 3" using f_facts[OF f iq(2)] .
      from e show ?thesis
      proof (cases rule: Eg_cases)
        case (1 k j)
        from vv_eq[of k j i q] 1 iq fi have jq: "j = q" "k = i" by auto
        show ?thesis
        proof (cases "Suc q \<le> f i")
          case True thus ?thesis using 1 jq iq by auto
        next
          case False
          hence "Suc j = Suc (f i)" using jq iq by simp
          hence "y \<in> Tf m f" using 1 jq Tf_mem[OF f iq(2), of "Suc q"] fi iq by auto
          with yW show ?thesis by simp
        qed
      next
        case (2 k j)
        from vv_eq[of k "Suc j" i q] 2 iq fi have jq: "Suc j = q" "k = i" by auto
        show ?thesis
        proof (cases "j = 0")
          case True thus ?thesis using 2 by (auto simp: vv0)
          next
          case False
          have e1: "y = vv i j" using 2(3) jq(2) by simp
          have e2: "i < m" using iq(2) .
          have e3: "1 \<le> j" using False by arith
          have e4: "j \<le> f i" using jq(1) iq(4) by arith
          have "y \<in> {vv i q | i q. i < m \<and> 1 \<le> q \<and> q \<le> f i}"
            by (rule CollectI, rule exI[of _ i], rule exI[of _ j]) (intro conjI e1 e2 e3 e4)
          thus ?thesis by (rule insertI2)
        qed
      qed
    qed
  qed
  have "(0, 1) \<in> (Eg m \<inter> (?W \<times> ?W))\<^sup>*" using pc s t unfolding preconn_def by blast
  have gen: "(0, b) \<in> (Eg m \<inter> (?W \<times> ?W))\<^sup>* \<Longrightarrow> b \<in> ?A" for b
  proof (induction rule: rtrancl_induct)
    case base show ?case by simp
  next
    case (step y z)
    from step(2) step(3) show ?case by (rule closed)
  qed
  have one: "1 \<in> ?A" by (rule gen[OF \<open>(0, 1) \<in> (Eg m \<inter> (?W \<times> ?W))\<^sup>*\<close>])
  from one have "(\<exists>i q. 1 = vv i q \<and> i < m \<and> 1 \<le> q \<and> q \<le> f i)" by simp
  then obtain i q where iq: "1 = vv i q" "i < m" "1 \<le> q" "q \<le> f i" by auto
  have fi: "f i < 3" using f_facts[OF f iq(2)] .
  have "vv 0 4 = vv i q" using iq(1) by (simp add: vv4)
  have q4: "q \<le> 4" using iq(4) fi by arith
  have "4 = q" by (rule conjunct1[OF vv_eq[OF \<open>vv 0 4 = vv i q\<close> le_refl q4]])
  thus False using iq(4) fi by arith
qed

lemma preconn_sub:
  assumes f: "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat})" and S: "S \<subset> Tf m f"
  shows "preconn (Eg m) ({..<3 * m + 2} - S)"
proof -
  let ?W = "{..<3 * m + 2} - S"
  let ?R = "Eg m \<inter> (?W \<times> ?W)"
  have Ssub: "S \<subseteq> Tf m f" using S by auto
  obtain x where x: "x \<in> Tf m f" "x \<notin> S" using S by blast
  then obtain i where i: "i < m" "x = vv i (Suc (f i))" unfolding Tf_def by auto
  have inW: "k < m \<Longrightarrow> q \<le> 4 \<Longrightarrow> q \<noteq> Suc (f k) \<Longrightarrow> vv k q \<in> ?W" for k q
  proof -
    assume k: "k < m" "q \<le> 4" "q \<noteq> Suc (f k)"
    have "vv k q \<notin> Tf m f" using Tf_mem[OF f k(1) k(2)] k(3) by simp
    with Ssub have "vv k q \<notin> S" by auto
    moreover have "vv k q < 3 * m + 2" using vv_range k by simp
    ultimately show ?thesis by simp
  qed
  have xW: "vv i (Suc (f i)) \<in> ?W"
  proof -
    have "vv i (Suc (f i)) < 3 * m + 2"
      using vv_range i(1) f_facts[OF f i(1)] by simp
    thus ?thesis using x i by simp
  qed
  have allW: "q \<le> 4 \<Longrightarrow> vv i q \<in> ?W" for q
    using inW[OF i(1)] xW by (cases "q = Suc (f i)") auto
  have c10: "(1, 0) \<in> ?R\<^sup>*"
  proof -
    have "(vv i 0, vv i (0 + 4)) \<in> ?R\<^sup>*"
      by (rule chain[OF i(1)], simp, intro allI impI allW, arith)
    hence "(0, 1) \<in> ?R\<^sup>*" by (simp add: vv0 vv4)
    thus ?thesis using sym_R by (meson sym_rtrancl symD)
  qed
  have to0: "v \<in> ?W \<Longrightarrow> (v, 0) \<in> ?R\<^sup>*" for v
  proof -
    assume vW: "v \<in> ?W"
    hence vlt: "v < 3 * m + 2" by simp
    show "(v, 0) \<in> ?R\<^sup>*"
    proof (cases "v < 2")
      case True
      show ?thesis
      proof (cases "v = 0")
        case True thus ?thesis by simp
      next
        case False
        with \<open>v < 2\<close> have "v = 1" by arith
        thus ?thesis using c10 by simp
      qed
    next
      case False
      define k where "k = (v - 2) div 3"
      define q where "q = (v - 2) mod 3 + 1"
      have kq: "v = vv k q" "k < m" "1 \<le> q" "q \<le> 3"
        using False vlt unfolding k_def q_def vv_def by auto
      have kq4: "q \<le> 4" using kq by simp
      show ?thesis
      proof (cases "q \<le> Suc (f k)")
        case True
        note qle = True
        have "(vv k 0, vv k (0 + q)) \<in> ?R\<^sup>*"
        proof (rule chain[OF kq(2)])
          show "0 + q \<le> 4" using kq by simp
          show "\<forall>q'. 0 \<le> q' \<longrightarrow> q' \<le> 0 + q \<longrightarrow> vv k q' \<in> ?W"
          proof (intro allI impI)
            fix q' assume q': "q' \<le> 0 + q"
            show "vv k q' \<in> ?W"
            proof (cases "q' = q")
              case True thus ?thesis using kq(1) vW by metis
            next
              case False
              have q1: "q' \<le> 4" and q2: "q' \<noteq> Suc (f k)" using q' False qle kq by arith+
              show ?thesis by (rule inW[OF kq(2) q1 q2])
            qed
          qed
        qed
        hence "(0, v) \<in> ?R\<^sup>*" using kq by (simp add: vv0)
        thus ?thesis using sym_R by (meson sym_rtrancl symD)
      next
        case False
        note qgt = False
        have "(vv k q, vv k (q + (4 - q))) \<in> ?R\<^sup>*"
        proof (rule chain[OF kq(2)])
          show "q + (4 - q) \<le> 4" using kq by simp
          show "\<forall>q'. q \<le> q' \<longrightarrow> q' \<le> q + (4 - q) \<longrightarrow> vv k q' \<in> ?W"
          proof (intro allI impI)
            fix q' assume q': "q \<le> q'" "q' \<le> q + (4 - q)"
            show "vv k q' \<in> ?W"
            proof (cases "q' = q")
              case True thus ?thesis using kq(1) vW by metis
            next
              case False
              have q1: "q' \<le> 4" and q2: "q' \<noteq> Suc (f k)" using q' False qgt kq by arith+
              show ?thesis by (rule inW[OF kq(2) q1 q2])
            qed
          qed
        qed
        hence "(v, 1) \<in> ?R\<^sup>*" using kq by (simp add: vv4)
        thus ?thesis by (rule rtrancl_trans[OF _ c10])
      qed
    qed
  qed
  show ?thesis unfolding preconn_def
  proof (intro ballI)
    fix a b assume a: "a \<in> ?W" and b: "b \<in> ?W"
    have "(0, b) \<in> ?R\<^sup>*" using to0[OF b] sym_R by (meson sym_rtrancl symD)
    thus "(a, b) \<in> ?R\<^sup>*" by (rule rtrancl_trans[OF to0[OF a]])
  qed
qed

lemma Tf_min_cut:
  assumes "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat})"
  shows "Tf m f \<in> cuts (3 * m + 2) (Eg m)"
  unfolding cuts_def min_cut_def using Tf_sub[OF assms] not_preconn[OF assms]
    preconn_sub[OF assms] by auto

lemma Tf_inj:
  assumes f: "f \<in> PiE {..<m} (\<lambda>_. {..<3::nat})" and g: "g \<in> PiE {..<m} (\<lambda>_. {..<3::nat})"
    and eq: "Tf m f = Tf m g"
  shows "f = g"
proof (rule extensionalityI[of f "{..<m}" g])
  show "f \<in> extensional {..<m}" "g \<in> extensional {..<m}" using f g by (auto simp: PiE_iff)
next
  fix i assume "i \<in> {..<m}"
  hence i: "i < m" by simp
  have "vv i (Suc (f i)) \<in> Tf m f" using i unfolding Tf_def by auto
  hence "vv i (Suc (f i)) \<in> Tf m g" using eq by simp
  from Tf_mem[OF g i, of "Suc (f i)"] this f_facts[OF f i]
  show "f i = g i" by auto
qed

section \<open>Seymour's observation\<close>

theorem seymour: "3 ^ m \<le> max_minimal_cuts (3 * m + 2)"
proof -
  let ?F = "PiE {..<m} (\<lambda>_. {..<3::nat})"
  let ?n = "3 * m + 2"
  have cF: "card ?F = 3 ^ m" by (simp add: card_PiE prod_constant)
  have fin: "finite (cuts ?n (Eg m))"
    by (rule finite_subset[OF cuts_subset]) simp
  have inj: "inj_on (Tf m) ?F" using Tf_inj by (intro inj_onI) blast
  have "card (Tf m ` ?F) \<le> card (cuts ?n (Eg m))"
    by (rule card_mono[OF fin], rule image_subsetI, rule Tf_min_cut, assumption)
  hence lo: "3 ^ m \<le> card (cuts ?n (Eg m))" using card_image[OF inj] cF by simp
  have mem: "card (cuts ?n (Eg m)) \<in> {k. \<exists>E. graph_on ?n E \<and> card (cuts ?n E) = k}"
    using graph_Eg by blast
  have up: "card (cuts ?n (Eg m)) \<le> max_minimal_cuts ?n"
    unfolding max_minimal_cuts_def by (rule cSup_upper[OF mem bdd_cut_counts])
  show ?thesis by (rule order_trans[OF lo up])
qed

end
