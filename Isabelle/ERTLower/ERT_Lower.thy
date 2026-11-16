(*  Title:      ERT_Lower.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Erdős–Rubin–Taylor lower bound for the bipartite list-colouring threshold: 2^k <= n(k) (formal-conjectures erdos_629 variant)
*)

theory ERT_Lower
  imports Main
begin

section \<open>Erdos--Rubin--Taylor 1980: the lower bound $2^{k-1} < n(k)$\<close>

text \<open>Definitions copied from the session ERT_Choosability (formal-conjectures, ErdosProblems/629.lean):
\<open>n_choose k\<close> is the least number of vertices of a bipartite graph with list-chromatic number above \<open>k\<close>.
We prove \<open>2 ^ k \<le> n_choose k\<close> for \<open>k \<ge> 1\<close>, hence \<open>2 ^ (k - 1) < n_choose k\<close>.\<close>

definition sgraph :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "sgraph m E \<longleftrightarrow> (\<forall>u v. E u v \<longrightarrow> u < m \<and> v < m) \<and> (\<forall>u v. E u v \<longrightarrow> E v u) \<and> (\<forall>v. \<not> E v v)"

definition bipartite :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "bipartite m E \<longleftrightarrow> (\<exists>f::nat \<Rightarrow> nat. (\<forall>v<m. f v < 2) \<and> (\<forall>u v. E u v \<longrightarrow> f u \<noteq> f v))"

definition choosable :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "choosable m E k \<longleftrightarrow> (\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<m. finite (L v) \<and> card (L v) = k) \<longrightarrow>
      (\<exists>c::nat \<Rightarrow> nat. (\<forall>v<m. c v \<in> L v) \<and> (\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v)))"

definition list_chrom :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "list_chrom m E = Inf {k. choosable m E k}"

definition n_choose :: "nat \<Rightarrow> nat" where
  "n_choose k = Inf {m. \<exists>E. sgraph m E \<and> bipartite m E \<and> k < list_chrom m E}"

subsection \<open>Monotonicity of choosability in the list size\<close>

lemma choosable_Suc: "choosable m E j \<Longrightarrow> choosable m E (Suc j)"
  unfolding choosable_def
proof (intro allI impI)
  fix L :: "nat \<Rightarrow> nat set"
  assume ch: "\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<m. finite (L v) \<and> card (L v) = j) \<longrightarrow>
      (\<exists>c::nat \<Rightarrow> nat. (\<forall>v<m. c v \<in> L v) \<and> (\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v))"
    and hL: "\<forall>v<m. finite (L v) \<and> card (L v) = Suc j"
  define L' where "L' v = L v - {SOME x. x \<in> L v}" for v
  have ne: "\<exists>x. x \<in> L v" if "v < m" for v
  proof -
    from that have "card (L v) = Suc j" using hL by auto
    hence "L v \<noteq> {}" by auto
    thus "\<exists>x. x \<in> L v" by blast
  qed
  have L'ok: "\<forall>v<m. finite (L' v) \<and> card (L' v) = j"
  proof (intro allI impI)
    fix v assume vm: "v < m"
    hence fin: "finite (L v)" and cd: "card (L v) = Suc j" using hL by auto
    from ne[OF vm] have "(SOME x. x \<in> L v) \<in> L v" by (rule someI_ex)
    thus "finite (L' v) \<and> card (L' v) = j"
      using fin cd by (simp add: L'_def card_Diff_singleton)
  qed
  from ch[rule_format, of L'] L'ok obtain c where
    c1: "\<forall>v<m. c v \<in> L' v" and c2: "\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v" by blast
  have "\<forall>v<m. c v \<in> L v" using c1 unfolding L'_def by auto
  thus "\<exists>c::nat \<Rightarrow> nat. (\<forall>v<m. c v \<in> L v) \<and> (\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v)" using c2 by blast
qed

lemma choosable_mono: "choosable m E j \<Longrightarrow> j \<le> k \<Longrightarrow> choosable m E k"
proof -
  assume ch: "choosable m E j" and le: "j \<le> k"
  obtain d where "k = j + d" using le by (auto simp: le_iff_add)
  thus ?thesis
  proof (induct d arbitrary: k)
    case 0 thus ?case using ch by simp
  next
    case (Suc d)
    have "choosable m E (j + d)" using Suc.hyps[of "j + d"] by simp
    hence "choosable m E (Suc (j + d))" by (rule choosable_Suc)
    thus ?case using Suc.prems by simp
  qed
qed

lemma list_chrom_le: "choosable m E k \<Longrightarrow> list_chrom m E \<le> k"
  unfolding list_chrom_def by (intro cInf_lower) auto

subsection \<open>(B) Bipartite graphs with fewer than $2^k$ vertices are $k$-choosable\<close>

text \<open>Counting argument. \<open>C\<close> is the union of the lists, \<open>n\<close> its size. A subset \<open>S \<subseteq> C\<close> is the set of colours
sent to side 0. A vertex of side 0 is bad for \<open>S\<close> if its list misses \<open>S\<close>; a vertex of side 1 is bad if its list is
inside \<open>S\<close>. Each vertex is bad for at most \<open>2^(n-k)\<close> sets, so fewer than \<open>2^n\<close> sets are bad for some vertex.\<close>

lemma bip_small_choosable:
  assumes g: "sgraph m E" and b: "bipartite m E" and small: "m < 2 ^ k"
  shows "choosable m E k"
  unfolding choosable_def
proof (intro allI impI)
  fix L :: "nat \<Rightarrow> nat set"
  assume hL: "\<forall>v<m. finite (L v) \<and> card (L v) = k"
  obtain f :: "nat \<Rightarrow> nat" where f2: "\<forall>v<m. f v < 2" and fE: "\<forall>u v. E u v \<longrightarrow> f u \<noteq> f v"
    using b unfolding bipartite_def by blast
  show "\<exists>c::nat \<Rightarrow> nat. (\<forall>v<m. c v \<in> L v) \<and> (\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v)"
  proof (cases "m = 0")
    case True
    hence "\<forall>u v. \<not> E u v" using g unfolding sgraph_def by auto
    thus ?thesis using True by (intro exI[of _ "\<lambda>_. 0"]) simp
  next
    case False
    define C where "C = (\<Union>v\<in>{..<m}. L v)"
    define n where "n = card C"
    have finC: "finite C" unfolding C_def using hL by auto
    have LC: "\<And>v. v < m \<Longrightarrow> L v \<subseteq> C" unfolding C_def by auto
    have kn: "k \<le> n"
    proof -
      have "0 < m" using False by simp
      hence "card (L 0) \<le> card C" using LC finC by (intro card_mono) auto
      moreover have "card (L 0) = k" using hL \<open>0 < m\<close> by simp
      ultimately show ?thesis unfolding n_def by simp
    qed
    define bad where "bad v = {S \<in> Pow C. if f v = 0 then S \<inter> L v = {} else L v \<subseteq> S}" for v
    have badcard: "card (bad v) \<le> 2 ^ (n - k)" if vm: "v < m" for v
    proof -
      have fin: "finite (L v)" and cd: "card (L v) = k" using hL vm by auto
      have cdiff: "card (C - L v) = n - k"
        using card_Diff_subset[OF fin LC[OF vm]] cd unfolding n_def by simp
      have finD: "finite (C - L v)" using finC by simp
      have cP: "card (Pow (C - L v)) = 2 ^ (n - k)" using card_Pow[OF finD] cdiff by simp
      have finP: "finite (Pow (C - L v))" using finD by simp
      show "card (bad v) \<le> 2 ^ (n - k)"
      proof (cases "f v = 0")
        case True
        have "bad v \<subseteq> Pow (C - L v)" unfolding bad_def using True by auto
        from card_mono[OF finP this] cP show ?thesis by simp
      next
        case False
        have "bad v \<subseteq> (\<lambda>T. L v \<union> T) ` Pow (C - L v)"
        proof
          fix S assume "S \<in> bad v"
          hence SC: "S \<subseteq> C" and LS: "L v \<subseteq> S" using False unfolding bad_def by auto
          have "S - L v \<in> Pow (C - L v)" using SC by auto
          moreover have "S = L v \<union> (S - L v)" using LS by auto
          ultimately show "S \<in> (\<lambda>T. L v \<union> T) ` Pow (C - L v)" by (metis imageI)
        qed
        hence "card (bad v) \<le> card ((\<lambda>T. L v \<union> T) ` Pow (C - L v))"
          using finP by (intro card_mono) auto
        also have "\<dots> \<le> card (Pow (C - L v))" by (rule card_image_le[OF finP])
        finally show ?thesis using cP by simp
      qed
    qed
    have badsub: "\<And>v. bad v \<subseteq> Pow C" unfolding bad_def by auto
    have finPC: "finite (Pow C)" using finC by simp
    have finU: "finite (\<Union>v\<in>{..<m}. bad v)"
    proof (rule finite_subset[OF _ finPC])
      show "(\<Union>v\<in>{..<m}. bad v) \<subseteq> Pow C" using badsub by blast
    qed
    have "card (\<Union>v\<in>{..<m}. bad v) \<le> (\<Sum>v\<in>{..<m}. card (bad v))"
      by (rule card_UN_le) simp
    also have "\<dots> \<le> card {..<m} * 2 ^ (n - k)"
      using sum_bounded_above[of "{..<m}" "\<lambda>v. card (bad v)" "2 ^ (n - k)"] badcard by simp
    also have "\<dots> < 2 ^ k * 2 ^ (n - k)" using small by simp
    also have "\<dots> = 2 ^ n" using kn by (simp flip: power_add)
    finally have lt: "card (\<Union>v\<in>{..<m}. bad v) < 2 ^ n" .
    have "\<exists>S\<in>Pow C. S \<notin> (\<Union>v\<in>{..<m}. bad v)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "Pow C \<subseteq> (\<Union>v\<in>{..<m}. bad v)" by blast
      from card_mono[OF finU this] have "2 ^ n \<le> card (\<Union>v\<in>{..<m}. bad v)"
        using card_Pow[OF finC] unfolding n_def by simp
      thus False using lt by simp
    qed
    then obtain S where SC: "S \<in> Pow C" and Sn: "\<forall>v<m. S \<notin> bad v" by auto
    have pick: "\<exists>x. x \<in> L v \<and> (x \<in> S \<longleftrightarrow> f v = 0)" if vm: "v < m" for v
    proof -
      from Sn vm have nb: "S \<notin> bad v" by blast
      show "\<exists>x. x \<in> L v \<and> (x \<in> S \<longleftrightarrow> f v = 0)"
      proof (cases "f v = 0")
        case True
        with nb SC have "S \<inter> L v \<noteq> {}" unfolding bad_def by auto
        thus ?thesis using True by auto
      next
        case False
        with nb SC have "\<not> L v \<subseteq> S" unfolding bad_def by auto
        thus ?thesis using False by auto
      qed
    qed
    define c where "c v = (SOME x. x \<in> L v \<and> (x \<in> S \<longleftrightarrow> f v = 0))" for v
    have cp: "\<And>v. v < m \<Longrightarrow> c v \<in> L v \<and> (c v \<in> S \<longleftrightarrow> f v = 0)"
      unfolding c_def by (rule someI_ex[OF pick])
    have "\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v"
    proof (intro allI impI notI)
      fix u v assume e: "E u v" and eq: "c u = c v"
      hence um: "u < m" and vm: "v < m" using g unfolding sgraph_def by auto
      have "(c u \<in> S) = (f u = 0)" "(c v \<in> S) = (f v = 0)" using cp um vm by auto
      hence "(f u = 0) = (f v = 0)" using eq by simp
      moreover have "f u < 2" "f v < 2" "f u \<noteq> f v" using f2 um vm fE e by auto
      ultimately show False by arith
    qed
    moreover have "\<forall>v<m. c v \<in> L v" using cp by blast
    ultimately show ?thesis by blast
  qed
qed

subsection \<open>(A) The graphs $K_{M,M}$ with $M = \binom{2k-1}{k}$\<close>

definition KMM :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "KMM M u v \<longleftrightarrow> (u < M \<and> M \<le> v \<and> v < 2 * M) \<or> (v < M \<and> M \<le> u \<and> u < 2 * M)"

lemma KMM_sgraph: "sgraph (2 * M) (KMM M)"
  unfolding sgraph_def KMM_def by auto

lemma KMM_bipartite: "bipartite (2 * M) (KMM M)"
  unfolding bipartite_def KMM_def by (intro exI[of _ "\<lambda>v. if v < M then 0 else 1"]) auto

text \<open>Non-emptiness of the set defining \<open>list_chrom\<close>: with lists of size \<open>M + 1\<close> the left side picks one colour
each (at most \<open>M\<close> colours), so every right list has a free colour.\<close>

lemma KMM_choosable_big: "choosable (2 * M) (KMM M) (M + 1)"
  unfolding choosable_def
proof (intro allI impI)
  fix L :: "nat \<Rightarrow> nat set"
  assume hL: "\<forall>v<2 * M. finite (L v) \<and> card (L v) = M + 1"
  define A where "A = {..<M}"
  define B where "B = {M..<2 * M}"
  define cA where "cA v = (SOME x. x \<in> L v)" for v
  have ne: "\<exists>x. x \<in> L v" if "v < 2 * M" for v
  proof -
    from that have "card (L v) = M + 1" using hL by auto
    hence "L v \<noteq> {}" by auto
    thus "\<exists>x. x \<in> L v" by blast
  qed
  have cAin: "\<forall>a\<in>A. cA a \<in> L a"
  proof
    fix a assume "a \<in> A"
    hence "a < 2 * M" unfolding A_def by auto
    from ne[OF this] show "cA a \<in> L a" unfolding cA_def by (rule someI_ex)
  qed
  have Bfree: "\<forall>b\<in>B. \<exists>z. z \<in> L b \<and> z \<notin> cA ` A"
  proof
    fix b assume bB: "b \<in> B"
    hence bm: "b < 2 * M" unfolding B_def by auto
    have fin: "finite (L b)" and cd: "card (L b) = M + 1" using hL bm by auto
    show "\<exists>z. z \<in> L b \<and> z \<notin> cA ` A"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence sub: "L b \<subseteq> cA ` A" by blast
      have "card (cA ` A) \<le> card A" by (rule card_image_le) (simp add: A_def)
      hence "card (cA ` A) \<le> M" by (simp add: A_def)
      have fi: "finite (cA ` A)" by (simp add: A_def)
      have "card (L b) \<le> card (cA ` A)" by (rule card_mono[OF fi sub])
      with \<open>card (cA ` A) \<le> M\<close> have "card (L b) \<le> M" by simp
      thus False using cd by simp
    qed
  qed
  define c where "c v = (if v < M then cA v else (SOME z. z \<in> L v \<and> z \<notin> cA ` A))" for v
  have cL: "\<forall>v<2 * M. c v \<in> L v"
  proof (intro allI impI)
    fix v assume vm: "v < 2 * M"
    show "c v \<in> L v"
    proof (cases "v < M")
      case True thus ?thesis using cAin unfolding c_def A_def by simp
    next
      case False
      hence "v \<in> B" using vm unfolding B_def by auto
      from Bfree[rule_format, OF this] have "\<exists>z. z \<in> L v \<and> z \<notin> cA ` A" .
      from someI_ex[OF this] show ?thesis using False unfolding c_def by simp
    qed
  qed
  have cfree: "c b \<notin> cA ` A" if "M \<le> b" and "b < 2 * M" for b
  proof -
    from that have "b \<in> B" unfolding B_def by auto
    from Bfree[rule_format, OF this] have "\<exists>z. z \<in> L b \<and> z \<notin> cA ` A" .
    from someI_ex[OF this] show "c b \<notin> cA ` A" using \<open>M \<le> b\<close> unfolding c_def by simp
  qed
  have "\<forall>u v. KMM M u v \<longrightarrow> c u \<noteq> c v"
  proof (intro allI impI)
    fix u v assume "KMM M u v"
    hence "(u < M \<and> M \<le> v \<and> v < 2 * M) \<or> (v < M \<and> M \<le> u \<and> u < 2 * M)" unfolding KMM_def .
    thus "c u \<noteq> c v"
    proof
      assume h: "u < M \<and> M \<le> v \<and> v < 2 * M"
      hence "c u = cA u" unfolding c_def by simp
      moreover have "cA u \<in> cA ` A" using h unfolding A_def by auto
      ultimately show ?thesis using cfree h by metis
    next
      assume h: "v < M \<and> M \<le> u \<and> u < 2 * M"
      hence "c v = cA v" unfolding c_def by simp
      moreover have "cA v \<in> cA ` A" using h unfolding A_def by auto
      ultimately show ?thesis using cfree h by metis
    qed
  qed
  with cL show "\<exists>c::nat \<Rightarrow> nat. (\<forall>v<2 * M. c v \<in> L v) \<and> (\<forall>u v. KMM M u v \<longrightarrow> c u \<noteq> c v)" by blast
qed

text \<open>Non-choosability with all $k$-subsets of \<open>{..<2k-1}\<close> as lists.\<close>

lemma KMM_not_choosable:
  assumes k1: "1 \<le> k" and M: "M = (2 * k - 1) choose k"
  shows "\<not> choosable (2 * M) (KMM M) k"
proof
  assume ch: "choosable (2 * M) (KMM M) k"
  define U :: "nat set" where "U = {..<2 * k - 1}"
  define F :: "nat set set" where "F = {S. S \<subseteq> U \<and> card S = k}"
  have finU: "finite U" unfolding U_def by simp
  have cU: "card U = 2 * k - 1" unfolding U_def by simp
  have cF: "card F = M" unfolding F_def M using n_subsets[OF finU, of k] cU by simp
  have finF: "finite F"
  proof (rule finite_subset[of F "Pow U"])
    show "F \<subseteq> Pow U" unfolding F_def by auto
    show "finite (Pow U)" using finU by simp
  qed
  have Mpos: "0 < M" unfolding M using k1 by (simp add: zero_less_binomial_iff)
  obtain h where bij: "bij_betw h {0..<card F} F" using ex_bij_betw_nat_finite[OF finF] by blast
  hence bijM: "bij_betw h {0..<M} F" using cF by simp
  define Lst :: "nat \<Rightarrow> nat set" where "Lst v = h (v mod M)" for v
  have hF: "h (v mod M) \<in> F" for v
  proof -
    have "v mod M \<in> {0..<M}" using Mpos by simp
    thus "h (v mod M) \<in> F" using bij_betw_apply[OF bijM] by blast
  qed
  have LstOK: "\<forall>v<2 * M. finite (Lst v) \<and> card (Lst v) = k"
  proof (intro allI impI)
    fix v assume "v < 2 * M"
    have "Lst v \<in> F" unfolding Lst_def by (rule hF)
    hence "Lst v \<subseteq> U" "card (Lst v) = k" unfolding F_def by auto
    thus "finite (Lst v) \<and> card (Lst v) = k" using finU by (auto intro: finite_subset)
  qed
  from ch[unfolded choosable_def, rule_format, of Lst] LstOK obtain c where
    c1: "\<forall>v<2 * M. c v \<in> Lst v" and c2: "\<forall>u v. KMM M u v \<longrightarrow> c u \<noteq> c v" by blast
  define A where "A = c ` {..<M}"
  have hLeft: "\<And>u. u < M \<Longrightarrow> Lst u = h u" unfolding Lst_def by simp
  have meet: "S \<inter> A \<noteq> {}" if "S \<in> F" for S
  proof -
    from that have "S \<in> h ` {0..<M}" using bijM by (simp add: bij_betw_def)
    then obtain u where uM: "u \<in> {0..<M}" and Su: "S = h u" by blast
    have "c u \<in> Lst u" using c1 uM by auto
    hence "c u \<in> S" using hLeft Su uM by auto
    moreover have "c u \<in> A" unfolding A_def using uM by auto
    ultimately show "S \<inter> A \<noteq> {}" by auto
  qed
  have small: "card (U - A) < k"
  proof (rule ccontr)
    assume "\<not> card (U - A) < k"
    hence "k \<le> card (U - A)" by simp
    then obtain B where Bs: "B \<subseteq> U - A" and Bc: "card B = k" by (rule obtain_subset_with_card_n)
    have "B \<in> F" unfolding F_def using Bs Bc by auto
    from meet[OF this] Bs show False by auto
  qed
  have split: "card U = card (U - A) + card (U \<inter> A)"
  proof -
    have "U = (U - A) \<union> (U \<inter> A)" by auto
    moreover have "(U - A) \<inter> (U \<inter> A) = {}" by auto
    ultimately show ?thesis
      using card_Un_disjoint[of "U - A" "U \<inter> A"] finU by (metis finite_Diff finite_Int)
  qed
  have big: "k \<le> card (U \<inter> A)" using split small cU k1 by arith
  obtain B where Bs: "B \<subseteq> U \<inter> A" and Bc: "card B = k"
    using obtain_subset_with_card_n[OF big] by blast
  have BF: "B \<in> F" unfolding F_def using Bs Bc by auto
  then obtain w where wM: "w \<in> {0..<M}" and Bw: "B = h w"
    using bijM by (auto simp: bij_betw_def)
  define v where "v = M + w"
  have v1: "M \<le> v" and v2: "v < 2 * M" using wM unfolding v_def by auto
  have Lv: "Lst v = B"
  proof -
    have "(M + w) mod M = w" using wM by simp
    thus ?thesis unfolding Lst_def v_def using Bw by simp
  qed
  have "c v \<in> B" using c1 v2 Lv by auto
  hence "c v \<in> A" using Bs by auto
  then obtain u where uM: "u < M" and cu: "c u = c v" unfolding A_def by auto
  have "KMM M u v" unfolding KMM_def using uM v1 v2 by auto
  from c2[rule_format, OF this] cu show False by simp
qed

lemma KMM_list_chrom_gt:
  assumes k1: "1 \<le> k" and M: "M = (2 * k - 1) choose k"
  shows "k < list_chrom (2 * M) (KMM M)"
proof -
  have ne: "{j. choosable (2 * M) (KMM M) j} \<noteq> {}" using KMM_choosable_big by auto
  from Inf_nat_def1[OF ne] have "choosable (2 * M) (KMM M) (list_chrom (2 * M) (KMM M))"
    unfolding list_chrom_def by simp
  thus ?thesis
    using choosable_mono KMM_not_choosable[OF k1 M] by (metis not_le_imp_less)
qed

subsection \<open>(C) The theorem\<close>

theorem ert_lower_strong:
  assumes k1: "1 \<le> k"
  shows "2 ^ k \<le> n_choose k"
proof -
  define M where "M = (2 * k - 1) choose k"
  let ?S = "{m. \<exists>E. sgraph m E \<and> bipartite m E \<and> k < list_chrom m E}"
  have in2M: "2 * M \<in> ?S"
    using KMM_sgraph KMM_bipartite KMM_list_chrom_gt[OF k1 M_def] by blast
  have ge: "\<forall>m\<in>?S. 2 ^ k \<le> m"
  proof
    fix m assume "m \<in> ?S"
    then obtain E where g: "sgraph m E" and b: "bipartite m E" and lc: "k < list_chrom m E" by blast
    show "2 ^ k \<le> m"
    proof (rule ccontr)
      assume "\<not> 2 ^ k \<le> m"
      hence "m < 2 ^ k" by simp
      from bip_small_choosable[OF g b this] have "list_chrom m E \<le> k" by (rule list_chrom_le)
      thus False using lc by simp
    qed
  qed
  show ?thesis unfolding n_choose_def using in2M ge by (intro cInf_greatest) auto
qed

theorem ert_lower: "1 \<le> k \<Longrightarrow> 2 ^ (k - 1) < n_choose k"
proof -
  assume k1: "1 \<le> k"
  then obtain j where kj: "k = Suc j" by (cases k) auto
  have "(2::nat) ^ j < 2 ^ Suc j" by (rule power_strict_increasing) simp_all
  also have "\<dots> \<le> n_choose k" using ert_lower_strong[OF k1] kj by simp
  finally show ?thesis using kj by simp
qed

end
