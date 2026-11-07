theory Erdos_1186_Probabilistic
  imports Main "HOL-Library.Extended_Real" "HOL-Library.Liminf_Limsup"
begin

section \<open>Monochromatic arithmetic progressions in 2-colourings: the probabilistic upper bound\<close>

text \<open>Transcription of the definitions of Erd\H{o}s problem 1186 as stated in the formal-conjectures
  repository (\<open>FormalConjectures/ErdosProblems/1186.lean\<close>). The progression with first term \<open>a\<close>
  and common difference \<open>d \<ge> 1\<close> is the pair \<open>(a, d)\<close>, \<open>1 \<le> a, d \<le> n\<close>, \<open>a + (k-1) d \<le> n\<close>.
  Colourings are \<open>nat \<Rightarrow> bool\<close>. The limit inferior is taken in the extended reals (the quotient lies
  in \<open>[0,1]\<close>, so this agrees with the real limit inferior).\<close>

definition aps :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "aps k n = {p \<in> {1..n} \<times> {1..n}. fst p + (k - 1) * snd p \<le> n}"

definition mono_count :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "mono_count k n c = card {p \<in> {1..n} \<times> {1..n}. fst p + (k - 1) * snd p \<le> n \<and>
      (\<forall>i<k. c (fst p + i * snd p) = c (fst p))}"

definition min_mono_count :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "min_mono_count k n = Inf {m. \<exists>c. mono_count k n c = m}"

definition delta :: "nat \<Rightarrow> ereal" where
  "delta k = Liminf sequentially (\<lambda>n. ereal (real (min_mono_count k n) / real n ^ 2))"

section \<open>Counting colourings that are constant on a set\<close>

lemma card_supersets:
  assumes "finite N" "P \<subseteq> N"
  shows "card {S. S \<subseteq> N \<and> P \<subseteq> S} = 2 ^ (card N - card P)"
proof -
  have "{S. S \<subseteq> N \<and> P \<subseteq> S} = (\<lambda>T. T \<union> P) ` Pow (N - P)"
  proof (intro set_eqI iffI)
    fix S assume "S \<in> {S. S \<subseteq> N \<and> P \<subseteq> S}"
    then have "S \<subseteq> N" "P \<subseteq> S" by auto
    then show "S \<in> (\<lambda>T. T \<union> P) ` Pow (N - P)"
      by (intro image_eqI[where x = "S - P"]) auto
  next
    fix S assume "S \<in> (\<lambda>T. T \<union> P) ` Pow (N - P)"
    then show "S \<in> {S. S \<subseteq> N \<and> P \<subseteq> S}" using assms(2) by auto
  qed
  moreover have "inj_on (\<lambda>T. T \<union> P) (Pow (N - P))" by (auto simp: inj_on_def)
  ultimately have "card {S. S \<subseteq> N \<and> P \<subseteq> S} = card (Pow (N - P))"
    by (simp add: card_image)
  also have "\<dots> = 2 ^ card (N - P)" using assms by (simp add: card_Pow finite_subset)
  also have "card (N - P) = card N - card P" using assms by (simp add: card_Diff_subset finite_subset)
  finally show ?thesis .
qed

lemma card_disjoint_sets:
  assumes "finite N"
  shows "card {S. S \<subseteq> N \<and> P \<inter> S = {}} = 2 ^ card (N - P)"
proof -
  have "{S. S \<subseteq> N \<and> P \<inter> S = {}} = Pow (N - P)" by auto
  then show ?thesis using assms by (simp add: card_Pow)
qed

section \<open>The points of a progression\<close>

definition pts :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat set" where
  "pts k p = (\<lambda>i. fst p + i * snd p) ` {..<k}"

lemma card_pts:
  assumes "1 \<le> snd p"
  shows "card (pts k p) = k"
proof -
  have "inj_on (\<lambda>i. fst p + i * snd p) {..<k}" using assms by (auto simp: inj_on_def)
  then show ?thesis by (simp add: pts_def card_image)
qed

lemma pts_sub:
  assumes "p \<in> aps k n" "2 \<le> k"
  shows "pts k p \<subseteq> {1..n}"
proof
  fix x assume "x \<in> pts k p"
  then obtain i where i: "i < k" "x = fst p + i * snd p" by (auto simp: pts_def)
  from assms have a: "1 \<le> fst p" "fst p + (k - 1) * snd p \<le> n" by (auto simp: aps_def)
  have "i * snd p \<le> (k - 1) * snd p" using i by (intro mult_right_mono) auto
  then have "x \<le> n" "1 \<le> x" using i a by linarith+
  then show "x \<in> {1..n}" by simp
qed

lemma mono_iff:
  assumes "0 < k"
  shows "(\<forall>i<k. (fst p + i * snd p \<in> S) = (fst p \<in> S)) \<longleftrightarrow>
         (pts k p \<subseteq> S \<or> pts k p \<inter> S = {})"
proof
  assume H: "\<forall>i<k. (fst p + i * snd p \<in> S) = (fst p \<in> S)"
  show "pts k p \<subseteq> S \<or> pts k p \<inter> S = {}"
  proof (cases "fst p \<in> S")
    case True
    then have "pts k p \<subseteq> S" using H by (auto simp: pts_def)
    then show ?thesis by simp
  next
    case False
    then have "pts k p \<inter> S = {}" using H by (auto simp: pts_def)
    then show ?thesis by simp
  qed
next
  assume H: "pts k p \<subseteq> S \<or> pts k p \<inter> S = {}"
  have 0: "fst p \<in> pts k p" using assms by (auto simp: pts_def intro: image_eqI[where x = 0])
  show "\<forall>i<k. (fst p + i * snd p \<in> S) = (fst p \<in> S)"
  proof (intro allI impI)
    fix i assume i: "i < k"
    have 1: "fst p + i * snd p \<in> pts k p" using i by (auto simp: pts_def)
    from H show "(fst p + i * snd p \<in> S) = (fst p \<in> S)" using 0 1 by blast
  qed
qed

section \<open>Total number of monochromatic progressions over all subsets colourings\<close>

lemma mono_count_sum:
  assumes k: "2 \<le> k" and nk: "k \<le> n"
  shows "(\<Sum>S\<in>Pow {1..n}. mono_count k n (\<lambda>x. x \<in> S)) = card (aps k n) * (2 * 2 ^ (n - k))"
proof -
  let ?N = "{1..n}"
  have fin: "finite (aps k n)" unfolding aps_def by auto
  have fP: "finite (Pow ?N)" by simp
  have mc: "\<And>S. mono_count k n (\<lambda>x. x \<in> S) =
      (\<Sum>p\<in>aps k n. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then 1 else 0)"
  proof -
    fix S
    have eq: "{p \<in> {1..n} \<times> {1..n}. fst p + (k - 1) * snd p \<le> n \<and>
            (\<forall>i<k. (fst p + i * snd p \<in> S) = (fst p \<in> S))} =
          {p \<in> aps k n. pts k p \<subseteq> S \<or> pts k p \<inter> S = {}}"
      using mono_iff[of k] k by (auto simp: aps_def)
    have "mono_count k n (\<lambda>x. x \<in> S) = card {p \<in> aps k n. pts k p \<subseteq> S \<or> pts k p \<inter> S = {}}"
      unfolding mono_count_def using eq by (rule arg_cong[where f = card])
    also have "\<dots> = (\<Sum>p\<in>{p \<in> aps k n. pts k p \<subseteq> S \<or> pts k p \<inter> S = {}}. 1)" by (rule card_eq_sum)
    also have "\<dots> = (\<Sum>p\<in>aps k n. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then 1 else 0)"
      by (rule sum.inter_filter[OF fin])
    finally show "mono_count k n (\<lambda>x. x \<in> S) = (\<Sum>p\<in>aps k n. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then 1 else 0)" .
  qed
  have per: "\<And>p. p \<in> aps k n \<Longrightarrow>
      (\<Sum>S\<in>Pow ?N. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then (1::nat) else 0) = 2 * 2 ^ (n - k)"
  proof -
    fix p assume p: "p \<in> aps k n"
    then have d: "1 \<le> snd p" by (auto simp: aps_def)
    have sub: "pts k p \<subseteq> ?N" using pts_sub p k by blast
    have fpts: "finite (pts k p)" using sub by (rule finite_subset) simp
    have cp: "card (pts k p) = k" using card_pts d by blast
    have ne: "pts k p \<noteq> {}"
    proof
      assume e: "pts k p = {}"
      then have "k = 0" using cp by simp
      then show False using k by simp
    qed
    let ?A = "{S. S \<subseteq> ?N \<and> pts k p \<subseteq> S}"
    let ?B = "{S. S \<subseteq> ?N \<and> pts k p \<inter> S = {}}"
    have sA: "?A \<subseteq> Pow ?N" by auto
    have sB: "?B \<subseteq> Pow ?N" by auto
    have fA: "finite ?A" using sA fP by (rule finite_subset)
    have fB: "finite ?B" using sB fP by (rule finite_subset)
    have "card {S \<in> Pow ?N. pts k p \<subseteq> S \<or> pts k p \<inter> S = {}} =
          (\<Sum>S\<in>{S \<in> Pow ?N. pts k p \<subseteq> S \<or> pts k p \<inter> S = {}}. 1)" by (rule card_eq_sum)
    also have "\<dots> = (\<Sum>S\<in>Pow ?N. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then 1 else 0)"
      by (rule sum.inter_filter[OF fP])
    finally have key: "(\<Sum>S\<in>Pow ?N. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then 1 else 0) =
          card {S \<in> Pow ?N. pts k p \<subseteq> S \<or> pts k p \<inter> S = {}}" by (rule sym)
    have un: "{S \<in> Pow ?N. pts k p \<subseteq> S \<or> pts k p \<inter> S = {}} = ?A \<union> ?B" by auto
    have dis: "?A \<inter> ?B = {}" using ne by blast
    have cA: "card ?A = 2 ^ (n - k)"
    proof -
      have "card ?A = 2 ^ (card ?N - card (pts k p))" by (rule card_supersets[OF finite_atLeastAtMost sub])
      then show ?thesis using cp by simp
    qed
    have cB: "card ?B = 2 ^ (n - k)"
    proof -
      have "card (?N - pts k p) = card ?N - card (pts k p)" by (rule card_Diff_subset[OF fpts sub])
      then have "card (?N - pts k p) = n - k" using cp by simp
      moreover have "card ?B = 2 ^ card (?N - pts k p)" by (rule card_disjoint_sets[OF finite_atLeastAtMost])
      ultimately show ?thesis by simp
    qed
    have "card (?A \<union> ?B) = card ?A + card ?B" by (rule card_Un_disjoint[OF fA fB dis])
    then show "(\<Sum>S\<in>Pow ?N. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then (1::nat) else 0) = 2 * 2 ^ (n - k)"
      using key un cA cB by simp
  qed
  have "(\<Sum>S\<in>Pow ?N. mono_count k n (\<lambda>x. x \<in> S)) =
        (\<Sum>S\<in>Pow ?N. \<Sum>p\<in>aps k n. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then 1 else 0)"
    by (rule sum.cong[OF refl]) (rule mc)
  also have "\<dots> = (\<Sum>p\<in>aps k n. \<Sum>S\<in>Pow ?N. if pts k p \<subseteq> S \<or> pts k p \<inter> S = {} then 1 else 0)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>p\<in>aps k n. 2 * 2 ^ (n - k))" by (rule sum.cong[OF refl per])
  also have "\<dots> = card (aps k n) * (2 * 2 ^ (n - k))" by simp
  finally show ?thesis .
qed

section \<open>The number of progressions\<close>

lemma sum_formula:
  fixes m n D :: nat
  shows "m * D \<le> n \<Longrightarrow> 2 * (\<Sum>d\<in>{1..D}. n - m * d) + m * D * (D + 1) = 2 * n * D"
proof (induction D)
  case 0
  then show ?case by simp
next
  case (Suc D)
  have "m * D \<le> m * Suc D" by simp
  with Suc.prems have h: "m * D \<le> n" by linarith
  have IH: "2 * (\<Sum>d\<in>{1..D}. n - m * d) + m * D * (D + 1) = 2 * n * D" using Suc.IH h by blast
  have pr: "m * Suc D \<le> n" using Suc.prems by simp
  obtain q where q: "n = q + m * (Suc D)" using le_Suc_ex[OF pr] by (auto simp: add.commute)
  have "(\<Sum>d\<in>{1..Suc D}. n - m * d) = (\<Sum>d\<in>{1..D}. n - m * d) + (n - m * Suc D)"
    by (simp add: sum.cl_ivl_Suc)
  moreover have "n - m * Suc D = q" using q by simp
  ultimately have S: "(\<Sum>d\<in>{1..Suc D}. n - m * d) = (\<Sum>d\<in>{1..D}. n - m * d) + q" by simp
  show ?case using IH S q by (simp add: algebra_simps)
qed

lemma card_aps:
  assumes "1 \<le> m" "m = k - 1"
  shows "card (aps k n) = (\<Sum>d\<in>{1..n div m}. n - m * d)"
proof -
  have "aps k n = prod.swap ` (SIGMA d:{1..n div m}. {1..n - m * d})"
  proof (intro set_eqI iffI)
    fix p assume "p \<in> aps k n"
    then obtain a d where p: "p = (a, d)" "1 \<le> a" "a \<le> n" "1 \<le> d" "d \<le> n" "a + m * d \<le> n"
      using assms by (cases p) (auto simp: aps_def)
    have mpos: "0 < m" using assms(1) by simp
    have h1: "m * d \<le> n" using p(6) by (rule le_trans[OF le_add2])
    then have "d * m \<le> n" by (simp add: mult.commute)
    then have "d \<le> n div m" using mpos by (simp add: less_eq_div_iff_mult_less_eq)
    then show "p \<in> prod.swap ` (SIGMA d:{1..n div m}. {1..n - m * d})"
      using p by (intro image_eqI[where x = "(d, a)"]) auto
  next
    fix p assume "p \<in> prod.swap ` (SIGMA d:{1..n div m}. {1..n - m * d})"
    then obtain d a where p: "p = (a, d)" "1 \<le> d" "d \<le> n div m" "1 \<le> a" "a \<le> n - m * d" by auto
    have mpos: "0 < m" using assms(1) by simp
    have "d * m \<le> n" using p(3) mpos by (simp add: less_eq_div_iff_mult_less_eq)
    then have "m * d \<le> n" by (simp add: mult.commute)
    moreover have "d \<le> n" using p(2,3) assms(1) div_le_dividend le_trans by blast
    ultimately show "p \<in> aps k n" using p assms by (auto simp: aps_def)
  qed
  then show ?thesis
    by (simp add: card_image inj_on_def card_SigmaI)
qed

lemma aps_bound:
  assumes "2 \<le> k"
  shows "2 * (k - 1) * card (aps k n) \<le> n ^ 2"
proof -
  define m where "m = k - 1"
  have m1: "1 \<le> m" using assms m_def by simp
  define D where "D = n div m"
  have mD: "m * D \<le> n" unfolding D_def by simp
  have "card (aps k n) = (\<Sum>d\<in>{1..D}. n - m * d)" using card_aps m1 m_def D_def by blast
  then obtain S where S: "S = card (aps k n)" and e: "2 * S + m * D * (D + 1) = 2 * n * D"
    using sum_formula[OF mD] by metis
  from arg_cong[where f = real, OF e]
  have er: "2 * real S + real m * real D * (real D + 1) = 2 * real n * real D"
    by (simp only: of_nat_add of_nat_mult of_nat_1 of_nat_numeral)
  have e1: "2 * real S = 2 * real n * real D - real m * real D * (real D + 1)" using er by linarith
  have e2: "real n ^ 2 - 2 * real m * real S = (real n - real m * real D) ^ 2 + real m * (real m * real D)"
  proof -
    have "2 * real m * real S = real m * (2 * real S)" by simp
    also have "\<dots> = real m * (2 * real n * real D - real m * real D * (real D + 1))" by (simp only: e1)
    finally have "2 * real m * real S = real m * (2 * real n * real D - real m * real D * (real D + 1))" .
    then show ?thesis by (simp add: power2_eq_square algebra_simps)
  qed
  have e3: "0 \<le> (real n - real m * real D) ^ 2 + real m * (real m * real D)" by (simp add: zero_le_mult_iff)
  have "2 * real m * real S \<le> real n ^ 2" using e2 e3 by linarith
  then have "real (2 * m * S) \<le> real (n ^ 2)" by simp
  then have "2 * m * S \<le> n ^ 2" by (simp only: of_nat_le_iff)
  then show ?thesis using S m_def by simp
qed

section \<open>The probabilistic bound\<close>

lemma min_le_aps:
  assumes "2 \<le> k"
  shows "2 ^ (k - 1) * min_mono_count k n \<le> card (aps k n)"
proof (cases "k \<le> n")
  case False
  then have "aps k n = {}"
  proof -
    have "\<And>a d. 1 \<le> a \<Longrightarrow> 1 \<le> d \<Longrightarrow> \<not> a + (k - 1) * d \<le> n"
    proof -
      fix a d :: nat assume ad: "1 \<le> a" "1 \<le> d"
      have "(k - 1) * 1 \<le> (k - 1) * d" using ad(2) by (rule mult_le_mono2)
      then have "k - 1 \<le> (k - 1) * d" by simp
      then show "\<not> a + (k - 1) * d \<le> n" using ad(1) False assms by linarith
    qed
    then show ?thesis unfolding aps_def by auto
  qed
  then have z: "mono_count k n (\<lambda>_. True) = 0"
    unfolding mono_count_def aps_def by (auto simp: Collect_empty_eq)
  have "min_mono_count k n \<le> mono_count k n (\<lambda>_. True)"
    unfolding min_mono_count_def by (rule cInf_lower) auto
  then show ?thesis using z by simp
next
  case True
  let ?m = "min_mono_count k n"
  have lower: "\<And>S. ?m \<le> mono_count k n (\<lambda>x. x \<in> S)"
    unfolding min_mono_count_def by (rule cInf_lower) auto
  have "(\<Sum>S\<in>Pow {1..n}. ?m) \<le> (\<Sum>S\<in>Pow {1..n}. mono_count k n (\<lambda>x. x \<in> S))"
    by (rule sum_mono) (use lower in auto)
  then have "2 ^ n * ?m \<le> card (aps k n) * (2 * 2 ^ (n - k))"
    using mono_count_sum[OF assms True] by (simp add: card_Pow)
  moreover have "(2::nat) ^ n =2 ^ (k - 1) * (2 * 2 ^ (n - k))"
  proof -
    have "n = (k - 1) + 1 + (n - k)" using assms True by simp
    then have "(2::nat) ^ n = 2 ^ ((k - 1) + 1 + (n - k))" by simp
    also have "\<dots> = 2 ^ (k - 1) * (2 * 2 ^ (n - k))" by (simp add: power_add)
    finally show ?thesis .
  qed
  ultimately have "(2 ^ (k - 1) * ?m) * (2 * 2 ^ (n - k)) \<le> card (aps k n) * (2 * 2 ^ (n - k))"
    by (simp add: algebra_simps)
  then show ?thesis by simp
qed

theorem erdos_1186_probabilistic:
  assumes k: "2 \<le> k"
  shows "delta k \<le> ereal (1 / (real (k - 1) * 2 ^ k))"
proof -
  have ev: "eventually (\<lambda>n. ereal (real (min_mono_count k n) / real n ^ 2) \<le>
      ereal (1 / (real (k - 1) * 2 ^ k))) sequentially"
  proof (rule eventually_sequentiallyI[where c = 1])
    fix n :: nat assume n: "1 \<le> n"
    let ?m = "real (min_mono_count k n)"
    have h1: "2 ^ (k - 1) * min_mono_count k n \<le> card (aps k n)" using min_le_aps k by blast
    have h2: "2 * (k - 1) * card (aps k n) \<le> n ^ 2" using aps_bound k by blast
    have "2 * (k - 1) * (2 ^ (k - 1) * min_mono_count k n) \<le> n ^ 2"
      using h1 h2 by (meson mult_le_mono2 le_trans)
    then have "real (2 * (k - 1) * (2 ^ (k - 1) * min_mono_count k n)) \<le> real (n ^ 2)" by (rule of_nat_mono)
    then have h3: "2 * real (k - 1) * (2 ^ (k - 1) * ?m) \<le> real n ^ 2" by simp
    obtain j where j: "k = Suc j" using k by (cases k) auto
    have kk: "(2::real) ^ k = 2 * 2 ^ (k - 1)" using j by simp
    have kpos: "0 < real (k - 1)" using k by simp
    have npos: "0 < real n ^ 2" using n by simp
    have "?m / real n ^ 2 \<le> 1 / (real (k - 1) * 2 ^ k)"
      using h3 kpos npos kk by (simp add: field_simps)
    then show "ereal (?m / real n ^ 2) \<le> ereal (1 / (real (k - 1) * 2 ^ k))" by simp
  qed
  have "delta k \<le> Liminf sequentially (\<lambda>_. ereal (1 / (real (k - 1) * 2 ^ k)))"
    unfolding delta_def by (rule Liminf_mono[OF ev])
  also have "\<dots> = ereal (1 / (real (k - 1) * 2 ^ k))" by (rule Liminf_const) simp
  finally show ?thesis .
qed

end
