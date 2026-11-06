theory Consecutive_Coprime_Divisors
  imports "HOL-Computational_Algebra.Primes" "HOL-Computational_Algebra.Squarefree"
begin

section \<open>Consecutive coprime divisors\<close>

text \<open>
  For a natural number @{term n} let @{text ds} be the increasing list of its divisors,
  and let @{text "\<tau>\<^sub>\<bottom>(n)"} be the number of indices @{text i} such that
  @{text "ds ! i"} and @{text "ds ! (i+1)"} are coprime.  We prove that for every @{text k}
  there is a squarefree @{text n} with exactly @{text k} distinct prime factors and
  @{text "\<tau>\<^sub>\<bottom>(n) = k"} (following Erdos and Hall: take @{text "n = p\<^sub>1 \<cdots> p\<^sub>k"} with
  @{text "p\<^sub>i > p\<^sub>1 \<cdots> p\<^sub>(i-1)"}).
\<close>

subsection \<open>Faithful definitions\<close>

definition divs :: "nat \<Rightarrow> nat list" where
  "divs n = sorted_list_of_set {d. d dvd n}"

definition tau_perp :: "nat \<Rightarrow> nat" where
  "tau_perp n = card {i. i + 1 < length (divs n) \<and> coprime (divs n ! i) (divs n ! (i + 1))}"


lemma divs_0 [simp]: "divs 0 = []"
  by (simp add: divs_def)

lemma tau_perp_0 [simp]: "tau_perp 0 = 0"
  by (simp add: tau_perp_def)

lemma divs_1 [simp]: "divs 1 = [1]"
  by (simp add: divs_def)

lemma tau_perp_1 [simp]: "tau_perp 1 = 0"
  unfolding tau_perp_def divs_1 by simp

subsection \<open>Counting adjacent coprime pairs in a list\<close>

fun cc :: "nat list \<Rightarrow> nat" where
  "cc [] = 0"
| "cc [x] = 0"
| "cc (x # y # r) = (if coprime x y then 1 else 0) + cc (y # r)"

lemma cc_card:
  "card {i. i + 1 < length xs \<and> coprime (xs ! i) (xs ! (i + 1))} = cc xs"
proof (induction xs rule: cc.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y r)
  let ?S = "{i. i + 1 < length (y # r) \<and> coprime ((y # r) ! i) ((y # r) ! (i + 1))}"
  have eq: "{i. i + 1 < length (x # y # r) \<and> coprime ((x # y # r) ! i) ((x # y # r) ! (i + 1))}
      = (if coprime x y then {0} else {}) \<union> Suc ` ?S"
  proof (rule set_eqI)
    fix i
    show "i \<in> {i. i + 1 < length (x # y # r) \<and> coprime ((x # y # r) ! i) ((x # y # r) ! (i + 1))}
        \<longleftrightarrow> i \<in> (if coprime x y then {0} else {}) \<union> Suc ` ?S"
    proof (cases i)
      case 0
      then show ?thesis by simp
    next
      case (Suc j)
      then show ?thesis by (auto simp: image_iff)
    qed
  qed
  have "finite ?S"
    by (rule finite_subset[of _ "{..< length (y # r)}"]) auto
  then have "card (Suc ` ?S) = card ?S"
    by (simp add: card_image)
  then show ?case
    using 3 eq by (cases "coprime x y") (simp_all add: card_Un_disjoint finite_imageI)
qed

lemma cc_append:
  assumes "A \<noteq> []"
  shows "cc (A @ (b # B)) = cc A + (if coprime (last A) b then 1 else 0) + cc (b # B)"
  using assms
proof (induction A rule: cc.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y r)
  then show ?case by simp
qed

lemma cc_map_mult:
  assumes "p > 1"
  shows "cc (map (\<lambda>d. d * p) A) = 0"
proof (induction A rule: cc.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y r)
  have "\<not> coprime (x * p) (y * p)"
  proof
    assume c: "coprime (x * p) (y * p)"
    have "is_unit p"
      by (rule coprime_common_divisor[OF c]) simp_all
    with assms show False by simp
  qed
  with 3 show ?case by simp
qed

subsection \<open>Superincreasing prime sequences and their divisor lists\<close>

inductive ss :: "nat list \<Rightarrow> bool" where
  ss_Nil: "ss []"
| ss_snoc: "ss ps \<Longrightarrow> prime p \<Longrightarrow> p > prod_list ps \<Longrightarrow> ss (ps @ [p])"

definition D :: "nat list \<Rightarrow> nat list" where
  "D ps = foldl (\<lambda>A p. A @ map (\<lambda>d. d * p) A) [1] ps"

lemma D_Nil [simp]: "D [] = [1]"
  by (simp add: D_def)

lemma D_snoc: "D (ps @ [p]) = D ps @ map (\<lambda>d. d * p) (D ps)"
  by (simp add: D_def)

lemma ss_pos: "ss ps \<Longrightarrow> prod_list ps > 0 \<and> (\<forall>x\<in>set ps. x \<le> prod_list ps)"
proof (induction rule: ss.induct)
  case ss_Nil
  then show ?case by simp
next
  case (ss_snoc ps p)
  have p1: "p > 0" using ss_snoc by (metis prime_gt_0_nat)
  have "prod_list ps \<le> prod_list ps * p"
    using p1 by simp
  moreover have "p \<le> prod_list ps * p"
    using ss_snoc(4) p1 by (metis ss_snoc.IH mult_le_cancel2 One_nat_def Suc_leI mult_1)
  ultimately show ?case
    using ss_snoc by (auto intro: order_trans)
qed

lemma ss_divisors:
  assumes "ss ps"
  shows "set (D ps) = {d. d dvd prod_list ps}"
    and "sorted_wrt (<) (D ps)"
    and "D ps \<noteq> []"
    and "hd (D ps) = 1"
    and "last (D ps) = prod_list ps"
  using assms
proof (induction rule: ss.induct)
  case ss_Nil
  then show "set (D []) = {d. d dvd prod_list []}"
    and "sorted_wrt (<) (D [])" and "D [] \<noteq> []" and "hd (D []) = 1"
    and "last (D []) = prod_list []"
    by simp_all
next
  case (ss_snoc ps p)
  note IH = ss_snoc.IH
  note pr = ss_snoc.hyps(2)
  note big = ss_snoc.hyps(3)
  define q where "q = prod_list ps"
  have qpos: "q > 0" unfolding q_def using ss_pos[OF ss_snoc.hyps(1)] by simp
  have p1: "p > 1" using prime_gt_1_nat[OF pr] .
  have pq: "p > q" using big unfolding q_def .
  have prod: "prod_list (ps @ [p]) = q * p" by (simp add: q_def)
  have a1: "set (D ps) = {d. d dvd q}" using IH unfolding q_def by simp
  have a2: "sorted_wrt (<) (D ps)" using IH by simp
  have a3: "D ps \<noteq> []" using IH by simp
  have a4: "hd (D ps) = 1" using IH by simp
  have a5: "last (D ps) = q" using IH unfolding q_def by simp
  have nd: "\<not> p dvd q"
    using pq qpos by (simp add: nat_dvd_not_less)
  show "set (D (ps @ [p])) = {d. d dvd prod_list (ps @ [p])}"
  proof
    show "set (D (ps @ [p])) \<subseteq> {d. d dvd prod_list (ps @ [p])}"
    proof
      fix d assume "d \<in> set (D (ps @ [p]))"
      then consider "d \<in> set (D ps)" | e where "e \<in> set (D ps)" "d = e * p"
        by (auto simp: D_snoc)
      then show "d \<in> {d. d dvd prod_list (ps @ [p])}"
      proof cases
        case 1
        with a1 have "d dvd q" by simp
        then have "d dvd q * p" by simp
        then show ?thesis unfolding mem_Collect_eq prod by assumption
      next
        case 2
        with a1 have "e dvd q" by simp
        then have "e * p dvd q * p" by simp
        then show ?thesis using 2 unfolding mem_Collect_eq prod by (simp add: q_def)
      qed
    qed
  next
    show "{d. d dvd prod_list (ps @ [p])} \<subseteq> set (D (ps @ [p]))"
    proof
      fix d assume "d \<in> {d. d dvd prod_list (ps @ [p])}"
      then have dd: "d dvd q * p" by (simp add: q_def)
      show "d \<in> set (D (ps @ [p]))"
      proof (cases "p dvd d")
        case True
        then obtain e where e: "d = p * e" by blast
        with dd have "e dvd q" using p1 by simp
        then show ?thesis using a1 e by (auto simp: D_snoc mult.commute)
      next
        case False
        have "coprime p d" by (rule prime_imp_coprime[OF pr False])
        then have "coprime d p" by (simp add: ac_simps)
        with dd have "d dvd q" by (simp add: coprime_dvd_mult_left_iff)
        then show ?thesis using a1 by (simp add: D_snoc)
      qed
    qed
  qed
  show "sorted_wrt (<) (D (ps @ [p]))"
  proof -
    have "sorted_wrt (<) (map (\<lambda>d. d * p) (D ps))"
      using a2 p1 by (simp add: sorted_wrt_map)
    moreover have "\<forall>x\<in>set (D ps). \<forall>y\<in>set (map (\<lambda>d. d * p) (D ps)). x < y"
    proof (intro ballI)
      fix x y assume x: "x \<in> set (D ps)" and y: "y \<in> set (map (\<lambda>d. d * p) (D ps))"
      from x a1 have "x dvd q" by simp
      then have "x \<le> q" using qpos by (simp add: dvd_imp_le)
      from y obtain d where d: "d \<in> set (D ps)" "y = d * p" by auto
      from d(1) a1 have "d dvd q" by simp
      then have "d > 0" using qpos by (metis dvd_0_left_iff gr0I less_irrefl)
      then have "p \<le> d * p" by simp
      with \<open>x \<le> q\<close> pq d(2) show "x < y" by linarith
    qed
    ultimately show ?thesis
      using a2 by (simp add: D_snoc sorted_wrt_append)
  qed
  show "D (ps @ [p]) \<noteq> []" using a3 by (simp add: D_snoc)
  show "hd (D (ps @ [p])) = 1" using a3 a4 by (simp add: D_snoc)
  show "last (D (ps @ [p])) = prod_list (ps @ [p])"
    using a3 a5 by (simp add: D_snoc q_def last_map)
qed

lemma ss_divs: "ss ps \<Longrightarrow> divs (prod_list ps) = D ps"
proof -
  assume h: "ss ps"
  have fin: "finite {d. d dvd prod_list ps}"
    using ss_pos[OF h] by (simp add: finite_divisors_nat)
  have "sorted_wrt (<) (sorted_list_of_set {d. d dvd prod_list ps})"
    using strict_sorted_iff[of "sorted_list_of_set {d. d dvd prod_list ps}"] by simp
  moreover have "set (sorted_list_of_set {d. d dvd prod_list ps}) = set (D ps)"
    using fin ss_divisors(1)[OF h] by simp
  ultimately show ?thesis
    unfolding divs_def using ss_divisors(2)[OF h] strict_sorted_equal by blast
qed

lemma ss_cc: "ss ps \<Longrightarrow> cc (D ps) = length ps"
proof (induction rule: ss.induct)
  case ss_Nil
  then show ?case by simp
next
  case (ss_snoc ps p)
  note pr = ss_snoc.hyps(2)
  have p1: "p > 1" using prime_gt_1_nat[OF pr] .
  obtain A where A: "D ps = A" by blast
  have ne: "A \<noteq> []" using ss_divisors(3)[OF ss_snoc.hyps(1)] A by simp
  have hd1: "hd A = 1" using ss_divisors(4)[OF ss_snoc.hyps(1)] A by simp
  have lastq: "last A = prod_list ps" using ss_divisors(5)[OF ss_snoc.hyps(1)] A by simp
  have qpos: "prod_list ps > 0" using ss_pos[OF ss_snoc.hyps(1)] by simp
  have nd: "\<not> p dvd prod_list ps"
    using ss_snoc.hyps(3) qpos by (simp add: nat_dvd_not_less)
  have cop: "coprime (prod_list ps) p"
    using prime_imp_coprime[OF pr nd] by (simp add: ac_simps)
  obtain b B where B: "map (\<lambda>d. d * p) A = b # B"
    using ne by (cases A) auto
  have bp: "b = p"
    using B hd1 ne by (cases A) auto
  have cB: "cc (b # B) = 0"
    using cc_map_mult[OF p1, of A] B by simp
  have "cc (D (ps @ [p])) = cc (A @ (b # B))"
    using B A by (simp add: D_snoc)
  also have "\<dots> = cc A + (if coprime (last A) b then 1 else 0) + cc (b # B)"
    by (rule cc_append[OF ne])
  also have "\<dots> = length ps + 1"
    using ss_snoc.IH A lastq bp cop cB by simp
  finally show ?case by simp
qed

lemma sqf_one_nat: "squarefree (prod_list ([] :: nat list))"
  unfolding squarefree_def prod_list.Nil
proof (intro allI impI)
  fix x :: nat
  assume h: "x ^ 2 dvd 1"
  have "x dvd x ^ 2" by (simp add: power2_eq_square)
  from dvd_trans[OF this h] show "x dvd 1" .
qed

lemma ss_squarefree_omega:
  assumes "ss ps"
  shows "squarefree (prod_list ps)" and "prime_factors (prod_list ps) = set ps"
    and "distinct ps"
  using assms
proof (induction rule: ss.induct)
  case ss_Nil
  show "squarefree (prod_list ([] :: nat list))"
    using sqf_one_nat by blast
  show "prime_factors (prod_list ([] :: nat list)) = set []" by simp
  show "distinct []" by simp
next
  case (ss_snoc ps p)
  note pr = ss_snoc.hyps(2)
  have qpos: "prod_list ps > 0" using ss_pos[OF ss_snoc.hyps(1)] by simp
  have nd: "\<not> p dvd prod_list ps"
    using ss_snoc.hyps(3) qpos by (simp add: nat_dvd_not_less)
  have cop: "coprime (prod_list ps) p"
    using prime_imp_coprime[OF pr nd] by (simp add: ac_simps)
  have pn: "p \<notin> set ps"
    using ss_pos[OF ss_snoc.hyps(1)] ss_snoc.hyps(3) by force
  show "squarefree (prod_list (ps @ [p]))"
    using squarefree_mult_coprime[OF cop ss_snoc.IH(1) squarefree_prime[OF pr]] by simp
  show "prime_factors (prod_list (ps @ [p])) = set (ps @ [p])"
    using ss_snoc.IH(2) qpos pr
    by (simp add: prime_factors_product prime_prime_factors)
  show "distinct (ps @ [p])"
    using ss_snoc.IH(3) pn by simp
qed

lemma ss_exists: "\<exists>ps. ss ps \<and> length ps = k"
proof (induction k)
  case 0
  then show ?case by (auto intro: ss_Nil)
next
  case (Suc k)
  then obtain ps where ps: "ss ps" "length ps = k" by blast
  obtain p where p: "prime p" "p > prod_list ps" using bigger_prime by blast
  from ps p show ?case by (intro exI[of _ "ps @ [p]"]) (auto intro: ss_snoc)
qed

subsection \<open>Main theorem\<close>

theorem erdos_1100_eq_omega:
  "\<exists>n. squarefree n \<and> card (prime_factors n) = k \<and> tau_perp n = k"
proof -
  obtain ps where ps: "ss ps" "length ps = k" using ss_exists by blast
  have "squarefree (prod_list ps)" using ss_squarefree_omega(1)[OF ps(1)] .
  moreover have "card (prime_factors (prod_list ps)) = k"
    using ss_squarefree_omega(2,3)[OF ps(1)] ps(2)
    by (simp add: distinct_card)
  moreover have "tau_perp (prod_list ps) = k"
    unfolding tau_perp_def using ss_divs[OF ps(1)] ss_cc[OF ps(1)] ps(2) cc_card by simp
  ultimately show ?thesis by blast
qed

end
