(*  Title:      Caballero_Divisor_Words.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
*)

section \<open>Divisor words: \<open>D\<^sub>n \<setminus> 2D\<^sub>n = D\<^sub>m\<close>, \<open>2D\<^sub>n \<setminus> D\<^sub>n = 2\<^sup>e D\<^sub>m\<close>, and the word is Dyck\<close>

theory Caballero_Divisor_Words
  imports "HOL-Number_Theory.Number_Theory"
begin

text \<open>
  Let \<open>D\<^sub>n\<close> be the set of divisors of \<open>n\<close> and \<open>n = 2\<^sup>e\<^sup>-\<^sup>1 m\<close> with \<open>m\<close> odd, \<open>e \<ge> 1\<close>. We prove
  \<^item> \<open>D\<^sub>n \<setminus> 2D\<^sub>n = D\<^sub>m\<close> and \<open>2D\<^sub>n \<setminus> D\<^sub>n = 2\<^sup>e D\<^sub>m\<close> (the reduction lemma);
  \<^item> the word \<open>f(n)\<close>, the increasing list of \<open>(D\<^sub>n \<setminus> 2D\<^sub>n) \<union> (2D\<^sub>n \<setminus> D\<^sub>n)\<close> with each odd element read as an
    opening letter (\<open>True\<close>) and each even one as a closing letter (\<open>False\<close>), has \<open>\<tau>(m)\<close> openings and
    \<open>\<tau>(m)\<close> closings;
  \<^item> every prefix of \<open>f(n)\<close> has at least as many openings as closings (it is a Dyck word), by pairing \<open>d\<close>
    with \<open>2\<^sup>e d > d\<close>.
\<close>

definition divs :: "nat \<Rightarrow> nat set" where "divs n = {d. d dvd n}"

definition dword :: "nat \<Rightarrow> bool list" where
  "dword n = map odd (sorted_list_of_set
     ((divs n - (*) 2 ` divs n) \<union> ((*) 2 ` divs n - divs n)))"

lemma odd_dvd_pow2_mult:
  fixes d m k :: nat
  assumes "odd d" shows "d dvd 2 ^ k * m \<longleftrightarrow> d dvd m"
proof -
  have "coprime d (2 ^ k)"
    using assms by (simp add: coprime_commute coprime_power_right_iff)
  then show ?thesis by (simp add: coprime_dvd_mult_right_iff)
qed

lemma diff_two_D:
  assumes "odd m" "n = 2 ^ e' * m"
  shows "divs n - (*) 2 ` divs n = divs m"
proof (rule set_eqI, rule iffI)
  fix d assume h: "d \<in> divs n - (*) 2 ` divs n"
  hence dn: "d dvd n" and nimg: "d \<notin> (*) 2 ` divs n" by (auto simp: divs_def)
  have "odd d"
  proof (rule ccontr)
    assume "\<not> odd d"
    then obtain k where k: "d = 2 * k" by auto
    have "k dvd d" using k by simp
    hence "k dvd n" using dn by (rule dvd_trans)
    hence "d \<in> (*) 2 ` divs n" using k by (auto simp: divs_def)
    with nimg show False by blast
  qed
  thus "d \<in> divs m" using dn assms(2) odd_dvd_pow2_mult by (simp add: divs_def)
next
  fix d assume h: "d \<in> divs m"
  hence dm: "d dvd m" by (simp add: divs_def)
  have od: "odd d" using dm assms(1) by (metis dvd_def even_mult_iff)
  have dn: "d dvd n" using dm assms(2) by simp
  have "d \<notin> (*) 2 ` divs n"
  proof
    assume "d \<in> (*) 2 ` divs n"
    then obtain k where "d = 2 * k" by auto
    with od show False by simp
  qed
  with dn show "d \<in> divs n - (*) 2 ` divs n" by (simp add: divs_def)
qed

lemma diff_D_two:
  assumes "odd m" "n = 2 ^ e' * m"
  shows "(*) 2 ` divs n - divs n = (*) (2 ^ Suc e') ` divs m"
proof (rule set_eqI, rule iffI)
  fix x assume h: "x \<in> (*) 2 ` divs n - divs n"
  then obtain d where x: "x = 2 * d" and dn: "d dvd n" and nx: "\<not> x dvd n"
    by (auto simp: divs_def)
  from dn assms(2) obtain b c where d: "d = b * c" and b: "b dvd 2 ^ e'" and c: "c dvd m"
    using division_decomp by blast
  from b obtain i where i: "i \<le> e'" "b = 2 ^ i" using divides_primepow[of 2 b e'] by auto
  have "i = e'"
  proof (rule ccontr)
    assume "i \<noteq> e'"
    with i have lt: "Suc i \<le> e'" by simp
    have "(2::nat) ^ Suc i dvd 2 ^ e'" by (rule le_imp_power_dvd[OF lt])
    hence "2 ^ Suc i * c dvd 2 ^ e' * m" using c by (rule mult_dvd_mono)
    moreover have "x = 2 ^ Suc i * c" using x d i by simp
    ultimately show False using nx assms(2) by simp
  qed
  hence "x = 2 ^ Suc e' * c" using x d i by simp
  thus "x \<in> (*) (2 ^ Suc e') ` divs m" using c by (auto simp: divs_def)
next
  fix x assume h: "x \<in> (*) (2 ^ Suc e') ` divs m"
  then obtain c where x: "x = 2 ^ Suc e' * c" and c: "c dvd m" by (auto simp: divs_def)
  have "2 ^ e' * c dvd n" using c assms(2) by (simp add: mult_dvd_mono)
  moreover have "x = 2 * (2 ^ e' * c)" using x by simp
  ultimately have in2: "x \<in> (*) 2 ` divs n" by (auto simp: divs_def)
  have "\<not> x dvd n"
  proof
    assume "x dvd n"
    hence "2 ^ e' * (2 * c) dvd 2 ^ e' * m" using x assms(2) by (simp add: mult_ac)
    hence "2 * c dvd m" by simp
    then obtain r where "m = 2 * c * r" unfolding dvd_def by auto
    with assms(1) show False by simp
  qed
  with in2 show "x \<in> (*) 2 ` divs n - divs n" by (simp add: divs_def)
qed

text \<open>The abstract Dyck argument: pair \<open>a\<close> with \<open>t a > a\<close>.\<close>

lemma dyck_general:
  fixes A :: "nat set" and t :: nat
  assumes fin: "finite A" and odd: "\<forall>a\<in>A. odd a" and t: "even t" "t \<ge> 2"
  defines "S \<equiv> A \<union> (*) t ` A"
  shows "length (filter Not (map odd (take k (sorted_list_of_set S))))
         \<le> length (filter id (map odd (take k (sorted_list_of_set S))))"
proof -
  have finS: "finite S" using fin by (simp add: S_def)
  define L where "L = sorted_list_of_set S"
  define P where "P = take k L"
  have sorted: "sorted_wrt (<) L" using finS by (simp add: L_def)
  have setL: "set L = S" using finS by (simp add: L_def)
  have distL: "distinct L" using finS by (simp add: L_def)
  have dP: "distinct P" using distL by (simp add: P_def)
  have LPQ: "L = P @ drop k L" by (simp add: P_def)
  have down: "\<And>y p. y \<in> S \<Longrightarrow> p \<in> set P \<Longrightarrow> y < p \<Longrightarrow> y \<in> set P"
  proof -
    fix y p assume y: "y \<in> S" and p: "p \<in> set P" and lt: "y < p"
    show "y \<in> set P"
    proof (rule ccontr)
      assume "y \<notin> set P"
      with y setL LPQ have "y \<in> set (drop k L)" by (metis Un_iff set_append)
      moreover from sorted LPQ have "sorted_wrt (<) (P @ drop k L)" by simp
      ultimately have "p < y" using p by (auto simp: sorted_wrt_append)
      with lt show False by simp
    qed
  qed
  let ?E = "{x \<in> set P. even x}" and ?O = "{x \<in> set P. odd x}"
  have lhs: "length (filter Not (map odd P)) = card ?E"
    by (simp add: filter_map o_def distinct_card[OF distinct_filter[OF dP], symmetric] set_filter
        Collect_conj_eq del: distinct_filter)
  have rhs: "length (filter id (map odd P)) = card ?O"
    by (simp add: filter_map o_def distinct_card[OF distinct_filter[OF dP], symmetric] set_filter
        Collect_conj_eq del: distinct_filter)
  have fP: "finite (set P)" by simp
  have key: "\<And>x. x \<in> ?E \<Longrightarrow> \<exists>a\<in>A. x = t * a"
  proof -
    fix x assume "x \<in> ?E"
    hence xS: "x \<in> S" and ev: "even x" using setL P_def by (auto dest: in_set_takeD)
    hence "x \<in> A \<or> x \<in> (*) t ` A" by (simp add: S_def)
    thus "\<exists>a\<in>A. x = t * a"
    proof
      assume "x \<in> A" with odd ev show ?thesis by auto
    next
      assume "x \<in> (*) t ` A" thus ?thesis by auto
    qed
  qed
  have "card ?E = card ((\<lambda>x. x div t) ` ?E)"
  proof (rule card_image[symmetric], rule inj_onI)
    fix x y assume x: "x \<in> ?E" and y: "y \<in> ?E" and e: "x div t = y div t"
    from key[OF x] key[OF y] obtain a b where "x = t * a" "y = t * b" by blast
    with e t show "x = y" by simp
  qed
  also have "\<dots> \<le> card ?O"
  proof (rule card_mono)
    show "finite ?O" using fP by simp
    show "(\<lambda>x. x div t) ` ?E \<subseteq> ?O"
    proof
      fix z assume "z \<in> (\<lambda>x. x div t) ` ?E"
      then obtain x where x: "x \<in> ?E" and z: "z = x div t" by auto
      from key[OF x] obtain a where a: "a \<in> A" "x = t * a" by blast
      have za: "z = a" using z a t by simp
      have oa: "odd a" using odd a by simp
      have "a > 0" using oa by (cases a) auto
      have "2 * a \<le> t * a" using t(2) by (rule mult_le_mono1)
      hence lt: "a < x" using a(2) `a > 0` by linarith
      have aS: "a \<in> S" using a by (simp add: S_def)
      have "x \<in> set P" using x by simp
      from down[OF aS this lt] oa za show "z \<in> ?O" by simp
    qed
  qed
  finally show ?thesis using lhs rhs by (simp add: P_def L_def)
qed

text \<open>Main statements for \<open>n = 2^(e-1) m\<close>, \<open>m\<close> odd, \<open>e \<ge> 1\<close>.\<close>

theorem reduction_lemma:
  assumes "odd m" "e \<ge> 1" "n = 2 ^ (e - 1) * m"
  shows "divs n - (*) 2 ` divs n = divs m"
    and "(*) 2 ` divs n - divs n = (*) (2 ^ e) ` divs m"
proof -
  obtain e' where e: "e = Suc e'" using assms(2) by (cases e) auto
  have n: "n = 2 ^ e' * m" using assms(3) e by simp
  show "divs n - (*) 2 ` divs n = divs m" by (rule diff_two_D[OF assms(1) n])
  show "(*) 2 ` divs n - divs n = (*) (2 ^ e) ` divs m" using diff_D_two[OF assms(1) n] e by simp
qed

theorem dword_counts_and_dyck:
  assumes "odd m" "e \<ge> 1" "n = 2 ^ (e - 1) * m"
  shows "length (filter id (dword n)) = card (divs m)"
    and "length (filter Not (dword n)) = card (divs m)"
    and "\<And>k. length (filter Not (take k (dword n))) \<le> length (filter id (take k (dword n)))"
proof -
  have m0: "m > 0" using assms(1) by (cases m) auto
  have fin: "finite (divs m)" using m0 by (simp add: divs_def)
  have odd: "\<forall>a\<in>divs m. odd a" unfolding divs_def using assms(1) by (metis dvd_def even_mult_iff mem_Collect_eq)
  have ev: "even (2 ^ e :: nat)" using assms(2) by simp
  have t2: "(2 ^ e :: nat) \<ge> 2"
  proof -
    have "(2::nat) ^ 1 \<le> 2 ^ e" using assms(2) by (rule power_increasing) simp
    thus ?thesis by simp
  qed
  have S: "(divs n - (*) 2 ` divs n) \<union> ((*) 2 ` divs n - divs n) = divs m \<union> (*) (2 ^ e) ` divs m"
    using reduction_lemma[OF assms] by simp
  have W: "dword n = map odd (sorted_list_of_set (divs m \<union> (*) (2 ^ e) ` divs m))"
    using S by (simp add: dword_def)
  have finS: "finite (divs m \<union> (*) (2 ^ e) ` divs m)" using fin by simp
  let ?S = "divs m \<union> (*) (2 ^ e) ` divs m"
  have dL: "distinct (sorted_list_of_set ?S)" using finS by simp
  have setL: "set (sorted_list_of_set ?S) = ?S" using finS by simp
  have inj: "inj_on ((*) (2 ^ e :: nat)) (divs m)" by (rule inj_onI) simp
  have opens: "length (filter id (dword n)) = card {x \<in> ?S. odd x}"
    using W dL setL by (simp add: filter_map o_def distinct_card[OF distinct_filter[OF dL], symmetric] set_filter
        Collect_conj_eq del: distinct_filter)
  have closes: "length (filter Not (dword n)) = card {x \<in> ?S. even x}"
    using W dL setL by (simp add: filter_map o_def distinct_card[OF distinct_filter[OF dL], symmetric] set_filter
        Collect_conj_eq del: distinct_filter)
  have o: "{x \<in> ?S. odd x} = divs m" using odd ev by auto
  have c: "{x \<in> ?S. even x} = (*) (2 ^ e) ` divs m" using odd ev by auto
  show "length (filter id (dword n)) = card (divs m)" using opens o by simp
  show "length (filter Not (dword n)) = card (divs m)" using closes c card_image[OF inj] by simp
  show "\<And>k. length (filter Not (take k (dword n))) \<le> length (filter id (take k (dword n)))"
    unfolding W take_map using dyck_general[OF fin odd ev t2, of _] by (simp add: take_map)
qed

end
