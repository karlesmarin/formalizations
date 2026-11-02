(*  Title:      Perfect_Difference_Bound.thy
    Author:     Carles Marin

    The greedy perfect difference set with the least admissible new element (Lev 2004, Section 3)
    has a_n <= 70 n^3, where a_n is the larger element of the representation of n.
    This is erdos_1194.variants.greedy_upper_bound of google-deepmind/formal-conjectures.
    Admissibility is phrased with sums (Sidon property), so that every forbidden value of the new
    element z is one of 8 functions of a triple of old elements: at most 8 m^3 of them.
*)

theory Perfect_Difference_Bound
  imports Perfect_Difference_Set HOL.Real
begin

section \<open>Sidon sets\<close>

definition sidon :: "nat set \<Rightarrow> bool" where
  "sidon A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>A. \<forall>c\<in>A. \<forall>e\<in>A.
      a + b = c + e \<longrightarrow> (a = c \<and> b = e) \<or> (a = e \<and> b = c))"

lemma sidon_uniq:
  assumes s: "sidon A" shows "uniq A"
  unfolding uniq_def
proof (intro ballI impI)
  fix a b c e
  assume m: "a \<in> A" "b \<in> A" "c \<in> A" "e \<in> A" and ba: "b < a" and ec: "e < c"
    and eq: "a - b = c - e"
  have "a + e = c + b" using ba ec eq by arith
  then have "(a = c \<and> e = b) \<or> (a = b \<and> e = c)"
    using s m unfolding sidon_def by blast
  then show "a = c \<and> b = e" using ba by auto
qed

lemma sidon_insert:
  assumes s: "sidon A"
    and h1: "\<And>x y u. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> u \<in> A \<Longrightarrow> x + y \<noteq> z + u"
    and h2: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x + y \<noteq> 2 * z"
  shows "sidon (insert z A)"
  unfolding sidon_def
proof (intro ballI impI)
  fix a b c e
  assume a: "a \<in> insert z A" and b: "b \<in> insert z A" and c: "c \<in> insert z A"
    and e: "e \<in> insert z A" and eq: "a + b = c + e"
  have sA: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> c \<in> A \<Longrightarrow> e \<in> A \<Longrightarrow> (a = c \<and> b = e) \<or> (a = e \<and> b = c)"
    using s eq unfolding sidon_def by blast
  show "(a = c \<and> b = e) \<or> (a = e \<and> b = c)"
    using a b c e sA eq h1[of c e b] h1[of c e a] h1[of a b e] h1[of a b c] h2[of c e] h2[of a b]
    by auto
qed

section \<open>Admissible new elements\<close>

definition adm :: "nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "adm A z \<longleftrightarrow> 0 < z \<and> (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>u\<in>A.
      x + y \<noteq> z + u \<and> x + y \<noteq> 2 * z \<and> x + y \<noteq> z + gap A + u \<and> x + y \<noteq> 2 * z + gap A \<and>
      x + y \<noteq> 2 * z + 2 * gap A \<and> u \<noteq> z + gap A \<and> u \<noteq> z + 2 * gap A \<and> z \<noteq> gap A + u)"

lemma nd_gap:
  assumes fin: "finite A" and x: "x \<in> A" and y: "y \<in> A"
  shows "x \<noteq> y + gap A"
proof
  assume xy: "x = y + gap A"
  have g: "0 < gap A" "gap A \<notin> pdiffs A" using gap[OF fin] by auto
  then have "y < x" "x - y = gap A" using xy by auto
  then have "gap A \<in> pdiffs A" unfolding pdiffs_iff using x y by blast
  then show False using g by blast
qed

lemma adm_sidon:
  assumes fin: "finite A" and s: "sidon A" and ad: "adm A z"
  shows "sidon (A \<union> {z, z + gap A})"
proof -
  define d where "d = gap A"
  define w where "w = z + d"
  have dpos: "0 < d" using gap[OF fin] by (simp add: d_def)
  have H: "\<And>x y u. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> u \<in> A \<Longrightarrow>
      x + y \<noteq> z + u \<and> x + y \<noteq> 2 * z \<and> x + y \<noteq> z + d + u \<and> x + y \<noteq> 2 * z + d \<and>
      x + y \<noteq> 2 * z + 2 * d \<and> u \<noteq> z + d \<and> u \<noteq> z + 2 * d \<and> z \<noteq> d + u"
    using ad unfolding adm_def d_def by blast
  have nd: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y + d"
    using nd_gap[OF fin] by (simp add: d_def)
  have s1: "sidon (insert z A)"
    by (rule sidon_insert[OF s]) (use H in blast)+
  have h1: "x + y \<noteq> w + u"
    if x: "x \<in> insert z A" and y: "y \<in> insert z A" and u: "u \<in> insert z A" for x y u
    using x y u H[of x y u] H[of x y x] H[of u u u] H[of y y y] H[of x x x] nd[of y u] nd[of x u] dpos
    unfolding w_def by auto
  have h2: "x + y \<noteq> 2 * w"
    if x: "x \<in> insert z A" and y: "y \<in> insert z A" for x y
    using x y H[of x y x] H[of y y y] H[of x x x] dpos
    unfolding w_def by auto
  have s2: "sidon (insert w (insert z A))"
    by (rule sidon_insert[OF s1]) (use h1 h2 in blast)+
  have "A \<union> {z, z + gap A} = insert w (insert z A)"
    unfolding w_def d_def by auto
  then show ?thesis using s2 by simp
qed

section \<open>Counting the forbidden values\<close>

definition badf :: "nat \<Rightarrow> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat" where
  "badf d = (\<lambda>(x, y, u, i).
     if i = 0 then x + y - u else if i = 1 then (x + y) div 2
     else if i = 2 then x + y - d - u else if i = 3 then (x + y - d) div 2
     else if i = 4 then (x + y - 2 * d) div 2 else if i = 5 then u - d
     else if i = 6 then u - 2 * d else d + u)"

lemma adm_if_not_bad:
  assumes z: "0 < z" and nb: "z \<notin> badf (gap A) ` (A \<times> A \<times> A \<times> {..<8})"
  shows "adm A z"
proof -
  define d where "d = gap A"
  have key: "x + y \<noteq> z + u \<and> x + y \<noteq> 2 * z \<and> x + y \<noteq> z + d + u \<and> x + y \<noteq> 2 * z + d \<and>
      x + y \<noteq> 2 * z + 2 * d \<and> u \<noteq> z + d \<and> u \<noteq> z + 2 * d \<and> z \<noteq> d + u"
    if x: "x \<in> A" and y: "y \<in> A" and u: "u \<in> A" for x y u
  proof -
  have n: "z \<noteq> badf d (x, y, u, i)" if "i < 8" for i
  proof -
    have "(x, y, u, i) \<in> A \<times> A \<times> A \<times> {..<8}" using x y u that by simp
    then have "badf d (x, y, u, i) \<in> badf d ` (A \<times> A \<times> A \<times> {..<8})" by (rule imageI)
    then show ?thesis using nb unfolding d_def by auto
  qed
  have n0: "z \<noteq> x + y - u" using n[of 0] by (simp add: badf_def)
  have n1: "z \<noteq> (x + y) div 2" using n[of 1] by (simp add: badf_def)
  have n2: "z \<noteq> x + y - d - u" using n[of 2] by (simp add: badf_def)
  have n3: "z \<noteq> (x + y - d) div 2" using n[of 3] by (simp add: badf_def)
  have n4: "z \<noteq> (x + y - 2 * d) div 2" using n[of 4] by (simp add: badf_def)
  have n5: "z \<noteq> u - d" using n[of 5] by (simp add: badf_def)
  have n6: "z \<noteq> u - 2 * d" using n[of 6] by (simp add: badf_def)
  have n7: "z \<noteq> d + u" using n[of 7] by (simp add: badf_def)
  show ?thesis
  proof (intro conjI notI)
    assume "x + y = z + u" then show False using n0 by arith
  next
    assume "x + y = 2 * z" then show False using n1 by simp
  next
    assume "x + y = z + d + u" then show False using n2 by arith
  next
    assume "x + y = 2 * z + d" then show False using n3 by simp
  next
    assume "x + y = 2 * z + 2 * d" then show False using n4 by simp
  next
    assume "u = z + d" then show False using n5 by simp
  next
    assume "u = z + 2 * d" then show False using n6 by simp
  next
    assume "z = d + u" then show False using n7 by simp
  qed
  qed
  show ?thesis
    unfolding adm_def d_def[symmetric] using z key by blast
qed

lemma avoid: assumes "finite G" shows "\<exists>z\<in>{1..card G + 1}. z \<notin> G"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "{1..card G + 1} \<subseteq> G" by blast
  then have "card {1..card G + 1} \<le> card G" using assms by (rule card_mono[rotated])
  then show False by simp
qed

lemma adm_exists:
  assumes fin: "finite A"
  shows "\<exists>z. adm A z \<and> z \<le> 8 * card A ^ 3 + 1"
proof -
  let ?G = "badf (gap A) ` (A \<times> A \<times> A \<times> {..<8})"
  have finG: "finite ?G" using fin by simp
  have "card ?G \<le> card (A \<times> A \<times> A \<times> {..<8::nat})" by (rule card_image_le) (simp add: fin)
  also have "\<dots> = 8 * card A ^ 3" by (simp add: card_cartesian_product power3_eq_cube mult_ac)
  finally have cG: "card ?G \<le> 8 * card A ^ 3" .
  obtain z where z: "z \<in> {1..card ?G + 1}" "z \<notin> ?G" using avoid[OF finG] by blast
  then have "adm A z" using adm_if_not_bad[of z A] by auto
  moreover have "z \<le> 8 * card A ^ 3 + 1" using z cG by auto
  ultimately show ?thesis by blast
qed

definition zmin :: "nat set \<Rightarrow> nat" where
  "zmin A = (LEAST z. adm A z)"

lemma zmin:
  assumes fin: "finite A"
  shows "adm A (zmin A) \<and> zmin A \<le> 8 * card A ^ 3 + 1"
proof -
  obtain z where z: "adm A z" "z \<le> 8 * card A ^ 3 + 1" using adm_exists[OF fin] by blast
  have "adm A (zmin A)" unfolding zmin_def using z(1) by (rule LeastI)
  moreover have "zmin A \<le> z" unfolding zmin_def using z(1) by (rule Least_le)
  ultimately show ?thesis using z(2) by simp
qed

lemma card_pdiffs: assumes fin: "finite A" shows "card (pdiffs A) \<le> card A ^ 2"
proof -
  have "pdiffs A \<subseteq> (\<lambda>p. fst p - snd p) ` (A \<times> A)"
    unfolding pdiffs_def by force
  then have "card (pdiffs A) \<le> card ((\<lambda>p. fst p - snd p) ` (A \<times> A))"
    using fin by (simp add: card_mono)
  also have "\<dots> \<le> card (A \<times> A)" by (rule card_image_le) (simp add: fin)
  also have "\<dots> = card A ^ 2" by (simp add: card_cartesian_product power2_eq_square)
  finally show ?thesis .
qed

lemma gap_le: assumes fin: "finite A" shows "gap A \<le> card A ^ 2 + 1"
proof -
  have finP: "finite (pdiffs A)" by (rule pdiffs_finite[OF fin])
  obtain n where n: "n \<in> {1..card (pdiffs A) + 1}" "n \<notin> pdiffs A"
    using avoid[OF finP] by blast
  then have "gap A \<le> n" unfolding gap_def by (intro Least_le) simp
  then show ?thesis using n(1) card_pdiffs[OF fin] by auto
qed

section \<open>The greedy sequence with the least admissible element\<close>

definition step2 :: "nat set \<Rightarrow> nat set" where
  "step2 A = A \<union> {zmin A, zmin A + gap A}"

primrec seq2 :: "nat \<Rightarrow> nat set" where
  "seq2 0 = {}"
| "seq2 (Suc k) = step2 (seq2 k)"

lemma step2_sub: "A \<subseteq> step2 A"
  unfolding step2_def by blast

lemma cube_step: "64 * k ^ 3 + 4 * k ^ 2 + 2 \<le> 70 * (Suc k) ^ 3"
proof -
  have e: "(Suc k) ^ 3 = k ^ 3 + 3 * k ^ 2 + 3 * k + 1"
    by (simp add: power3_eq_cube power2_eq_square algebra_simps)
  show ?thesis unfolding e by (auto simp: algebra_simps)
qed

lemma seq2_props:
  "finite (seq2 k) \<and> sidon (seq2 k) \<and> 0 \<notin> seq2 k \<and> {1..k} \<subseteq> pdiffs (seq2 k) \<and>
   card (seq2 k) \<le> 2 * k \<and> (\<forall>x\<in>seq2 k. x \<le> 70 * k ^ 3)"
proof (induction k)
  case 0
  then show ?case by (simp add: sidon_def)
next
  case (Suc k)
  define A where "A = seq2 k"
  define z where "z = zmin A"
  define d where "d = gap A"
  have fin: "finite A" and s: "sidon A" and z0: "0 \<notin> A" and cov: "{1..k} \<subseteq> pdiffs A"
    and cA: "card A \<le> 2 * k" and bA: "\<forall>x\<in>A. x \<le> 70 * k ^ 3"
    using Suc by (auto simp: A_def)
  have st: "step2 A = A \<union> {z, z + d}" unfolding step2_def z_def d_def by simp
  have zm: "adm A z" "z \<le> 8 * card A ^ 3 + 1" using zmin[OF fin] by (auto simp: z_def)
  have dpos: "0 < d" and dnot: "d \<notin> pdiffs A" using gap[OF fin] by (auto simp: d_def)
  have "finite (step2 A)" using fin st by simp
  moreover have "sidon (step2 A)"
    using adm_sidon[OF fin s zm(1)] st by (simp add: d_def)
  moreover have "0 \<notin> step2 A" using z0 zm(1) st by (auto simp: adm_def)
  moreover have "{1..Suc k} \<subseteq> pdiffs (step2 A)"
  proof
    fix n assume n: "n \<in> {1..Suc k}"
    have dstep: "d \<in> pdiffs (step2 A)"
    proof -
      have "z \<in> step2 A" "z + d \<in> step2 A" "z < z + d" "(z + d) - z = d" using st dpos by auto
      then show ?thesis unfolding pdiffs_iff by blast
    qed
    show "n \<in> pdiffs (step2 A)"
    proof (cases "n \<le> k")
      case True
      then have "n \<in> pdiffs A" using cov n by auto
      then show ?thesis using pdiffs_mono[OF step2_sub] by blast
    next
      case False
      then have nk: "n = Suc k" using n by auto
      show ?thesis
      proof (cases "n < d")
        case True
        then have "n \<in> pdiffs A" using gap_least n by (auto simp: d_def)
        then show ?thesis using pdiffs_mono[OF step2_sub] by blast
      next
        case False
        have "d \<notin> {1..k}" using dnot cov by blast
        then have "Suc k \<le> d" using dpos by auto
        then have "n = d" using False nk by simp
        then show ?thesis using dstep by simp
      qed
    qed
  qed
  moreover have "card (step2 A) \<le> 2 * Suc k"
  proof -
    have "card {z, z + d} \<le> 2" by (cases "z = z + d") simp_all
    then have "card (step2 A) \<le> card A + 2" using st card_Un_le[of A "{z, z + d}"] by simp
    then show ?thesis using cA by simp
  qed
  moreover have "\<forall>x\<in>step2 A. x \<le> 70 * (Suc k) ^ 3"
  proof
    fix x assume x: "x \<in> step2 A"
    have m3: "card A ^ 3 \<le> 8 * k ^ 3"
    proof -
      have "card A ^ 3 \<le> (2 * k) ^ 3" using cA by (rule power_mono) simp
      then show ?thesis by (simp add: power_mult_distrib)
    qed
    have m2: "card A ^ 2 \<le> 4 * k ^ 2"
    proof -
      have "card A ^ 2 \<le> (2 * k) ^ 2" using cA by (rule power_mono) simp
      then show ?thesis by (simp add: power_mult_distrib)
    qed
    have zb: "z \<le> 64 * k ^ 3 + 1" using zm(2) m3 by linarith
    have db: "d \<le> 4 * k ^ 2 + 1" using gap_le[OF fin] m2 unfolding d_def by linarith
    have kk: "k ^ 3 \<le> (Suc k) ^ 3" by (rule power_mono) simp_all
    have c: "64 * k ^ 3 + 4 * k ^ 2 + 2 \<le> 70 * (Suc k) ^ 3" by (rule cube_step)
    have kk70: "70 * k ^ 3 \<le> 70 * (Suc k) ^ 3" using kk by simp
    consider (old) "x \<in> A" | (new1) "x = z" | (new2) "x = z + d" using x st by auto
    then show "x \<le> 70 * (Suc k) ^ 3"
    proof cases
      case old
      then have "x \<le> 70 * k ^ 3" using bA by blast
      then show ?thesis using kk70 by linarith
    next
      case new1
      then show ?thesis using zb c by linarith
    next
      case new2
      then show ?thesis using zb db c by linarith
    qed
  qed
  ultimately show ?case by (simp add: A_def)
qed

definition S2 :: "nat set" where
  "S2 = (\<Union>k. seq2 k)"

lemma S2_uniq: "uniq S2"
  unfolding S2_def
  by (rule uniq_chain) (simp_all add: step2_sub sidon_uniq seq2_props)

lemma S2_zero: "0 \<notin> S2"
  unfolding S2_def using seq2_props by blast

lemma S2_cov: "0 < n \<Longrightarrow> n \<in> pdiffs S2"
proof -
  assume "0 < n"
  then have "n \<in> pdiffs (seq2 n)" using seq2_props[of n] by auto
  moreover have "seq2 n \<subseteq> S2" unfolding S2_def by blast
  ultimately show ?thesis using pdiffs_mono by blast
qed

section \<open>The cubic bound as stated in formal-conjectures\<close>

text \<open>\<open>IsLargerElement A n a\<close> of formal-conjectures is \<open>a \<in> A \<and> \<exists>b \<in> A, a = b + n\<close>.\<close>

theorem greedy_upper_bound:
  "\<exists>A :: nat set. (0 \<notin> A \<and>
     bij_betw (\<lambda>(a, b). int a - int b) {(a, b). a \<in> A \<and> b \<in> A \<and> a \<noteq> b} {x :: int. x \<noteq> 0}) \<and>
     (\<exists>C :: real. \<forall>n. 0 < n \<longrightarrow> (\<forall>a. (a \<in> A \<and> (\<exists>b\<in>A. a = b + n)) \<longrightarrow> real a \<le> C * real n ^ 3))"
proof (intro exI conjI)
  show "0 \<notin> S2" by (rule S2_zero)
  show "bij_betw (\<lambda>(a, b). int a - int b) {(a, b). a \<in> S2 \<and> b \<in> S2 \<and> a \<noteq> b} {x :: int. x \<noteq> 0}"
    by (rule bij_of_uniq[OF S2_uniq S2_cov])
  show "\<forall>n. 0 < n \<longrightarrow> (\<forall>a. (a \<in> S2 \<and> (\<exists>b\<in>S2. a = b + n)) \<longrightarrow> real a \<le> 70 * real n ^ 3)"
  proof (intro allI impI)
    fix n a assume n: "0 < n" and h: "a \<in> S2 \<and> (\<exists>b\<in>S2. a = b + n)"
    then obtain b where a: "a \<in> S2" and b: "b \<in> S2" and ab: "a = b + n" by blast
    have "n \<in> pdiffs (seq2 n)" using seq2_props[of n] n by auto
    then obtain a0 b0 where a0: "a0 \<in> seq2 n" and b0: "b0 \<in> seq2 n" and lt: "b0 < a0"
      and d0: "a0 - b0 = n"
      unfolding pdiffs_iff by blast
    have sub: "seq2 n \<subseteq> S2" unfolding S2_def by blast
    have "b < a" "a - b = a0 - b0" using ab n d0 by auto
    then have "a = a0"
      using S2_uniq a b a0 b0 sub lt unfolding uniq_def by blast
    then have "a \<le> 70 * n ^ 3" using seq2_props[of n] a0 by auto
    then have "real a \<le> real (70 * n ^ 3)" by (simp only: of_nat_le_iff)
    then show "real a \<le> 70 * real n ^ 3" by simp
  qed
qed

end
