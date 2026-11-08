(*  Title:      Prime_Degree_Family.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

section \<open>An unsolvable polynomial of every prime degree\<close>

theory Prime_Degree_Family
  imports Prime_Degree_Criterion
begin

text \<open>For a prime \<open>p \<ge> 5\<close> put \<open>k = (p - 3) div 2\<close> and
  $f_p(x) = x\,\bigl(x^2 + 2(k+1)^3\bigr)\prod_{i=1}^{k}\bigl(x^2 - 4i^2\bigr) - 2$.
  (1) Every non-leading coefficient is even and the constant term is \<open>-2\<close>, so \<open>f\<^sub>p\<close> is irreducible by
  Eisenstein's criterion at 2. (2) At the odd integers \<open>\<plusminus>1, \<plusminus>3, \<dots>, \<plusminus>(2k+1)\<close> the product has absolute value at
  least $2(k+1)^3 + 1 > 2$ and alternating sign, so \<open>f\<^sub>p\<close> has at least \<open>p - 2\<close> real roots. (3) \<open>f\<^sub>p\<close> has no
  term in $x^{p-1}$ and a positive coefficient \<open>c\<close> of $x^{p-2}$; by Vieta's formulas the squares of its \<open>p\<close>
  complex roots sum to \<open>-2c < 0\<close>, so not all of them are real. Since non-real roots come in conjugate
  pairs, exactly two are non-real, and the criterion applies.\<close>

definition fam_k :: "nat \<Rightarrow> nat" where "fam_k p = (p - 3) div 2"

definition fam :: "nat \<Rightarrow> int poly" where
  "fam p = [:0, 1:] * [:2 * (int (fam_k p) + 1) ^ 3, 0, 1:]
           * (\<Prod>i\<in>{1..fam_k p}. [:- (4 * int i ^ 2), 0, 1:]) - [:2:]"

definition famC :: "nat \<Rightarrow> complex poly" where "famC p = map_poly of_int (fam p)"

definition famR :: "nat \<Rightarrow> real poly" where "famR p = map_poly of_int (fam p)"

subsection \<open>Auxiliary lemmas on the coefficients\<close>


lemma ex_Suc1: "1 \<le> j \<Longrightarrow> \<exists>j'. j = Suc j'"
  by (cases j) auto

lemma ex_Suc2: "2 \<le> j \<Longrightarrow> \<exists>j'. j = Suc (Suc j')"
  by (cases j) (use ex_Suc1 in auto)

lemma prod_Suc_1: "(\<Prod>i\<in>{1..Suc n}. f i) = (\<Prod>i\<in>{1..n}. f i) * (f (Suc n) :: 'a::comm_monoid_mult)"
  by (simp add: atLeastAtMostSuc_conv mult.commute)

lemma sum_Suc_1: "(\<Sum>i\<in>{1..Suc n}. f i) = (\<Sum>i\<in>{1..n}. f i) + (f (Suc n) :: 'a::comm_monoid_add)"
  by (simp add: atLeastAtMostSuc_conv add.commute)

lemma coeff_quad_0: "coeff (q * [:b, 0, 1:]) 0 = b * coeff (q :: 'a::comm_ring_1 poly) 0"
  by (simp add: mult_pCons_right)

lemma coeff_quad_1: "coeff (q * [:b, 0, 1:]) 1 = b * coeff (q :: 'a::comm_ring_1 poly) 1"
  by (simp add: mult_pCons_right coeff_pCons)

lemma coeff_quad_2: "coeff (q * [:b, 0, 1:]) (Suc (Suc j))
    = coeff (q :: 'a::comm_ring_1 poly) j + b * coeff q (Suc (Suc j))"
  by (simp add: mult_pCons_right coeff_pCons)

lemma coeff_lin_0: "coeff ([:b, 1:] * q) 0 = b * coeff (q :: 'a::comm_ring_1 poly) 0"
  by (simp add: mult_pCons_left)

lemma coeff_lin_Suc: "coeff ([:b, 1:] * q) (Suc j) = coeff (q :: 'a::comm_ring_1 poly) j + b * coeff q (Suc j)"
  by (simp add: mult_pCons_left coeff_pCons)

subsection \<open>The even product\<close>

definition famG :: "nat \<Rightarrow> int poly" where
  "famG n = (\<Prod>i\<in>{1..n}. [:- (4 * int i ^ 2), 0, 1:])"

lemma famG_0 [simp]: "famG 0 = 1" by (simp add: famG_def)

lemma famG_Suc: "famG (Suc n) = famG n * [:- (4 * int (Suc n) ^ 2), 0, 1:]"
  by (simp add: famG_def prod_Suc_1)

lemma famG_props:
  "(\<forall>j>2*n. coeff (famG n) j = 0) \<and> coeff (famG n) (2*n) = 1
   \<and> (\<forall>j. coeff (famG n) (2*j+1) = 0)
   \<and> (\<forall>m. n = Suc m \<longrightarrow> coeff (famG n) (2*m) = - (\<Sum>i\<in>{1..n}. 4 * int i ^ 2))
   \<and> (\<forall>j. j \<noteq> 2*n \<longrightarrow> even (coeff (famG n) j))"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define b where "b = - (4 * int (Suc n) ^ 2)"
  have even_b: "even b" unfolding b_def by simp
  have step: "famG (Suc n) = famG n * [:b, 0, 1:]" by (simp add: famG_Suc b_def)
  have A: "\<And>j. 2*n < j \<Longrightarrow> coeff (famG n) j = 0" using Suc.IH by blast
  have B: "coeff (famG n) (2*n) = 1" using Suc.IH by blast
  have C: "\<And>j. coeff (famG n) (2*j+1) = 0" using Suc.IH by blast
  have D: "\<And>m. n = Suc m \<Longrightarrow> coeff (famG n) (2*m) = - (\<Sum>i\<in>{1..n}. 4 * int i ^ 2)"
    using Suc.IH by blast
  have E: "\<And>j. j \<noteq> 2*n \<Longrightarrow> even (coeff (famG n) j)" using Suc.IH by blast
  have p1: "\<forall>j>2*Suc n. coeff (famG (Suc n)) j = 0"
  proof (intro allI impI)
    fix j assume j: "2 * Suc n < j"
    obtain j' where jj: "j = Suc (Suc j')" using ex_Suc2[of j] j by auto
    have "coeff (famG n) j' = 0" using A j jj by simp
    moreover have "coeff (famG n) (Suc (Suc j')) = 0" using A j jj by simp
    ultimately show "coeff (famG (Suc n)) j = 0" by (simp add: step jj coeff_quad_2)
  qed
  have p2: "coeff (famG (Suc n)) (2 * Suc n) = 1"
  proof -
    have "2 * Suc n = Suc (Suc (2*n))" by simp
    then show ?thesis using A B by (simp add: step coeff_quad_2)
  qed
  have p3: "\<forall>j. coeff (famG (Suc n)) (2*j+1) = 0"
  proof
    fix j show "coeff (famG (Suc n)) (2*j+1) = 0"
    proof (cases j)
      case 0
      then show ?thesis using C[of 0] by (simp add: step coeff_quad_1)
    next
      case (Suc j')
      have "2*j+1 = Suc (Suc (2*j'+1))" using Suc by simp
      then show ?thesis using C[of j'] C[of j] Suc by (simp add: step coeff_quad_2)
    qed
  qed
  have p4: "\<forall>m. Suc n = Suc m \<longrightarrow> coeff (famG (Suc n)) (2*m) = - (\<Sum>i\<in>{1..Suc n}. 4 * int i ^ 2)"
  proof (intro allI impI)
    fix m assume "Suc n = Suc m"
    then have mn: "m = n" by simp
    show "coeff (famG (Suc n)) (2*m) = - (\<Sum>i\<in>{1..Suc n}. 4 * int i ^ 2)"
    proof (cases n)
      case 0
      have "coeff (famG (Suc n)) (2*m) = b"
      proof -
        have "coeff (famG (Suc n)) (2*m) = coeff (famG n * [:b, 0, 1:]) (2*m)" by (simp only: step)
        also have "\<dots> = b * coeff (famG n) 0" using mn 0 by (simp add: coeff_quad_0)
        also have "\<dots> = b" using 0 by simp
        finally show ?thesis .
      qed
      moreover have "b = - (\<Sum>i\<in>{1..Suc n}. 4 * int i ^ 2)" using 0 by (simp add: b_def)
      ultimately show ?thesis by simp
    next
      case (Suc n')
      have "2 * n = Suc (Suc (2*n'))" using Suc by simp
      moreover have "coeff (famG n) (2*n') = - (\<Sum>i\<in>{1..n}. 4 * int i ^ 2)" using D Suc by blast
      ultimately show ?thesis
        using B mn by (simp add: step coeff_quad_2 sum_Suc_1 b_def)
    qed
  qed
  have p5: "\<forall>j. j \<noteq> 2 * Suc n \<longrightarrow> even (coeff (famG (Suc n)) j)"
  proof (intro allI impI)
    fix j assume j: "j \<noteq> 2 * Suc n"
    show "even (coeff (famG (Suc n)) j)"
    proof (cases j)
      case 0
      then show ?thesis using even_b by (simp add: step coeff_quad_0)
    next
      case (Suc j1)
      show ?thesis
      proof (cases j1)
        case 0
        then show ?thesis using Suc even_b by (simp add: step coeff_quad_1)
      next
        case (Suc j2)
        have "j2 \<noteq> 2 * n" using j Suc \<open>j = Suc j1\<close> by simp
        then have "even (coeff (famG n) j2)" using E by blast
        then show ?thesis using \<open>j = Suc j1\<close> Suc even_b by (simp add: step coeff_quad_2)
      qed
    qed
  qed
  show ?case using p1 p2 p3 p4 p5 by blast
qed

lemma sum_squares_formula: "3 * (\<Sum>i\<in>{1..n}. 4 * int i ^ 2) = 2 * int n * (int n + 1) * (2 * int n + 1)"
  by (induction n) (auto simp: sum_Suc_1 algebra_simps power2_eq_square)


lemma fam_k_eq: assumes "odd p" "3 \<le> p" shows "p = 2 * fam_k p + 3"
proof -
  obtain m where "p = 2 * m + 1" using assms(1) by (rule oddE)
  then show ?thesis using assms(2) unfolding fam_k_def by arith
qed

lemma fam_alt: "fam p = [:0, 1:] * ([:2 * (int (fam_k p) + 1) ^ 3, 0, 1:] * famG (fam_k p)) - [:2:]"
  by (simp add: fam_def famG_def mult.assoc)

lemma coeff_fam_Suc:
  "coeff (fam p) (Suc j) = coeff (famG (fam_k p) * [:2 * (int (fam_k p) + 1) ^ 3, 0, 1:]) j"
  by (simp add: fam_alt mult.commute)

lemma coeff_fam_zero: "coeff (fam p) 0 = -2"
  by (simp add: fam_alt)

lemma fam_top:
  assumes "odd p" "3 \<le> p"
  shows "(\<forall>j>p. coeff (fam p) j = 0)" and "coeff (fam p) p = 1" and "\<forall>j<p. even (coeff (fam p) j)"
proof -
  define k where "k = fam_k p"
  define C where "C = 2 * (int k + 1) ^ 3"
  have even_C: "even C" unfolding C_def by simp
  have pk: "p = 2 * k + 3" using fam_k_eq[OF assms] k_def by simp
  have A: "\<And>j. 2*k < j \<Longrightarrow> coeff (famG k) j = 0" using famG_props[of k] by blast
  have B: "coeff (famG k) (2*k) = 1" using famG_props[of k] by blast
  have E: "\<And>j. j \<noteq> 2*k \<Longrightarrow> even (coeff (famG k) j)" using famG_props[of k] by blast
  show "\<forall>j>p. coeff (fam p) j = 0"
  proof (intro allI impI)
    fix j assume j: "p < j"
    obtain j1 where j1: "j = Suc j1" using ex_Suc1[of j] j by auto
    obtain j2 where j2: "j1 = Suc (Suc j2)" using ex_Suc2[of j1] j j1 pk by auto
    have "coeff (famG k) j2 = 0" "coeff (famG k) (Suc (Suc j2)) = 0" using A j j1 j2 pk by auto
    then show "coeff (fam p) j = 0"
      by (simp add: j1 j2 coeff_fam_Suc coeff_quad_2 k_def[symmetric] C_def[symmetric])
  qed
  show "coeff (fam p) p = 1"
  proof -
    have e: "coeff (fam p) p = coeff (fam p) (Suc (Suc (Suc (2*k))))"
      by (rule arg_cong[where f = "coeff (fam p)"]) (simp add: pk)
    have "coeff (famG k) (Suc (Suc (2*k))) = 0" using A by simp
    then have "coeff (fam p) (Suc (Suc (Suc (2*k)))) = 1" using B
      by (simp add: coeff_fam_Suc coeff_quad_2 k_def[symmetric] C_def[symmetric])
    then show ?thesis using e by simp
  qed
  show "\<forall>j<p. even (coeff (fam p) j)"
  proof (intro allI impI)
    fix j assume j: "j < p"
    show "even (coeff (fam p) j)"
    proof (cases j)
      case 0
      then show ?thesis by (simp add: coeff_fam_zero)
    next
      case (Suc j1)
      show ?thesis
      proof (cases j1)
        case 0
        then show ?thesis using Suc even_C
          by (simp add: coeff_fam_Suc coeff_quad_0 k_def[symmetric] C_def[symmetric])
      next
        case (Suc j2)
        show ?thesis
        proof (cases j2)
          case 0
          then show ?thesis using \<open>j = Suc j1\<close> Suc even_C
            by (simp add: coeff_fam_Suc coeff_quad_1 k_def[symmetric] C_def[symmetric])
        next
          case (Suc j3)
          have "j3 \<noteq> 2 * k" using j pk \<open>j = Suc j1\<close> \<open>j1 = Suc j2\<close> Suc by simp
          then have "even (coeff (famG k) j3)" by (rule E)
          then show ?thesis using \<open>j = Suc j1\<close> \<open>j1 = Suc j2\<close> Suc even_C
            by (simp add: coeff_fam_Suc coeff_quad_2 k_def[symmetric] C_def[symmetric])
        qed
      qed
    qed
  qed
qed

lemma fam_next:
  assumes "odd p" "5 \<le> p"
  shows "coeff (fam p) (p - 1) = 0"
    and "coeff (fam p) (p - 2) = 2 * (int (fam_k p) + 1) ^ 3 - (\<Sum>i\<in>{1..fam_k p}. 4 * int i ^ 2)"
proof -
  define k where "k = fam_k p"
  define C where "C = 2 * (int k + 1) ^ 3"
  have pk: "p = 2 * k + 3" using fam_k_eq[of p] assms k_def by simp
  obtain m where km: "k = Suc m" using pk assms(2) by (cases k) auto
  have B: "coeff (famG k) (2*k) = 1" using famG_props[of k] by blast
  have C1: "\<And>j. coeff (famG k) (2*j+1) = 0" using famG_props[of k] by blast
  have D: "coeff (famG k) (2*m) = - (\<Sum>i\<in>{1..k}. 4 * int i ^ 2)" using famG_props[of k] km by blast
  have e1: "p - 1 = Suc (Suc (Suc (2*m+1)))" using pk km by simp
  have e2: "p - 2 = Suc (Suc (Suc (2*m)))" using pk km by simp
  have g1: "coeff (famG k) (Suc (2*m)) = 0" using C1[of m] by simp
  have g2: "coeff (famG k) (Suc (Suc (Suc (2*m)))) = 0"
  proof -
    have "Suc (Suc (Suc (2*m))) = 2 * (m+1) + 1" by simp
    then show ?thesis using C1[of "m+1"] by simp
  qed
  have g3: "coeff (famG k) (Suc (Suc (2*m))) = 1" using B km by simp
  show "coeff (fam p) (p - 1) = 0"
    using g1 g2 by (subst e1) (simp add: coeff_fam_Suc coeff_quad_2 k_def[symmetric] C_def[symmetric])
  show "coeff (fam p) (p - 2) = 2 * (int (fam_k p) + 1) ^ 3 - (\<Sum>i\<in>{1..fam_k p}. 4 * int i ^ 2)"
    using D g3 km by (subst e2) (simp add: coeff_fam_Suc coeff_quad_2 k_def[symmetric] C_def[symmetric])
qed

subsection \<open>Degree and coefficients\<close>

lemma degree_fam:
  assumes "odd p" "3 \<le> p" shows "degree (fam p) = p"
proof (rule antisym)
  show "degree (fam p) \<le> p" by (rule degree_le) (use fam_top(1)[OF assms] in auto)
  show "p \<le> degree (fam p)" by (rule le_degree) (use fam_top(2)[OF assms] in simp)
qed

lemma lead_coeff_fam:
  assumes "odd p" "3 \<le> p" shows "lead_coeff (fam p) = 1"
  using degree_fam[OF assms] fam_top(2)[OF assms] by simp

lemma coeff_fam_even:
  assumes "odd p" "3 \<le> p" "i < p" shows "2 dvd coeff (fam p) i"
  using fam_top(3)[OF assms(1,2)] assms(3) by blast

lemma coeff_fam_0: "coeff (fam p) 0 = -2"
  by (rule coeff_fam_zero)

subsection \<open>Irreducibility\<close>

lemma content_fam:
  assumes "odd p" "3 \<le> p" shows "Polynomial.content (fam p) = 1"
proof -
  have e: "coeff (fam p) p = 1" by (rule fam_top(2)[OF assms])
  have d: "Polynomial.content (fam p) dvd 1" using Polynomial.content_dvd_coeff[of "fam p" p, unfolded e] .
  have "Polynomial.content (fam p) = normalize (Polynomial.content (fam p))"
    by (rule sym[OF Polynomial.normalize_content])
  also have "\<dots> = 1" by (rule is_unit_normalize[OF d])
  finally show ?thesis .
qed

text \<open>A degree-0 factor of @{term "fam p"} is a unit (the polynomial is primitive).\<close>
lemma fam_deg0_factor_unit:
  assumes ok: "Polynomial.content (fam p) = 1" and eq: "fam p = smult c q"
  shows "[:c:] dvd 1"
proof -
  have c1: "Polynomial.content (smult c q) = 1" using ok[unfolded eq] .
  have "Polynomial.content (smult c q) = normalize c * Polynomial.content q" by (rule Polynomial.content_smult)
  then have "1 = normalize c * Polynomial.content q" using c1 by simp
  then have "normalize c dvd 1" by (rule dvdI)
  then show "[:c:] dvd 1" by (simp add: is_unit_const_poly_iff)
qed

lemma irreducible_fam:
  assumes "odd p" "5 \<le> p" shows "irreducible (fam p)"
proof (rule irreducibleI)
  have p3: "3 \<le> p" using assms(2) by simp
  have dg: "degree (fam p) = p" by (rule degree_fam[OF assms(1) p3])
  have ok: "Polynomial.content (fam p) = 1" by (rule content_fam[OF assms(1) p3])
  show "fam p \<noteq> 0" using dg assms(2) by auto
  show "\<not> fam p dvd 1" using dg assms(2) by (auto dest!: dvd_imp_degree_le)
next
  fix a b assume eq: "fam p = a * b"
  have p3: "3 \<le> p" using assms(2) by simp
  have dg: "degree (fam p) = p" by (rule degree_fam[OF assms(1) p3])
  have ok: "Polynomial.content (fam p) = 1" by (rule content_fam[OF assms(1) p3])
  show "a dvd 1 \<or> b dvd 1"
  proof (rule ccontr)
    assume nd: "\<not> (a dvd 1 \<or> b dvd 1)"
    have sec: False if "degree a = 0 \<or> degree b = 0"
    proof -
      show False
      proof (cases "degree a = 0")
        case True
        then obtain c where ac: "a = [:c:]" by (rule degree_eq_zeroE)
        have "fam p = smult c b" using eq ac by simp
        then have "[:c:] dvd 1" by (rule fam_deg0_factor_unit[OF ok])
        then have "a dvd 1" using ac by simp
        with nd show False by simp
      next
        case False
        then have "degree b = 0" using that by simp
        then obtain c where bc: "b = [:c:]" by (rule degree_eq_zeroE)
        have "fam p = smult c a" using eq bc by simp
        then have "[:c:] dvd 1" by (rule fam_deg0_factor_unit[OF ok])
        then have "b dvd 1" using bc by simp
        with nd show False by simp
      qed
    qed
    have dga: "0 < degree a"
    proof (rule ccontr)
      assume "\<not> 0 < degree a"
      then have "degree a = 0" by simp
      then show False using sec by blast
    qed
    have dgb: "0 < degree b"
    proof (rule ccontr)
      assume "\<not> 0 < degree b"
      then have "degree b = 0" by simp
      then show False using sec by blast
    qed
    have l2: "\<not> (2::int) dvd lead_coeff (fam p)" using lead_coeff_fam[OF assms(1) p3] by simp
    have mid: "\<And>i. i < degree (fam p) \<Longrightarrow> (2::int) dvd coeff (fam p) i"
    proof -
      fix i assume "i < degree (fam p)"
      then have "i < p" using dg by simp
      then show "(2::int) dvd coeff (fam p) i" by (rule coeff_fam_even[OF assms(1) p3])
    qed
    have c2: "\<not> (2::int)^2 dvd coeff (fam p) 0"
    proof -
      have "\<not> (4::int) dvd -2" by presburger
      then show ?thesis unfolding coeff_fam_0 by simp
    qed
    show False
      by (rule Quintic_Example.eisenstein_no_factor[of 2 "fam p" a b, OF _ eq l2 mid c2 dga dgb]) simp
  qed
qed

lemma famC_poly_over_Rats: "famC p \<in> poly_over (\<rat> :: complex set)"
  by (simp add: famC_def coeff_map_poly poly_over_iff_aux)

lemma map_of_rat_of_int_fam:
  "map_poly of_rat (map_poly of_int (fam p) :: rat poly) = (famC p :: complex poly)"
  by (simp add: famC_def map_poly_map_poly o_def)

theorem irreducible_over_Rats_famC:
  assumes "odd p" "5 \<le> p" shows "irreducible_over (\<rat> :: complex set) (famC p)"
proof -
  have p3: "3 \<le> p" using assms(2) by simp
  have dg: "degree (fam p) \<noteq> 0" using degree_fam[OF assms(1) p3] assms(2) by simp
  have "irreducible (map_poly of_int (fam p) :: rat poly)"
    using irreducible_fam[OF assms] dg content_fam[OF assms(1) p3]
    by (metis Polynomial_Factorial.irreducible_int_imp_rat)
  moreover have "degree (map_poly of_int (fam p) :: rat poly) > 0"
    using dg by (simp add: degree_map_poly)
  ultimately show ?thesis
    using irreducible_imp_irreducible_over_Rats map_of_rat_of_int_fam by fastforce
qed

subsection \<open>Real roots\<close>


lemma poly_famG: "poly (famG n) x = (\<Prod>i\<in>{1..n}. x^2 - 4 * int i ^ 2)"
  unfolding famG_def poly_prod by (rule prod.cong) (simp_all add: power2_eq_square)

definition gz :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "gz k x = x * (x^2 + 2 * (int k + 1)^3) * (\<Prod>i\<in>{1..k}. x^2 - 4 * int i ^ 2)"

lemma poly_fam: "poly (fam p) x = gz (fam_k p) x - 2"
  by (simp add: fam_alt poly_famG gz_def algebra_simps power2_eq_square)

lemma gz_odd: "gz k (-x) = - gz k x" by (simp add: gz_def)

lemma sign_odd_prod:
  assumes "m \<le> n"
  shows "0 < (-1::int)^(n - m) * (\<Prod>i\<in>{1..n}. (2 * int m + 1)^2 - 4 * int i ^ 2)"
proof -
  obtain d where n: "n = m + d" using assms by (metis le_Suc_ex)
  define g where "g i = (2 * int m + 1)^2 - 4 * int i ^ 2" for i :: nat
  have "0 < (-1::int)^d * (\<Prod>i\<in>{1..m+d}. g i)"
  proof (induction d)
    case 0
    have "0 < (\<Prod>i\<in>{1..m}. g i)"
    proof (rule prod_pos)
      fix i assume "i \<in> {1..m}"
      then have h1: "int i \<le> int m" by simp
      have h2: "0 \<le> int i" by simp
      have h3: "0 \<le> int m" by simp
      have p1: "0 < 2 * int m + 1 - 2 * int i" using h1 by linarith
      have p2: "0 < 2 * int m + 1 + 2 * int i" using h2 h3 by linarith
      have "0 < (2 * int m + 1 - 2 * int i) * (2 * int m + 1 + 2 * int i)"
        by (rule mult_pos_pos[OF p1 p2])
      moreover have "(2 * int m + 1 - 2 * int i) * (2 * int m + 1 + 2 * int i) = g i"
        unfolding g_def by (simp add: algebra_simps power2_eq_square)
      ultimately show "0 < g i" by simp
    qed
    then show ?case by simp
  next
    case (Suc d)
    have md: "0 \<le> int m" "0 \<le> int d" by simp_all
    have q1: "0 < 2 * int d + 1" using md by linarith
    have q2: "0 < 4 * int m + 2 * int d + 3" using md by linarith
    have "0 < (2 * int d + 1) * (4 * int m + 2 * int d + 3)" by (rule mult_pos_pos[OF q1 q2])
    moreover have "(2 * int d + 1) * (4 * int m + 2 * int d + 3) = - g (Suc (m+d))"
      unfolding g_def by (simp add: algebra_simps power2_eq_square)
    ultimately have neg: "0 < - g (Suc (m+d))" by simp
    have eq: "(-1::int)^(Suc d) * (\<Prod>i\<in>{1..m+Suc d}. g i)
        = ((-1)^d * (\<Prod>i\<in>{1..m+d}. g i)) * (- g (Suc (m+d)))"
      by (simp add: prod_Suc_1)
    have "0 < ((-1::int)^d * (\<Prod>i\<in>{1..m+d}. g i)) * (- g (Suc (m+d)))"
      by (rule mult_pos_pos[OF Suc.IH neg])
    then show ?case using eq by simp
  qed
  then show ?thesis using n g_def by simp
qed

lemma gz_sign:
  assumes "m \<le> k" shows "3 \<le> (-1::int)^(k - m) * gz k (2 * int m + 1)"
proof -
  define x where "x = 2 * int m + 1"
  define u where "u = (-1::int)^(k - m) * (\<Prod>i\<in>{1..k}. x^2 - 4 * int i ^ 2)"
  have u1: "0 < u" unfolding u_def x_def by (rule sign_odd_prod[OF assms])
  then have u2: "1 \<le> u" by simp
  have x1: "1 \<le> x" unfolding x_def by simp
  have c1: "1 \<le> (int k + 1)^3" by (rule one_le_power) simp
  have x2: "1 \<le> x^2" using x1 by (rule one_le_power)
  have y3: "3 \<le> x^2 + 2 * (int k + 1)^3" using x2 c1 by linarith
  have A: "3 \<le> x * (x^2 + 2 * (int k + 1)^3)"
  proof -
    have "1 * (x^2 + 2 * (int k + 1)^3) \<le> x * (x^2 + 2 * (int k + 1)^3)"
      by (rule mult_right_mono) (use x1 y3 in linarith)+
    then have h: "x^2 + 2 * (int k + 1)^3 \<le> x * (x^2 + 2 * (int k + 1)^3)" by simp
    show ?thesis by (rule order_trans[OF y3 h])
  qed
  have "(-1::int)^(k-m) * gz k x = (x * (x^2 + 2 * (int k + 1)^3)) * u"
    unfolding gz_def u_def by (simp add: algebra_simps)
  moreover have "3 \<le> (x * (x^2 + 2 * (int k + 1)^3)) * u"
  proof -
    have "3 * 1 \<le> (x * (x^2 + 2 * (int k + 1)^3)) * u"
      by (rule mult_mono) (use A u2 in linarith)+
    then show ?thesis by linarith
  qed
  ultimately show ?thesis unfolding x_def by simp
qed

lemma gz_abs3:
  assumes "m \<le> k" shows "3 \<le> \<bar>gz k (2 * int m + 1)\<bar>"
proof -
  have "3 \<le> \<bar>(-1::int)^(k - m) * gz k (2 * int m + 1)\<bar>"
    using gz_sign[OF assms] by (rule order_trans) (rule abs_ge_self)
  then show ?thesis by (simp add: abs_mult)
qed

lemma gz_alt:
  assumes "m < k" shows "gz k (2 * int m + 1) * gz k (2 * int (Suc m) + 1) < 0"
proof -
  define u where "u = (-1::int)^(k - Suc m)"
  have e: "k - m = Suc (k - Suc m)" using assms by arith
  have s1: "3 \<le> (-u) * gz k (2 * int m + 1)" using gz_sign[of m k] assms e u_def by simp
  have s2: "3 \<le> u * gz k (2 * int (Suc m) + 1)" using gz_sign[of "Suc m" k] assms u_def by simp
  have uu: "u * u = 1" unfolding u_def by (simp flip: power_mult_distrib)
  define a where "a = gz k (2 * int m + 1)"
  define b where "b = gz k (2 * int (Suc m) + 1)"
  have "3 * 3 \<le> ((-u) * a) * (u * b)"
    by (rule mult_mono) (use s1 s2 in \<open>simp add: a_def b_def; linarith\<close>)+
  then have h9: "9 \<le> ((-u) * a) * (u * b)" by simp
  have eq: "((-u) * a) * (u * b) = - ((u * u) * (a * b))" by algebra
  have h3: "9 \<le> - ((u * u) * (a * b))" using h9[unfolded eq] .
  have h4: "9 \<le> - (1 * (a * b))" using h3[unfolded uu] .
  then show ?thesis unfolding a_def b_def by simp
qed

lemma ineq_prod:
  fixes a b :: int
  assumes "3 \<le> \<bar>a\<bar>" "3 \<le> \<bar>b\<bar>" "a * b < 0"
  shows "(a - 2) * (b - 2) < 0"
proof -
  have "(0 < a \<and> b < 0) \<or> (a < 0 \<and> 0 < b)" using assms(3) by (simp add: mult_less_0_iff)
  then show ?thesis
  proof
    assume h: "0 < a \<and> b < 0"
    then have "3 \<le> a" using assms(1) by (simp add: abs_of_pos)
    then have "0 < a - 2" by simp
    moreover have "b - 2 < 0" using h by simp
    ultimately show ?thesis by (rule mult_pos_neg)
  next
    assume h: "a < 0 \<and> 0 < b"
    then have "3 \<le> b" using assms(2) by (simp add: abs_of_pos)
    then have "0 < b - 2" by simp
    moreover have "a - 2 < 0" using h by simp
    ultimately show ?thesis by (metis mult_neg_pos)
  qed
qed

lemma gz_consec:
  assumes "j \<le> 2 * k" and T: "t = 2 * int j - (2 * int k + 1)"
  shows "gz k t * gz k (t + 2) < 0 \<and> 3 \<le> \<bar>gz k t\<bar> \<and> 3 \<le> \<bar>gz k (t + 2)\<bar>"
proof -
  consider "k < j" | "j = k" | "j < k" by linarith
  then show ?thesis
  proof cases
    case 1
    then obtain m where jm: "j = Suc k + m" by (metis Suc_le_eq le_Suc_ex)
    have mk: "m < k" using jm assms(1) by arith
    have ij: "int j = int k + 1 + int m" using jm by simp
    have t1: "t = 2 * int m + 1" using ij T by linarith
    have t2: "t + 2 = 2 * int (Suc m) + 1" using ij T by simp
    have e1: "gz k t = gz k (2 * int m + 1)" by (simp only: t1)
    have e2: "gz k (t + 2) = gz k (2 * int (Suc m) + 1)" by (simp only: t2)
    show ?thesis unfolding e1 e2 using gz_alt[OF mk] gz_abs3[of m k] gz_abs3[of "Suc m" k] mk by simp
  next
    case 2
    have t1: "t = - 1" using 2 T by simp
    have t2: "t + 2 = 1" using t1 by simp
    have h3: "3 \<le> \<bar>gz k 1\<bar>" using gz_abs3[of 0 k] by simp
    have od: "gz k (-1) = - gz k 1" using gz_odd[of k 1] by simp
    have e1: "gz k t = - gz k 1" using od by (simp only: t1)
    have e2: "gz k (t + 2) = gz k 1" by (simp only: t2)
    have "3 * 3 \<le> \<bar>gz k 1\<bar> * \<bar>gz k 1\<bar>" by (rule mult_mono) (use h3 in linarith)+
    then have "9 \<le> gz k 1 * gz k 1" using abs_mult_self_eq[of "gz k 1"] by simp
    then show ?thesis unfolding e1 e2 using h3 by simp
  next
    case 3
    then obtain m where km: "k = Suc j + m" by (metis Suc_le_eq le_Suc_ex)
    have mk: "m < k" using km by arith
    have mk2: "Suc m \<le> k" using km by arith
    have ik: "int k = int j + 1 + int m" using km by simp
    have t1: "t = - (2 * int (Suc m) + 1)" using ik T by simp
    have t2: "t + 2 = - (2 * int m + 1)" using ik T by simp
    have e1: "gz k t = - gz k (2 * int (Suc m) + 1)" using gz_odd[of k "2 * int (Suc m) + 1"]
      by (simp only: t1)
    have e2: "gz k (t + 2) = - gz k (2 * int m + 1)" using gz_odd[of k "2 * int m + 1"]
      by (simp only: t2)
    show ?thesis unfolding e1 e2 using gz_alt[OF mk] gz_abs3[of m k] gz_abs3[of "Suc m" k] mk2
      by (simp add: mult.commute)
  qed
qed

lemma fam_consec_poly:
  assumes "j \<le> 2 * fam_k p"
  shows "poly (fam p) (2 * int j - (2 * int (fam_k p) + 1))
       * poly (fam p) (2 * int j - (2 * int (fam_k p) + 1) + 2) < 0"
proof -
  have c: "gz (fam_k p) (2 * int j - (2 * int (fam_k p) + 1)) * gz (fam_k p) (2 * int j - (2 * int (fam_k p) + 1) + 2) < 0
    \<and> 3 \<le> \<bar>gz (fam_k p) (2 * int j - (2 * int (fam_k p) + 1))\<bar>
    \<and> 3 \<le> \<bar>gz (fam_k p) (2 * int j - (2 * int (fam_k p) + 1) + 2)\<bar>"
    by (rule gz_consec[OF assms refl])
  show ?thesis unfolding poly_fam by (rule ineq_prod) (use c in blast)+
qed

lemma poly_map_of_int: "poly (map_poly of_int q :: 'a::comm_ring_1 poly) (of_int x) = of_int (poly q x)"
  by (induction q rule: pCons_induct) (simp_all add: map_poly_pCons)

lemma famR_eval: "poly (famR p) (of_int x) = of_int (poly (fam p) x)"
  unfolding famR_def by (rule poly_map_of_int)

lemma coeff_famR: "coeff (famR p) i = of_int (coeff (fam p) i)"
  by (simp add: famR_def coeff_map_poly)

lemma coeff_famC: "coeff (famC p) i = of_int (coeff (fam p) i)"
  by (simp add: famC_def coeff_map_poly)

lemma famR_ne0: assumes "odd p" "3 \<le> p" shows "famR p \<noteq> 0"
proof
  assume "famR p = 0"
  then have "coeff (famR p) p = 0" by simp
  then show False using fam_top(2)[OF assms] by (simp add: coeff_famR)
qed

lemma root_between:
  fixes P :: "real poly" and a b :: real
  assumes "a < b" "poly P a * poly P b < 0"
  shows "\<exists>x. a < x \<and> x < b \<and> poly P x = 0"
proof -
  have "(0 < poly P a \<and> poly P b < 0) \<or> (poly P a < 0 \<and> 0 < poly P b)"
    using assms(2) by (simp add: mult_less_0_iff)
  then show ?thesis
  proof
    assume "0 < poly P a \<and> poly P b < 0"
    then show ?thesis using poly_IVT_neg[OF assms(1)] by blast
  next
    assume "poly P a < 0 \<and> 0 < poly P b"
    then show ?thesis using poly_IVT_pos[OF assms(1)] by blast
  qed
qed

lemma famR_real_roots_ge:
  assumes "odd p" "5 \<le> p" shows "p - 2 \<le> card {x::real. poly (famR p) x = 0}"
proof -
  define k where "k = fam_k p"
  have pk: "p = 2 * k + 3" using fam_k_eq[of p] assms k_def by simp
  have ex_tt: "\<exists>tt :: nat \<Rightarrow> int. \<forall>j. tt j = 2 * int j - (2 * int (fam_k p) + 1)"
    by (rule exI[of _ "\<lambda>j. 2 * int j - (2 * int (fam_k p) + 1)"]) simp
  then obtain tt :: "nat \<Rightarrow> int" where tt_all: "\<forall>j. tt j = 2 * int j - (2 * int (fam_k p) + 1)" by blast
  have tt_def: "\<And>j. tt j = 2 * int j - (2 * int (fam_k p) + 1)" using tt_all by blast
  have ex: "\<forall>j. \<exists>x. j \<le> 2 * k \<longrightarrow> (real_of_int (tt j) < x \<and> x < real_of_int (tt j) + 2
                                    \<and> poly (famR p) x = 0)"
  proof
    fix j
    show "\<exists>x. j \<le> 2 * k \<longrightarrow> (real_of_int (tt j) < x \<and> x < real_of_int (tt j) + 2
                                    \<and> poly (famR p) x = 0)"
    proof (cases "j \<le> 2 * k")
      case True
      have h: "poly (fam p) (tt j) * poly (fam p) (tt j + 2) < 0"
      proof -
        have e1: "tt j = 2 * int j - (2 * int (fam_k p) + 1)" by (rule tt_def)
        have jk: "j \<le> 2 * fam_k p" using True k_def by simp
        show ?thesis unfolding e1 by (rule fam_consec_poly[OF jk])
      qed
      have h0: "(of_int (poly (fam p) (tt j) * poly (fam p) (tt j + 2)) :: real) < of_int 0"
        using h by (simp only: of_int_less_iff)
      then have hh: "(of_int (poly (fam p) (tt j)) :: real) * of_int (poly (fam p) (tt j + 2)) < 0"
        by simp
      have t2: "(of_int (tt j) + 2 :: real) = of_int (tt j + 2)" by simp
      have hr: "poly (famR p) (of_int (tt j)) * poly (famR p) (of_int (tt j) + 2) < 0"
        unfolding t2 famR_eval by (rule hh)
      from root_between[OF _ hr] obtain x where "of_int (tt j) < x" "x < of_int (tt j) + 2"
        "poly (famR p) x = 0" by auto
      then show ?thesis by blast
    qed blast
  qed
  then obtain r where hr: "\<And>j. j \<le> 2 * k \<Longrightarrow> real_of_int (tt j) < r j \<and> r j < real_of_int (tt j) + 2
                               \<and> poly (famR p) (r j) = 0"
    by metis
  have sub: "r ` {0..2*k} \<subseteq> {x. poly (famR p) x = 0}" using hr by auto
  have mono: "i < j \<Longrightarrow> real_of_int (tt i) + 2 \<le> real_of_int (tt j)" for i j
  proof -
    assume ij: "i < j"
    have "int i < int j" using ij by simp
    then have "tt i + 2 \<le> tt j" using tt_def[of i] tt_def[of j] by linarith
    then have "(of_int (tt i + 2) :: real) \<le> of_int (tt j)" by (simp only: of_int_le_iff)
    then show "real_of_int (tt i) + 2 \<le> real_of_int (tt j)" by simp
  qed
  have inj: "inj_on r {0..2*k}"
  proof (rule inj_onI)
    fix i j assume i: "i \<in> {0..2*k}" and j: "j \<in> {0..2*k}" and eq: "r i = r j"
    show "i = j"
    proof (rule ccontr)
      assume ne: "i \<noteq> j"
      then consider "i < j" | "j < i" by linarith
      then show False
      proof cases
        case 1
        have "r i < real_of_int (tt i) + 2" "real_of_int (tt j) < r j" using hr i j by auto
        then show False using mono[OF 1] eq by linarith
      next
        case 2
        have "r j < real_of_int (tt j) + 2" "real_of_int (tt i) < r i" using hr i j by auto
        then show False using mono[OF 2] eq by linarith
      qed
    qed
  qed
  have fin: "finite {x::real. poly (famR p) x = 0}" using famR_ne0[OF assms(1)] assms(2) poly_roots_finite by auto
  have "card (r ` {0..2*k}) \<le> card {x::real. poly (famR p) x = 0}" by (rule card_mono[OF fin sub])
  moreover have "card (r ` {0..2*k}) = 2 * k + 1" using inj by (simp add: card_image)
  ultimately show ?thesis using pk by simp
qed


lemma vieta:
  fixes A :: "'a::comm_ring_1 set"
  assumes fin: "finite A"
  shows "(\<forall>j>card A. coeff (\<Prod>a\<in>A. [:- a, 1:]) j = 0) \<and> coeff (\<Prod>a\<in>A. [:- a, 1:]) (card A) = 1
    \<and> (\<forall>m. card A = Suc m \<longrightarrow> coeff (\<Prod>a\<in>A. [:- a, 1:]) m = - (\<Sum>a\<in>A. a))
    \<and> (\<forall>m. card A = Suc (Suc m) \<longrightarrow>
        2 * coeff (\<Prod>a\<in>A. [:- a, 1:]) m = (\<Sum>a\<in>A. a)^2 - (\<Sum>a\<in>A. a^2))
    \<and> (card A \<le> 1 \<longrightarrow> (\<Sum>a\<in>A. a)^2 = (\<Sum>a\<in>A. a^2))"
  using fin
proof (induction A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  define q where "q = (\<Prod>x\<in>A. [:- x, 1:])"
  define n where "n = card A"
  define s where "s = (\<Sum>x\<in>A. x)"
  define s2 where "s2 = (\<Sum>x\<in>A. x^2)"
  have cA: "card (insert a A) = Suc n" using insert unfolding n_def by simp
  have pq: "(\<Prod>x\<in>insert a A. [:- x, 1:]) = [:- a, 1:] * q" using insert unfolding q_def by simp
  have ss: "(\<Sum>x\<in>insert a A. x) = a + s" using insert unfolding s_def by simp
  have ss2: "(\<Sum>x\<in>insert a A. x^2) = a^2 + s2" using insert unfolding s2_def by simp
  have I1: "\<And>j. n < j \<Longrightarrow> coeff q j = 0" using insert.IH unfolding q_def n_def by blast
  have I2: "coeff q n = 1" using insert.IH unfolding q_def n_def by blast
  have I3: "\<And>m. n = Suc m \<Longrightarrow> coeff q m = - s" using insert.IH unfolding q_def n_def s_def by blast
  have I4: "\<And>m. n = Suc (Suc m) \<Longrightarrow> 2 * coeff q m = s^2 - s2"
    using insert.IH unfolding q_def n_def s_def s2_def by blast
  have I5: "n \<le> 1 \<Longrightarrow> s^2 = s2" using insert.IH unfolding n_def s_def s2_def by blast
  have c1: "\<forall>j>Suc n. coeff ([:- a, 1:] * q) j = 0"
  proof (intro allI impI)
    fix j assume j: "Suc n < j"
    then obtain j' where jj: "j = Suc j'" by (cases j) auto
    show "coeff ([:- a, 1:] * q) j = 0" using j jj I1 by (simp add: coeff_lin_Suc)
  qed
  have c2: "coeff ([:- a, 1:] * q) (Suc n) = 1" using I1 I2 by (simp add: coeff_lin_Suc)
  have c3: "\<forall>m. Suc n = Suc m \<longrightarrow> coeff ([:- a, 1:] * q) m = - (a + s)"
  proof (intro allI impI)
    fix m assume "Suc n = Suc m"
    then have mn: "m = n" by simp
    show "coeff ([:- a, 1:] * q) m = - (a + s)"
    proof (cases n)
      case 0
      then have "s = 0" using insert unfolding s_def n_def by simp
      then show ?thesis using mn 0 I2 by (simp add: coeff_lin_0)
    next
      case (Suc j)
      then show ?thesis using mn I3[of j] I2 by (simp add: coeff_lin_Suc)
    qed
  qed
  have c4: "\<forall>m. Suc n = Suc (Suc m) \<longrightarrow> 2 * coeff ([:- a, 1:] * q) m = (a + s)^2 - (a^2 + s2)"
  proof (intro allI impI)
    fix m assume "Suc n = Suc (Suc m)"
    then have mn: "n = Suc m" by simp
    show "2 * coeff ([:- a, 1:] * q) m = (a + s)^2 - (a^2 + s2)"
    proof (cases m)
      case 0
      have "coeff q 0 = - s" using I3[of 0] mn 0 by simp
      moreover have "s^2 = s2" using I5 mn 0 by simp
      ultimately show ?thesis using 0 by (simp add: coeff_lin_0 algebra_simps power2_eq_square)
    next
      case (Suc j)
      have "2 * coeff q j = s^2 - s2" using I4[of j] mn Suc by simp
      moreover have "coeff q (Suc j) = - s" using I3[of "Suc j"] mn Suc by simp
      ultimately show ?thesis using Suc by (simp add: coeff_lin_Suc algebra_simps power2_eq_square)
    qed
  qed
  have c5: "Suc n \<le> 1 \<longrightarrow> (a + s)^2 = a^2 + s2"
  proof
    assume "Suc n \<le> 1"
    then have "n = 0" by simp
    then have "A = {}" using insert unfolding n_def by simp
    then show "(a + s)^2 = a^2 + s2" unfolding s_def s2_def by simp
  qed
  show ?case unfolding cA pq ss ss2 using c1 c2 c3 c4 c5 by blast
qed

lemma poly_map_of_real: "poly (map_poly of_real q :: complex poly) (of_real x) = of_real (poly q x)"
  by (induction q rule: pCons_induct) (simp_all add: map_poly_pCons)

lemma famC_of_real: "famC p = map_poly of_real (famR p)"
  by (intro poly_eqI) (simp add: coeff_famC coeff_famR coeff_map_poly)

lemma poly_famC_of_real: "poly (famC p) (of_real x) = of_real (poly (famR p) x)"
  by (simp add: famC_of_real poly_map_of_real)

lemma famC_degree:
  assumes "odd p" "5 \<le> p" shows "degree (famC p) = p" "lead_coeff (famC p) = 1" "famC p \<noteq> 0"
proof -
  have p3: "3 \<le> p" using assms(2) by simp
  show d: "degree (famC p) = p" unfolding famC_def
    using degree_fam[OF assms(1) p3] by (simp add: degree_map_poly)
  show "lead_coeff (famC p) = 1" using d fam_top(2)[OF assms(1) p3] by (simp add: coeff_famC)
  show "famC p \<noteq> 0" using d assms(2) by auto
qed

lemma famC_roots:
  assumes "odd p" "5 \<le> p"
  shows "rsquarefree (famC p)" "card {z. poly (famC p) z = 0} = p" "finite {z. poly (famC p) z = 0}"
proof -
  have rsf: "rsquarefree (famC p)"
    by (rule irreducible_over_Rats_rsquarefree[OF famC_poly_over_Rats irreducible_over_Rats_famC[OF assms]])
  show "rsquarefree (famC p)" by (rule rsf)
  show "card {z. poly (famC p) z = 0} = p"
    using card_roots_eq_degree[OF famC_degree(3)[OF assms] rsf] famC_degree(1)[OF assms] by simp
  show "finite {z. poly (famC p) z = 0}" using famC_degree(3)[OF assms] poly_roots_finite by blast
qed

lemma fam_c_pos: "0 < 2 * (int k + 1) ^ 3 - (\<Sum>i\<in>{1..k}. 4 * int i ^ 2)"
proof -
  have h: "3 * (\<Sum>i\<in>{1..k}. 4 * int i ^ 2) = 2 * int k * (int k + 1) * (2 * int k + 1)"
    by (rule sum_squares_formula)
  have kk: "0 \<le> int k" by simp
  have k2: "0 \<le> (int k)^2" by simp
  have q1: "0 < int k + 1" using kk by linarith
  have q2: "0 < (int k)^2 + 5 * int k + 3" using kk k2 by linarith
  have pos: "0 < 2 * (int k + 1) * ((int k)^2 + 5 * int k + 3)"
    by (rule mult_pos_pos[OF mult_pos_pos[OF _ q1] q2]) simp
  define c where "c = 2 * (int k + 1) ^ 3 - (\<Sum>i\<in>{1..k}. 4 * int i ^ 2)"
  have eq: "3 * c = 2 * (int k + 1) * ((int k)^2 + 5 * int k + 3)"
    unfolding c_def using h by algebra
  have "0 < 3 * c" using pos eq by simp
  then have "0 < c" by simp
  then show ?thesis unfolding c_def .
qed

lemma famR_not_all_real:
  assumes "odd p" "5 \<le> p" shows "card {x::real. poly (famR p) x = 0} < p"
proof (rule ccontr)
  assume "\<not> card {x::real. poly (famR p) x = 0} < p"
  then have ge: "p \<le> card {x::real. poly (famR p) x = 0}" by simp
  define R where "R = {x::real. poly (famR p) x = 0}"
  define Z where "Z = {z. poly (famC p) z = 0}"
  have p3: "3 \<le> p" using assms(2) by simp
  have cardZ: "card Z = p" and finZ: "finite Z" unfolding Z_def
    using famC_roots[OF assms] by simp_all
  have sub: "of_real ` R \<subseteq> Z" unfolding R_def Z_def by (auto simp: poly_famC_of_real)
  have cardR: "card (of_real ` R :: complex set) = card R"
    by (rule card_image) (use inj_of_real in \<open>auto simp: inj_on_def\<close>)
  have cle: "card (of_real ` R :: complex set) \<le> card Z" by (rule card_mono[OF finZ sub])
  have ge': "p \<le> card R" using ge unfolding R_def .
  have ceq: "card (of_real ` R :: complex set) = card Z" using cle cardR cardZ ge' by arith
  have eqZ: "of_real ` R = Z" by (rule card_subset_eq[OF finZ sub ceq])
  have decomp: "smult (lead_coeff (famC p)) (\<Prod>z | poly (famC p) z = 0. [:- z, 1:]) = famC p"
    by (rule complex_poly_decompose_rsquarefree[OF famC_roots(1)[OF assms]])
  have prodP: "famC p = (\<Prod>z\<in>Z. [:- z, 1:])"
    using decomp famC_degree(2)[OF assms] unfolding Z_def by simp
  obtain m where pm: "p = Suc (Suc m)" using ex_Suc2[of p] assms(2) by auto
  have i1: "p - 1 = Suc m" and i2: "p - 2 = m" using pm by simp_all
  define cc where "cc = 2 * (int (fam_k p) + 1) ^ 3 - (\<Sum>i\<in>{1..fam_k p}. 4 * int i ^ 2)"
  have a1: "coeff (famC p) (Suc m) = 0"
  proof -
    have "coeff (fam p) (Suc m) = 0" using fam_next(1)[OF assms] unfolding i1 .
    then show ?thesis by (simp add: coeff_famC)
  qed
  have a2: "coeff (famC p) m = of_int cc"
  proof -
    have "coeff (fam p) m = cc" using fam_next(2)[OF assms] unfolding i2 cc_def .
    then show ?thesis by (simp add: coeff_famC)
  qed
  have ccpos: "0 < cc" unfolding cc_def by (rule fam_c_pos)
  have cz: "card Z = Suc (Suc m)" using cardZ pm by simp
  note V = vieta[OF finZ]
  have v3: "coeff (\<Prod>z\<in>Z. [:- z, 1:]) (Suc m) = - (\<Sum>z\<in>Z. z)" using V cz by blast
  have v4: "2 * coeff (\<Prod>z\<in>Z. [:- z, 1:]) m = (\<Sum>z\<in>Z. z)^2 - (\<Sum>z\<in>Z. z^2)" using V cz by blast
  have s1: "(\<Sum>z\<in>Z. z) = 0" using v3 a1[unfolded prodP] by simp
  have t: "2 * (of_int cc :: complex) = (\<Sum>z\<in>Z. z)^2 - (\<Sum>z\<in>Z. z^2)"
    using v4 a2[unfolded prodP] by simp
  have s2: "(\<Sum>z\<in>Z. z^2) = - (2 * (of_int cc :: complex))" using t s1 by algebra
  have e: "(- (2 * of_int cc) :: complex) = of_real (- (2 * real_of_int cc))" by simp
  have s3: "(\<Sum>z\<in>Z. z^2) = of_real (- (2 * real_of_int cc))" using s2[unfolded e] .
  have re1: "Re (\<Sum>z\<in>Z. z^2) = - (2 * real_of_int cc)" unfolding s3 by (rule Re_complex_of_real)
  have nn: "\<And>z. z \<in> Z \<Longrightarrow> 0 \<le> Re (z^2)"
  proof -
    fix z assume zZ: "z \<in> Z"
    then have "z \<in> of_real ` R" by (simp only: eqZ)
    then obtain r where r: "z = of_real r" by auto
    have h: "z^2 = of_real (r^2)" using r by (simp add: of_real_power)
    have "Re (z^2) = r^2" unfolding h by (rule Re_complex_of_real)
    then show "0 \<le> Re (z^2)" by simp
  qed
  have "0 \<le> (\<Sum>z\<in>Z. Re (z^2))" by (rule sum_nonneg) (use nn in blast)
  then have re2: "0 \<le> Re (\<Sum>z\<in>Z. z^2)" by (simp add: Re_sum)
  have "0 < real_of_int cc" using ccpos by simp
  with re1 re2 show False by linarith
qed

theorem famC_two_nonreal_roots:
  assumes "prime p" "5 \<le> p" shows "card {z. poly (famC p) z = 0 \<and> z \<notin> \<real>} = 2"
proof -
  have odd: "odd p" using assms prime_odd_nat by auto
  have P_over: "famC p \<in> poly_over (\<rat> :: complex set)" by (rule famC_poly_over_Rats)
  have real: "\<And>i. coeff (famC p) i \<in> \<real>" using P_over poly_over_Rats_coeff_real by blast
  define R where "R = {x::real. poly (famR p) x = 0}"
  define Z where "Z = {z. poly (famC p) z = 0}"
  define N where "N = {z. poly (famC p) z = 0 \<and> z \<in> \<real>}"
  define W where "W = {z. poly (famC p) z = 0 \<and> z \<notin> \<real>}"
  have cardZ: "card Z = p" and finZ: "finite Z" unfolding Z_def
    using famC_roots[OF odd assms(2)] by simp_all
  have NR: "N = of_real ` R"
  proof
    show "N \<subseteq> of_real ` R"
    proof
      fix z assume "z \<in> N"
      then have zz: "poly (famC p) z = 0" "z \<in> \<real>" unfolding N_def by auto
      obtain r where zr: "z = of_real r" using zz(2) by (auto simp: Reals_def)
      have "of_real (poly (famR p) r) = (0::complex)" using zz(1) zr by (simp add: poly_famC_of_real)
      then have "poly (famR p) r = 0" by simp
      then show "z \<in> of_real ` R" using zr unfolding R_def by auto
    qed
    show "of_real ` R \<subseteq> N" unfolding N_def R_def by (auto simp: poly_famC_of_real)
  qed
  have cardN: "card N = card R"
    unfolding NR by (rule card_image) (use inj_of_real in \<open>auto simp: inj_on_def\<close>)
  have ge: "p - 2 \<le> card R" unfolding R_def using famR_real_roots_ge[OF odd assms(2)] .
  have lt: "card R < p" unfolding R_def using famR_not_all_real[OF odd assms(2)] .
  have NZ: "N \<subseteq> Z" unfolding N_def Z_def by auto
  have WZ: "W = Z - N" unfolding W_def N_def Z_def by auto
  have cardW: "card W = p - card N" unfolding WZ using card_Diff_subset[OF finite_subset[OF NZ finZ] NZ] cardZ by simp
  have W1: "1 \<le> card W" and W2: "card W \<le> 2" using cardW cardN ge lt assms(2) by auto
  have finW: "finite W" unfolding WZ using finZ by simp
  have cnjW: "\<And>w. w \<in> W \<Longrightarrow> cnj w \<in> W"
    unfolding W_def using real_coeff_cnj_poly[OF real] by (auto simp: Reals_cnj_iff)
  have "card W \<noteq> 1"
  proof
    assume c1: "card W = 1"
    then obtain w where Ww: "W = {w}" by (auto simp: card_1_singleton_iff)
    then have "w \<in> W" by simp
    then have "cnj w \<in> W" by (rule cnjW)
    with Ww have "cnj w = w" by simp
    then have "w \<in> \<real>" by (simp add: Reals_cnj_iff)
    moreover have "w \<notin> \<real>" using \<open>w \<in> W\<close> unfolding W_def by simp
    ultimately show False by contradiction
  qed
  then have "card W = 2" using W1 W2 by arith
  then show ?thesis unfolding W_def .
qed

subsection \<open>Main result\<close>

theorem fam_not_solvable_by_radicals:
  assumes "prime p" "5 \<le> p"
  shows "\<not> solvable_by_radicals (\<rat> :: complex set) {r. poly (famC p) r = 0}"
proof -
  have odd: "odd p" using assms prime_odd_nat by auto
  show ?thesis
    by (rule prime_degree_not_solvable_by_radicals
        [OF famC_poly_over_Rats irreducible_over_Rats_famC[OF odd assms(2)]
            famC_degree(1)[OF odd assms(2)] assms(1) assms(2) famC_two_nonreal_roots[OF assms]])
qed

end
