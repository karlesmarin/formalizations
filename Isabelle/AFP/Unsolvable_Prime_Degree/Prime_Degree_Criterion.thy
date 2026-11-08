(*  Title:      Prime_Degree_Criterion.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

section \<open>Irreducible rational polynomials of prime degree with two non-real roots\<close>

theory Prime_Degree_Criterion
  imports Unsolvable_Quintic.Abel_Ruffini_Quintic
begin

text \<open>We prove the classical criterion: an irreducible polynomial over \<open>\<rat>\<close> of prime degree
  \<open>p \<ge> 5\<close> with exactly two non-real roots has a non-solvable Galois group, hence is not solvable by
  radicals. The example quintic of @{session Unsolvable_Quintic} is an instance with \<open>p = 5\<close>.
  Complex conjugation transposes the two non-real roots and irreducibility makes the Galois action
  transitive. The group-theoretic step, valid for every prime \<open>p \<ge> 5\<close>, is the following lemma
  of @{session "HOL-New_Algebra"}:

  @{thm [source] Group_Action.not_solvable_of_transitive_with_transposition}.\<close>

subsection \<open>Root structure\<close>

lemma poly_over_Rats_coeff_real:
  fixes P :: "complex poly"
  assumes "P \<in> poly_over (\<rat> :: complex set)"
  shows "coeff P i \<in> \<real>"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have "coeff P i \<in> (\<rat> :: complex set)"
    using assms Subfield.poly_over_coeff[OF sfQ] by blast
  moreover have QR: "(\<rat> :: complex set) \<subseteq> \<real>"
    using Reals_cnj_iff cnj_fixes_Rats by blast
  ultimately show ?thesis by blast
qed

lemma real_coeff_cnj_poly:
  fixes P :: "complex poly"
  assumes real: "\<And>i. coeff P i \<in> \<real>"
  shows "poly P (cnj z) = cnj (poly P z)"
proof -
  have cnjP: "map_poly cnj P = P"
    by (rule poly_eqI) (use real in \<open>simp add: coeff_map_poly Reals_cnj_iff\<close>)
  show ?thesis by (metis cnjP poly_cnj)
qed

text \<open>An irreducible polynomial over \<open>\<rat>\<close> has no repeated complex root.\<close>
lemma irreducible_over_Rats_rsquarefree:
  fixes P :: "complex poly"
  assumes "P \<in> poly_over (\<rat> :: complex set)" and "irreducible_over (\<rat> :: complex set) P"
  shows "rsquarefree P"
proof (unfold rsquarefree_roots, intro allI notI)
  fix a assume a: "poly P a = 0 \<and> poly (pderiv P) a = 0"
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have alg: "algebraic_over (\<rat> :: complex set) a"
    using assms a unfolding algebraic_over_def irreducible_over_def by blast
  define m where "m \<equiv> minpoly (\<rat> :: complex set) a"
  have ism: "is_minpoly (\<rat> :: complex set) a m"
    unfolding m_def by (rule Subfield.is_minpoly_minpoly[OF sfQ alg])
  obtain k where k0: "k \<noteq> 0" and Pk: "P = smult k m"
    using Subfield.irreducible_over_minpoly_assoc[OF sfQ assms(2) ism _ assms(1)] a by blast
  have rsf: "rsquarefree m" unfolding m_def by (rule rsquarefree_minpoly[OF sfQ alg])
  have "poly m a = 0" using a Pk k0 by simp
  moreover have "poly (pderiv m) a = 0"
    using a Pk k0 by (simp add: pderiv_smult)
  ultimately show False using rsf unfolding rsquarefree_roots by blast
qed

lemma card_roots_eq_degree:
  fixes P :: "complex poly"
  assumes "P \<noteq> 0" and "rsquarefree P"
  shows "card {z. poly P z = 0} = degree P"
proof -
  have decomp: "smult (lead_coeff P) (\<Prod>z | poly P z = 0. [:- z, 1:]) = P"
    using assms(2) by (rule complex_poly_decompose_rsquarefree)
  have lead: "lead_coeff P \<noteq> 0" using assms(1) by simp
  have "degree P = degree (\<Prod>z | poly P z = 0. [:- z, 1:])"
    by (metis decomp degree_smult_eq lead)
  also have "\<dots> = (\<Sum>z | poly P z = 0. degree [:- z, 1:])"
    by (simp add: degree_prod_eq_sum_degree)
  also have "\<dots> = card {z. poly P z = 0}" by simp
  finally show ?thesis by simp
qed

text \<open>For a polynomial with real coefficients, two non-real roots form one conjugate pair.\<close>
lemma two_nonreal_roots_conj_pair:
  fixes P :: "complex poly"
  assumes real: "\<And>i. coeff P i \<in> \<real>" and two: "card {z. poly P z = 0 \<and> z \<notin> \<real>} = 2"
  obtains a where "{z. poly P z = 0 \<and> z \<notin> \<real>} = {a, cnj a}" and "a \<noteq> cnj a"
proof -
  have fin: "finite {z. poly P z = 0 \<and> z \<notin> \<real>}" using two by (simp add: card_ge_0_finite)
  have cnj_poly: "poly P (cnj z) = cnj (poly P z)" for z
    by (rule real_coeff_cnj_poly[OF real])
  obtain a where a: "poly P a = 0" and anr: "a \<notin> \<real>"
    using two card_2_iff' by (metis (mono_tags, lifting) card_2_iff' mem_Collect_eq)
  have sub: "{a, cnj a} \<subseteq> {z. poly P z = 0 \<and> z \<notin> \<real>}"
    using a anr by (simp add: cnj_poly Reals_cnj_iff)
  have ne: "a \<noteq> cnj a" using anr by (metis Reals_cnj_iff)
  have card2: "card {a, cnj a} = 2" using ne by simp
  have "{z. poly P z = 0 \<and> z \<notin> \<real>} = {a, cnj a}"
    using sub card2 two fin by (metis card_subset_eq)
  with ne that show ?thesis by blast
qed

subsection \<open>The criterion\<close>

theorem prime_degree_galois_group_not_solvable:
  fixes P :: "complex poly" and p :: nat
  assumes P: "P \<in> poly_over (\<rat> :: complex set)" and irr: "irreducible_over (\<rat> :: complex set) P"
    and deg: "degree P = p" and prime: "prime p" and p5: "5 \<le> p"
    and two: "card {z. poly P z = 0 \<and> z \<notin> \<real>} = 2"
  defines "X \<equiv> {z. poly P z = 0}"
  defines "K \<equiv> generate_field (\<rat> \<union> X)"
  shows "\<not> Group.solvable (field_auto K \<rat>) (compose K) (identity K)"
proof -
  have P0: "P \<noteq> 0" using deg prime by auto
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have rsf: "rsquarefree P" by (rule irreducible_over_Rats_rsquarefree[OF P irr])
  have finX: "finite X" unfolding X_def using P0 poly_roots_finite by blast
  have cardX: "card X = p" unfolding X_def using card_roots_eq_degree[OF P0 rsf] deg by simp
  have FK: "(\<rat> :: complex set) \<subseteq> K" unfolding K_def using subset_generate_field by blast
  have XK: "X \<subseteq> K" unfolding K_def using subset_generate_field by blast
  have sfK: "Subfield K" unfolding K_def by (rule subfield_generate_field)
  have closed: "\<exists>b. poly q b = 0" if "0 < degree q" for q :: "complex poly"
    using that by (intro fundamental_theorem_of_algebra) (simp add: constant_degree)
  interpret GA: Group_Action "field_auto K \<rat>" "compose K" "identity K" "\<lambda>\<sigma>. restrict \<sigma> X" X
    using FK P XK X_def finX galois_group_action sfK sfQ by blast
  obtain e where ebij: "bij_betw e {0..<p} X"
    using ex_bij_betw_nat_finite[OF finX] cardX by force
  have Kgen: "K = gen_subfield (\<rat> \<union> X)"
    by (simp add: K_def gen_subfield_eq_generate_field)
  have faith: "GA.faithful"
    unfolding GA.faithful_def
  proof (intro ballI impI)
    fix \<sigma> assume s: "\<sigma> \<in> field_auto K \<rat>" and triv: "\<forall>x\<in>X. restrict \<sigma> X x = x"
    have sgen: "\<sigma> \<in> field_auto (gen_subfield (\<rat> \<union> X)) \<rat>" using s Kgen by simp
    have "complex_subfield K" using sfK by (simp add: complex_subfield_iff_subfield)
    then have allK: "\<forall>x\<in>K. \<sigma> x = x"
      by (metis Kgen field_auto_faithful restrict_apply s triv)
    have sext: "\<sigma> \<in> K \<rightarrow>\<^sub>E K" using s by (simp only: field_auto_mem_iff)
    with allK show "\<sigma> = identity K"
      by (metis PiE_restrict restrict_ext)
  qed
  have finGal: "finite (field_auto K \<rat>)"
  proof -
    have "inj_on (\<lambda>\<sigma>. restrict \<sigma> X) (field_auto K \<rat>)"
      using GA.faithful_inj [OF faith] inj_on_restrict_eq by blast
    moreover have "(\<lambda>\<sigma>. restrict \<sigma> X) ` field_auto K \<rat> \<subseteq> transformations.Sym X"
      using GA.hom_closed by auto
    moreover have "finite (transformations.Sym X)"
      by (metis GA.mem_UnitsD finX finite_PiE finite_subset subsetI)
    ultimately show ?thesis by (metis inj_on_finite finite_subset)
  qed
  have trans: "\<exists>s\<in>X. GA.orbit s = X"
  proof -
    have "X \<noteq> {}" using cardX prime prime_gt_0_nat by auto
    then obtain a where aX: "a \<in> X" by blast
    have surj: "\<forall>b\<in>X. \<exists>\<sigma>\<in>field_auto K \<rat>. restrict \<sigma> X a = b"
      using galois_action_transitive[OF sfQ finX P irr _ closed aX]
      unfolding K_def X_def by blast
    have "X \<subseteq> GA.orbit a"
      using GA.orbit_mem_iff aX surj by force
    then show ?thesis using aX GA.orbit_subset by blast
  qed
  have real: "\<And>i. coeff P i \<in> \<real>"
    using P poly_over_Rats_coeff_real by blast
  have cnj_poly: "\<And>z. poly P (cnj z) = cnj (poly P z)"
    by (rule real_coeff_cnj_poly[OF real])
  have transp: "\<exists>i j. i < p \<and> j < p \<and> i \<noteq> j
                  \<and> Transposition.transpose i j \<in> (\<lambda>\<sigma>. pull p e (restrict \<sigma> X)) ` field_auto K \<rat>"
  proof -
    have cnjXX: "cnj ` X = X"
      unfolding X_def using cnj_image_eq cnj_poly by force
    obtain a where Xnr: "{z. poly P z = 0 \<and> z \<notin> \<real>} = {a, cnj a}" and ane: "a \<noteq> cnj a"
      by (rule two_nonreal_roots_conj_pair[OF real two])
    have aroot: "poly P a = 0" and anr: "a \<notin> \<real>" using Xnr by auto
    have aX: "a \<in> X" using aroot unfolding X_def by simp
    have caX: "cnj a \<in> X" using aroot cnj_poly unfolding X_def by simp
    have cnjK: "cnj ` K = K"
      using Kgen cnjXX splitting_subfield_cnj_closed by presburger
    have QR: "(\<rat> :: complex set) \<subseteq> \<real>"
      using Reals_cnj_iff cnj_fixes_Rats by blast
    have cnjaut: "restrict cnj K \<in> field_auto K \<rat>"
      using FK QR cnjK cnj_field_auto complex_subfield_iff_subfield sfK by presburger
    have fixed: "cnj x = x" if "x \<in> X" "x \<noteq> a" "x \<noteq> cnj a" for x
      using Reals_cnj_iff X_def Xnr that by blast
    have invol: "cnj (cnj x) = x" for x by simp
    define i where "i \<equiv> inv_into {0..<p} e a"
    define j where "j \<equiv> inv_into {0..<p} e (cnj a)"
    have pull_t: "pull p e (restrict cnj X) = Transposition.transpose i j"
      unfolding i_def j_def
      by (rule pull_involution_two_points_transpose[OF ebij cnjXX invol aX caX ane fixed])
    obtain ij: "i < p" "j < p" unfolding i_def j_def
      by (meson ebij aX caX inv_e_lt)
    have inej: "i \<noteq> j"
      unfolding i_def j_def by (metis aX ane caX e_inv_e ebij)
    have "Transposition.transpose i j = pull p e (restrict (restrict cnj K) X)"
      using pull_t by (simp add: Int_absorb1 XK)
    then have "Transposition.transpose i j \<in> (\<lambda>\<sigma>. pull p e (restrict \<sigma> X)) ` field_auto K \<rat>"
      using cnjaut by blast
    then show ?thesis using ij inej by blast
  qed
  show ?thesis
    by (rule GA.not_solvable_of_transitive_with_transposition
              [OF ebij prime p5 finGal faith trans transp])
qed

theorem prime_degree_not_solvable_by_radicals:
  fixes P :: "complex poly" and p :: nat
  assumes P: "P \<in> poly_over (\<rat> :: complex set)" and irr: "irreducible_over (\<rat> :: complex set) P"
    and deg: "degree P = p" and prime: "prime p" and p5: "5 \<le> p"
    and two: "card {z. poly P z = 0 \<and> z \<notin> \<real>} = 2"
  shows "\<not> solvable_by_radicals (\<rat> :: complex set) {r. poly P r = 0}"
proof
  assume solv: "solvable_by_radicals (\<rat> :: complex set) {r. poly P r = 0}"
  define X where "X \<equiv> {r. poly P r = 0}"
  define Kq where "Kq \<equiv> generate_field (\<rat> \<union> X)"
  have P0: "P \<noteq> 0" using deg prime by auto
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have finX: "finite X" unfolding X_def using P0 poly_roots_finite by blast
  obtain Fs where tower: "radical_tower (\<rat> :: complex set) Fs"
    and Xtop: "{r. poly P r = 0} \<subseteq> tower_top (\<rat> :: complex set) Fs"
    using solv by (auto simp: solvable_by_radicals_def)
  have Xtop': "X \<subseteq> tower_top (\<rat> :: complex set) Fs" using Xtop by (simp add: X_def)
  have X_eq: "X = {r. poly P r = 0}" by (simp add: X_def)
  have solvKq: "Group.solvable (field_auto Kq \<rat>) (compose Kq) (identity Kq)"
    unfolding Kq_def
    by (rule radical_tower_root_field_solvable
      [OF sfQ tower P irr X_eq finX Xtop' alg_closed_imp_poly_has_root])
  have "\<not> Group.solvable (field_auto Kq \<rat>) (compose Kq) (identity Kq)"
    using prime_degree_galois_group_not_solvable[OF P irr deg prime p5 two]
    unfolding Kq_def X_def by simp
  with solvKq show False by contradiction
qed

end
