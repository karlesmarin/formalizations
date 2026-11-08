(*  Title:      Supports_Lemma.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: BSR(4,4) = 11, Lema 3 (lem:supports): piezas de la cota r >= a+1 (Observacion, ortogonalidad del haz,
   autovector comun de endomorfismos que conmutan, caso s = a = r, caso s < a condicionado a la inclusion del haz);
   usa endomorph_has_eigenvector de la AFP Rep_Fin_Groups *)
theory Supports_Lemma
  imports Complex_Main "HOL-Computational_Algebra.Fundamental_Theorem_Algebra" Rep_Fin_Groups.Rep_Fin_Groups
begin

text \<open>Pieces of the proof of Lemma 3 of the note ``Every $4\times4$ biquadratic sum of squares is a sum of eleven
  squares'' (doi:10.5281/zenodo.24055900). The setting is abstract: $T_c\colon A\to E$ for $c$ in an index type
  (\<open>T c x\<close> $=T(x\otimes c)$), and $J$ a form on $E$; the Hankel condition (2.2) of the note is
  \<open>J (T b x) (T c y) = J (T c x) (T b y)\<close>. A covector $(y\otimes c)\mapsto\varphi(y,c)$ is \emph{simple} when it
  factors as $\alpha(y)\beta(c)$ and is non-zero.

  Covered here: the Observation; the orthogonality half of the pencil inclusion (2.3); the existence of a common
  eigenvector for a family of pairwise commuting endomorphisms of a finite-dimensional space over an algebraically
  closed field (a classical result, proved here by induction on the dimension from the existence of one eigenvector,
  \<open>FinDimVectorSpace.endomorph_has_eigenvector\<close>, of the AFP entry \<open>Rep_Fin_Groups\<close> by Jeremy Sylvestre); the
  commutation of the operators $T_b^{-1}T_c$; the whole case $s=a=r$ of the bound $r\ge a+1$; the case $s<a$ given
  the inclusion $T_c(\ker T_b)\subseteq U$ and a radical of dimension at most one; and the counting steps.
  Not covered: the inclusion $T_c(\ker T_b)\subseteq\operatorname{im}T_b$ (maximal rank in a pencil), the bound
  $\dim(U\cap U^{\perp})\le\min(s-1,r-s)$ as a statement on subspaces, and the Segre bound
  $r\le(a-1)(b_0-1)$.\<close>

section \<open>The Observation\<close>

text \<open>If $T_cx=\beta(c)e$ for all $c$ and $\beta(d)\ne0$, the covector $(y\otimes c)\mapsto\langle e,T_cy\rangle_J$
  is $\beta(c)/\beta(d)$ times $\langle e,T_dy\rangle_J$.\<close>

lemma observation_factor:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> complex" and T :: "'c \<Rightarrow> 'a \<Rightarrow> 'e"
    and sm :: "complex \<Rightarrow> 'e \<Rightarrow> 'e"
  assumes sym: "\<And>b c x y. J (T b x) (T c y) = J (T c x) (T b y)"
    and Jscal: "\<And>t u w. J (sm t u) w = t * J u w"
    and Tx: "\<And>c. T c x = sm (\<beta> c) e"
    and d: "\<beta> d \<noteq> 0"
  shows "J e (T c y) = (\<beta> c / \<beta> d) * J e (T d y)"
proof -
  have "\<beta> c * J e (T d y) = J (T c x) (T d y)" using Tx Jscal by simp
  also have "\<dots> = J (T d x) (T c y)" by (rule sym)
  also have "\<dots> = \<beta> d * J e (T c y)" using Tx Jscal by simp
  finally show ?thesis using d by (simp add: field_simps)
qed

text \<open>Non-vanishing: $J$ is non-degenerate and $T$ is onto, which we use in the combined form
  ``a vector $J$-orthogonal to every $T_cy$ is zero''.\<close>

lemma observation_nonzero:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> complex" and T :: "'c \<Rightarrow> 'a \<Rightarrow> 'e"
    and sm :: "complex \<Rightarrow> 'e \<Rightarrow> 'e"
  assumes nondeg: "\<And>z. (\<And>c y. J z (T c y) = 0) \<Longrightarrow> z = 0" and e: "e \<noteq> 0"
  shows "\<exists>c y. J e (T c y) \<noteq> 0"
  using nondeg[of e] e by blast

theorem observation:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> complex" and T :: "'c \<Rightarrow> 'a \<Rightarrow> 'e"
    and sm :: "complex \<Rightarrow> 'e \<Rightarrow> 'e"
  assumes sym: "\<And>b c x y. J (T b x) (T c y) = J (T c x) (T b y)"
    and Jscal: "\<And>t u w. J (sm t u) w = t * J u w"
    and nondeg: "\<And>z. (\<And>c y. J z (T c y) = 0) \<Longrightarrow> z = 0"
    and Tx: "\<And>c. T c x = sm (\<beta> c) e" and d: "\<beta> d \<noteq> 0" and e: "e \<noteq> 0"
  shows "(\<forall>c y. J e (T c y) = (\<beta> c / \<beta> d) * J e (T d y)) \<and> (\<exists>y. J e (T d y) \<noteq> 0)"
proof -
  have fac: "\<forall>c y. J e (T c y) = (\<beta> c / \<beta> d) * J e (T d y)"
    using observation_factor[of J T, OF sym Jscal Tx d] by blast
  obtain c y where cy: "J e (T c y) \<noteq> 0" using nondeg[of e] e by blast
  have "J e (T c y) = (\<beta> c / \<beta> d) * J e (T d y)" using fac by blast
  then have "J e (T d y) \<noteq> 0" using cy by (cases "J e (T d y) = 0") simp_all
  with fac show ?thesis by blast
qed

section \<open>The pencil inclusion (2.3): the orthogonality half\<close>

text \<open>For $x\in\ker T_b$, $T_cx$ is $J$-orthogonal to $U=\operatorname{im}T_b$. With the inclusion
  $T_c(\ker T_b)\subseteq U$ (not formalized here), $T_c(\ker T_b)$ lies in the radical $U\cap U^{\perp_J}$.\<close>

lemma pencil_orthogonal:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> complex" and T :: "'c \<Rightarrow> 'a \<Rightarrow> 'e"
    and sm :: "complex \<Rightarrow> 'e \<Rightarrow> 'e"
  assumes sym: "\<And>b c x y. J (T b x) (T c y) = J (T c x) (T b y)"
    and Jadd: "\<And>u v w. J (u + v) w = J u w + J v w"
    and x: "T b x = 0"
  shows "J (T c x) (T b y) = 0"
proof -
  have J0: "J 0 w = 0" for w using Jadd[of 0 0 w] by simp
  have "J (T c x) (T b y) = J (T b x) (T c y)" using sym by simp
  also have "\<dots> = 0" using x J0 by simp
  finally show ?thesis .
qed

section \<open>The case $s<a$, given the pencil inclusion and a radical of dimension at most one\<close>

text \<open>Let $x\ne0$ in $\ker T_b$ be outside the radical of $H$ in $A$ (some $T_cx\ne0$). If every $T_cx$ lies in
  $U=\operatorname{im}T_b$ (the unformalized half of (2.3)) and the radical $U\cap U^{\perp_J}$ lies on a line
  $\mathbb C e$, the image of $H$ contains a simple covector.\<close>

theorem case_s_lt_a:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> complex" and T :: "'c \<Rightarrow> 'a \<Rightarrow> 'e"
    and sm :: "complex \<Rightarrow> 'e \<Rightarrow> 'e"
  assumes sym: "\<And>b c x y. J (T b x) (T c y) = J (T c x) (T b y)"
    and Jscal: "\<And>t u w. J (sm t u) w = t * J u w"
    and Jadd: "\<And>u v w. J (u + v) w = J u w + J v w"
    and nondeg: "\<And>z. (\<And>c y. J z (T c y) = 0) \<Longrightarrow> z = 0"
    and x: "T b x = 0" and xrad: "T d0 x \<noteq> 0"
    and inU: "\<And>c. T c x \<in> range (T b)"
    and line: "\<And>u. u \<in> range (T b) \<Longrightarrow> (\<forall>y. J u (T b y) = 0) \<Longrightarrow> \<exists>t. u = sm t e"
  shows "\<exists>e' \<beta> d. e' \<noteq> 0 \<and> \<beta> d \<noteq> 0 \<and> (\<forall>c y. J e' (T c y) = (\<beta> c / \<beta> d) * J e' (T d y))
           \<and> (\<exists>y. J e' (T d y) \<noteq> 0)"
proof -
  have ex: "\<exists>t. T c x = sm t e" for c
  proof (rule line[OF inU[of c]], rule allI)
    fix y
    show "J (T c x) (T b y) = 0" by (rule pencil_orthogonal[of J T, OF sym Jadd x])
  qed
  define \<beta> where "\<beta> c = (SOME t. T c x = sm t e)" for c
  have Tx: "T c x = sm (\<beta> c) e" for c unfolding \<beta>_def using ex[of c] by (rule someI_ex)
  have J0: "J 0 w = 0" for w using Jadd[of 0 0 w] by simp
  have sm0: "sm 0 u = 0" for u by (rule nondeg) (simp add: Jscal)
  have sme: "sm t 0 = 0" for t by (rule nondeg) (simp add: Jscal J0)
  have d: "\<beta> d0 \<noteq> 0" using xrad Tx[of d0] sm0 by auto
  have e: "e \<noteq> 0" using xrad Tx[of d0] sme by auto
  show ?thesis using observation[of J T, OF sym Jscal nondeg Tx d e] e d by blast
qed

section \<open>A common eigenvector of commuting endomorphisms\<close>

text \<open>A classical fact of linear algebra, proved here inside the vector-space locales of the AFP entry
  \<open>Rep_Fin_Groups\<close> by induction on the dimension: a non-zero subspace invariant under a family of pairwise
  commuting endomorphisms, over an algebraically closed field, contains a common eigenvector. If every member acts
  as a scalar on the subspace, any non-zero vector works; otherwise a member $T$ that is not a scalar has an
  eigenvalue $c$ there (\<open>endomorph_has_eigenvector\<close>), and the eigenspace is a smaller non-zero subspace
  invariant under the whole family.\<close>

lemma (in R_scalar_mult) dim_R_pos:
  assumes fg: "R_fingen M" and m: "m \<in> M" "m \<noteq> 0"
  shows "0 < dim_R M"
proof (rule ccontr)
  assume "\<not> 0 < dim_R M"
  then have d0: "dim_R M = 0" by simp
  let ?P = "\<lambda>n. \<exists>ms. length ms = n \<and> set ms \<subseteq> M \<and> RSpan ms = M"
  from fg have ex: "\<exists>n. ?P n" by blast
  have "?P (LEAST n. ?P n)" using LeastI_ex[OF ex] .
  moreover have "dim_R M = (LEAST n. ?P n)" using fg unfolding dim_R_def by simp
  ultimately have "?P 0" using d0 by simp
  then have "M = 0" by auto
  with m show False by simp
qed

theorem (in FinDimVectorSpace) common_eigenvector:
  assumes alg_closed: "\<And>p::'a poly. degree p > 0 \<Longrightarrow> \<exists>c. poly p c = 0"
    and add: "\<And>T u v. T \<in> F \<Longrightarrow> u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> T (u + v) = T u + T v"
    and hom: "\<And>T a u. T \<in> F \<Longrightarrow> u \<in> V \<Longrightarrow> T (a \<cdot> u) = a \<cdot> T u"
    and comm: "\<And>S T u. S \<in> F \<Longrightarrow> T \<in> F \<Longrightarrow> u \<in> V \<Longrightarrow> S (T u) = T (S u)"
  shows "Subspace W \<Longrightarrow> (\<exists>w\<in>W. w \<noteq> 0) \<Longrightarrow> (\<And>T. T \<in> F \<Longrightarrow> T ` W \<subseteq> W)
           \<Longrightarrow> \<exists>u\<in>W. u \<noteq> 0 \<and> (\<forall>T\<in>F. \<exists>c. T u = c \<cdot> u)"
proof (induction "dim W" arbitrary: W rule: less_induct)
  case less
  note Wsub = less.prems(1) and Wnz = less.prems(2) and Winv = less.prems(3)
  have WV: "W \<subseteq> V" using Wsub by blast
  have VSW: "VectorSpace (\<cdot>) W" using Wsub SubspaceD1 by blast
  have fgW: "findim W" using Wsub Subspace_is_findim by blast
  have fdW: "FinDimVectorSpace (\<cdot>) W" using VectorSpace.FinDimVectorSpaceI[OF VSW fgW] .
  obtain w0 where w0: "w0 \<in> W" "w0 \<noteq> 0" using Wnz by blast
  have dimW: "dim W > 0" using R_scalar_mult.dim_R_pos[OF R_scalar_mult fgW w0] .
  show ?case
  proof (cases "\<forall>T\<in>F. \<exists>c. \<forall>w\<in>W. T w = c \<cdot> w")
    case True
    then show ?thesis using w0 by blast
  next
    case False
    then obtain T where TF: "T \<in> F" and nsc: "\<And>c. \<exists>w\<in>W. T w \<noteq> c \<cdot> w" by blast
    define R where "R = T \<down> W"
    have Wadd: "u + v \<in> W" if "u \<in> W" "v \<in> W" for u v
      using that VSW by (simp add: VectorSpace.add_closed)
    have Wsm: "a \<cdot> u \<in> W" if "u \<in> W" for a u
      using that VSW by (simp add: VectorSpace.smult_closed)
    have homR: "VectorSpaceHom (\<cdot>) W (\<cdot>) R"
    proof (rule VectorSpace.VectorSpaceHomI_fromaxioms[OF VSW])
      show "R (g + g') = R g + R g'" if "g \<in> W" "g' \<in> W" for g g'
        using that Wadd[OF that] add[OF TF] WV unfolding R_def by auto
      show "supp R \<subseteq> W" unfolding R_def by (rule supp_restrict0)
      show "R (r \<cdot> m) = r \<cdot> R m" if "m \<in> W" for r m
        using that Wsm[OF that] hom[OF TF] WV unfolding R_def by auto
    qed
    have endR: "VectorSpaceEnd (\<cdot>) W R"
      by (rule VectorSpaceEndI[OF homR]) (use Winv[OF TF] in \<open>auto simp: R_def\<close>)
    obtain c u where u: "u \<in> W" "u \<noteq> 0" "R u = c \<cdot> u"
      using FinDimVectorSpace.endomorph_has_eigenvector[OF fdW alg_closed dimW endR] by blast
    define E where "E = {m \<in> W. R m = c \<cdot> m}"
    have RH: "RModuleHom UNIV (\<cdot>) W (\<cdot>) R"
      using homR unfolding VectorSpaceHom_def ModuleHom_def by blast
    have scom: "s \<cdot> c \<cdot> m = c \<cdot> s \<cdot> m" if "m \<in> W" for s m
    proof -
      have mV: "m \<in> V" using that WV by blast
      have "s \<cdot> c \<cdot> m = (s * c) \<cdot> m" using mV by simp
      also have "\<dots> = (c * s) \<cdot> m" by (simp add: mult.commute)
      also have "\<dots> = c \<cdot> s \<cdot> m" using mV by simp
      finally show ?thesis .
    qed
    have EW: "RModule.RSubmodule UNIV (\<cdot>) W E"
      unfolding E_def by (rule RSubmodule_eigenspace[OF RH]) (use scom in auto)
    have Esub: "Subspace E" using EW WV by blast
    have Ene: "E \<noteq> W"
    proof
      assume "E = W"
      obtain w where w: "w \<in> W" "T w \<noteq> c \<cdot> w" using nsc by blast
      have "w \<in> E" using \<open>E = W\<close> w(1) by simp
      then have "R w = c \<cdot> w" unfolding E_def by blast
      moreover have "R w = T w" using w(1) unfolding R_def by simp
      ultimately show False using w(2) by simp
    qed
    have dimlt: "dim E < dim W"
      using FinDimVectorSpace.Subspace_dim_lt[OF fdW] EW Ene by blast
    have uE: "u \<in> E" using u unfolding E_def by blast
    have Einv: "S ` E \<subseteq> E" if SF: "S \<in> F" for S
    proof
      fix v assume "v \<in> S ` E"
      then obtain m where m: "m \<in> E" and v: "v = S m" by blast
      have mW: "m \<in> W" and Rm: "T m = c \<cdot> m" using m unfolding E_def R_def by auto
      have mV: "m \<in> V" using mW WV by blast
      have SmW: "S m \<in> W" using Winv[OF SF] mW by blast
      have "T (S m) = S (T m)" using comm[OF SF TF mV] by simp
      also have "\<dots> = c \<cdot> S m" using Rm hom[OF SF mV] by simp
      finally show "v \<in> E" using SmW v unfolding E_def R_def by simp
    qed
    obtain u' where u': "u' \<in> E" "u' \<noteq> 0" "\<forall>T\<in>F. \<exists>c. T u' = c \<cdot> u'"
      using less.hyps[OF dimlt Esub _ Einv] uE u(2) by blast
    have "u' \<in> W" using u'(1) unfolding E_def by blast
    with u' show ?thesis by blast
  qed
qed

text \<open>The complex numbers satisfy the hypothesis \<open>alg_closed\<close>.\<close>

lemma complex_alg_closed: "degree (p :: complex poly) > 0 \<Longrightarrow> \<exists>c. poly p c = 0"
  using fundamental_theorem_of_algebra constant_degree by (metis neq0_conv)

section \<open>The operators $T_b^{-1}T_c$ commute\<close>

text \<open>If $T_b$ is bijective, $J$ non-degenerate and $T_c=T_bM_c$, the Hankel symmetry (2.2) forces
  $M_cM_d=M_dM_c$: both $\langle T_bM_cM_dx,T_by\rangle_J$ and $\langle T_bM_dM_cx,T_by\rangle_J$ equal
  $\langle T_dx,T_cy\rangle_J=\langle T_cx,T_dy\rangle_J$.\<close>

lemma pencil_operators_commute:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> 'k::ab_group_add" and T :: "'c \<Rightarrow> 'a::ab_group_add \<Rightarrow> 'e"
  assumes sym: "\<And>b c x y. J (T b x) (T c y) = J (T c x) (T b y)"
    and Jdiff: "\<And>u v w. J (u - v) w = J u w - J v w"
    and nondeg: "\<And>z. (\<And>w. J z w = 0) \<Longrightarrow> z = 0"
    and Tb_diff: "\<And>u v. T b (u - v) = T b u - T b v"
    and Tb_inj: "\<And>u. T b u = 0 \<Longrightarrow> u = 0"
    and Tb_onto: "\<And>w. \<exists>y. w = T b y"
    and M: "\<And>c x. T c x = T b (M c x)"
  shows "M c (M d x) = M d (M c x)"
proof -
  define z where "z = M c (M d x) - M d (M c x)"
  have Tz: "T b z = T c (M d x) - T d (M c x)" unfolding z_def Tb_diff M[symmetric] ..
  have "J (T b z) w = 0" for w
  proof -
    obtain y where y: "w = T b y" using Tb_onto by blast
    have "J (T b z) w = J (T c (M d x)) (T b y) - J (T d (M c x)) (T b y)" using Tz Jdiff y by simp
    also have "J (T c (M d x)) (T b y) = J (T b (M d x)) (T c y)" by (rule sym)
    also have "J (T d (M c x)) (T b y) = J (T b (M c x)) (T d y)" by (rule sym)
    also have "J (T b (M d x)) (T c y) - J (T b (M c x)) (T d y) = J (T d x) (T c y) - J (T c x) (T d y)"
      using M by simp
    also have "\<dots> = 0" using sym[of d x c y] by simp
    finally show ?thesis .
  qed
  then have "T b z = 0" by (rule nondeg)
  then have "z = 0" by (rule Tb_inj)
  then show ?thesis unfolding z_def by simp
qed

section \<open>The case $s=a=r$\<close>

text \<open>If $T_b\colon A\to E$ is an isomorphism ($s=a=r$), the operators $M_c=T_b^{-1}T_c$ commute; a common eigenvector
  $x$ gives $T_cx=\lambda_cT_bx$ for all $c$, with $\lambda_b\ne0$, and the Observation gives a simple covector in the
  image. The space $A$ (scalar multiplication \<open>smA\<close>) is any complex vector space that is finite-dimensional in the
  sense of \<open>Rep_Fin_Groups\<close>; $E$ carries the scalar multiplication \<open>sm\<close>, and only the identities used are
  assumed of it.\<close>

theorem case_s_eq_a:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> complex" and T :: "'c \<Rightarrow> 'a::ab_group_add \<Rightarrow> 'e"
    and sm :: "complex \<Rightarrow> 'e \<Rightarrow> 'e" and smA :: "complex \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes fd: "FinDimVectorSpace smA (UNIV :: 'a set)" and nz: "\<exists>w::'a. w \<noteq> 0"
    and sym: "\<And>b c x y. J (T b x) (T c y) = J (T c x) (T b y)"
    and Jadd: "\<And>u v w. J (u + v) w = J u w + J v w"
    and Jscal: "\<And>t u w. J (sm t u) w = t * J u w"
    and nondeg: "\<And>z. (\<And>w. J z w = 0) \<Longrightarrow> z = 0"
    and Tadd: "\<And>c u v. T c (u + v) = T c u + T c v"
    and Tscal: "\<And>c t u. T c (smA t u) = sm t (T c u)"
    and Tb_inj: "\<And>u. T b u = 0 \<Longrightarrow> u = 0"
    and Tb_onto: "\<And>w. \<exists>y. w = T b y"
  shows "\<exists>e \<beta>. e \<noteq> 0 \<and> \<beta> b \<noteq> 0 \<and> (\<forall>c y. J e (T c y) = (\<beta> c / \<beta> b) * J e (T b y))
           \<and> (\<exists>y. J e (T b y) \<noteq> 0)"
proof -
  have Tb_eq: "u = v" if "T b u = T b v" for u v
  proof -
    have "T b (u - v) = T b u - T b v"
      using Tadd[of b "u - v" v] by (simp add: algebra_simps)
    then have "T b (u - v) = 0" using that by simp
    then have "u - v = 0" by (rule Tb_inj)
    then show ?thesis by simp
  qed
  define M where "M c x = (SOME y. T c x = T b y)" for c x
  have M: "T c x = T b (M c x)" for c x
    unfolding M_def using Tb_onto[of "T c x"] by (rule someI_ex)
  have Madd: "M c (u + v) = M c u + M c v" for c u v
    by (rule Tb_eq) (simp add: M[symmetric] Tadd)
  have Mscal: "M c (smA t u) = smA t (M c u)" for c t u
    by (rule Tb_eq) (simp add: M[symmetric] Tscal)
  have Jdiff: "J (u - v) w = J u w - J v w" for u v w
    using Jadd[of "u - v" v w] by (simp add: algebra_simps)
  have Tb_diff: "T b (u - v) = T b u - T b v" for u v
    using Tadd[of b "u - v" v] by (simp add: algebra_simps)
  have Mcomm: "M c (M d x) = M d (M c x)" for c d x
    by (rule pencil_operators_commute[of J T, OF sym Jdiff nondeg Tb_diff Tb_inj Tb_onto M])
  have VSA: "VectorSpace smA (UNIV :: 'a set)" using fd unfolding FinDimVectorSpace_def by blast
  have VS: "RModule.RSubmodule UNIV smA (UNIV :: 'a set) UNIV"
    using VSA unfolding VectorSpace_def Module_def by blast
  have ex: "\<exists>u\<in>(UNIV :: 'a set). u \<noteq> 0 \<and> (\<forall>N\<in>range M. \<exists>c. N u = smA c u)"
    apply (rule FinDimVectorSpace.common_eigenvector[OF fd complex_alg_closed])
    using VS nz by (auto simp: Madd Mscal Mcomm)
  then obtain x where x: "x \<noteq> 0" and eig: "\<forall>N\<in>range M. \<exists>c. N x = smA c x" by blast
  define mu where "mu c = (SOME l. M c x = smA l x)" for c
  have lam: "M c x = smA (mu c) x" for c
  proof -
    have "\<exists>l. M c x = smA l x" using eig by blast
    then show ?thesis unfolding mu_def by (rule someI_ex)
  qed
  define e where "e = T b x"
  have Tx: "T c x = sm (mu c) e" for c unfolding e_def using M[of c x] lam[of c] Tscal by simp
  have e: "e \<noteq> 0" unfolding e_def using x Tb_inj by blast
  have lb: "mu b \<noteq> 0"
  proof
    assume l0: "mu b = 0"
    have "M b x = x" by (rule Tb_eq) (simp add: M[symmetric])
    moreover have "M b x = 0" using lam[of b] l0 VectorSpace.zero_smult[OF VSA] by simp
    ultimately show False using x by simp
  qed
  have nd': "z = 0" if z: "\<And>c y. J z (T c y) = 0" for z
  proof (rule nondeg)
    fix w
    obtain y where "w = T b y" using Tb_onto by blast
    then show "J z w = 0" using z by simp
  qed
  have "(\<forall>c y. J e (T c y) = (mu c / mu b) * J e (T b y)) \<and> (\<exists>y. J e (T b y) \<noteq> 0)"
    by (rule observation[where J = J and T = T and sm = sm, OF sym Jscal nd' Tx lb e])
  then show ?thesis using lb e by blast
qed

section \<open>Counting steps\<close>

text \<open>The radical of $U$ has dimension at most $s-1$ and at most $r-s$; with $r\le4$ that is at most one.
  And with $s\le r\le a$ and $s\le a$, either $s<a$ or $s=a=r$.\<close>

lemma radical_count: "(r::nat) \<le> 4 \<Longrightarrow> min (s - 1) (r - s) \<le> 1"
  by linarith

lemma rank_cases: "(s::nat) \<le> r \<Longrightarrow> r \<le> a \<Longrightarrow> s < a \<or> (s = a \<and> a = r)"
  by linarith

end
