(*  Title:      BSR_m4_Invariant.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Lemma lem:invariant-plane ("Invariant extension of an isotropic plane") of
    the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation), label lem:invariant-plane.
    Setting: a real vector space V with a symmetric bilinear form ip (not assumed nondegenerate), a parameter space
    C, a linear map p : C -> V (the p_c) and operators B_c = B c (linear in c and in the argument) that are
    self-adjoint for ip.  P = range p.  Hypotheses of the lemma: P isotropic, B_c p_d = B_d p_c,
    [B_c,B_d] P subset P, [B_c,B_d] P^perp subset P, <p_c, B_c^j p_c> = 0 for j = 1..4.
    Proved (every symmetry the proof asserts is derived from these hypotheses, with the general polarization
    theorem BSR_m4_Polar.polar of arbitrary arity):
      T_zero    the trilinear form <p_c, B_d p_e> vanishes            (B_c P subset P^perp)
      R_zero    the four-linear form <B_c p_d, B_e p_f> vanishes      (uses [B,B]P subset P and P isotropic)
      P'_iso    P' = span(P u {B_c p_d}) is totally isotropic
      U_zero    the five-linear form <B_i B_j p_k, B_l p_m> vanishes   (uses both commutator hypotheses)
      invariant_dim3  if the quotient P'^perp/P' is positive definite (hypothesis pos), B_i P' subset P' for all i
      invariant_dim2  if B_c p_d in P for all c, d (P' = P), P is invariant.
    Not formalized: that the negative index <= 3 of W gives dim P' <= 3 and the positivity of P'^perp/P' when
    dim P' = 3 (Witt's theorem); pos is an explicit hypothesis, used only to turn <x,x> = 0, x perpendicular to P',
    into x in P'.  The dimension count "dim P' is two or three" is therefore not part of the conclusion.
*)

theory BSR_m4_Invariant
  imports BSR_m4_Polar
begin

locale iso_setup =
  fixes ip :: "'v::real_vector \<Rightarrow> 'v \<Rightarrow> real"
    and p :: "'c::real_vector \<Rightarrow> 'v"
    and B :: "'c \<Rightarrow> 'v \<Rightarrow> 'v"
  assumes ip_add1: "\<And>x x' y. ip (x + x') y = ip x y + ip x' y"
    and ip_sc1: "\<And>s x y. ip (s *\<^sub>R x) y = s * ip x y"
    and ip_sym: "\<And>x y. ip x y = ip y x"
    and p_add: "\<And>c c'. p (c + c') = p c + p c'"
    and p_sc: "\<And>s c. p (s *\<^sub>R c) = s *\<^sub>R p c"
    and B_add_c: "\<And>c c' x. B (c + c') x = B c x + B c' x"
    and B_sc_c: "\<And>s c x. B (s *\<^sub>R c) x = s *\<^sub>R B c x"
    and B_add_x: "\<And>c x y. B c (x + y) = B c x + B c y"
    and B_sc_x: "\<And>c s x. B c (s *\<^sub>R x) = s *\<^sub>R B c x"
    and selfadj: "\<And>c x y. ip (B c x) y = ip x (B c y)"
    and iso: "\<And>c d. ip (p c) (p d) = 0"
    and Bsym: "\<And>c d. B c (p d) = B d (p c)"
    and comm1: "\<And>c d e. B c (B d (p e)) - B d (B c (p e)) \<in> range p"
    and comm2: "\<And>c d x. (\<And>e. ip x (p e) = 0) \<Longrightarrow> B c (B d x) - B d (B c x) \<in> range p"
    and mom1: "\<And>c. ip (p c) ((B c ^^ 1) (p c)) = 0"
    and mom2: "\<And>c. ip (p c) ((B c ^^ 2) (p c)) = 0"
    and mom3: "\<And>c. ip (p c) ((B c ^^ 3) (p c)) = 0"
    and mom4: "\<And>c. ip (p c) ((B c ^^ 4) (p c)) = 0"
begin

lemma ip_add2: "ip x (y + y') = ip x y + ip x y'" using ip_add1 ip_sym by metis
lemma ip_sc2: "ip x (s *\<^sub>R y) = s * ip x y" using ip_sc1 ip_sym by metis
lemma ip_0_2: "ip x 0 = 0" using ip_sc2[of x 0 0] by simp
lemma ip_0_1: "ip 0 y = 0" using ip_sym ip_0_2 by metis

lemma B_0_x: "B c 0 = 0" using B_sc_x[of c 0 0] by simp
lemma p_0: "p 0 = 0" using p_sc[of 0 0] by simp

lemma pw1: "(B c ^^ 1) y = B c y" by simp
lemma pw2: "(B c ^^ 2) y = B c (B c y)" by (simp add: eval_nat_numeral)
lemma pw3: "(B c ^^ 3) y = B c (B c (B c y))" by (simp add: eval_nat_numeral)
lemma pw4: "(B c ^^ 4) y = B c (B c (B c (B c y)))" by (simp add: eval_nat_numeral)

lemma e2: "Suc (Suc 0) = 2" by simp

lemma ip_range_p: "x \<in> range p \<Longrightarrow> ip x (p e) = 0"
  using iso by auto

subsection \<open>Kernels of linear functionals on a span\<close>

lemma ker_span:
  assumes lin: "linear phi" and G: "\<And>x. x \<in> G \<Longrightarrow> phi x = 0" and x: "x \<in> span G"
  shows "phi x = 0"
proof -
  have ker: "subspace {y. phi y = 0}"
    by (simp add: subspace_def linear_0[OF lin] linear_add[OF lin] linear_cmul[OF lin])
  have "G \<subseteq> {y. phi y = 0}" using G by auto
  from span_minimal[OF this ker] x show ?thesis by blast
qed

lemma lin_ip1: "linear (\<lambda>x. ip x y)"
  by (simp add: linear_iff ip_add1 ip_sc1)
lemma lin_ip2: "linear (\<lambda>y. ip x y)"
  by (simp add: linear_iff ip_add2 ip_sc2)
lemma lin_B: "linear (B c)"
  by (simp add: linear_iff B_add_x B_sc_x)
lemma lin_ipB: "linear (\<lambda>x. ip (B c x) y)"
  by (simp add: linear_iff B_add_x B_sc_x ip_add1 ip_sc1)

subsection \<open>The trilinear form: B_c P is perpendicular to P\<close>

definition vec3 :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c" where
  "vec3 c d e = (\<lambda>i. if i = 0 then c else if i = 1 then d else e)"

definition fT :: "(nat \<Rightarrow> 'c) \<Rightarrow> real" where
  "fT v = ip (p (v 0)) (B (v 1) (p (v 2)))"

lemma T_swap01: "ip (p d) (B c (p e)) = ip (p c) (B d (p e))"
proof -
  have "ip (p d) (B c (p e)) = ip (B c (p d)) (p e)" by (rule selfadj[symmetric])
  also have "B c (p d) = B d (p c)" by (rule Bsym)
  also have "ip (B d (p c)) (p e) = ip (p c) (B d (p e))" by (rule selfadj)
  finally show ?thesis .
qed

interpretation Tf: pol_form 3 fT
proof
  fix v w :: "nat \<Rightarrow> 'c"
  assume h: "\<And>i. i < 3 \<Longrightarrow> v i = w i"
  show "fT v = fT w" using h[of 0] h[of 1] h[of 2] by (simp add: fT_def)
next
  fix v :: "nat \<Rightarrow> 'c" and i :: nat and a b :: 'c
  assume i: "i < 3"
  then have "i = 0 \<or> i = 1 \<or> i = 2" by arith
  then show "fT (v(i := a + b)) = fT (v(i := a)) + fT (v(i := b))"
    by (elim disjE) (simp_all add: fT_def p_add ip_add1 ip_add2 B_add_c B_add_x)
next
  fix v :: "nat \<Rightarrow> 'c" and i :: nat and s :: real and a :: 'c
  assume i: "i < 3"
  then have "i = 0 \<or> i = 1 \<or> i = 2" by arith
  then show "fT (v(i := s *\<^sub>R a)) = s * fT (v(i := a))"
    by (elim disjE) (simp_all add: fT_def p_sc ip_sc1 ip_sc2 B_sc_c B_sc_x)
next
  fix v :: "nat \<Rightarrow> 'c" and i
  assume i: "Suc i < 3"
  then have "i = 0 \<or> i = 1" by arith
  then show "fT (v \<circ> Fun.swap i (Suc i) id) = fT v"
    by (elim disjE) (simp_all add: fT_def Fun.swap_def T_swap01 Bsym e2)
qed

lemma T_zero: "ip (p c) (B d (p e)) = 0"
proof -
  have "fT (vec3 c d e) = 0" by (rule Tf.polar) (simp add: fT_def mom1[unfolded pw1])
  then show ?thesis by (simp add: fT_def vec3_def)
qed

lemma B_perp: "ip (B d (p e)) (p c) = 0"
  using T_zero[of c d e] by (simp add: ip_sym)

subsection \<open>The four-linear form R(c,d,e,f) = <B_c p_d, B_e p_f>\<close>

definition vec4 :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c" where
  "vec4 c d e f = (\<lambda>i. if i = 0 then c else if i = 1 then d else if i = 2 then e else f)"

definition fR :: "(nat \<Rightarrow> 'c) \<Rightarrow> real" where
  "fR v = ip (B (v 1) (p (v 0))) (B (v 2) (p (v 3)))"

lemma R_swap: "ip (B e (p d)) (B c (p f)) = ip (B c (p d)) (B e (p f))"
proof -
  have "ip (B e (p d)) (B c (p f)) = ip (p d) (B e (B c (p f)))" by (rule selfadj)
  moreover have "ip (B c (p d)) (B e (p f)) = ip (p d) (B c (B e (p f)))" by (rule selfadj)
  moreover have "ip (p d) (B e (B c (p f)) - B c (B e (p f))) = 0"
  proof -
    obtain g where g: "B e (B c (p f)) - B c (B e (p f)) = p g" using comm1[of e c f] by auto
    then show ?thesis using iso by simp
  qed
  moreover have "ip (p d) (B e (B c (p f)) - B c (B e (p f)))
      = ip (p d) (B e (B c (p f))) - ip (p d) (B c (B e (p f)))"
    using ip_add2[of "p d" "B e (B c (p f))" "- (B c (B e (p f)))"] ip_sc2[of "p d" "-1" "B c (B e (p f))"]
    by (simp add: algebra_simps)
  ultimately show ?thesis by simp
qed

interpretation Rf: pol_form 4 fR
proof
  fix v w :: "nat \<Rightarrow> 'c"
  assume h: "\<And>i. i < 4 \<Longrightarrow> v i = w i"
  show "fR v = fR w" using h[of 0] h[of 1] h[of 2] h[of 3] by (simp add: fR_def)
next
  fix v :: "nat \<Rightarrow> 'c" and i :: nat and a b :: 'c
  assume i: "i < 4"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by arith
  then show "fR (v(i := a + b)) = fR (v(i := a)) + fR (v(i := b))"
    by (elim disjE) (simp_all add: fR_def p_add ip_add1 ip_add2 B_add_c B_add_x)
next
  fix v :: "nat \<Rightarrow> 'c" and i :: nat and s :: real and a :: 'c
  assume i: "i < 4"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by arith
  then show "fR (v(i := s *\<^sub>R a)) = s * fR (v(i := a))"
    by (elim disjE) (simp_all add: fR_def p_sc ip_sc1 ip_sc2 B_sc_c B_sc_x)
next
  fix v :: "nat \<Rightarrow> 'c" and i
  assume i: "Suc i < 4"
  then have "i = 0 \<or> i = 1 \<or> i = 2" by arith
  then show "fR (v \<circ> Fun.swap i (Suc i) id) = fR v"
  proof (elim disjE)
    assume "i = 0" then show ?thesis by (simp add: fR_def Fun.swap_def Bsym)
  next
    assume "i = 1"
    then show ?thesis
      using R_swap[of "v 2" "v 0" "v 1" "v 3"] by (simp add: fR_def Fun.swap_def e2)
  next
    assume "i = 2" then show ?thesis by (simp add: fR_def Fun.swap_def Bsym)
  qed
qed

lemma R_zero: "ip (B c (p d)) (B e (p f)) = 0"
proof -
  have "fR (vec4 d c e f) = 0"
  proof (rule Rf.polar)
    fix x :: 'c
    have "ip (B x (p x)) (B x (p x)) = ip (p x) (B x (B x (p x)))" by (rule selfadj)
    then show "fR (\<lambda>_. x) = 0" using mom2[of x] by (simp add: fR_def pw2)
  qed
  then show ?thesis by (simp add: fR_def vec4_def)
qed

subsection \<open>The space P' = P + sum_c B_c P is totally isotropic\<close>

definition gens :: "'v set" where
  "gens = range p \<union> {x. \<exists>c d. x = B c (p d)}"

definition Pp :: "'v set" where
  "Pp = span gens"

lemma gens_p: "p c \<in> gens" by (simp add: gens_def)
lemma gens_Bp: "B c (p d) \<in> gens" by (auto simp: gens_def)
lemma Pp_p: "p c \<in> Pp" using gens_p by (simp add: Pp_def span_base)
lemma Pp_Bp: "B c (p d) \<in> Pp" using gens_Bp by (simp add: Pp_def span_base)

lemma gens_iso:
  assumes "x \<in> gens" "y \<in> gens"
  shows "ip x y = 0"
  using assms by (auto simp: gens_def iso T_zero B_perp R_zero)

theorem Pp_iso:
  assumes x: "x \<in> Pp" and y: "y \<in> Pp"
  shows "ip x y = 0"
proof -
  have "\<And>y0. y0 \<in> gens \<Longrightarrow> ip x y0 = 0"
  proof -
    fix y0 assume y0: "y0 \<in> gens"
    have "\<And>x0. x0 \<in> gens \<Longrightarrow> ip x0 y0 = 0" using gens_iso y0 by blast
    from ker_span[OF lin_ip1 this] x show "ip x y0 = 0" by (simp add: Pp_def)
  qed
  from ker_span[OF lin_ip2 this] y show ?thesis by (simp add: Pp_def)
qed

subsection \<open>The five-linear form U(i,j,k,l,m) = <B_i B_j p_k, B_l p_m>\<close>

definition vec5 :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c" where
  "vec5 k j i l m = (\<lambda>n. if n = 0 then k else if n = 1 then j else if n = 2 then i else if n = 3 then l else m)"

definition fU :: "(nat \<Rightarrow> 'c) \<Rightarrow> real" where
  "fU v = ip (B (v 2) (B (v 1) (p (v 0)))) (B (v 3) (p (v 4)))"

lemma comm_range:
  "B i (B j (p k)) - B j (B i (p k)) \<in> range p" using comm1 by blast

lemma ip_minus1: "ip (- y) z = - ip y z"
proof -
  have "ip (- y) z = ip ((- 1) *\<^sub>R y) z" by simp
  also have "\<dots> = (- 1) * ip y z" by (rule ip_sc1)
  finally show ?thesis by simp
qed

lemma ip_sub1: "ip (x - y) z = ip x z - ip y z"
proof -
  have "ip x z = ip ((x - y) + y) z" by simp
  also have "\<dots> = ip (x - y) z + ip y z" by (rule ip_add1)
  finally show ?thesis by simp
qed

lemma ip_sub2: "ip x (y - y') = ip x y - ip x y'"
  using ip_sub1[of y y' x] by (simp add: ip_sym)

lemma U_swap_inner: "ip (B i (B j (p k))) (B l (p m)) = ip (B j (B i (p k))) (B l (p m))"
proof -
  obtain g where g: "B i (B j (p k)) - B j (B i (p k)) = p g" using comm_range[of i j k] by auto
  have "ip (B i (B j (p k))) (B l (p m)) - ip (B j (B i (p k))) (B l (p m)) = ip (p g) (B l (p m))"
    using g ip_sub1[of "B i (B j (p k))" "B j (B i (p k))" "B l (p m)"] by simp
  also have "\<dots> = 0" using T_zero[of g l m] by simp
  finally show ?thesis by simp
qed

lemma U_swap_outer: "ip (B i (B j (p k))) (B l (p m)) = ip (B l (B j (p k))) (B i (p m))"
proof -
  have e1: "ip (B i (B j (p k))) (B l (p m)) = ip (B j (p k)) (B i (B l (p m)))" by (rule selfadj)
  have e2: "ip (B l (B j (p k))) (B i (p m)) = ip (B j (p k)) (B l (B i (p m)))" by (rule selfadj)
  obtain g where g: "B i (B l (p m)) - B l (B i (p m)) = p g" using comm_range[of i l m] by auto
  have "ip (B j (p k)) (B i (B l (p m))) - ip (B j (p k)) (B l (B i (p m))) = ip (B j (p k)) (p g)"
    using g ip_sub2[of "B j (p k)" "B i (B l (p m))" "B l (B i (p m))"] by simp
  also have "\<dots> = 0" using B_perp[of j k g] by (simp add: ip_sym)
  finally show ?thesis using e1 e2 by simp
qed

interpretation Uf: pol_form 5 fU
proof
  fix v w :: "nat \<Rightarrow> 'c"
  assume h: "\<And>i. i < 5 \<Longrightarrow> v i = w i"
  show "fU v = fU w" using h[of 0] h[of 1] h[of 2] h[of 3] h[of 4] by (simp add: fU_def)
next
  fix v :: "nat \<Rightarrow> 'c" and i :: nat and a b :: 'c
  assume i: "i < 5"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4" by arith
  then show "fU (v(i := a + b)) = fU (v(i := a)) + fU (v(i := b))"
    by (elim disjE) (simp_all add: fU_def p_add ip_add1 ip_add2 B_add_c B_add_x)
next
  fix v :: "nat \<Rightarrow> 'c" and i :: nat and s :: real and a :: 'c
  assume i: "i < 5"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4" by arith
  then show "fU (v(i := s *\<^sub>R a)) = s * fU (v(i := a))"
    by (elim disjE) (simp_all add: fU_def p_sc ip_sc1 ip_sc2 B_sc_c B_sc_x)
next
  fix v :: "nat \<Rightarrow> 'c" and i
  assume i: "Suc i < 5"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by arith
  then show "fU (v \<circ> Fun.swap i (Suc i) id) = fU v"
  proof (elim disjE)
    assume "i = 0" then show ?thesis by (simp add: fU_def Fun.swap_def Bsym)
  next
    assume "i = 1"
    then show ?thesis
      using U_swap_inner[where i = "v 2" and j = "v 1" and k = "v 0" and l = "v 3" and m = "v 4"]
      by (simp add: fU_def Fun.swap_def e2)
  next
    assume "i = 2"
    then show ?thesis
      using U_swap_outer[where i = "v 2" and j = "v 1" and k = "v 0" and l = "v 3" and m = "v 4"]
      by (simp add: fU_def Fun.swap_def e2)
  next
    assume "i = 3" then show ?thesis by (simp add: fU_def Fun.swap_def Bsym)
  qed
qed

lemma U_zero: "ip (B i (B j (p k))) (B l (p m)) = 0"
proof -
  have "fU (vec5 k j i l m) = 0"
  proof (rule Uf.polar)
    fix x :: 'c
    have "ip (B x (B x (p x))) (B x (p x)) = ip (B x (p x)) (B x (B x (p x)))" by (rule ip_sym)
    also have "\<dots> = ip (p x) (B x (B x (B x (p x))))" by (rule selfadj)
    finally show "fU (\<lambda>_. x) = 0" using mom3[of x] by (simp add: fU_def pw3)
  qed
  then show ?thesis by (simp add: fU_def vec5_def)
qed

subsection \<open>B_i maps P' into the orthogonal of P'\<close>

lemma B_perp_Pp:
  assumes x: "x \<in> Pp" and y: "y \<in> Pp"
  shows "ip (B i x) y = 0"
proof -
  have gg: "\<And>x0 y0. x0 \<in> gens \<Longrightarrow> y0 \<in> gens \<Longrightarrow> ip (B i x0) y0 = 0"
  proof -
    fix x0 y0 assume gx: "x0 \<in> gens" and gy: "y0 \<in> gens"
    have c1: "\<And>k l. ip (B i (p k)) (p l) = 0" by (rule B_perp)
    have c2: "\<And>k m l. ip (B i (p k)) (B m (p l)) = 0" by (rule R_zero)
    have c3: "\<And>j k l. ip (B i (B j (p k))) (p l) = 0"
    proof -
      fix j k l
      have "ip (B i (B j (p k))) (p l) = ip (B j (p k)) (B i (p l))" by (rule selfadj)
      then show "ip (B i (B j (p k))) (p l) = 0" using R_zero by simp
    qed
    have c4: "\<And>j k m l. ip (B i (B j (p k))) (B m (p l)) = 0" by (rule U_zero)
    from gx have "(\<exists>k. x0 = p k) \<or> (\<exists>j k. x0 = B j (p k))" by (auto simp: gens_def)
    moreover from gy have "(\<exists>l. y0 = p l) \<or> (\<exists>m l. y0 = B m (p l))" by (auto simp: gens_def)
    ultimately show "ip (B i x0) y0 = 0" using c1 c2 c3 c4 by auto
  qed
  have "\<And>y0. y0 \<in> gens \<Longrightarrow> ip (B i x) y0 = 0"
  proof -
    fix y0 assume y0: "y0 \<in> gens"
    have "\<And>x0. x0 \<in> gens \<Longrightarrow> ip (B i x0) y0 = 0" using gg y0 by blast
    from ker_span[OF lin_ipB this] x show "ip (B i x) y0 = 0" by (simp add: Pp_def)
  qed
  from ker_span[OF lin_ip2 this] y show ?thesis by (simp add: Pp_def)
qed

subsection \<open>Invariance of P'\<close>

theorem invariant_dim3:
  assumes pos: "\<And>x. (\<And>y. y \<in> Pp \<Longrightarrow> ip x y = 0) \<Longrightarrow> ip x x = 0 \<Longrightarrow> x \<in> Pp"
  shows "x \<in> Pp \<Longrightarrow> B i x \<in> Pp"
proof -
  have Pp_sub: "subspace Pp" by (simp add: Pp_def)
  have sq_perp: "\<And>c y. y \<in> Pp \<Longrightarrow> ip (B c (B c (p c))) y = 0"
  proof -
    fix c y assume y: "y \<in> Pp"
    show "ip (B c (B c (p c))) y = 0" by (rule B_perp_Pp[OF Pp_Bp[of c c] y])
  qed
  have sq_in: "\<And>c. B c (B c (p c)) \<in> Pp"
  proof -
    fix c
    have "ip (B c (B c (p c))) (B c (B c (p c))) = ip (B c (p c)) (B c (B c (B c (p c))))" by (rule selfadj)
    also have "\<dots> = ip (p c) (B c (B c (B c (B c (p c)))))" by (rule selfadj)
    finally have "ip (B c (B c (p c))) (B c (B c (p c))) = 0" using mom4[of c] by (simp add: pw4)
    with sq_perp show "B c (B c (p c)) \<in> Pp" by (rule pos)
  qed
  have BB_in: "\<And>i j k. B i (B j (p k)) \<in> Pp"
  proof -
    fix i j k
    have w_perp: "\<And>y. y \<in> Pp \<Longrightarrow> ip (B i (B j (p k))) y = 0" using B_perp_Pp[OF Pp_Bp] by simp
    have scalar: "\<And>y. (\<And>y'. y' \<in> Pp \<Longrightarrow> ip y y' = 0) \<Longrightarrow> ip (B i (B j (p k))) y = 0"
    proof -
      fix y assume yP: "\<And>y'. y' \<in> Pp \<Longrightarrow> ip y y' = 0"
      define fY :: "(nat \<Rightarrow> 'c) \<Rightarrow> real" where "fY = (\<lambda>v. ip (B (v 2) (B (v 1) (p (v 0)))) y)"
      interpret Yf: pol_form 3 fY
      proof
        fix v w :: "nat \<Rightarrow> 'c"
        assume h: "\<And>i. i < 3 \<Longrightarrow> v i = w i"
        show "fY v = fY w" using h[of 0] h[of 1] h[of 2] by (simp add: fY_def)
      next
        fix v :: "nat \<Rightarrow> 'c" and i :: nat and a b :: 'c
        assume i: "i < 3"
        then have "i = 0 \<or> i = 1 \<or> i = 2" by arith
        then show "fY (v(i := a + b)) = fY (v(i := a)) + fY (v(i := b))"
          by (elim disjE) (simp_all add: fY_def p_add ip_add1 ip_add2 B_add_c B_add_x)
      next
        fix v :: "nat \<Rightarrow> 'c" and i :: nat and s :: real and a :: 'c
        assume i: "i < 3"
        then have "i = 0 \<or> i = 1 \<or> i = 2" by arith
        then show "fY (v(i := s *\<^sub>R a)) = s * fY (v(i := a))"
          by (elim disjE) (simp_all add: fY_def p_sc ip_sc1 ip_sc2 B_sc_c B_sc_x)
      next
        fix v :: "nat \<Rightarrow> 'c" and i
        assume i: "Suc i < 3"
        then have "i = 0 \<or> i = 1" by arith
        then show "fY (v \<circ> Fun.swap i (Suc i) id) = fY v"
        proof (elim disjE)
          assume "i = 0" then show ?thesis by (simp add: fY_def Fun.swap_def Bsym)
        next
          assume "i = 1"
          obtain g where g: "B (v 2) (B (v 1) (p (v 0))) - B (v 1) (B (v 2) (p (v 0))) = p g"
            using comm_range[of "v 2" "v 1" "v 0"] by auto
          have "ip (B (v 2) (B (v 1) (p (v 0)))) y - ip (B (v 1) (B (v 2) (p (v 0)))) y = ip (p g) y"
            using g ip_sub1[of "B (v 2) (B (v 1) (p (v 0)))" "B (v 1) (B (v 2) (p (v 0)))" y] by simp
          moreover have "ip (p g) y = 0" using yP[OF Pp_p[of g]] by (simp add: ip_sym)
          ultimately show ?thesis using \<open>i = 1\<close> by (simp add: fY_def Fun.swap_def e2)
        qed
      qed
      have "fY (vec3 k j i) = 0"
      proof (rule Yf.polar)
        fix x :: 'c
        show "fY (\<lambda>_. x) = 0" using yP[OF sq_in[of x]] by (simp add: fY_def ip_sym)
      qed
      then show "ip (B i (B j (p k))) y = 0" by (simp add: fY_def vec3_def)
    qed
    have "ip (B i (B j (p k))) (B i (B j (p k))) = 0" by (rule scalar) (use w_perp in \<open>simp add: ip_sym\<close>)
    with w_perp show "B i (B j (p k)) \<in> Pp" by (intro pos) simp_all
  qed
  have "\<And>x. x \<in> Pp \<Longrightarrow> B i x \<in> Pp"
  proof -
    fix x assume x: "x \<in> Pp"
    have sub: "subspace {z. B i z \<in> Pp}"
      by (simp add: subspace_def B_0_x B_add_x B_sc_x span_add span_scale span_0 Pp_def)
    have "gens \<subseteq> {z. B i z \<in> Pp}"
    proof
      fix z assume "z \<in> gens"
      then obtain k j where "z = p k \<or> z = B j (p k)" by (auto simp: gens_def)
      then show "z \<in> {z. B i z \<in> Pp}" using Pp_Bp BB_in by auto
    qed
    from span_minimal[OF this sub] x show "B i x \<in> Pp" by (auto simp: Pp_def)
  qed
  then show "x \<in> Pp \<Longrightarrow> B i x \<in> Pp" by blast
qed

theorem invariant_dim2:
  assumes inP: "\<And>c d. B c (p d) \<in> range p"
  shows "Pp = range p" and "x \<in> range p \<Longrightarrow> B i x \<in> range p"
proof -
  have sub: "subspace (range p)"
    by (simp add: subspace_def p_0 p_add p_sc) (metis p_0 range_eqI p_add p_sc)
  have "gens \<subseteq> range p" using inP by (auto simp: gens_def)
  from span_minimal[OF this sub] have "Pp \<subseteq> range p" by (simp add: Pp_def)
  moreover have "range p \<subseteq> Pp" using Pp_p by auto
  ultimately show "Pp = range p" by blast
  show "x \<in> range p \<Longrightarrow> B i x \<in> range p" using inP by auto
qed

end

end
