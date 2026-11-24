(*  Title:      BSR_m4_LowIndex.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Algebraic steps of Lemma lem:low-index-four ("Low negative index") of
    the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation), label lem:low-index-four.
    (a) low_invariant, case k = 0, dim P = 3 (and, with the same proof, the case (k,h) = (1,2), rank <= 1,
        P_c = p_c phi): from <p_c, B_c p_c> = 0 polarization gives B_c P subset P^perp (T_zero_low);
        from <B_c p_c, B_c p_c> = <p_c, B_c^2 p_c> = 0 and P^perp/P positive definite, B_c p_c in P;
        with B_c p_d - B_d p_c in P, polarization gives B_c p_d in P for all c, d (B_c P subset P).
        The hypothesis B_c p_d = B_d p_c is weakened to "equal modulo P", which covers both cases.
    (b) rank2_invariant, case (k,h) = (1,2), dim P = 2, some P_c of rank two: (L2) gives A_c P subset P^perp
        and every vector of A_c P null, hence A_c P subset P (positive quotient).  generic_to_all: a linear
        condition in c that holds on a nonempty open set holds for every c ("first generically and then for every c").
    (c) count_*: the arithmetic of the beginning of the proof: (L1) and small rows give 2 <= h <= q <= 4 and
        r >= a+1; for r = a+1, k > 0: (k,h) in {(1,2),(2,3),(3,4)}.
    The positivity of P^perp/P (negative index, Witt) is an explicit hypothesis (pos), used only to turn
    "x perpendicular to P, <x,x> = 0" into "x in P".
    NOT formalized: the Schur complement expansion that produces (L2) (statement (d): the coefficients 2Q_c,
    -3P*P, 4P*AP, -5P*A^2P for general block matrices), the rank-one matrix-space classification, the
    consequence "the five rows map into an isotropic four-space, contradicting small rows" (BSR_m4_Small_Rows),
    and the case k = 0, dim P = 2 (Lemma invariant-plane, theory BSR_m4_Invariant).
*)

theory BSR_m4_LowIndex
  imports BSR_m4_Polar
begin

section \<open>(a) Polarization steps and positivity: B_c P is contained in P\<close>

locale low_setup =
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
    and Bsym_mod: "\<And>c d. B c (p d) - B d (p c) \<in> range p"
    and mom1: "\<And>c. ip (p c) (B c (p c)) = 0"
    and mom2: "\<And>c. ip (p c) (B c (B c (p c))) = 0"
begin

lemma ip_add2: "ip x (y + y') = ip x y + ip x y'" using ip_add1 ip_sym by metis
lemma ip_sc2: "ip x (s *\<^sub>R y) = s * ip x y" using ip_sc1 ip_sym by metis

lemma ip_sub1: "ip (x - y) z = ip x z - ip y z"
proof -
  have "ip x z = ip ((x - y) + y) z" by simp
  also have "\<dots> = ip (x - y) z + ip y z" by (rule ip_add1)
  finally show ?thesis by simp
qed

lemma ip_range_p1: "x \<in> range p \<Longrightarrow> ip x (p e) = 0" using iso by auto
lemma ip_range_p2: "x \<in> range p \<Longrightarrow> ip (p e) x = 0" using iso by auto

lemma e2: "Suc (Suc 0) = 2" by simp

definition vec3 :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c" where
  "vec3 c d e = (\<lambda>i. if i = 0 then c else if i = 1 then d else e)"

definition fT :: "(nat \<Rightarrow> 'c) \<Rightarrow> real" where
  "fT v = ip (p (v 0)) (B (v 1) (p (v 2)))"

lemma T_swap01: "ip (p d) (B c (p e)) = ip (p c) (B d (p e))"
proof -
  obtain g where g: "B c (p d) - B d (p c) = p g" using Bsym_mod[of c d] by auto
  have "ip (B c (p d)) (p e) - ip (B d (p c)) (p e) = ip (p g) (p e)"
    using g ip_sub1[of "B c (p d)" "B d (p c)" "p e"] by simp
  then have "ip (B c (p d)) (p e) = ip (B d (p c)) (p e)" using iso by simp
  then have "ip (p d) (B c (p e)) = ip (p c) (B d (p e))" by (simp add: selfadj)
  then show ?thesis .
qed

lemma T_swap12: "ip (p c) (B e (p d)) = ip (p c) (B d (p e))"
proof -
  obtain g where g: "B e (p d) - B d (p e) = p g" using Bsym_mod[of e d] by auto
  have "ip (p c) (B e (p d)) - ip (p c) (B d (p e)) = ip (p c) (p g)"
    using g ip_sub1[of "B e (p d)" "B d (p e)" "p c"] by (simp add: ip_sym)
  then show ?thesis using iso by simp
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
  proof (elim disjE)
    assume "i = 0" then show ?thesis using T_swap01[of "v 1" "v 0" "v 2"] by (simp add: fT_def Fun.swap_def)
  next
    assume "i = 1" then show ?thesis using T_swap12[of "v 0" "v 2" "v 1"] by (simp add: fT_def Fun.swap_def e2)
  qed
qed

theorem T_zero_low: "ip (p c) (B d (p e)) = 0"
proof -
  have "fT (vec3 c d e) = 0" by (rule Tf.polar) (simp add: fT_def mom1)
  then show ?thesis by (simp add: fT_def vec3_def)
qed

lemma B_perp_low: "ip (B d (p e)) (p c) = 0"
  using T_zero_low[of c d e] by (simp add: ip_sym)

definition vec2 :: "'c \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c" where
  "vec2 c d = (\<lambda>i. if i = 0 then c else d)"

theorem low_invariant:
  assumes pos: "\<And>x. (\<And>e. ip x (p e) = 0) \<Longrightarrow> ip x x = 0 \<Longrightarrow> x \<in> range p"
  shows "B c (p d) \<in> range p"
proof -
  have diag_in: "\<And>c. B c (p c) \<in> range p"
  proof -
    fix c
    have "ip (B c (p c)) (B c (p c)) = ip (p c) (B c (B c (p c)))" by (rule selfadj)
    then have "ip (B c (p c)) (B c (p c)) = 0" using mom2 by simp
    moreover have "\<And>e. ip (B c (p c)) (p e) = 0" by (rule B_perp_low)
    ultimately show "B c (p c) \<in> range p" by (rule pos[rotated])
  qed
  have scalar: "\<And>y. (\<And>e. ip y (p e) = 0) \<Longrightarrow> ip (B c (p d)) y = 0"
  proof -
    fix y assume yP: "\<And>e. ip y (p e) = 0"
    have yr: "\<And>x. x \<in> range p \<Longrightarrow> ip x y = 0" using yP ip_sym by auto
    define g :: "(nat \<Rightarrow> 'c) \<Rightarrow> real" where "g = (\<lambda>v. ip (B (v 0) (p (v 1))) y)"
    interpret Gf: pol_form 2 g
    proof
      fix v w :: "nat \<Rightarrow> 'c"
      assume h: "\<And>i. i < 2 \<Longrightarrow> v i = w i"
      show "g v = g w" using h[of 0] h[of 1] by (simp add: g_def)
    next
      fix v :: "nat \<Rightarrow> 'c" and i :: nat and a b :: 'c
      assume i: "i < 2"
      then have "i = 0 \<or> i = 1" by arith
      then show "g (v(i := a + b)) = g (v(i := a)) + g (v(i := b))"
        by (elim disjE) (simp_all add: g_def p_add ip_add1 ip_add2 B_add_c B_add_x)
    next
      fix v :: "nat \<Rightarrow> 'c" and i :: nat and s :: real and a :: 'c
      assume i: "i < 2"
      then have "i = 0 \<or> i = 1" by arith
      then show "g (v(i := s *\<^sub>R a)) = s * g (v(i := a))"
        by (elim disjE) (simp_all add: g_def p_sc ip_sc1 ip_sc2 B_sc_c B_sc_x)
    next
      fix v :: "nat \<Rightarrow> 'c" and i
      assume i: "Suc i < 2"
      then have "i = 0" by arith
      then show "g (v \<circ> Fun.swap i (Suc i) id) = g v"
      proof -
        obtain r where r: "B (v 1) (p (v 0)) - B (v 0) (p (v 1)) = p r" using Bsym_mod[of "v 1" "v 0"] by auto
        have "ip (B (v 1) (p (v 0))) y - ip (B (v 0) (p (v 1))) y = ip (p r) y"
          using r ip_sub1[of "B (v 1) (p (v 0))" "B (v 0) (p (v 1))" y] by simp
        moreover have "ip (p r) y = 0" using yr by auto
        ultimately show ?thesis using \<open>i = 0\<close> by (simp add: g_def Fun.swap_def)
      qed
    qed
    have "g (vec2 c d) = 0"
    proof (rule Gf.polar)
      fix x :: 'c
      show "g (\<lambda>_. x) = 0" using yr[OF diag_in[of x]] by (simp add: g_def)
    qed
    then show "ip (B c (p d)) y = 0" by (simp add: g_def vec2_def)
  qed
  have "ip (B c (p d)) (B c (p d)) = 0" by (rule scalar) (rule B_perp_low)
  moreover have "\<And>e. ip (B c (p d)) (p e) = 0" by (rule B_perp_low)
  ultimately show ?thesis by (rule pos[rotated])
qed

corollary low_invariant_P:
  assumes "\<And>x. (\<And>e. ip x (p e) = 0) \<Longrightarrow> ip x x = 0 \<Longrightarrow> x \<in> range p" and "x \<in> range p"
  shows "B c x \<in> range p"
  using low_invariant[OF assms(1)] assms(2) B_add_x by auto

end

section \<open>(b) Rank two: A_c P is contained in P\<close>

locale rank2_setup =
  fixes ip :: "'v::real_vector \<Rightarrow> 'v \<Rightarrow> real"
    and A :: "'v \<Rightarrow> 'v" and Pc :: "'u::real_vector \<Rightarrow> 'v"
  assumes ip_sym: "\<And>x y. ip x y = ip y x"
    and selfadj: "\<And>x y. ip (A x) y = ip x (A y)"
    and L2a: "\<And>u u'. ip (Pc u) (A (Pc u')) = 0"
    and L2b: "\<And>u u'. ip (Pc u) (A (A (Pc u'))) = 0"
begin

theorem rank2_invariant:
  assumes pos: "\<And>x. (\<And>y. y \<in> range Pc \<Longrightarrow> ip x y = 0) \<Longrightarrow> ip x x = 0 \<Longrightarrow> x \<in> range Pc"
  assumes x: "x \<in> range Pc"
  shows "A x \<in> range Pc"
proof -
  obtain u where u: "x = Pc u" using x by auto
  have perp: "\<And>y. y \<in> range Pc \<Longrightarrow> ip (A x) y = 0"
  proof -
    fix y assume "y \<in> range Pc"
    then obtain u' where u': "y = Pc u'" by auto
    have "ip (A x) y = ip x (A y)" by (rule selfadj)
    then show "ip (A x) y = 0" using u u' L2a by simp
  qed
  have "ip (A x) (A x) = ip x (A (A x))" by (rule selfadj)
  also have "\<dots> = 0" using u L2b by simp
  finally have "ip (A x) (A x) = 0" .
  from pos[OF perp this] show ?thesis .
qed

end

text \<open>"First generically and then for every c": a linear condition in c that holds on a nonempty open set holds
  everywhere.\<close>

lemma subspace_open_all:
  fixes T :: "'c::real_normed_vector set"
  assumes sub: "subspace T" and S: "open S" "S \<noteq> {}" "S \<subseteq> T"
  shows "T = UNIV"
proof -
  obtain s where s: "s \<in> S" using S(2) by auto
  obtain e where e: "e > 0" "ball s e \<subseteq> S" using S(1) s by (meson openE)
  have all: "\<And>x. x \<in> T"
  proof -
    fix x
    show "x \<in> T"
    proof (cases "x = 0")
      case True then show ?thesis using sub by (simp add: subspace_0)
    next
      case False
      let ?t = "e / (2 * norm x)"
      have tpos: "0 < ?t" using e False by simp
      have "s + ?t *\<^sub>R x \<in> ball s e"
        using e False by (simp add: dist_norm)
      then have "s + ?t *\<^sub>R x \<in> T" using e S(3) by auto
      moreover have "s \<in> T" using s S(3) by auto
      ultimately have "?t *\<^sub>R x \<in> T" using sub subspace_diff[OF sub, of "s + ?t *\<^sub>R x" s] by simp
      then have "inverse ?t *\<^sub>R (?t *\<^sub>R x) \<in> T" using sub subspace_scale by blast
      moreover have "inverse ?t *\<^sub>R (?t *\<^sub>R x) = x" using tpos e(1) False by (simp add: field_simps)
      ultimately show "x \<in> T" by simp
    qed
  qed
  then show ?thesis by auto
qed

theorem generic_to_all:
  fixes A :: "'c::real_normed_vector \<Rightarrow> 'v::real_vector \<Rightarrow> 'v" and Pset :: "'v set"
  assumes A_add: "\<And>c c' x. A (c + c') x = A c x + A c' x"
    and A_sc: "\<And>s c x. A (s *\<^sub>R c) x = s *\<^sub>R A c x"
    and Psub: "subspace Pset"
    and open_set: "open S" "S \<noteq> {}" and gen: "\<And>c x. c \<in> S \<Longrightarrow> x \<in> Pset \<Longrightarrow> A c x \<in> Pset"
  shows "x \<in> Pset \<Longrightarrow> A c x \<in> Pset"
proof -
  let ?T = "{c. \<forall>x\<in>Pset. A c x \<in> Pset}"
  have "subspace ?T"
  proof (rule subspaceI)
    show "0 \<in> ?T"
    proof -
      have "A 0 x = 0" for x using A_sc[of 0 0 x] by simp
      then show ?thesis using Psub by (simp add: subspace_0)
    qed
    show "\<And>x y. x \<in> ?T \<Longrightarrow> y \<in> ?T \<Longrightarrow> x + y \<in> ?T"
    proof (intro CollectI ballI)
      fix x y z assume hx: "x \<in> ?T" and hy: "y \<in> ?T" and hz: "z \<in> Pset"
      have "A x z \<in> Pset" "A y z \<in> Pset" using hx hy hz by auto
      then show "A (x + y) z \<in> Pset" using A_add[of x y z] subspace_add[OF Psub] by simp
    qed
    show "\<And>c x. x \<in> ?T \<Longrightarrow> c *\<^sub>R x \<in> ?T"
    proof (intro CollectI ballI)
      fix c x z assume hx: "x \<in> ?T" and hz: "z \<in> Pset"
      have "A x z \<in> Pset" using hx hz by auto
      then show "A (c *\<^sub>R x) z \<in> Pset" using A_sc[of c x z] subspace_scale[OF Psub] by simp
    qed
  qed
  moreover have "S \<subseteq> ?T" using gen by auto
  ultimately have "?T = UNIV" using subspace_open_all open_set by blast
  then show "x \<in> Pset \<Longrightarrow> A c x \<in> Pset" by auto
qed

section \<open>(c) The counting at the start of the proof\<close>

text \<open>Notation of the paper: a = effective row support, s = rank T_{b_0}, k = a - s, h = dim (U inter U^perp),
  q = negative index, r = rank H.  Hypotheses (each one is a statement of the paper's text, not proved here):
  L1h  (k > 0): 2 <= h (nonzero complex row maps have rank >= 2) and h <= q (U inter U^perp is isotropic);
  hq   q <= 4;
  hrs  (k > 0): h <= r - s;
  SR   (k > 0): the case k >= h contradicts Lemma small-rows (an h-plane of ker T_{b_0} maps into the isotropic h-plane);
  K0   (k = 0): r <= a is impossible (commuting self-adjoint slices have a common eigenvector: rank-one row).\<close>

theorem count_r_ge_a1:
  fixes a s k h q r :: nat
  assumes a_def: "a = s + k"
    and L1h: "0 < k \<Longrightarrow> 2 \<le> h \<and> h \<le> q" and hq: "q \<le> 4"
    and hrs: "0 < k \<Longrightarrow> h \<le> r - s"
    and SR: "0 < k \<Longrightarrow> h \<le> k \<Longrightarrow> False"
    and K0: "k = 0 \<Longrightarrow> r \<le> a \<Longrightarrow> False"
  shows "a + 1 \<le> r"
proof (rule ccontr)
  assume "\<not> a + 1 \<le> r"
  then have ra: "r \<le> a" by simp
  show False
  proof (cases "k = 0")
    case True then show ?thesis using K0 ra by simp
  next
    case False
    then have kpos: "0 < k" by simp
    have "h \<le> k" using hrs[OF kpos] ra a_def by simp
    then show ?thesis using SR[OF kpos] by simp
  qed
qed

theorem count_kh:
  fixes a s k h q r :: nat
  assumes a_def: "a = s + k"
    and L1h: "0 < k \<Longrightarrow> 2 \<le> h \<and> h \<le> q" and hq: "q \<le> 4"
    and hrs: "0 < k \<Longrightarrow> h \<le> r - s"
    and SR: "0 < k \<Longrightarrow> h \<le> k \<Longrightarrow> False"
    and ra: "r = a + 1" and kpos: "0 < k"
  shows "(k = 1 \<and> h = 2) \<or> (k = 2 \<and> h = 3) \<or> (k = 3 \<and> h = 4)"
proof -
  have "k < h" using SR[OF kpos] by (meson not_less)
  moreover have "h \<le> k + 1" using hrs[OF kpos] ra a_def by simp
  moreover have "2 \<le> h" "h \<le> 4" using L1h[OF kpos] hq by simp_all
  ultimately show ?thesis by arith
qed

end
