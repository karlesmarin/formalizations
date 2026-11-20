(*  Title:      Prop_Aux.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Proposition 7.2 (prop:aux, "the case q = e^perp of Theorem one") of the paper "Rational sums-of-squares
   lengths of biquadratic forms and orthogonal dilations" (Carles Marín, in preparation), built on top of the
   theory Rational_Plane_Rotations (queue entry 265; imported unmodified through the session
   LengthsPlaneRotations, whose copy lives in the subfolder lib265).

   STATUS: PARTIAL. Two parts are unconditional, one is conditional on two named assumptions.

   Setting. 'n and 'h are finite types, n = CARD('n) >= 3, h = CARD('h); vectors are rat^'n (dotp = standard
   scalar product), e = (1,...,1), H_n = (J - I)/(n - 1), lam = -1/(n - 1). The space Q^n (+) Q^h is rat^('n + 'h);
   V p = { (x, y) : x . e = 0, y in p } is the form "q perp p" of the paper (q = restriction of the standard
   product to e^perp, p a subspace of Q^h with the form I_h restricted).

   (a) The rational length. The paper defines l_Q(H) <= r by "P_H is a sum of r squares of bilinear forms
       over Q" and proves (Proposition 2.1) that this is equivalent to: there are A, B in Q^{r x n} with
       A^T A = B^T B = I and A^T B + B^T A = 2H. We use THAT matrix form (repr_Q; len_le with an index type of
       cardinality r; for r = n + h the index type is 'n + 'h). The equivalence with sums of squares
       (Proposition 2.1, (1) <=> (2)) is not formalized here.

   (b) UNCONDITIONAL (planes_give_length, length_le_of_planes): if p is a subspace of Q^h and V p has an
       orthogonal basis of planes of type lam (planes of the theory 265), then there are A = (I;0) and B with
       repr_Q H_n A B, i.e. l_Q(H_n) <= n + h, and the image of the last h rows D of B lies in p (so
       rank D <= dim p, the "d_Q <= dim p" of the paper). No assumption other than n >= 3.

   (c) UNCONDITIONAL linear algebra of the converse direction (section "Converse direction"): from a
       representation A = (I;0), B = (T;D) (the normal form of Proposition 2.1 (3); the normalization A = (I;0)
       is the Witt-cancellation step of Proposition 2.1 and is NOT formalized) we get T e = e, D e = 0,
       T^T e = e, T = lam + S on e^perp with S skew and e^perp-stable, Delta = I - T^T T = delta + S^2 = D^T D
       on e^perp, the splitting Q^n = ker Delta (+) im Delta (orthogonal, with im Delta inside e^perp), and the
       exact algebraic identity q((iota + S) x, (iota + S) y) = - q(Delta x, y) with iota^2 = -delta, proved on
       pairs (u, v) = u + iota v of rational vectors (section "The iota identity").
       NOT formalized: that the form on W_L = im Delta (x) L, transported by iota + S, makes (q perp p)_L
       hyperbolic (needs quadratic forms over L = Q(sqrt(-delta)) and Witt cancellation over L).

   (d) The statement of the paper (locale prop_aux_hyp). The predicate "(q perp p)_L is hyperbolic" is a locale
       parameter hyp (a predicate on subspaces of rat^('n + 'h)), constrained ONLY by two named assumptions:
         hyperbolic_iff_planes : hyp S <=> S has an orthogonal basis of planes of type lam
                                 (the plane extraction of Theorem 5.1 plus Witt cancellation over L, A08);
         hyp_of_representation : if (T, D) represents H_n then hyp (V (D(e^perp)))
                                 (the last step of the converse of prop:aux, W_L = -r_L, point (c) above).
       From them: prop_aux_if / prop_aux_only_if / prop_aux_normal_form prove, for representations in the normal
       form A = (I;0): exists B with repr_Q H_n (I;0) B  <=>  exists a subspace p of Q^h with hyp (V p), and then
       the defect clause holds (image of D inside p, so rank D <= dim p). The final theorem prop_aux, with an
       arbitrary A (the statement "l_Q(H_n) <= n + h" of the paper), takes in addition the Witt normalization
       A = (I;0) of Proposition 2.1 ((2) implies (3)) as a third named premise witt_normalization.
       All of (d) is therefore CONDITIONAL on hyperbolic_iff_planes, hyp_of_representation and (for prop_aux
       only) witt_normalization; (b) and (c) are not. hyp is abstract: the two assumptions are the only things
       said about it, so (d) is a reduction to those two statements, not a proof of them.

   Not formalized, in summary: Proposition 2.1 (1) <=> (2) (sums of squares versus matrices) and (2) => (3)
   (Witt); the plane extraction (hyperbolic => orthogonal sum of planes); the last step of the converse.
   Hypothesis not written in the proposition: n >= 3 (the paper says "let n >= 3" in the Reduction paragraph
   before prop:aux, lengths.tex l.639; for n = 2, lam = -1 and delta = 0).
*)
theory Prop_Aux
  imports "LengthsPlaneRotations.Rational_Plane_Rotations"
begin

section \<open>Setting: e, H_n, lambda, and the sum space\<close>

definition evec :: "rat^'n::finite" where "evec = (\<chi> i. 1)"

definition lamn :: "'n::finite itself \<Rightarrow> rat" where
  "lamn _ = - 1 / (of_nat CARD('n) - 1)"

definition Hn :: "rat^'n::finite^'n" where
  "Hn = (\<chi> i j. if i = j then 0 else 1 / (of_nat CARD('n) - 1))"

lemma evec_comp [simp]: "(evec::rat^'n::finite) $ i = 1"
  by (simp add: evec_def)

lemma dotp_evec: "dotp x evec = (\<Sum>i\<in>UNIV. x $ i)"
  by (simp add: dotp_def evec_def)

lemma dotp_evec_evec: "dotp (evec::rat^'n::finite) evec = of_nat CARD('n)"
  by (simp add: dotp_def evec_def)

lemma dotp_nonneg: "0 \<le> dotp w w"
proof (cases "w = 0")
  case True then show ?thesis by simp
next
  case False then show ?thesis by (simp add: dotp_pos less_imp_le)
qed

lemma dotp_self_zero: "dotp w w = 0 \<Longrightarrow> w = 0"
  using dotp_pos by force

lemma three_le_rat:
  assumes "3 \<le> CARD('n::finite)"
  shows "(3::rat) \<le> of_nat CARD('n)"
proof -
  have "(of_nat 3::rat) \<le> of_nat CARD('n)" by (rule of_nat_mono[OF assms])
  then show ?thesis by simp
qed

lemma lamn_range:
  assumes "3 \<le> CARD('n::finite)"
  shows "- 1 < lamn TYPE('n)" "lamn TYPE('n) < 1"
proof -
  have m3: "(3::rat) \<le> of_nat CARD('n)" by (rule three_le_rat[OF assms])
  have pos: "0 < (of_nat CARD('n)::rat) - 1" using m3 by linarith
  have "1 / ((of_nat CARD('n)::rat) - 1) < 1" using m3 pos by (simp add: divide_less_eq)
  moreover have "0 < 1 / ((of_nat CARD('n)::rat) - 1)" using pos by simp
  moreover have "lamn TYPE('n) = - (1 / ((of_nat CARD('n)::rat) - 1))" by (simp add: lamn_def)
  ultimately show "- 1 < lamn TYPE('n)" "lamn TYPE('n) < 1" by linarith+
qed

lemma mv_smult:
  fixes A :: "rat^'m::finite^'n::finite"
  shows "A *v (c *s x) = c *s (A *v x)"
proof (rule vec_eq_iff[THEN iffD2], rule allI)
  fix i
  have "(\<Sum>j\<in>UNIV. A $ i $ j * (c * x $ j)) = (\<Sum>j\<in>UNIV. c * (A $ i $ j * x $ j))"
    by (rule sum.cong[OF refl]) (simp add: algebra_simps)
  then show "(A *v (c *s x)) $ i = (c *s (A *v x)) $ i"
    by (simp add: matrix_vector_mult_def sum_distrib_left)
qed

lemma mat_eq_iff_dotp:
  fixes A B :: "rat^'m::finite^'n::finite"
  shows "A = B \<longleftrightarrow> (\<forall>x y. dotp x (A *v y) = dotp x (B *v y))"
  using mat_eq_by_dotp by auto

lemma dotp_tAB: "dotp x ((transpose A ** B) *v y) = dotp (A *v x) (B *v y)"
  by (simp add: mv_mv dotp_mv)

lemma Hn_mv:
  "(Hn::rat^'n::finite^'n) *v y = (1 / (of_nat CARD('n) - 1)) *s (dotp y evec *s evec - y)"
proof (rule vec_eq_iff[THEN iffD2], rule allI)
  fix i
  let ?a = "1 / (of_nat CARD('n) - 1) :: rat"
  have t: "\<And>j. (if i = j then 0 else ?a) * y $ j = ?a * y $ j - (if j = i then ?a * y $ j else 0)"
    by (auto)
  have "(Hn *v y) $ i = (\<Sum>j\<in>UNIV. (if i = j then 0 else ?a) * y $ j)"
    by (simp add: Hn_def matrix_vector_mult_def)
  also have "\<dots> = (\<Sum>j\<in>UNIV. ?a * y $ j) - (\<Sum>j\<in>UNIV. if j = i then ?a * y $ j else 0)"
    by (simp add: t sum_subtractf)
  also have "\<dots> = ?a * (\<Sum>j\<in>UNIV. y $ j) - ?a * y $ i"
    by (simp add: sum_distrib_left)
  finally show "(Hn *v y) $ i = (?a *s (dotp y evec *s evec - y)) $ i"
    by (simp add: dotp_evec algebra_simps)
qed

lemma dotp_Hn:
  "dotp x ((Hn::rat^'n::finite^'n) *v y)
   = (1 / (of_nat CARD('n) - 1)) * (dotp x evec * dotp y evec - dotp x y)"
  by (simp only: Hn_mv dotp_smult_right dotp_diff_right, simp add: mult.commute)

lemma alg_id:
  fixes n xy se te :: rat
  assumes "n \<noteq> 0" "n \<noteq> 1"
  shows "2 * (- 1 / (n - 1)) * (xy - te / n * se) + 2 * (te / n * se)
       = 2 * (1 / (n - 1) * (se * te - xy))"
proof -
  have "n - 1 \<noteq> 0" using assms(2) by simp
  then show ?thesis using assms(1) by (simp add: divide_simps algebra_simps)
qed

section \<open>The rational length (matrix form of Proposition 2.1)\<close>

definition repr_Q :: "rat^'n::finite^'n \<Rightarrow> rat^'n^'r::finite \<Rightarrow> rat^'n^'r \<Rightarrow> bool" where
  "repr_Q H A B \<longleftrightarrow> transpose A ** A = mat 1 \<and> transpose B ** B = mat 1
      \<and> transpose A ** B + transpose B ** A = sm 2 H"

definition len_le :: "'r::finite itself \<Rightarrow> rat^'n::finite^'n \<Rightarrow> bool" where
  "len_le _ H \<longleftrightarrow> (\<exists>A B::rat^'n^'r. repr_Q H A B)"

section \<open>The sum space rat^('n + 'h)\<close>

definition emb :: "rat^'n::finite \<Rightarrow> rat^('n + 'h::finite)" where
  "emb x = (\<chi> i. case i of Inl j \<Rightarrow> x $ j | Inr _ \<Rightarrow> 0)"

definition fstv :: "rat^('n::finite + 'h::finite) \<Rightarrow> rat^'n" where
  "fstv v = (\<chi> j. v $ Inl j)"

definition sndv :: "rat^('n::finite + 'h::finite) \<Rightarrow> rat^'h" where
  "sndv v = (\<chi> j. v $ Inr j)"

lemma emb_comp [simp]: "emb x $ Inl j = x $ j" "emb x $ Inr j = 0"
  by (simp_all add: emb_def)

lemma fstv_comp [simp]: "fstv v $ j = v $ Inl j"
  by (simp add: fstv_def)

lemma sndv_comp [simp]: "sndv v $ j = v $ Inr j"
  by (simp add: sndv_def)

lemma fstv_emb [simp]: "fstv (emb x) = x" by (simp add: vec_eq_iff emb_def)
lemma sndv_emb [simp]: "sndv (emb x) = 0" by (simp add: vec_eq_iff emb_def)

lemma fstv_add: "fstv (a + b) = fstv a + fstv b" by (simp add: vec_eq_iff)
lemma sndv_add: "sndv (a + b) = sndv a + sndv b" by (simp add: vec_eq_iff)

lemma emb_add: "emb (x + y) = emb x + emb y"
  by (simp add: vec_eq_iff emb_def split: sum.splits)

lemma emb_diff: "emb (x - y) = emb x - emb y"
  by (simp add: vec_eq_iff emb_def split: sum.splits)

lemma emb_smult: "emb (c *s x) = c *s emb x"
  by (simp add: vec_eq_iff emb_def split: sum.splits)

lemma dotp_split:
  fixes v w :: "rat^('n::finite + 'h::finite)"
  shows "dotp v w = dotp (fstv v) (fstv w) + dotp (sndv v) (sndv w)"
proof -
  have "(\<Sum>i\<in>(UNIV::('n + 'h) set). v $ i * w $ i)
      = (\<Sum>j\<in>(UNIV::'n set). v $ Inl j * w $ Inl j) + (\<Sum>j\<in>(UNIV::'h set). v $ Inr j * w $ Inr j)"
    by (subst UNIV_Plus_UNIV[symmetric], subst sum.Plus) (simp_all add: comp_def)
  then show ?thesis by (simp add: dotp_def)
qed

lemma dotp_emb_left: "dotp (emb x) v = dotp x (fstv v)"
  by (simp add: dotp_split)

lemma dotp_emb_emb: "dotp (emb x) (emb y) = dotp x y"
  by (simp add: dotp_emb_left)

definition iota_mat :: "rat^'n::finite^('n + 'h::finite)" where
  "iota_mat = (\<chi> i j. case i of Inl a \<Rightarrow> (if a = j then 1 else 0) | Inr _ \<Rightarrow> 0)"

lemma iota_mv: "iota_mat *v x = emb x"
proof (rule vec_eq_iff[THEN iffD2], rule allI)
  fix i
  show "(iota_mat *v x) $ i = emb x $ i"
  proof (cases i)
    case (Inl a)
    have "(\<Sum>j\<in>UNIV. (if a = j then 1 else 0) * x $ j) = (\<Sum>j\<in>UNIV. if j = a then x $ j else 0)"
      by (rule sum.cong[OF refl]) auto
    also have "\<dots> = x $ a" by simp
    finally have "(\<Sum>j\<in>UNIV. (if a = j then 1 else 0) * x $ j) = x $ a" .
    then show ?thesis using Inl by (simp add: iota_mat_def matrix_vector_mult_def)
  next
    case (Inr b)
    then show ?thesis by (simp add: iota_mat_def matrix_vector_mult_def emb_def)
  qed
qed

lemma iota_orth: "transpose (iota_mat::rat^'n::finite^('n + 'h::finite)) ** iota_mat = mat 1"
proof (rule mat_eq_by_dotp)
  fix x y :: "rat^'n"
  show "dotp x ((transpose (iota_mat::rat^'n^('n + 'h)) ** iota_mat) *v y) = dotp x (mat 1 *v y)"
    by (simp add: dotp_tAB iota_mv dotp_emb_emb mv_one)
qed

definition lin_sub :: "(rat^'h::finite) set \<Rightarrow> bool" where
  "lin_sub p \<longleftrightarrow> 0 \<in> p \<and> (\<forall>x\<in>p. \<forall>y\<in>p. x + y \<in> p) \<and> (\<forall>c x. x \<in> p \<longrightarrow> c *s x \<in> p)"

definition Vset :: "(rat^'h::finite) set \<Rightarrow> (rat^('n::finite + 'h)) set" where
  "Vset p = {v. dotp (fstv v) evec = 0 \<and> sndv v \<in> p}"

section \<open>The projection onto V on an orthogonal basis of planes\<close>

lemma planes_pos:
  assumes pls: "planes lam f g k" and lam: "- 1 < lam" "lam < 1" and i: "i < k"
  shows "0 < dotp (f i) (f i)" "0 < dotp (g i) (g i)" "dotp (f i) (g i) = 0" "dotp (g i) (f i) = 0"
proof -
  have pl: "plane lam (f i) (g i)" by (rule planes_unit[OF pls i])
  then show a: "0 < dotp (f i) (f i)" and "dotp (f i) (g i) = 0" "dotp (g i) (f i) = 0"
    by (simp_all add: plane_def dotp_comm)
  have d: "0 < 1 - lam\<^sup>2"
  proof -
    have "0 < (1 - lam) * (1 + lam)" using lam by (intro mult_pos_pos) linarith+
    moreover have "1 - lam\<^sup>2 = (1 - lam) * (1 + lam)" by (simp add: algebra_simps power2_eq_square)
    ultimately show ?thesis by linarith
  qed
  have "dotp (g i) (g i) = (1 - lam\<^sup>2) * dotp (f i) (f i)" using pl by (simp add: plane_def)
  with d a show "0 < dotp (g i) (g i)" by simp
qed

lemma span_coeff:
  assumes pls: "planes lam f g k" and lam: "- 1 < lam" "lam < 1" and j: "j < k"
  shows "dotp (\<Sum>i<k. c i *s f i + d i *s g i) (f j) = c j * dotp (f j) (f j)"
    and "dotp (\<Sum>i<k. c i *s f i + d i *s g i) (g j) = d j * dotp (g j) (g j)"
proof -
  have "dotp (\<Sum>i<k. c i *s f i + d i *s g i) (f j)
      = (\<Sum>i<k. c i * dotp (f i) (f j) + d i * dotp (g i) (f j))"
    by (simp add: dotp_sum_left dotp_add_left dotp_smult_left)
  also have "\<dots> = (\<Sum>i<k. if i = j then c j * dotp (f j) (f j) else 0)"
  proof (rule sum.cong[OF refl])
    fix i assume i: "i \<in> {..<k}"
    show "c i * dotp (f i) (f j) + d i * dotp (g i) (f j) = (if i = j then c j * dotp (f j) (f j) else 0)"
    proof (cases "i = j")
      case True then show ?thesis using planes_pos(4)[OF pls lam j] by simp
    next
      case False then show ?thesis using pls i j unfolding planes_def by auto
    qed
  qed
  also have "\<dots> = c j * dotp (f j) (f j)" using j by simp
  finally show "dotp (\<Sum>i<k. c i *s f i + d i *s g i) (f j) = c j * dotp (f j) (f j)" .
  have "dotp (\<Sum>i<k. c i *s f i + d i *s g i) (g j)
      = (\<Sum>i<k. c i * dotp (f i) (g j) + d i * dotp (g i) (g j))"
    by (simp add: dotp_sum_left dotp_add_left dotp_smult_left)
  also have "\<dots> = (\<Sum>i<k. if i = j then d j * dotp (g j) (g j) else 0)"
  proof (rule sum.cong[OF refl])
    fix i assume i: "i \<in> {..<k}"
    show "c i * dotp (f i) (g j) + d i * dotp (g i) (g j) = (if i = j then d j * dotp (g j) (g j) else 0)"
    proof (cases "i = j")
      case True then show ?thesis using planes_pos(3)[OF pls lam j] by simp
    next
      case False then show ?thesis using pls i j unfolding planes_def by auto
    qed
  qed
  also have "\<dots> = d j * dotp (g j) (g j)" using j by simp
  finally show "dotp (\<Sum>i<k. c i *s f i + d i *s g i) (g j) = d j * dotp (g j) (g j)" .
qed

lemma Pproj_on_span:
  assumes pls: "planes lam f g k" and lam: "- 1 < lam" "lam < 1" and x: "x \<in> Vspan f g k"
  shows "Pproj f g k *v x = x"
proof -
  obtain c d where xe: "x = (\<Sum>i<k. c i *s f i + d i *s g i)" using x by (auto simp: Vspan_def)
  have hP: "\<And>j. j \<in> {..<k} \<Longrightarrow> Pvec (f j) (g j) x = c j *s f j + d j *s g j"
  proof -
    fix j assume j: "j \<in> {..<k}"
    then have jk: "j < k" by simp
    have a: "dotp (f j) (f j) \<noteq> 0" using planes_pos(1)[OF pls lam jk] by simp
    have b: "dotp (g j) (g j) \<noteq> 0" using planes_pos(2)[OF pls lam jk] by simp
    show "Pvec (f j) (g j) x = c j *s f j + d j *s g j"
      using span_coeff(1)[OF pls lam jk, of c d] span_coeff(2)[OF pls lam jk, of c d] a b
      by (simp add: Pvec_def xe)
  qed
  have "Pproj f g k *v x = (\<Sum>j<k. Pvec (f j) (g j) x)" by (rule Pproj_mv)
  also have "\<dots> = (\<Sum>j<k. c j *s f j + d j *s g j)" by (rule sum.cong[OF refl hP])
  finally show ?thesis by (rule trans[OF _ xe[symmetric]])
qed

lemma Pproj_on_perp:
  assumes "\<And>v. v \<in> Vspan f g k \<Longrightarrow> dotp x v = 0"
  shows "Pproj f g k *v x = 0"
proof -
  have "\<And>i. i \<in> {..<k} \<Longrightarrow> Pvec (f i) (g i) x = 0"
    by (simp add: Pvec_def assms Vspan_gens)
  then show ?thesis by (simp add: Pproj_mv)
qed

section \<open>Part (b): planes give length n + h\<close>

lemma emb_in_V:
  assumes "lin_sub p" "dotp z evec = 0"
  shows "emb z \<in> Vset p"
  using assms by (simp add: Vset_def lin_sub_def)

lemma emb_e_perp:
  assumes "v \<in> Vset p"
  shows "dotp (emb (c *s evec)) v = 0"
proof -
  have "dotp (fstv v) evec = 0" using assms by (simp add: Vset_def)
  then have "dotp evec (fstv v) = 0" by (simp add: dotp_comm)
  then show ?thesis by (simp add: dotp_emb_left dotp_smult_left)
qed

lemma n_nonzero:
  assumes "3 \<le> CARD('n::finite)"
  shows "(of_nat CARD('n)::rat) \<noteq> 0" "(of_nat CARD('n)::rat) \<noteq> 1"
  using three_le_rat[OF assms] by linarith+

lemma emb_split:
  fixes y :: "rat^'n::finite"
  shows "emb y = emb (y - c *s evec) + emb (c *s evec)"
  by (simp flip: emb_add)

lemma P_emb:
  fixes y :: "rat^'n::finite" and p :: "(rat^'h::finite) set"
  assumes n3: "3 \<le> CARD('n)" and p: "lin_sub p"
    and pl: "planes (lamn TYPE('n)) f g k" and sp: "Vspan f g k = Vset p"
  shows "Pproj f g k *v (emb y :: rat^('n + 'h))
       = emb (y - (dotp y evec / of_nat CARD('n)) *s evec)"
proof -
  let ?c = "dotp y evec / of_nat CARD('n)"
  note lam = lamn_range[OF n3]
  have nz: "(of_nat CARD('n)::rat) \<noteq> 0" by (rule n_nonzero[OF n3])
  have z0: "dotp (y - ?c *s evec) evec = 0"
    using nz by (simp add: dotp_diff_left dotp_smult_left dotp_evec_evec)
  have u: "emb (y - ?c *s evec) \<in> Vspan f g k"
    using emb_in_V[OF p z0] sp by simp
  have w: "\<And>v. v \<in> Vspan f g k \<Longrightarrow> dotp (emb (?c *s evec)) v = 0"
    using emb_e_perp sp by simp
  have "Pproj f g k *v (emb y :: rat^('n + 'h))
      = Pproj f g k *v emb (y - ?c *s evec) + Pproj f g k *v emb (?c *s evec)"
    by (subst emb_split[of y ?c]) (rule matrix_vector_right_distrib)
  also have "\<dots> = emb (y - ?c *s evec)"
    using Pproj_on_span[OF pl lam u] Pproj_on_perp[OF w] by simp
  finally show ?thesis .
qed

theorem planes_give_length:
  fixes p :: "(rat^'h::finite) set" and f g :: "nat \<Rightarrow> rat^('n::finite + 'h)" and k :: nat
  assumes n3: "3 \<le> CARD('n)" and p: "lin_sub p"
    and pl: "planes (lamn TYPE('n)) f g k" and sp: "Vspan f g k = Vset p"
  shows "\<exists>B::rat^'n^('n + 'h). repr_Q (Hn::rat^'n^'n) iota_mat B \<and> (\<forall>x. sndv (B *v x) \<in> p)"
proof -
  note lam = lamn_range[OF n3]
  have nz: "(of_nat CARD('n)::rat) \<noteq> 0" "(of_nat CARD('n)::rat) \<noteq> 1" by (rule n_nonzero[OF n3])+
  obtain R :: "rat^('n + 'h)^('n + 'h)" where
    Rorth: "transpose R ** R = mat 1"
    and Rinv: "\<forall>x\<in>Vspan f g k. R *v x \<in> Vspan f g k"
    and Rperp: "\<forall>x. (\<forall>v\<in>Vspan f g k. dotp x v = 0) \<longrightarrow> R *v x = x"
    and Rsym: "R + transpose R = sm (2 * lamn TYPE('n)) (Pproj f g k) + sm 2 (mat 1 - Pproj f g k)"
    using orthogonal_planes_rotation[OF lam pl] by blast
  let ?B = "R ** (iota_mat :: rat^'n^('n + 'h))"
  have Bmv: "\<And>x. ?B *v x = R *v emb x" by (simp add: mv_mv iota_mv)
  have Rdot: "\<And>x y. dotp (R *v x) (R *v y) = dotp x y"
  proof -
    fix x y :: "rat^('n + 'h)"
    have "dotp (R *v x) (R *v y) = dotp x ((transpose R ** R) *v y)" by (simp add: dotp_tAB[symmetric])
    also have "\<dots> = dotp x y" by (simp add: Rorth mv_one)
    finally show "dotp (R *v x) (R *v y) = dotp x y" .
  qed
  have c2: "transpose ?B ** ?B = mat 1"
  proof (rule mat_eq_by_dotp)
    fix x y :: "rat^'n"
    show "dotp x ((transpose ?B ** ?B) *v y) = dotp x (mat 1 *v y)"
      by (simp add: dotp_tAB Bmv Rdot dotp_emb_emb mv_one)
  qed
  have c3: "transpose (iota_mat::rat^'n^('n + 'h)) ** ?B + transpose ?B ** iota_mat = sm 2 (Hn::rat^'n^'n)"
  proof (rule mat_eq_by_dotp)
    fix x y :: "rat^'n"
    let ?n = "of_nat CARD('n) :: rat"
    let ?c = "dotp y evec / ?n"
    let ?ex = "emb x :: rat^('n + 'h)"
    let ?ey = "emb y :: rat^('n + 'h)"
    have s1: "dotp x ((transpose (iota_mat::rat^'n^('n + 'h)) ** ?B + transpose ?B ** iota_mat) *v y)
        = dotp (?ex) (R *v ?ey) + dotp (R *v ?ex) (?ey)"
      by (simp add: mv_add dotp_add_right dotp_tAB iota_mv Bmv)
    have s2: "dotp (?ex) (R *v ?ey) + dotp (R *v ?ex) (?ey)
        = dotp (?ex) ((R + transpose R) *v ?ey)"
      by (simp add: mv_add dotp_add_right dotp_mv)
    have s3: "dotp (?ex) ((R + transpose R) *v ?ey)
        = 2 * lamn TYPE('n) * dotp (?ex) (Pproj f g k *v ?ey)
          + 2 * (dotp (?ex) (?ey) - dotp (?ex) (Pproj f g k *v ?ey))"
      by (simp add: Rsym mv_add mv_diff sm_mv mv_one dotp_add_right dotp_smult_right dotp_diff_right
          algebra_simps)
    have s4: "dotp (?ex) (Pproj f g k *v ?ey) = dotp x y - ?c * dotp x evec"
      by (simp add: P_emb[OF n3 p pl sp] dotp_emb_emb dotp_diff_right dotp_smult_right)
    have s5: "dotp x (sm 2 (Hn::rat^'n^'n) *v y) = 2 * (1 / (?n - 1) * (dotp x evec * dotp y evec - dotp x y))"
      by (simp add: sm_mv dotp_smult_right dotp_Hn)
    have s6: "lamn TYPE('n) = - 1 / (?n - 1)" by (simp add: lamn_def)
    show "dotp x ((transpose (iota_mat::rat^'n^('n + 'h)) ** ?B + transpose ?B ** iota_mat) *v y)
        = dotp x (sm 2 (Hn::rat^'n^'n) *v y)"
      using s1 s2 s3 s4 s5 s6 alg_id[OF nz, of "dotp x y" "dotp x evec" "dotp y evec"]
      by (simp add: dotp_emb_emb algebra_simps)
  qed
  have rep: "repr_Q (Hn::rat^'n^'n) iota_mat ?B"
    unfolding repr_Q_def using iota_orth c2 c3 by blast
  have inp: "\<forall>x. sndv (?B *v x) \<in> p"
  proof
    fix x :: "rat^'n"
    let ?c = "dotp x evec / of_nat CARD('n)"
    have nz0: "(of_nat CARD('n)::rat) \<noteq> 0" by (rule n_nonzero[OF n3])
    have z0: "dotp (x - ?c *s evec) evec = 0"
      using nz0 by (simp add: dotp_diff_left dotp_smult_left dotp_evec_evec)
    have u: "emb (x - ?c *s evec) \<in> Vspan f g k" using emb_in_V[OF p z0] sp by simp
    have w: "\<And>v. v \<in> Vspan f g k \<Longrightarrow> dotp (emb (?c *s evec)) v = 0" using emb_e_perp sp by simp
    have Ru: "R *v emb (x - ?c *s evec) \<in> Vset p" using Rinv u sp by auto
    have Rw: "R *v emb (?c *s evec) = emb (?c *s evec)" using Rperp w by blast
    have "?B *v x = R *v emb (x - ?c *s evec) + emb (?c *s evec)"
      by (subst Bmv, subst emb_split[of x ?c], simp add: matrix_vector_right_distrib Rw)
    then have "sndv (?B *v x) = sndv (R *v emb (x - ?c *s evec))" by (simp add: sndv_add)
    also have "\<dots> \<in> p" using Ru by (simp add: Vset_def)
    finally show "sndv (?B *v x) \<in> p" .
  qed
  from rep inp show ?thesis by blast
qed

corollary length_le_of_planes:
  fixes p :: "(rat^'h::finite) set" and f g :: "nat \<Rightarrow> rat^('n::finite + 'h)" and k :: nat
  assumes "3 \<le> CARD('n)" "lin_sub p" "planes (lamn TYPE('n)) f g k" "Vspan f g k = Vset p"
  shows "len_le (TYPE('n + 'h)) (Hn::rat^'n^'n)"
  using planes_give_length[OF assms] unfolding len_le_def by blast

section \<open>Part (c): the converse direction, linear algebra\<close>

lemma vec_comp_eq: "a = b \<Longrightarrow> a $ i = b $ i" by simp

text \<open>A representation in the normal form of Proposition 2.1 (3): T is n x n, D is h x n,
  T^T T + D^T D = I and T + T^T = 2 H_n.\<close>

definition contr_rep :: "rat^'n::finite^'n \<Rightarrow> rat^'n^'h::finite \<Rightarrow> bool" where
  "contr_rep T D \<longleftrightarrow> transpose T ** T + transpose D ** D = mat 1
      \<and> T + transpose T = sm 2 (Hn::rat^'n^'n)"

definition blk1 :: "rat^'n::finite^('n + 'h::finite) \<Rightarrow> rat^'n^'n" where
  "blk1 B = (\<chi> i j. B $ Inl i $ j)"

definition blk2 :: "rat^'n::finite^('n + 'h::finite) \<Rightarrow> rat^'n^'h" where
  "blk2 B = (\<chi> i j. B $ Inr i $ j)"

lemma fstv_Bmv: "fstv (B *v x) = blk1 B *v x"
  by (simp add: vec_eq_iff blk1_def matrix_vector_mult_def)

lemma sndv_Bmv: "sndv (B *v x) = blk2 B *v x"
  by (simp add: vec_eq_iff blk2_def matrix_vector_mult_def)

theorem repr_iff_contr:
  "repr_Q (Hn::rat^'n::finite^'n) (iota_mat::rat^'n^('n + 'h::finite)) B \<longleftrightarrow> contr_rep (blk1 B) (blk2 B)"
proof -
  let ?T = "blk1 B" and ?D = "blk2 B"
  have e1: "\<And>x y. dotp x ((transpose B ** B) *v y)
      = dotp x ((transpose ?T ** ?T + transpose ?D ** ?D) *v y)"
    by (simp add: dotp_tAB dotp_split fstv_Bmv sndv_Bmv mv_add dotp_add_right)
  have e2: "\<And>x y. dotp x ((transpose (iota_mat::rat^'n^('n + 'h)) ** B + transpose B ** iota_mat) *v y)
      = dotp x ((?T + transpose ?T) *v y)"
  proof -
    fix x y :: "rat^'n"
    have l1: "dotp x ((transpose (iota_mat::rat^'n^('n + 'h)) ** B + transpose B ** iota_mat) *v y)
        = dotp (iota_mat *v x) (B *v y) + dotp (B *v x) (iota_mat *v y)"
      by (simp only: mv_add dotp_add_right dotp_tAB)
    have a1: "dotp (iota_mat *v x) (B *v y) = dotp x (?T *v y)"
      by (simp only: iota_mv dotp_emb_left fstv_Bmv)
    have a2: "dotp (B *v x) (iota_mat *v y) = dotp (?T *v x) y"
    proof -
      have "dotp (B *v x) (iota_mat *v y) = dotp y (?T *v x)"
        by (simp only: iota_mv dotp_comm[of "B *v x" "emb y"] dotp_emb_left fstv_Bmv)
      then show ?thesis by (metis dotp_comm)
    qed
    have r1: "dotp x ((?T + transpose ?T) *v y) = dotp x (?T *v y) + dotp x (transpose ?T *v y)"
      by (simp only: mv_add dotp_add_right)
    have r2: "dotp x (transpose ?T *v y) = dotp (?T *v x) y" by (rule dotp_mv[symmetric])
    show "dotp x ((transpose (iota_mat::rat^'n^('n + 'h)) ** B + transpose B ** iota_mat) *v y)
        = dotp x ((?T + transpose ?T) *v y)"
      using l1 a1 a2 r1 r2 by simp
  qed
  have c2: "transpose B ** B = mat 1 \<longleftrightarrow> transpose ?T ** ?T + transpose ?D ** ?D = mat 1"
    using e1 by (auto simp: mat_eq_iff_dotp)
  have c3: "transpose (iota_mat::rat^'n^('n + 'h)) ** B + transpose B ** iota_mat = sm 2 (Hn::rat^'n^'n)
      \<longleftrightarrow> ?T + transpose ?T = sm 2 (Hn::rat^'n^'n)"
    using e2 by (auto simp: mat_eq_iff_dotp)
  show ?thesis unfolding repr_Q_def contr_rep_def using iota_orth c2 c3 by blast
qed

lemma one_div_mul: "x \<noteq> 0 \<Longrightarrow> 1 / x * x = (1::rat)" by (simp add: field_simps)

lemma He:
  assumes "3 \<le> CARD('n::finite)"
  shows "(Hn::rat^'n^'n) *v evec = evec"
proof (rule vec_eq_iff[THEN iffD2], rule allI)
  fix i
  let ?n = "of_nat CARD('n) :: rat"
  have nz: "?n - 1 \<noteq> 0" using n_nonzero[OF assms] by simp
  have e1: "((Hn::rat^'n^'n) *v evec) $ i = 1 / (?n - 1) * (dotp (evec::rat^'n) evec * evec $ i - evec $ i)"
    by (simp only: Hn_mv vector_smult_component vector_minus_component)
  also have "\<dots> = 1 / (?n - 1) * (?n * 1 - 1)" by (simp only: dotp_evec_evec evec_comp)
  also have "\<dots> = 1" by (simp only: mult_1_right, rule one_div_mul[OF nz])
  finally have fin: "((Hn::rat^'n^'n) *v evec) $ i = 1" .
  show "((Hn::rat^'n^'n) *v evec) $ i = evec $ i" by (simp only: evec_comp, rule fin)
qed

lemma H_on_V:
  assumes "dotp x evec = 0"
  shows "(Hn::rat^'n::finite^'n) *v x = lamn TYPE('n) *s x"
  using assms by (simp add: Hn_mv lamn_def vec_eq_iff algebra_simps divide_inverse)

lemma contr_dot:
  assumes cr: "contr_rep T D"
  shows "dotp (T *v x) (T *v y) + dotp (D *v x) (D *v y) = dotp x y"
    and "dotp (T *v x) y + dotp x (T *v y) = 2 * dotp x ((Hn::rat^'n::finite^'n) *v y)"
proof -
  have h1: "transpose T ** T + transpose D ** D = mat 1" using cr by (simp add: contr_rep_def)
  have "dotp x ((transpose T ** T + transpose D ** D) *v y) = dotp x (mat 1 *v y)" using h1 by simp
  then show "dotp (T *v x) (T *v y) + dotp (D *v x) (D *v y) = dotp x y"
    by (simp add: mv_add dotp_add_right dotp_tAB mv_one)
  have h2: "T + transpose T = sm 2 (Hn::rat^'n^'n)" using cr by (simp add: contr_rep_def)
  have "dotp x ((T + transpose T) *v y) = dotp x (sm 2 Hn *v y)" using h2 by simp
  then show "dotp (T *v x) y + dotp x (T *v y) = 2 * dotp x (Hn *v y)"
    by (simp add: mv_add dotp_add_right dotp_mv sm_mv dotp_smult_right algebra_simps)
qed

theorem contr_fixes_e:
  assumes n3: "3 \<le> CARD('n::finite)" and cr: "contr_rep T (D::rat^'n^'h::finite)"
  shows "T *v evec = evec" "D *v evec = 0" "transpose T *v evec = evec"
proof -
  have He': "(Hn::rat^'n^'n) *v evec = evec" by (rule He[OF n3])
  have hs: "2 * dotp (T *v evec) evec = 2 * dotp evec (evec::rat^'n)"
    using contr_dot(2)[OF cr, of evec evec] He' by (simp add: dotp_comm)
  have hn: "dotp (T *v evec) (T *v evec) + dotp (D *v evec) (D *v evec) = dotp evec (evec::rat^'n)"
    using contr_dot(1)[OF cr, of evec evec] .
  let ?a = "T *v evec - evec"
  have ex: "dotp ?a ?a = dotp (T *v evec) (T *v evec) - 2 * dotp (T *v evec) evec + dotp evec (evec::rat^'n)"
    by (simp add: dotp_diff_left dotp_diff_right dotp_comm[of evec "T *v evec"])
  have "dotp ?a ?a + dotp (D *v evec) (D *v evec) = 0" using ex hs hn by linarith
  moreover have "0 \<le> dotp ?a ?a" "0 \<le> dotp (D *v evec) (D *v evec)" by (rule dotp_nonneg)+
  ultimately have z1: "dotp ?a ?a = 0" and z2: "dotp (D *v evec) (D *v evec) = 0" by linarith+
  show Te: "T *v evec = evec" using dotp_self_zero[OF z1] by simp
  show "D *v evec = 0" by (rule dotp_self_zero[OF z2])
  have h2: "T + transpose T = sm 2 (Hn::rat^'n^'n)" using cr by (simp add: contr_rep_def)
  have "(T + transpose T) *v evec = sm 2 Hn *v evec" using h2 by simp
  then have "T *v evec + transpose T *v evec = 2 *s evec" by (simp add: mv_add sm_mv He')
  then show "transpose T *v evec = evec" using Te by (simp add: vec_eq_iff algebra_simps)
qed

definition Sm :: "rat^'n::finite^'n \<Rightarrow> rat^'n^'n" where
  "Sm T = T - sm (lamn TYPE('n)) (mat 1)"

lemma Sm_mv:
  fixes T :: "rat^'n::finite^'n"
  shows "Sm T *v x = T *v x - lamn TYPE('n) *s x"
  by (simp add: Sm_def mv_diff sm_mv mv_one)

theorem S_stable:
  assumes n3: "3 \<le> CARD('n::finite)" and cr: "contr_rep T (D::rat^'n^'h::finite)" and x: "dotp x evec = 0"
  shows "dotp (Sm T *v x) evec = 0"
proof -
  have "dotp (T *v x) evec = dotp x (transpose T *v evec)" by (simp add: dotp_mv)
  also have "\<dots> = 0" using contr_fixes_e(3)[OF n3 cr] x by simp
  finally show ?thesis by (simp add: Sm_mv dotp_diff_left dotp_smult_left x)
qed

theorem S_skew:
  assumes n3: "3 \<le> CARD('n::finite)" and cr: "contr_rep T (D::rat^'n^'h::finite)" and y: "dotp y evec = 0"
  shows "dotp (Sm T *v x) y + dotp x (Sm T *v y) = 0"
proof -
  have "dotp (T *v x) y + dotp x (T *v y) = 2 * dotp x ((Hn::rat^'n^'n) *v y)"
    by (rule contr_dot(2)[OF cr])
  then show ?thesis
    by (simp add: Sm_mv dotp_diff_left dotp_diff_right dotp_smult_left dotp_smult_right H_on_V[OF y])
qed

lemma tT_on_V:
  assumes n3: "3 \<le> CARD('n::finite)" and cr: "contr_rep T (D::rat^'n^'h::finite)" and z: "dotp z evec = 0"
  shows "transpose T *v z = lamn TYPE('n) *s z - Sm T *v z"
proof -
  have h2: "T + transpose T = sm 2 (Hn::rat^'n^'n)" using cr by (simp add: contr_rep_def)
  have "(T + transpose T) *v z = sm 2 Hn *v z" using h2 by simp
  then have eq: "T *v z + transpose T *v z = 2 *s (lamn TYPE('n) *s z)"
    by (simp add: mv_add sm_mv H_on_V[OF z])
  have key: "\<And>t u::rat^'n. t + u = 2 *s (lamn TYPE('n) *s z) \<Longrightarrow> u = lamn TYPE('n) *s z - (t - lamn TYPE('n) *s z)"
  proof -
    fix t u :: "rat^'n"
    assume h: "t + u = 2 *s (lamn TYPE('n) *s z)"
    show "u = lamn TYPE('n) *s z - (t - lamn TYPE('n) *s z)"
    proof (rule vec_eq_iff[THEN iffD2], rule allI)
      fix i
      have "t $ i + u $ i = 2 * (lamn TYPE('n) * z $ i)" using vec_comp_eq[OF h, of i] by simp
      then show "u $ i = (lamn TYPE('n) *s z - (t - lamn TYPE('n) *s z)) $ i" by simp
    qed
  qed
  show ?thesis by (simp only: Sm_mv, rule key[OF eq])
qed


theorem Delta_on_V:
  assumes n3: "3 \<le> CARD('n::finite)" and cr: "contr_rep T (D::rat^'n^'h::finite)" and x: "dotp x evec = 0"
  shows "x - transpose T *v (T *v x) = (1 - (lamn TYPE('n))\<^sup>2) *s x + Sm T *v (Sm T *v x)"
    and "x - transpose T *v (T *v x) = transpose D *v (D *v x)"
proof -
  let ?l = "lamn TYPE('n)"
  have Tx: "dotp (T *v x) evec = 0"
  proof -
    have "dotp (T *v x) evec = dotp x (transpose T *v evec)" by (simp add: dotp_mv)
    then show ?thesis using contr_fixes_e(3)[OF n3 cr] x by simp
  qed
  have h1: "transpose T *v (T *v x) = ?l *s (T *v x) - Sm T *v (T *v x)"
    by (rule tT_on_V[OF n3 cr Tx])
  have h2: "T *v x = ?l *s x + Sm T *v x" by (simp add: Sm_mv)
  have h3: "Sm T *v (T *v x) = Sm T *v (?l *s x + Sm T *v x)" by (rule arg_cong[OF h2])
  have step: "x - transpose T *v (T *v x) = x - (?l *s (T *v x) - Sm T *v (T *v x))" by (simp only: h1)
  have "x - (?l *s (T *v x) - Sm T *v (T *v x))
      = x - (?l *s (?l *s x + Sm T *v x) - Sm T *v (?l *s x + Sm T *v x))"
    by (simp only: h2)
  also have "\<dots> = (1 - ?l\<^sup>2) *s x + Sm T *v (Sm T *v x)"
    by (simp add: mv_add mv_smult vec_eq_iff algebra_simps power2_eq_square)
  finally show "x - transpose T *v (T *v x) = (1 - ?l\<^sup>2) *s x + Sm T *v (Sm T *v x)" using step by simp
  have h4: "transpose T ** T + transpose D ** D = mat 1" using cr by (simp add: contr_rep_def)
  have "(transpose T ** T + transpose D ** D) *v x = x" using h4 by (simp add: mv_one)
  then have eq: "transpose T *v (T *v x) + transpose D *v (D *v x) = x" by (simp add: mv_add mv_mv)
  show "x - transpose T *v (T *v x) = transpose D *v (D *v x)"
  proof (rule vec_eq_iff[THEN iffD2], rule allI)
    fix i
    have "(transpose T *v (T *v x)) $ i + (transpose D *v (D *v x)) $ i = x $ i"
      using vec_comp_eq[OF eq, of i] by simp
    then show "(x - transpose T *v (T *v x)) $ i = (transpose D *v (D *v x)) $ i" by simp
  qed
qed

section \<open>Kernel and image of Delta\<close>

text \<open>Delta = D^T D on Q^n (it equals delta + S^2 on e^perp by Delta_on_V). It is symmetric; this is all
  that the splitting uses, together with the positivity of the standard product over Q.\<close>

lemma ker_im_orth:
  fixes M :: "rat^'n::finite^'n"
  assumes sym: "\<And>x y. dotp (M *v x) y = dotp x (M *v y)" and "M *v u = 0"
  shows "dotp u (M *v z) = 0"
  using assms by (metis dotp_comm dotp_zero_left)

lemma ker_im_inter:
  fixes M :: "rat^'n::finite^'n"
  assumes sym: "\<And>x y. dotp (M *v x) y = dotp x (M *v y)" and "M *v w = 0" and "w = M *v z"
  shows "w = 0"
proof -
  have "dotp w w = dotp (M *v z) w" using assms(3) by simp
  also have "\<dots> = dotp z (M *v w)" by (rule sym)
  also have "\<dots> = 0" using assms(2) by simp
  finally show ?thesis by (rule dotp_self_zero)
qed

theorem ker_im_split:
  fixes M :: "rat^'n::finite^'n"
  assumes sym: "\<And>x y. dotp (M *v x) y = dotp x (M *v y)"
  shows "\<exists>u w. M *v u = 0 \<and> (\<exists>z. w = M *v z) \<and> x = u + w"
proof -
  let ?I = "((*v) M) ` (UNIV :: (rat^'n) set)"
  have lin: "Vector_Spaces.linear (*s) (*s) ((*v) M)" by (rule matrix_vector_mul_linear_gen)
  have subI: "vec.subspace ?I" by (rule vec.linear_subspace_image[OF lin vec.subspace_UNIV])
  have subMI: "vec.subspace (((*v) M) ` ?I)" by (rule vec.linear_subspace_image[OF lin subI])
  have inI: "((*v) M) ` ?I \<subseteq> ?I" by auto
  have inj: "inj_on ((*v) M) (vec.span ?I)"
  proof (rule inj_onI)
    fix a b assume a: "a \<in> vec.span ?I" and b: "b \<in> vec.span ?I" and eq: "M *v a = M *v b"
    have sp: "vec.span ?I = ?I" using subI by (simp add: vec.span_eq_iff)
    have "a - b \<in> ?I" using a b sp subI by (metis vec.subspace_diff)
    then obtain z where z: "a - b = M *v z" by auto
    have "M *v (a - b) = 0" using eq by (simp add: matrix_vector_mult_diff_distrib)
    then have "a - b = 0" by (rule ker_im_inter[OF sym _ z])
    then show "a = b" by simp
  qed
  have "vec.dim (((*v) M) ` ?I) = vec.dim ?I" by (rule vec.dim_image_eq[OF lin inj])
  then have "vec.dim ?I \<le> vec.dim (((*v) M) ` ?I)" by simp
  then have eqI: "((*v) M) ` ?I = ?I" by (rule vec.subspace_dim_equal[OF subMI subI inI])
  have "M *v x \<in> ?I" by auto
  then have "M *v x \<in> ((*v) M) ` ?I" using eqI by simp
  then obtain w where w1: "w \<in> ?I" and w2: "M *v x = M *v w" by (rule imageE)
  from w1 obtain z where wz: "w = M *v z" by (rule rangeE)
  have hz: "M *v (x - w) = 0" using w2 by (simp add: matrix_vector_mult_diff_distrib)
  show ?thesis
    by (rule exI[of _ "x - w"], rule exI[of _ w], rule conjI[OF hz], rule conjI, rule exI[of _ z], rule wz, simp)
qed

lemma DtD_sym:
  fixes D :: "rat^'n::finite^'h::finite"
  shows "dotp ((transpose D ** D) *v x) y = dotp x ((transpose D ** D) *v y)"
proof -
  have a: "dotp ((transpose D ** D) *v x) y = dotp (D *v y) (D *v x)"
    by (metis dotp_comm dotp_tAB)
  have b: "dotp x ((transpose D ** D) *v y) = dotp (D *v x) (D *v y)" by (rule dotp_tAB)
  have c: "dotp (D *v y) (D *v x) = dotp (D *v x) (D *v y)" by (rule dotp_comm)
  show ?thesis by (simp only: a b c)
qed

lemma DtD_e:
  assumes "D *v evec = 0"
  shows "(transpose D ** D) *v evec = 0" "dotp ((transpose D ** D) *v z) evec = 0"
proof -
  show "(transpose D ** D) *v evec = 0" using assms by (simp add: mv_mv matrix_vector_mult_0_right)
  then show "dotp ((transpose D ** D) *v z) evec = 0"
    using DtD_sym[of D z evec] by simp
qed

theorem split_V:
  assumes n3: "3 \<le> CARD('n::finite)" and cr: "contr_rep T (D::rat^'n^'h::finite)" and x: "dotp x evec = 0"
  shows "\<exists>u w z. (transpose D ** D) *v u = 0 \<and> dotp u evec = 0 \<and> w = (transpose D ** D) *v z
      \<and> dotp w evec = 0 \<and> x = u + w"
proof -
  let ?M = "transpose D ** D"
  obtain u w z where u: "?M *v u = 0" and w: "w = ?M *v z" and xe: "x = u + w"
    using ker_im_split[OF DtD_sym, of D x] by blast
  have we: "dotp w evec = 0" using w DtD_e(2)[OF contr_fixes_e(2)[OF n3 cr]] by simp
  have "dotp u evec = dotp x evec - dotp w evec" by (simp add: xe dotp_add_left)
  then have "dotp u evec = 0" using x we by simp
  then show ?thesis using u w we xe by blast
qed


section \<open>The iota identity\<close>

text \<open>Over L = Q(iota), iota^2 = -delta, a vector u + iota v of V_L is the pair (u, v) of rational vectors.
  The bilinear extension of q to pairs has real part q(u1,u2) - delta q(v1,v2) and imaginary part
  q(u1,v2) + q(v1,u2) (coefficients of 1 and iota). The map iota + S sends (u, v) to
  (S u - delta v, u + S v), and Delta = delta + S^2 acts componentwise. Only the following is used about S:
  it is skew for q on e^perp and preserves e^perp (both proved above for T = lam + S).\<close>

definition qL_re :: "rat \<Rightarrow> (rat^'n::finite) \<times> (rat^'n) \<Rightarrow> (rat^'n) \<times> (rat^'n) \<Rightarrow> rat" where
  "qL_re d X Y = dotp (fst X) (fst Y) - d * dotp (snd X) (snd Y)"

definition qL_im :: "rat \<Rightarrow> (rat^'n::finite) \<times> (rat^'n) \<Rightarrow> (rat^'n) \<times> (rat^'n) \<Rightarrow> rat" where
  "qL_im d X Y = dotp (fst X) (snd Y) + dotp (snd X) (fst Y)"

definition Phi :: "rat \<Rightarrow> rat^'n::finite^'n \<Rightarrow> (rat^'n) \<times> (rat^'n) \<Rightarrow> (rat^'n) \<times> (rat^'n)" where
  "Phi d S X = (S *v fst X - d *s snd X, fst X + S *v snd X)"

definition Dlt :: "rat \<Rightarrow> rat^'n::finite^'n \<Rightarrow> (rat^'n) \<times> (rat^'n) \<Rightarrow> (rat^'n) \<times> (rat^'n)" where
  "Dlt d S X = (d *s fst X + S *v (S *v fst X), d *s snd X + S *v (S *v snd X))"

theorem iota_identity:
  fixes S :: "rat^'n::finite^'n" and d :: rat and u1 v1 u2 v2 :: "rat^'n"
  assumes sk: "\<And>a b. dotp a evec = 0 \<Longrightarrow> dotp b evec = 0 \<Longrightarrow> dotp (S *v a) b = - dotp a (S *v b)"
    and st: "\<And>a. dotp a evec = 0 \<Longrightarrow> dotp (S *v a) evec = 0"
    and h: "dotp u1 evec = 0" "dotp v1 evec = 0" "dotp u2 evec = 0" "dotp v2 evec = 0"
  shows "qL_re d (Phi d S (u1, v1)) (Phi d S (u2, v2)) = - qL_re d (Dlt d S (u1, v1)) (u2, v2)"
    and "qL_im d (Phi d S (u1, v1)) (Phi d S (u2, v2)) = - qL_im d (Dlt d S (u1, v1)) (u2, v2)"
  using h
  by (simp_all add: qL_re_def qL_im_def Phi_def Dlt_def dotp_add_left dotp_add_right dotp_diff_left
      dotp_diff_right dotp_smult_left dotp_smult_right sk st algebra_simps)

lemma mv_uminus:
  fixes A :: "rat^'m::finite^'n::finite"
  shows "A *v (- w) = - (A *v w)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)

theorem Phi_injective:
  fixes M S :: "rat^'n::finite^'n" and d :: rat and u v :: "rat^'n"
  assumes sym: "\<And>x y. dotp (M *v x) y = dotp x (M *v y)"
    and hM: "M *v v = d *s v + S *v (S *v v)" and hv: "\<exists>z. v = M *v z"
    and ph: "Phi d S (u, v) = (0, 0)"
  shows "u = 0 \<and> v = 0"
proof -
  have e1: "S *v u - d *s v = 0" and e2: "u + S *v v = 0" using ph by (simp_all add: Phi_def)
  from e2 have u: "u = - (S *v v)" by (simp add: eq_neg_iff_add_eq_0)
  have e1': "S *v u = d *s v" using e1 by simp
  have "S *v u = - (S *v (S *v v))" by (simp add: u mv_uminus)
  then have "d *s v = - (S *v (S *v v))" using e1' by simp
  then have Mv0: "M *v v = 0" using hM by simp
  obtain z where z: "v = M *v z" using hv by blast
  have v0: "v = 0" by (rule ker_im_inter[OF sym Mv0 z])
  then show ?thesis using u by simp
qed


section \<open>Part (d): the statement of the paper, with named assumptions\<close>

lemma fstv_smult: "fstv (c *s v) = c *s fstv v" by (simp add: vec_eq_iff)
lemma sndv_smult: "sndv (c *s v) = c *s sndv v" by (simp add: vec_eq_iff)

lemma fstv_zero [simp]: "fstv 0 = 0" by (simp add: vec_eq_iff)
lemma sndv_zero [simp]: "sndv 0 = 0" by (simp add: vec_eq_iff)

lemma Vset_sub:
  assumes "lin_sub p"
  shows "lin_sub (Vset p :: (rat^('n::finite + 'h::finite)) set)"
  using assms unfolding lin_sub_def Vset_def
  by (auto simp: fstv_add sndv_add fstv_smult sndv_smult dotp_add_left dotp_smult_left)

lemma image_sub:
  "lin_sub {(D::rat^'n::finite^'h::finite) *v x | x. dotp x evec = 0}"
  unfolding lin_sub_def
proof (intro conjI ballI allI impI)
  show "0 \<in> {D *v x | x. dotp x evec = 0}" by (auto intro: exI[of _ 0])
next
  fix a b assume "a \<in> {D *v x | x. dotp x evec = 0}" "b \<in> {D *v x | x. dotp x evec = 0}"
  then obtain x y where "a = D *v x" "dotp x evec = 0" "b = D *v y" "dotp y evec = 0" by auto
  then show "a + b \<in> {D *v x | x. dotp x evec = 0}"
    by (auto simp: matrix_vector_right_distrib dotp_add_left intro!: exI[of _ "x + y"])
next
  fix c a assume "a \<in> {D *v x | x. dotp x evec = 0}"
  then obtain x where "a = D *v x" "dotp x evec = 0" by auto
  then show "c *s a \<in> {D *v x | x. dotp x evec = 0}"
    by (auto simp: mv_smult dotp_smult_left intro!: exI[of _ "c *s x"])
qed

text \<open>The two named assumptions. The parameter hyp stands for "the extension to L = Q(sqrt(-delta)) of the
  positive definite rational form on the subspace S of Q^n (+) Q^h is hyperbolic".
  hyperbolic_iff_planes is the plane extraction of Theorem 5.1 together with the converse, and Witt
  cancellation over L (A08 of the triage). hyp_of_representation is the last step of the converse of
  prop:aux: W_L = im Delta (x) L is carried by iota + S onto -r_L (iota_identity, Phi_injective), the kernel U
  is a sum of planes, and so (q perp p)_L is hyperbolic for p = D(e^perp) = D(W).\<close>

locale prop_aux_hyp =
  fixes hyp :: "(rat^('n::finite + 'h::finite)) set \<Rightarrow> bool"
  assumes n3: "3 \<le> CARD('n)"
    and hyperbolic_iff_planes:
      "\<And>S. lin_sub S \<Longrightarrow> hyp S \<longleftrightarrow> (\<exists>f g k. planes (lamn TYPE('n)) f g k \<and> Vspan f g k = S)"
    and hyp_of_representation:
      "\<And>(T::rat^'n^'n) (D::rat^'n^'h). contr_rep T D \<Longrightarrow> hyp (Vset {D *v x | x. dotp x evec = 0})"
begin

theorem prop_aux_if:
  assumes "lin_sub p" "hyp (Vset p)"
  shows "\<exists>B::rat^'n^('n + 'h). repr_Q (Hn::rat^'n^'n) iota_mat B \<and> (\<forall>x. sndv (B *v x) \<in> p)"
proof -
  have h: "hyp (Vset p) \<longleftrightarrow>
      (\<exists>f g k. planes (lamn TYPE('n)) f g k \<and> Vspan f g k = (Vset p :: (rat^('n + 'h)) set))"
    by (rule hyperbolic_iff_planes) (rule Vset_sub[OF assms(1)])
  have "\<exists>f g k. planes (lamn TYPE('n)) f g k \<and> Vspan f g k = (Vset p :: (rat^('n + 'h)) set)"
    using h assms(2) by blast
  then obtain f g k where "planes (lamn TYPE('n)) f g k" "Vspan f g k = (Vset p :: (rat^('n + 'h)) set)" by blast
  then show ?thesis using planes_give_length[OF n3 assms(1)] by blast
qed

theorem prop_aux_only_if:
  assumes rep: "repr_Q (Hn::rat^'n^'n) (iota_mat::rat^'n^('n + 'h)) B"
  shows "\<exists>p. lin_sub p \<and> hyp (Vset p) \<and> (\<forall>x. sndv (B *v x) \<in> p)"
proof -
  let ?D = "blk2 B"
  have cr: "contr_rep (blk1 B) ?D" using rep by (simp add: repr_iff_contr)
  let ?p = "{?D *v x | x. dotp x evec = 0}"
  have De: "?D *v evec = 0" by (rule contr_fixes_e(2)[OF n3 cr])
  have nz: "(of_nat CARD('n)::rat) \<noteq> 0" by (rule n_nonzero[OF n3])
  have "\<forall>x. sndv (B *v x) \<in> ?p"
  proof
    fix x :: "rat^'n"
    let ?c = "dotp x evec / of_nat CARD('n)"
    have z0: "dotp (x - ?c *s evec) evec = 0"
      using nz by (simp add: dotp_diff_left dotp_smult_left dotp_evec_evec)
    have "?D *v x = ?D *v (x - ?c *s evec)"
      by (simp add: matrix_vector_mult_diff_distrib mv_smult De)
    then show "sndv (B *v x) \<in> ?p" using z0 by (auto simp: sndv_Bmv)
  qed
  then show ?thesis using image_sub hyp_of_representation[OF cr] by blast
qed

theorem prop_aux_normal_form:
  "(\<exists>B::rat^'n^('n + 'h). repr_Q (Hn::rat^'n^'n) iota_mat B) \<longleftrightarrow> (\<exists>p. lin_sub p \<and> hyp (Vset p))"
  using prop_aux_if prop_aux_only_if by blast

text \<open>The statement of the paper, l_Q(H_n) <= n + h iff some p inside I_h makes (q perp p)_L hyperbolic, with
  the matrix form A, B arbitrary. It needs in addition the Witt normalization A = (I;0) of Proposition 2.1
  ((2) implies (3)), which is a third named assumption, the premise witt_normalization.\<close>

theorem prop_aux:
  assumes witt_normalization:
    "\<And>A B::rat^'n^('n + 'h). repr_Q (Hn::rat^'n^'n) A B
        \<Longrightarrow> \<exists>B'. repr_Q (Hn::rat^'n^'n) (iota_mat::rat^'n^('n + 'h)) B'"
  shows "len_le (TYPE('n + 'h)) (Hn::rat^'n^'n) \<longleftrightarrow> (\<exists>p. lin_sub p \<and> hyp (Vset p))"
proof
  assume "len_le (TYPE('n + 'h)) (Hn::rat^'n^'n)"
  then obtain A B :: "rat^'n^('n + 'h)" where "repr_Q (Hn::rat^'n^'n) A B" by (auto simp: len_le_def)
  then obtain B' where rep': "repr_Q (Hn::rat^'n^'n) (iota_mat::rat^'n^('n + 'h)) B'"
    using witt_normalization by blast
  from prop_aux_only_if[OF rep'] show "\<exists>p. lin_sub p \<and> hyp (Vset p)" by blast
next
  assume "\<exists>p. lin_sub p \<and> hyp (Vset p)"
  then obtain p where "lin_sub p" "hyp (Vset p)" by blast
  then obtain B :: "rat^'n^('n + 'h)" where "repr_Q (Hn::rat^'n^'n) iota_mat B"
    using prop_aux_if by blast
  then show "len_le (TYPE('n + 'h)) (Hn::rat^'n^'n)" unfolding len_le_def by blast
qed

end

end
