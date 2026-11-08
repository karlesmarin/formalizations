(*  Title:      Width3_Final.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: V236 section 4, branch e = 1 closed: with S > 0, an S-orthonormal basis (Gram-Schmidt) gives the
   congruence H~ = (I_3 (x) F)^T H (I_3 (x) F) with H~ <= I, tr H~ = a, rank <= a + 1 and a negative direction,
   which Trace_Rank.trace_rank_neg forbids: theorem width_three_trace *)
theory Width3_Final
  imports Width3_Trace Trace_Rank
begin

text \<open>The end of branch $e=1$. The note normalizes by the block congruence with $S^{-1/2}$; any $F$ with
  $F^{\mathsf T}SF=I_a$ whose columns span $\mathbb{R}^a$ does the same job, and Gram--Schmidt for the inner
  product $S\succ0$ provides one (\<open>gram_schmidt_S\<close>). With $\tilde H_{pq}=F^{\mathsf T}H_{pq}F$:
  $L\succeq0$ gives $\tilde H\preceq I_{3a}$; $\sum_j\tilde H_{jj}=F^{\mathsf T}SF=I_a$ gives
  $\operatorname{tr}\tilde H=a$; a factorization of $H$ through $a+1$ terms gives one of $\tilde H$; and a
  negative direction of $H$ is the image of one of $\tilde H$. \<open>trace_rank_neg\<close> then gives
  $\operatorname{tr}\tilde H<a$, a contradiction (\<open>width_three_trace\<close>).\<close>

section \<open>Linearity of the forms\<close>

lemma lin1: "(\<Sum>l\<in>L. (\<Sum>k\<in>K. c k * g k l) * R l) = (\<Sum>k\<in>K. c k * (\<Sum>l\<in>L. g k l * R l))"
  for R :: "'b \<Rightarrow> real"
  unfolding sum_distrib_right sum_distrib_left by (subst sum.swap) (simp add: mult_ac)

lemma sform_row: "sform a S x z = (\<Sum>l<a. x l * (\<Sum>l'<a. S l l' * z l'))"
  unfolding sform_def by (simp add: sum_distrib_left mult_ac)

lemma sform_col: "sform a S x z = (\<Sum>l'<a. z l' * (\<Sum>l<a. x l * S l l'))"
  unfolding sform_def sum_distrib_left by (subst sum.swap) (simp add: mult_ac)

lemma bf_row: "bf a h p q x z = (\<Sum>l<a. x l * (\<Sum>l'<a. h p q l l' * z l'))"
  unfolding bf_def by (simp add: sum_distrib_left mult_ac)

lemma bf_col: "bf a h p q x z = (\<Sum>l'<a. z l' * (\<Sum>l<a. x l * h p q l l'))"
  unfolding bf_def sum_distrib_left by (subst sum.swap) (simp add: mult_ac)

lemma sform_sum_left: "sform a S (\<lambda>l. \<Sum>k\<in>K. c k * g k l) z = (\<Sum>k\<in>K. c k * sform a S (g k) z)"
  unfolding sform_row by (rule lin1)

lemma sform_sum_right: "sform a S x (\<lambda>l. \<Sum>k\<in>K. c k * g k l) = (\<Sum>k\<in>K. c k * sform a S x (g k))"
  unfolding sform_col by (subst lin1) (simp add: mult_ac)

lemma bf_sum_left: "bf a h p q (\<lambda>l. \<Sum>k\<in>K. c k * g k l) z = (\<Sum>k\<in>K. c k * bf a h p q (g k) z)"
  unfolding bf_row by (rule lin1)

lemma bf_sum_right: "bf a h p q x (\<lambda>l. \<Sum>k\<in>K. c k * g k l) = (\<Sum>k\<in>K. c k * bf a h p q x (g k))"
  unfolding bf_col by (subst lin1) (simp add: mult_ac)

lemma sform_diff_left: "sform a S (\<lambda>l. x l - y l) z = sform a S x z - sform a S y z"
  unfolding sform_def by (simp add: left_diff_distrib sum_subtractf)

lemma sform_scale_left: "sform a S (\<lambda>l. x l / c) z = sform a S x z / c"
  unfolding sform_def by (simp add: sum_divide_distrib)

lemma sform_scale_right: "sform a S x (\<lambda>l. z l / c) = sform a S x z / c"
  unfolding sform_def by (simp add: sum_divide_distrib)

lemma sform_cong:
  assumes "\<forall>l<a. x l = x' l" "\<forall>l<a. z l = z' l" shows "sform a S x z = sform a S x' z'"
  unfolding sform_def using assms by simp

lemma bf_cong:
  assumes "\<forall>l<a. x l = x' l" "\<forall>l<a. z l = z' l" shows "bf a h p q x z = bf a h p q x' z'"
  unfolding bf_def using assms by simp

section \<open>Gram--Schmidt for $S\succ0$\<close>

definition unitv :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "unitv k = (\<lambda>i. if i = k then 1 else 0)"

lemma gram_schmidt_step:
  assumes Spd: "\<And>x. (\<exists>l<a. x l \<noteq> 0) \<Longrightarrow> 0 < sform a S x x"
    and Ssym: "\<forall>l l'. S l' l = S l l'" and n: "n \<le> a"
  shows "\<exists>f. (\<forall>k<n. \<forall>k'<n. sform a S (f k) (f k') = (if k = k' then 1 else 0))
           \<and> (\<forall>k<n. \<forall>l. k < l \<longrightarrow> f k l = 0)
           \<and> (\<forall>j<n. \<exists>d. \<forall>i<a. unitv j i = (\<Sum>k<n. d k * f k i))"
  using n
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  then obtain f where on: "\<forall>k<n. \<forall>k'<n. sform a S (f k) (f k') = (if k = k' then 1 else 0)"
    and sp: "\<forall>k<n. \<forall>l. k < l \<longrightarrow> f k l = 0"
    and sn: "\<forall>j<n. \<exists>d. \<forall>i<a. unitv j i = (\<Sum>k<n. d k * f k i)" by auto
  have na: "n < a" using Suc.prems by simp
  define c where "c k = sform a S (unitv n) (f k)" for k
  define z where "z i = unitv n i - (\<Sum>k<n. c k * f k i)" for i
  have zf: "sform a S z (f m) = 0" if m: "m < n" for m
  proof -
    have "sform a S z (f m) = c m - (\<Sum>k<n. c k * sform a S (f k) (f m))"
      unfolding z_def[abs_def] c_def sform_diff_left sform_sum_left by simp
    also have "(\<Sum>k<n. c k * sform a S (f k) (f m)) = (\<Sum>k<n. if k = m then c m else 0)"
      using on m by (intro sum.cong refl) auto
    also have "\<dots> = c m" using m by simp
    finally show ?thesis by simp
  qed
  have zn: "z n = 1" unfolding z_def unitv_def using sp by simp
  have zhi: "z l = 0" if "n < l" for l unfolding z_def unitv_def using sp that by simp
  define \<nu> where "\<nu> = sform a S z z"
  have \<nu>: "0 < \<nu>" unfolding \<nu>_def by (rule Spd) (use zn na in auto)
  define f' where "f' = f(n := (\<lambda>i. z i / sqrt \<nu>))"
  have on': "\<forall>k<Suc n. \<forall>k'<Suc n. sform a S (f' k) (f' k') = (if k = k' then 1 else 0)"
  proof (intro allI impI)
    fix k k' assume k: "k < Suc n" and k': "k' < Suc n"
    show "sform a S (f' k) (f' k') = (if k = k' then 1 else 0)"
    proof (cases "k = n"; cases "k' = n")
      assume "k = n" "k' = n"
      have "sform a S (\<lambda>i. z i / sqrt \<nu>) (\<lambda>i. z i / sqrt \<nu>) = \<nu> / sqrt \<nu> / sqrt \<nu>"
        by (simp add: sform_scale_left sform_scale_right \<nu>_def)
      also have "\<dots> = \<nu> / (sqrt \<nu> * sqrt \<nu>)" by simp
      also have "sqrt \<nu> * sqrt \<nu> = \<nu>" using \<nu> by simp
      finally show ?thesis unfolding f'_def using \<nu> \<open>k = n\<close> \<open>k' = n\<close> by simp
    next
      assume "k = n" "k' \<noteq> n"
      then show ?thesis unfolding f'_def using zf[of k'] k' by (simp add: sform_scale_left)
    next
      assume "k \<noteq> n" "k' = n"
      then show ?thesis unfolding f'_def using zf[of k] k sform_sym[OF Ssym, of a z "f k"]
        by (simp add: sform_scale_right)
    next
      assume "k \<noteq> n" "k' \<noteq> n"
      then show ?thesis unfolding f'_def using on k k' by simp
    qed
  qed
  have sp': "\<forall>k<Suc n. \<forall>l. k < l \<longrightarrow> f' k l = 0"
    unfolding f'_def using sp zhi by auto
  have sn': "\<forall>j<Suc n. \<exists>d. \<forall>i<a. unitv j i = (\<Sum>k<Suc n. d k * f' k i)"
  proof (intro allI impI)
    fix j assume j: "j < Suc n"
    show "\<exists>d. \<forall>i<a. unitv j i = (\<Sum>k<Suc n. d k * f' k i)"
    proof (cases "j = n")
      case True
      define d where "d k = (if k = n then sqrt \<nu> else c k)" for k
      have "unitv j i = (\<Sum>k<Suc n. d k * f' k i)" for i
      proof -
        have "(\<Sum>k<Suc n. d k * f' k i) = sqrt \<nu> * (z i / sqrt \<nu>) + (\<Sum>k<n. c k * f k i)"
          unfolding d_def f'_def by simp
        also have "\<dots> = unitv n i" unfolding z_def using \<nu> by simp
        finally show ?thesis using True by simp
      qed
      then show ?thesis by blast
    next
      case False
      then have "j < n" using j by simp
      then obtain d where d: "\<forall>i<a. unitv j i = (\<Sum>k<n. d k * f k i)" using sn by blast
      define d' where "d' k = (if k = n then 0 else d k)" for k
      have "unitv j i = (\<Sum>k<Suc n. d' k * f' k i)" if "i < a" for i
        using d that unfolding d'_def f'_def by simp
      then show ?thesis by blast
    qed
  qed
  show ?case using on' sp' sn' by blast
qed

text \<open>An $S$-orthonormal basis $f_0,\dots,f_{a-1}$ of $\mathbb{R}^a$: $f_k^{\mathsf T}Sf_{k'}=\delta_{kk'}$, and
  every vector is a combination of the $f_k$.\<close>
theorem gram_schmidt_S:
  assumes Spd: "\<And>x. (\<exists>l<a. x l \<noteq> 0) \<Longrightarrow> 0 < sform a S x x"
    and Ssym: "\<forall>l l'. S l' l = S l l'"
  shows "\<exists>f. (\<forall>k<a. \<forall>k'<a. sform a S (f k) (f k') = (if k = k' then 1 else 0))
           \<and> (\<forall>x. \<exists>c. \<forall>i<a. x i = (\<Sum>k<a. c k * f k i))"
proof -
  obtain f where on: "\<forall>k<a. \<forall>k'<a. sform a S (f k) (f k') = (if k = k' then 1 else 0)"
    and sn: "\<forall>j<a. \<exists>d. \<forall>i<a. unitv j i = (\<Sum>k<a. d k * f k i)"
    using gram_schmidt_step[OF Spd Ssym, of a] by auto
  have "\<forall>j. \<exists>d. j < a \<longrightarrow> (\<forall>i<a. unitv j i = (\<Sum>k<a. d k * f k i))" using sn by blast
  then obtain D where D0: "\<forall>j. j < a \<longrightarrow> (\<forall>i<a. unitv j i = (\<Sum>k<a. D j k * f k i))"
    by (metis choice)
  have D: "\<forall>j<a. \<forall>i<a. unitv j i = (\<Sum>k<a. D j k * f k i)" using D0 by blast
  have "\<exists>c. \<forall>i<a. x i = (\<Sum>k<a. c k * f k i)" for x
  proof -
    define c where "c k = (\<Sum>j<a. x j * D j k)" for k
    have "x i = (\<Sum>k<a. c k * f k i)" if i: "i < a" for i
    proof -
      have "x i = (\<Sum>j<a. x j * unitv j i)"
        unfolding unitv_def using i by (simp add: if_distrib cong: if_cong)
      also have "\<dots> = (\<Sum>j<a. x j * (\<Sum>k<a. D j k * f k i))" using D i by simp
      also have "\<dots> = (\<Sum>k<a. c k * f k i)"
        unfolding c_def sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
      finally show ?thesis .
    qed
    then show ?thesis by blast
  qed
  with on show ?thesis by blast
qed

section \<open>The congruence and the contradiction\<close>

text \<open>Branch $e=1$, the multiplier on $A'\otimes B$: blocks symmetric with $H_{pq}=H_{qp}$; $L=I_3\otimes
  S-H\succeq0$ (the second-order condition, through \<open>second_variation_identity\<close>); full support in
  $A'$; rank $\le a+1$, written as a factorization through $a+1$ terms; and a negative direction ($H$
  is indefinite). These are incompatible.\<close>
theorem width_three_trace:
  fixes h :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
    and W C :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> real"
  assumes hs: "\<forall>p q l l'. h q p l l' = h p q l l'" and bs: "\<forall>p q l l'. h p q l' l = h p q l l'"
    and L: "\<forall>u. 0 \<le> lform a h u u"
    and supp: "\<And>x. (\<forall>j<3. \<forall>w. hform a h (blk j x) w = 0) \<Longrightarrow> \<forall>l<a. x l = 0"
    and rank: "\<forall>p<3. \<forall>q<3. \<forall>l<a. \<forall>l'<a. h p q l l' = (\<Sum>t<Suc a. W t (p, l) * C t (q, l'))"
    and neg: "hform a h u0 u0 < 0"
  shows False
proof -
  have Ssym: "\<forall>l l'. Str h l' l = Str h l l'" unfolding Str_def using bs by simp
  have Spd: "0 < sform a (Str h) x x" if "\<exists>l<a. x l \<noteq> 0" for x
    by (rule S_pd[OF hs bs L supp that])
  obtain f where on: "\<forall>k<a. \<forall>k'<a. sform a (Str h) (f k) (f k') = (if k = k' then 1 else 0)"
    and sn: "\<forall>x. \<exists>c. \<forall>i<a. x i = (\<Sum>k<a. c k * f k i)"
    using gram_schmidt_S[OF Spd Ssym] by blast
  define I where "I = {..<(3::nat)} \<times> {..<a}"
  have fI: "finite I" unfolding I_def by simp
  define X where "X = (\<lambda>(p, k) (q, k'). bf a h p q (f k) (f k'))"
  text \<open>The vector $u=(I_3\otimes F)\tilde u$ of $\tilde u$.\<close>
  define emb where "emb w = (\<lambda>p l. \<Sum>k<a. w (p, k) * f k l)" for w :: "nat \<times> nat \<Rightarrow> real"
  have sumI: "(\<Sum>x\<in>I. g x) = (\<Sum>p<3. \<Sum>k<a. g (p, k))" for g :: "nat \<times> nat \<Rightarrow> real"
    unfolding I_def by (simp add: sum.cartesian_product)
  have qX: "qI I X w = hform a h (emb w) (emb w)" for w
  proof -
    have "bf a h p q (emb w p) (emb w q) = (\<Sum>k<a. \<Sum>k'<a. w (p, k) * X (p, k) (q, k') * w (q, k'))" for p q
      unfolding emb_def X_def bf_sum_left bf_sum_right by (simp add: sum_distrib_left mult_ac)
    then have "hform a h (emb w) (emb w)
        = (\<Sum>p<3. \<Sum>q<3. \<Sum>k<a. \<Sum>k'<a. w (p, k) * X (p, k) (q, k') * w (q, k'))"
      unfolding hform_def by simp
    also have "\<dots> = (\<Sum>p<3. \<Sum>k<a. \<Sum>q<3. \<Sum>k'<a. w (p, k) * X (p, k) (q, k') * w (q, k'))"
      by (rule sum.cong[OF refl], rule sum.swap)
    also have "\<dots> = qI I X w" unfolding qI_def sumI by simp
    finally show ?thesis by simp
  qed
  have dX: "dI I w w = (\<Sum>p<3. sform a (Str h) (emb w p) (emb w p))" for w
  proof -
    have "sform a (Str h) (emb w p) (emb w p) = (\<Sum>k<a. w (p, k) * w (p, k))" if "p < 3" for p
    proof -
      have "sform a (Str h) (emb w p) (emb w p)
          = (\<Sum>k<a. w (p, k) * (\<Sum>k'<a. w (p, k') * sform a (Str h) (f k) (f k')))"
        unfolding emb_def sform_sum_left sform_sum_right ..
      also have "\<dots> = (\<Sum>k<a. w (p, k) * w (p, k))"
      proof (rule sum.cong[OF refl])
        fix k assume k: "k \<in> {..<a}"
        have "(\<Sum>k'<a. w (p, k') * sform a (Str h) (f k) (f k')) = (\<Sum>k'<a. if k' = k then w (p, k) else 0)"
          using on k by (intro sum.cong refl) auto
        also have "\<dots> = w (p, k)" using k by simp
        finally show "w (p, k) * (\<Sum>k'<a. w (p, k') * sform a (Str h) (f k) (f k')) = w (p, k) * w (p, k)"
          by simp
      qed
      finally show ?thesis .
    qed
    then show ?thesis unfolding dI_def sumI by simp
  qed
  have bfT: "bf a h q p z x = bf a h p q x z" for p q x z
  proof -
    have "bf a h q p z x = (\<Sum>l<a. z l * (\<Sum>l'<a. h q p l l' * x l'))" by (rule bf_row)
    also have "\<dots> = (\<Sum>l<a. z l * (\<Sum>l'<a. x l' * h p q l' l))"
      using hs bs by (simp add: mult.commute)
    also have "\<dots> = bf a h p q x z" by (rule bf_col[symmetric])
    finally show ?thesis .
  qed
  have symX: "symI I X"
    unfolding symI_def X_def using bfT by auto
  have leX: "leI I X"
    unfolding leI_def
  proof
    fix w
    have "0 \<le> lform a h (emb w) (emb w)" using L by blast
    then show "qI I X w \<le> dI I w w" unfolding qX dX lform_def by simp
  qed
  have trX: "trI I X = real a"
  proof -
    have "trI I X = (\<Sum>k<a. \<Sum>p<3. bf a h p p (f k) (f k))"
      unfolding trI_def sumI X_def by (subst sum.swap) simp
    also have "\<dots> = (\<Sum>k<a. sform a (Str h) (f k) (f k))" by (simp add: sum_bf_diag)
    also have "\<dots> = real a" using on by simp
    finally show ?thesis .
  qed
  define W' where "W' t = (\<lambda>(p, k). \<Sum>l<a. W t (p, l) * f k l)" for t
  define C' where "C' t = (\<lambda>(q, k'). \<Sum>l'<a. C t (q, l') * f k' l')" for t
  have fX: "factI I {..<Suc a} W' C' X"
    unfolding factI_def
  proof (intro ballI)
    fix x y assume x: "x \<in> I" and y: "y \<in> I"
    obtain p k where xp: "x = (p, k)" and p: "p < 3" using x unfolding I_def by auto
    obtain q k' where yq: "y = (q, k')" and q: "q < 3" using y unfolding I_def by auto
    have "bf a h p q (f k) (f k') = (\<Sum>l<a. \<Sum>l'<a. \<Sum>t<Suc a. f k l * W t (p, l) * C t (q, l') * f k' l')"
      unfolding bf_def
    proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
      fix l l' assume l: "l \<in> {..<a}" and l': "l' \<in> {..<a}"
      have hr: "h p q l l' = (\<Sum>t<Suc a. W t (p, l) * C t (q, l'))" using rank p q l l' by simp
      show "f k l * h p q l l' * f k' l' = (\<Sum>t<Suc a. f k l * W t (p, l) * C t (q, l') * f k' l')"
        unfolding hr by (simp only: sum_distrib_left sum_distrib_right) (rule sum.cong[OF refl], simp add: mult_ac)
    qed
    also have "\<dots> = (\<Sum>l<a. \<Sum>t<Suc a. \<Sum>l'<a. f k l * W t (p, l) * C t (q, l') * f k' l')"
      by (rule sum.cong[OF refl], rule sum.swap)
    also have "\<dots> = (\<Sum>t<Suc a. \<Sum>l<a. \<Sum>l'<a. f k l * W t (p, l) * C t (q, l') * f k' l')"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>t<Suc a. (\<Sum>l<a. W t (p, l) * f k l) * (\<Sum>l'<a. C t (q, l') * f k' l'))"
      unfolding sum_product by (rule sum.cong[OF refl])+ (simp add: mult_ac)
    finally show "X x y = (\<Sum>t\<in>{..<Suc a}. W' t x * C' t y)"
      unfolding xp yq X_def W'_def C'_def by simp
  qed
  have "\<forall>p. \<exists>d. \<forall>i<a. u0 p i = (\<Sum>k<a. d k * f k i)" using sn by blast
  then obtain c where c: "\<forall>p. \<forall>i<a. u0 p i = (\<Sum>k<a. c p k * f k i)"
    by (metis choice)
  define w0 where "w0 = (\<lambda>(p, k). c p k)"
  have e: "\<forall>p. \<forall>i<a. emb w0 p i = u0 p i" unfolding emb_def w0_def using c by simp
  have "hform a h (emb w0) (emb w0) = hform a h u0 u0"
    unfolding hform_def using e by (intro sum.cong refl) (rule bf_cong, auto)
  then have negX: "qI I X w0 < 0" using neg qX by simp
  have "trI I X + 1 < real (card {..<Suc a})"
    by (rule trace_rank_neg[OF fI _ symX leX fX negX]) simp
  then show False using trX by simp
qed

end
