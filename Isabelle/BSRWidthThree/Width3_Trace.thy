(* encaje: V236 section 4, branch e = 1 (elementary part): the alternating-symbol variations D_i,
   the contraction identity of epsilon, sum_i H(D_i,D_i) = sum_p v_p^T S v_p - sum_pq v_p^T H_pq v_q,
   L = I_3 (x) S - H >= 0 gives S >= 0, and full support gives S > 0 *)
theory Width3_Trace
  imports BSR_Width3_Lower
begin

text \<open>Branch $e=1$ of section 4 of the note. The multiplier restricted to $A'\otimes B$ ($\dim A'=a$,
  $\dim B=3$) is a block matrix $H=(H_{pq})_{p,q<3}$ with $a\times a$ blocks, stored as
  \<open>h p q l l'\<close>; a vector of $A'\otimes B$ is \<open>u :: nat \<Rightarrow> nat \<Rightarrow> real\<close> with block \<open>u p\<close>
  ($p<3$, coordinates $<a$). The Hankel identity gives $H_{pq}=H_{qp}$ and symmetric blocks.

  Covered here:
  \<^item> the variations $D_i=\sum_{j,p}\varepsilon_{ijp}\,v_p\otimes y_j$ lie in the kernel of the
    differential: $\sum_i (x_0\otimes y_i)D_i=0$ as a form (\<open>variation_in_kernel\<close>);
  \<^item> the contraction identity $\sum_i\varepsilon_{ijp}\varepsilon_{ilq}=\delta_{jl}\delta_{pq}-\delta_{jq}\delta_{pl}$
    (\<open>eps_contract\<close>);
  \<^item> $\sum_iH(D_i,D_i)=\sum_pv_p^{\mathsf T}Sv_p-\sum_{p,q}v_p^{\mathsf T}H_{pq}v_q=L(v,v)$ with
    $S=\sum_jH_{jj}$ and $L=I_3\otimes S-H$ (\<open>second_variation_identity\<close>);
  \<^item> $L\succeq0\Rightarrow S\succeq0$ (\<open>S_psd\<close>) and, with full support, $S\succ0$ (\<open>S_pd\<close>).

  The second-order condition $\sum_iH(D_i,D_i)\ge0$ itself comes from the boundary point of section 2
  and enters as the hypothesis $L\succeq0$.\<close>

section \<open>Block forms\<close>

definition bf :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "bf a h p q x z = (\<Sum>l<a. \<Sum>l'<a. x l * h p q l l' * z l')"

text \<open>$H(u,w)=\sum_{p,q<3}u_p^{\mathsf T}H_{pq}w_q$.\<close>
definition hform :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> real" where
  "hform a h u w = (\<Sum>p<3. \<Sum>q<3. bf a h p q (u p) (w q))"

text \<open>$S=\sum_{j<3}H_{jj}$.\<close>
definition Str :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "Str h = (\<lambda>l l'. \<Sum>p<3. h p p l l')"

definition sform :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "sform a S x z = (\<Sum>l<a. \<Sum>l'<a. x l * S l l' * z l')"

text \<open>$L(u,w)=\sum_p u_p^{\mathsf T}Sw_p-H(u,w)$, i.e. $L=I_3\otimes S-H$.\<close>
definition lform :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> real" where
  "lform a h u w = (\<Sum>p<3. sform a (Str h) (u p) (w p)) - hform a h u w"

lemma bf_add_left: "bf a h p q (\<lambda>l. x l + x' l) z = bf a h p q x z + bf a h p q x' z"
  unfolding bf_def by (simp add: distrib_right sum.distrib)

lemma bf_add_right: "bf a h p q x (\<lambda>l. z l + z' l) = bf a h p q x z + bf a h p q x z'"
  unfolding bf_def by (simp add: distrib_left sum.distrib)

lemma bf_scale_left: "bf a h p q (\<lambda>l. c * x l) z = c * bf a h p q x z"
  unfolding bf_def by (simp add: sum_distrib_left mult_ac)

lemma bf_scale_right: "bf a h p q x (\<lambda>l. c * z l) = c * bf a h p q x z"
  unfolding bf_def by (simp add: sum_distrib_left mult_ac)

lemma bf_sum3_left: "bf a h p q (\<lambda>l. \<Sum>t<(3::nat). c t * x t l) z = (\<Sum>t<3. c t * bf a h p q (x t) z)"
  by (simp add: sum3 bf_add_left bf_scale_left)

lemma bf_sum3_right: "bf a h p q x (\<lambda>l. \<Sum>t<(3::nat). c t * z t l) = (\<Sum>t<3. c t * bf a h p q x (z t))"
  by (simp add: sum3 bf_add_right bf_scale_right)

lemma bf_swap_blocks:
  assumes "\<forall>l l'. h q p l l' = h p q l l'" shows "bf a h q p x z = bf a h p q x z"
  unfolding bf_def using assms by simp

lemma sum_bf_diag: "(\<Sum>j<3. bf a h j j x z) = sform a (Str h) x z"
  unfolding bf_def sform_def Str_def
  by (simp add: sum3 sum.distrib[symmetric] sum_distrib_left sum_distrib_right algebra_simps)

section \<open>The alternating symbol\<close>

definition eps :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "eps i j p = (if (i, j, p) \<in> {(0, 1, 2), (1, 2, 0), (2, 0, 1)} then 1
                else if (i, j, p) \<in> {(0, 2, 1), (2, 1, 0), (1, 0, 2)} then -1 else 0)"

lemma eps_contract:
  assumes "j < 3" "p < 3" "l < 3" "q < 3"
  shows "(\<Sum>i<3. eps i j p * eps i l q)
       = (if j = l \<and> p = q then 1 else 0) - (if j = q \<and> p = l then 1 else 0)"
  using less3_cases[OF assms(1)] less3_cases[OF assms(2)] less3_cases[OF assms(3)] less3_cases[OF assms(4)]
  by (elim disjE) (simp_all add: sum3 eps_def)

text \<open>The variations $D_i=\sum_{j,p}\varepsilon_{ijp}\,v_p\otimes y_j$, for $v_0,v_1,v_2\in A'$; block $j$ of
  $D_i$ is $\sum_p\varepsilon_{ijp}v_p$.\<close>
definition Dv :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "Dv v i j l = (\<Sum>p<3. eps i j p * v p l)"

text \<open>$D$ lies in the kernel of the differential at a representation whose first three summands are
  $x_0\otimes y_0,x_0\otimes y_1,x_0\otimes y_2$ (and $D_i=0$ for $i\ge3$): evaluated at any $(x,y)$,
  with $\xi=\langle x_0,x\rangle$ and $z_p=\langle v_p,x\rangle$, $\sum_i(\xi y_i)\,D_i(x,y)=0$.\<close>
lemma variation_in_kernel:
  "(\<Sum>i<3. (\<xi> * y i) * (\<Sum>j<3. \<Sum>p<3. eps i j p * z p * y j)) = (0::real)"
  by (simp add: sum3 eps_def algebra_simps)

section \<open>The second-variation identity\<close>

lemma hform_Dv:
  "hform a h (Dv v i) (Dv v i) = (\<Sum>j<3. \<Sum>l<3. \<Sum>p<3. \<Sum>q<3. eps i j p * eps i l q * bf a h j l (v p) (v q))"
proof -
  have "bf a h j l (Dv v i j) (Dv v i l) = (\<Sum>p<3. \<Sum>q<3. eps i j p * eps i l q * bf a h j l (v p) (v q))" for j l
  proof -
    have "bf a h j l (Dv v i j) (Dv v i l) = (\<Sum>p<3. eps i j p * bf a h j l (v p) (Dv v i l))"
      unfolding Dv_def[abs_def] by (simp only: bf_sum3_left)
    also have "\<dots> = (\<Sum>p<3. eps i j p * (\<Sum>q<3. eps i l q * bf a h j l (v p) (v q)))"
      unfolding Dv_def[abs_def] by (simp only: bf_sum3_right)
    finally show ?thesis by (simp add: sum_distrib_left mult_ac)
  qed
  then show ?thesis unfolding hform_def by simp
qed

text \<open>$\sum_iH(D_i,D_i)=\sum_pv_p^{\mathsf T}Sv_p-\sum_{p,q}v_p^{\mathsf T}H_{pq}v_q$; only $H_{pq}=H_{qp}$ is used.\<close>
theorem second_variation_identity:
  assumes hs: "\<forall>p q l l'. h q p l l' = h p q l l'"
  shows "(\<Sum>i<3. hform a h (Dv v i) (Dv v i)) = lform a h v v"
proof -
  have "(\<Sum>i<3. hform a h (Dv v i) (Dv v i))
      = (\<Sum>j<3. \<Sum>l<3. \<Sum>p<3. \<Sum>q<3. (\<Sum>i<3. eps i j p * eps i l q) * bf a h j l (v p) (v q))"
    unfolding hform_Dv by (simp add: sum3 algebra_simps)
  also have "\<dots> = (\<Sum>j<3. \<Sum>l<3. \<Sum>p<3. \<Sum>q<3.
        ((if j = l \<and> p = q then 1 else 0) - (if j = q \<and> p = l then 1 else 0)) * bf a h j l (v p) (v q))"
    by (intro sum.cong refl) (simp add: eps_contract)
  also have "\<dots> = (\<Sum>p<3. \<Sum>j<3. bf a h j j (v p) (v p)) - (\<Sum>p<3. \<Sum>q<3. bf a h p q (v p) (v q))"
  proof -
    have s: "bf a h q p x z = bf a h p q x z" for p q x z by (rule bf_swap_blocks) (use hs in blast)
    show ?thesis by (simp add: sum3 s[of 1 0] s[of 2 0] s[of 2 1] s[of "Suc 0" 0] s[of 2 "Suc 0"] algebra_simps)
  qed
  also have "\<dots> = lform a h v v"
    unfolding lform_def hform_def by (simp add: sum_bf_diag)
  finally show ?thesis .
qed

section \<open>$S\succeq0$ and $S\succ0$\<close>

text \<open>The block vector $x\otimes y_j$.\<close>
definition blk :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "blk j x = (\<lambda>p l. if p = j then x l else 0)"

lemma sform_zero_left: "sform a S (\<lambda>l. 0) z = 0" and sform_zero_right: "sform a S x (\<lambda>l. 0) = 0"
  unfolding sform_def by simp_all

lemma bf_zero_left: "bf a h p q (\<lambda>l. 0) z = 0" and bf_zero_right: "bf a h p q x (\<lambda>l. 0) = 0"
  unfolding bf_def by simp_all

lemma blk_apply: "blk j x p = (if p = j then x else (\<lambda>l. 0))"
  unfolding blk_def by auto

lemma hform_blk:
  assumes "j < 3" shows "hform a h (blk j x) (blk j x) = bf a h j j x x"
  using less3_cases[OF assms]
  by (auto simp: hform_def sum3 blk_apply bf_zero_left bf_zero_right)

lemma lform_blk:
  assumes "j < 3" shows "lform a h (blk j x) (blk j x) = sform a (Str h) x x - bf a h j j x x"
  using less3_cases[OF assms]
  by (auto simp: lform_def hform_blk[OF assms] sum3 blk_apply sform_zero_left sform_zero_right)

text \<open>The three diagonal blocks of $L$ add up to $2S$.\<close>
lemma lform_blk_sum: "(\<Sum>j<3. lform a h (blk j x) (blk j x)) = 2 * sform a (Str h) x x"
proof -
  have "(\<Sum>j<3. lform a h (blk j x) (blk j x)) = (\<Sum>j<3. sform a (Str h) x x - bf a h j j x x)"
    by (intro sum.cong refl) (simp add: lform_blk)
  also have "\<dots> = 3 * sform a (Str h) x x - sform a (Str h) x x"
    by (simp add: sum_subtractf sum_bf_diag)
  finally show ?thesis by simp
qed

theorem S_psd:
  assumes L: "\<forall>u. 0 \<le> lform a h u u"
  shows "0 \<le> sform a (Str h) x x"
proof -
  have "0 \<le> (\<Sum>j<3. lform a h (blk j x) (blk j x))" by (rule sum_nonneg) (use L in blast)
  then show ?thesis using lform_blk_sum by simp
qed

text \<open>A positive semidefinite form vanishes on the vectors where its quadratic form vanishes; the form
  is only used through the expansion of $Q(x+tw,x+tw)$.\<close>
lemma psd_kernel:
  fixes Qxx Qxw Qww :: real
  assumes exp: "\<And>t. 0 \<le> Qxx + 2 * t * Qxw + t\<^sup>2 * Qww" and z: "Qxx = 0" and w: "0 \<le> Qww"
  shows "Qxw = 0"
proof -
  define t where "t = - Qxw / (Qww + 1)"
  have d: "Qww + 1 > 0" using w by simp
  have "0 \<le> 2 * t * Qxw + t\<^sup>2 * Qww" using exp[of t] z by simp
  then have "0 \<le> (2 * t * Qxw + t\<^sup>2 * Qww) * (Qww + 1)\<^sup>2" using d by simp
  also have "(2 * t * Qxw + t\<^sup>2 * Qww) * (Qww + 1)\<^sup>2 = - Qxw\<^sup>2 * (Qww + 2)"
  proof -
    have e: "t * (Qww + 1) = - Qxw" unfolding t_def using d by simp
    have "(2 * t * Qxw + t\<^sup>2 * Qww) * (Qww + 1)\<^sup>2
        = 2 * Qxw * (t * (Qww + 1)) * (Qww + 1) + (t * (Qww + 1))\<^sup>2 * Qww"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = - Qxw\<^sup>2 * (Qww + 2)" unfolding e by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  finally have "Qxw\<^sup>2 * (Qww + 2) \<le> 0" by simp
  then have "Qxw\<^sup>2 \<le> 0" using w by (simp add: mult_le_0_iff)
  then show ?thesis by simp
qed

lemma sform_expand:
  "sform a S (\<lambda>l. x l + t * w l) (\<lambda>l. x l + t * w l)
     = sform a S x x + t * (sform a S x w + sform a S w x) + t\<^sup>2 * sform a S w w"
  unfolding sform_def
  by (simp add: algebra_simps power2_eq_square sum.distrib sum_distrib_left)

lemma sform_sym:
  assumes "\<forall>l l'. S l' l = S l l'" shows "sform a S w x = sform a S x w"
  unfolding sform_def using assms by (subst sum.swap) (simp add: mult_ac)

lemma lform_expand:
  "lform a h (\<lambda>p l. u p l + t * w p l) (\<lambda>p l. u p l + t * w p l)
     = lform a h u u + t * (lform a h u w + lform a h w u) + t\<^sup>2 * lform a h w w"
  unfolding lform_def hform_def sform_def bf_def
  by (simp add: algebra_simps power2_eq_square sum.distrib sum_distrib_left sum_subtractf)

lemma lform_sym:
  assumes hs: "\<forall>p q l l'. h q p l l' = h p q l l'" and bs: "\<forall>p q l l'. h p q l' l = h p q l l'"
  shows "lform a h w u = lform a h u w"
proof -
  have S: "\<forall>l l'. Str h l' l = Str h l l'" unfolding Str_def using bs by simp
  have "bf a h p q (w p) (u q) = bf a h q p (u q) (w p)" for p q
    unfolding bf_def using hs bs by (subst sum.swap) (simp add: mult_ac)
  then have "hform a h w u = hform a h u w"
    unfolding hform_def by (subst sum.swap) simp
  then show ?thesis unfolding lform_def using sform_sym[OF S] by simp
qed

text \<open>Minimality of the support: $S\succ0$. If $x^{\mathsf T}Sx=0$, the nonnegative numbers
  $L(x\otimes y_j,x\otimes y_j)$ add up to $0$, so $L(x\otimes y_j,\cdot)=0$; also $Sx=0$; hence
  $H(x\otimes y_j,\cdot)=0$ for every $j$, and full support gives $x=0$.\<close>
theorem S_pd:
  assumes hs: "\<forall>p q l l'. h q p l l' = h p q l l'" and bs: "\<forall>p q l l'. h p q l' l = h p q l l'"
    and L: "\<forall>u. 0 \<le> lform a h u u"
    and supp: "\<And>x. (\<forall>j<3. \<forall>w. hform a h (blk j x) w = 0) \<Longrightarrow> \<forall>l<a. x l = 0"
    and x: "\<exists>l<a. x l \<noteq> 0"
  shows "0 < sform a (Str h) x x"
proof (rule ccontr)
  assume "\<not> 0 < sform a (Str h) x x"
  then have z: "sform a (Str h) x x = 0" using S_psd[OF L, of x] by simp
  have Ssym: "\<forall>l l'. Str h l' l = Str h l l'" unfolding Str_def using bs by simp
  have Spsd: "\<forall>y. 0 \<le> sform a (Str h) y y" using S_psd[OF L] by blast
  have Sx: "sform a (Str h) x w = 0" for w
  proof (rule psd_kernel)
    show "0 \<le> sform a (Str h) x x + 2 * t * sform a (Str h) x w + t\<^sup>2 * sform a (Str h) w w" for t
    proof -
      have "0 \<le> sform a (Str h) (\<lambda>l. x l + t * w l) (\<lambda>l. x l + t * w l)" using Spsd by blast
      then show ?thesis unfolding sform_expand sform_sym[OF Ssym, of a w x]
        by (simp add: algebra_simps)
    qed
  qed (use z Spsd in auto)
  have Lj0: "lform a h (blk j x) (blk j x) = 0" if "j < 3" for j
  proof -
    have "(\<Sum>j<3. lform a h (blk j x) (blk j x)) = 0" using lform_blk_sum z by simp
    then have "\<forall>j\<in>{..<3}. lform a h (blk j x) (blk j x) = 0"
      by (subst sum_nonneg_eq_0_iff[symmetric]) (use L in auto)
    then show ?thesis using that by simp
  qed
  have Lj: "lform a h (blk j x) w = 0" if j: "j < 3" for j w
  proof (rule psd_kernel)
    show "0 \<le> lform a h (blk j x) (blk j x) + 2 * t * lform a h (blk j x) w + t\<^sup>2 * lform a h w w" for t
    proof -
      have "0 \<le> lform a h (\<lambda>p l. blk j x p l + t * w p l) (\<lambda>p l. blk j x p l + t * w p l)"
        using L by blast
      then show ?thesis unfolding lform_expand lform_sym[OF hs bs, of a w "blk j x"]
        by (simp add: algebra_simps)
    qed
  qed (use Lj0[OF j] L in auto)
  have "hform a h (blk j x) w = 0" if j: "j < 3" for j w
  proof -
    have "(\<Sum>p<3. sform a (Str h) (blk j x p) (w p)) = sform a (Str h) x (w j)"
      using less3_cases[OF j] by (auto simp: sum3 blk_apply sform_zero_left)
    then show ?thesis using Lj[OF j, of w] Sx[of "w j"] unfolding lform_def by simp
  qed
  then have "\<forall>l<a. x l = 0" using supp by blast
  then show False using x by blast
qed

end
