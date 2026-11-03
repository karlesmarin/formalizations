theory Catalecticant
  imports Main
begin

section \<open>Sylvester's catalecticant\<close>

text \<open>
  Setting.  A binary form of degree @{text n} is
  @{text "f(x,y) = \<Sum>_{i=0}^n a_i C(n,i) x^{n-i} y^i"}.  If
  @{text "f = \<Sum>_k \<lambda>_k (\<alpha>_k x + \<beta>_k y)^n"}, the binomial theorem gives
  @{text "(\<alpha>x+\<beta>y)^n = \<Sum>_i C(n,i) \<alpha>^{n-i} \<beta>^i x^{n-i} y^i"}, so comparing the
  coefficient of @{text "C(n,i) x^{n-i} y^i"} gives exactly
  @{text "a_i = \<Sum>_k \<lambda>_k \<alpha>_k^{n-i} \<beta>_k^i"}.  This is the hypothesis
  below, so the statement is the same as the one in the theorem, with
  the binomial weights absorbed in the normalisation of @{text "a_i"}.
\<close>

definition coef_pow :: "('k \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> 'k set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "coef_pow lam al be K n i = (\<Sum>k\<in>K. lam k * al k ^ (n - i) * be k ^ i)"

subsection \<open>Direction (necessity)\<close>

text \<open>
  Only the vanishing @{text "h(\<alpha>_k,\<beta>_k) = 0"} is used, which is weaker than
  the factorisation of @{text h} into distinct linear factors; distinctness
  is needed only for the converse.
\<close>

theorem catalecticant_necessary:
  fixes lam al be :: "'k \<Rightarrow> 'a::comm_ring_1" and c :: "nat \<Rightarrow> 'a"
  assumes fin: "finite K"
    and hz: "\<And>k. k \<in> K \<Longrightarrow> (\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l) = 0"
    and jr: "j + r \<le> n"
  shows "(\<Sum>l\<in>{..r}. coef_pow lam al be K n (j + l) * c l) = 0"
proof -
  obtain m where m: "n = j + r + m" using jr le_Suc_ex by blast
  have tm: "\<And>k l. l \<in> {..r} \<Longrightarrow>
      lam k * al k ^ (n - (j + l)) * be k ^ (j + l) * c l
      = lam k * al k ^ m * be k ^ j * (c l * al k ^ (r - l) * be k ^ l)"
  proof -
    fix k l assume "l \<in> {..r}"
    then have "n - (j + l) = m + (r - l)" using m by auto
    then show "lam k * al k ^ (n - (j + l)) * be k ^ (j + l) * c l
      = lam k * al k ^ m * be k ^ j * (c l * al k ^ (r - l) * be k ^ l)"
      by (simp add: power_add algebra_simps)
  qed
  have "(\<Sum>l\<in>{..r}. coef_pow lam al be K n (j + l) * c l)
      = (\<Sum>l\<in>{..r}. \<Sum>k\<in>K. lam k * al k ^ (n - (j + l)) * be k ^ (j + l) * c l)"
    by (simp add: coef_pow_def sum_distrib_right)
  also have "\<dots> = (\<Sum>k\<in>K. \<Sum>l\<in>{..r}. lam k * al k ^ (n - (j + l)) * be k ^ (j + l) * c l)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>k\<in>K. lam k * al k ^ m * be k ^ j * (\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l))"
    by (rule sum.cong[OF refl]) (simp add: sum_distrib_left tm)
  also have "\<dots> = 0"
    by (rule sum.neutral) (simp add: hz)
  finally show ?thesis .
qed

text \<open>
  The vanishing hypothesis follows from the factorisation
  @{text "h(x,y) = \<Prod>_m (-\<beta>_m x + \<alpha>_m y)"} (as polynomial identity in
  @{text "x,y"}), since the factor with @{text "m = k"} vanishes at
  @{text "(\<alpha>_k,\<beta>_k)"}.
\<close>

lemma factor_vanishes:
  fixes al be :: "'k \<Rightarrow> 'a::comm_ring_1" and c :: "nat \<Rightarrow> 'a"
  assumes fin: "finite K" and k: "k \<in> K"
    and fac: "\<And>x y. (\<Sum>l\<in>{..r}. c l * x ^ (r - l) * y ^ l)
                    = (\<Prod>m\<in>K. (- be m * x + al m * y))"
  shows "(\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l) = 0"
proof -
  have "(\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l)
      = (\<Prod>m\<in>K. (- be m * al k + al m * be k))"
    using fac[where x = "al k" and y = "be k"] .
  also have "\<dots> = 0"
    by (rule prod_zero[OF fin bexI[where x = k]]) (simp_all add: k mult.commute)
  finally show ?thesis .
qed

corollary catalecticant_necessary_factored:
  fixes lam al be :: "'k \<Rightarrow> 'a::comm_ring_1" and c :: "nat \<Rightarrow> 'a"
  assumes fin: "finite K"
    and fac: "\<And>x y. (\<Sum>l\<in>{..r}. c l * x ^ (r - l) * y ^ l)
                    = (\<Prod>m\<in>K. (- be m * x + al m * y))"
    and jr: "j + r \<le> n"
  shows "(\<Sum>l\<in>{..r}. coef_pow lam al be K n (j + l) * c l) = 0"
  using catalecticant_necessary[OF fin _ jr] factor_vanishes[OF fin _ fac] by blast

subsection \<open>The catalecticant of the binary quartic\<close>

definition det3 :: "'a::comm_ring \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "det3 a0 a1 a2 a3 a4 =
    a0 * (a2 * a4 - a3 * a3) - a1 * (a1 * a4 - a3 * a2) + a2 * (a1 * a3 - a2 * a2)"

text \<open>
  @{text det3} is the determinant of the Hankel matrix
  @{text "[[a0,a1,a2],[a1,a2,a3],[a2,a3,a4]]"} (Laplace expansion along the
  first row).
\<close>

theorem catalecticant_quartic:
  fixes a b c d e f lam mu nu :: "'a::comm_ring_1"
  defines "A i \<equiv> lam * a ^ (4 - i) * b ^ i + mu * c ^ (4 - i) * d ^ i + nu * e ^ (4 - i) * f ^ i"
  shows "det3 (A 0) (A 1) (A 2) (A 3) (A 4)
    = lam * mu * nu * ((a * d - b * c) ^ 2 * (a * f - b * e) ^ 2 * (c * f - d * e) ^ 2)"
  by (simp add: det3_def A_def power2_eq_square algebra_simps numeral_eq_Suc)

end
