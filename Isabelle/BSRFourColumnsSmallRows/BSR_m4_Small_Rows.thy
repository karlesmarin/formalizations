(*  Title:      BSR_m4_Small_Rows.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   The three algebraic steps of Lemma "Small row images" (label lem:small-rows) of the paper "Every m x 4 biquadratic
   sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (C. Marín, 2026, in preparation; earlier working title
   "Boundary inertia and sums of squares of biquadratic forms").

   (1) row_rank_one_simple: if a row of T has rank one, the covector (c,d) -> <e,T(c,d)> is a simple tensor
       alpha(c) * mu(d)  (uses flatness (H) only).
   (2) mixed_flatness / evaluation_step: G_b(F_a(c)) = G_c(F_a(b)); hence F_a(b0) = 0 implies F_a(B) in ker G_b0.
       row_in_line adds: if ker G_b0 lies on a line spanned by w, the row a is rank <= 1.
   (3) small_rows_contradiction: common eigenvector of the C_b, injectivity of the tableau, and absence of nonzero
       rank-one tableau members give False.
   Not formalized: dimension counting (d <= s, s = d), the identification of D with S and the matrices C_b, the
   existence of b0 with dim ker G_b0 <= 1 (Lemma small-tableaux), the commutator step and the common eigenvector
   (Lemma common-line, see BSR_m4_Linear2), and the final deduction that a nonzero row is excluded via nondegeneracy
   and surjectivity. The statements are over an arbitrary field; scalar action is explicit (sm) as in BSR_m4_Linear2. *)
theory BSR_m4_Small_Rows
  imports Main
begin

section \<open>(1) Row-rank observation\<close>

text \<open>E is an abstract space ('e) with scalar action sm over a field ('k); J is a bilinear form, linear in the first
  argument; T c d is bilinear in (c,d) (bilinearity is not needed here). Flatness (H):
  J (T x b) (T y c) = J (T x c) (T y b).\<close>

theorem row_rank_one_simple:
  fixes J :: "'e \<Rightarrow> 'e \<Rightarrow> 'k::field"
    and sm :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and T :: "'a \<Rightarrow> 'b \<Rightarrow> 'e" and lam :: "'b \<Rightarrow> 'k"
  assumes Jsm: "\<And>t u w. J (sm t u) w = t * J u w"
    and flat: "\<And>x y b c. J (T x b) (T y c) = J (T x c) (T y b)"
    and row: "\<And>b. T a b = sm (lam b) e"
    and b0: "lam b0 \<noteq> 0"
  shows "\<exists>alpha mu. \<forall>c d. J e (T c d) = alpha c * mu d"
proof (intro exI allI)
  fix c d
  let ?alpha = "\<lambda>c. J e (T c b0)" and ?mu = "\<lambda>d. lam d / lam b0"
  have key: "\<And>b d c. lam b * J e (T c d) = lam d * J e (T c b)"
  proof -
    fix b d c
    have "lam b * J e (T c d) = J (sm (lam b) e) (T c d)" by (simp add: Jsm)
    also have "\<dots> = J (T a b) (T c d)" by (simp add: row)
    also have "\<dots> = J (T a d) (T c b)" by (rule flat)
    also have "\<dots> = lam d * J e (T c b)" by (simp add: row Jsm)
    finally show "lam b * J e (T c d) = lam d * J e (T c b)" .
  qed
  have "lam b0 * J e (T c d) = lam d * J e (T c b0)" by (rule key)
  with b0 show "J e (T c d) = ?alpha c * ?mu d" by (simp add: field_simps eq_divide_eq)
qed

text \<open>Both factors can be taken nonzero as soon as the covector is: if J e (T c0 d0) \<noteq> 0 then alpha c0 \<noteq> 0 and
  mu d0 \<noteq> 0.\<close>

corollary row_rank_one_simple_nonzero:
  fixes J :: "'e \<Rightarrow> 'e \<Rightarrow> 'k::field"
    and sm :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and T :: "'a \<Rightarrow> 'b \<Rightarrow> 'e" and lam :: "'b \<Rightarrow> 'k"
  assumes "\<And>t u w. J (sm t u) w = t * J u w"
    and "\<And>x y b c. J (T x b) (T y c) = J (T x c) (T y b)"
    and "\<And>b. T a b = sm (lam b) e" and "lam b0 \<noteq> 0" and "J e (T c0 d0) \<noteq> 0"
  shows "\<exists>alpha mu. (\<forall>c d. J e (T c d) = alpha c * mu d) \<and> alpha c0 \<noteq> 0 \<and> mu d0 \<noteq> 0"
proof -
  from row_rank_one_simple[of J sm T a lam e b0, OF assms(1-4)]
  obtain alpha mu
    where h: "\<And>c d. J e (T c d) = alpha c * mu d" by blast
  from assms(5) h[of c0 d0] have "alpha c0 \<noteq> 0" "mu d0 \<noteq> 0" by auto
  with h show ?thesis by blast
qed

section \<open>(2) Evaluation step\<close>

text \<open>G b z c = J z (T c b) is the covector of the tableau, F a b = T a b the row map.
  Mixed flatness: G_b (F_a c) = G_c (F_a b).\<close>

theorem mixed_flatness:
  fixes J :: "'e \<Rightarrow> 'e \<Rightarrow> 'k" and T :: "'a \<Rightarrow> 'b \<Rightarrow> 'e"
  assumes flat: "\<And>x y b c. J (T x b) (T y c) = J (T x c) (T y b)"
  shows "J (T a c) (T x b) = J (T a b) (T x c)"
  by (rule flat)

theorem evaluation_step:
  fixes J :: "'e::zero \<Rightarrow> 'e \<Rightarrow> 'k::zero" and T :: "'a \<Rightarrow> 'b \<Rightarrow> 'e"
  assumes flat: "\<And>x y b c. J (T x b) (T y c) = J (T x c) (T y b)"
    and J0: "\<And>w. J 0 w = 0"
    and zero: "T a b0 = 0"
  shows "J (T a b) (T c b0) = 0"
proof -
  have "J (T a b) (T c b0) = J (T a b0) (T c b)" by (rule flat)
  also have "\<dots> = 0" using zero J0 by simp
  finally show ?thesis .
qed

text \<open>Equivalently F_a(B) lies in ker G_b0 whenever F_a(b0) = 0. If that kernel is on a line spanned by w, the row a
  has rank at most one: T a b = lam b * w.\<close>

corollary row_in_line:
  fixes J :: "'e::zero \<Rightarrow> 'e \<Rightarrow> 'k::zero" and T :: "'a \<Rightarrow> 'b \<Rightarrow> 'e"
    and sm :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
  assumes "\<And>x y b c. J (T x b) (T y c) = J (T x c) (T y b)" and "\<And>w. J 0 w = 0" and "T a b0 = 0"
    and line: "\<And>z. (\<forall>c. J z (T c b0) = 0) \<Longrightarrow> \<exists>t. z = sm t w"
  shows "\<exists>lam. \<forall>b. T a b = sm (lam b) w"
proof -
  have "\<exists>t. T a b = sm t w" for b
  proof (rule line)
    show "\<forall>c. J (T a b) (T c b0) = 0"
    proof
      fix c
      show "J (T a b) (T c b0) = 0"
        by (rule evaluation_step) (fact assms(1), fact assms(2), fact assms(3))
    qed
  qed
  then show ?thesis by metis
qed

section \<open>(3) Final contradiction\<close>

text \<open>G b z is a covector (a function of c, values in a field), G b = G b0 o C b, C b z = lam b * z, and the map
  z -> (b -> G b z) is injective (kernel form: G b z = 0 for all b forces z = 0). No nonzero tableau member has the
  form b -> mu b * w (every such member vanishes). The hypothesis z \<noteq> 0 is essential.\<close>

theorem small_rows_contradiction:
  fixes G :: "'b \<Rightarrow> 'e::zero \<Rightarrow> 'c \<Rightarrow> 'k::field"
    and C :: "'b \<Rightarrow> 'e \<Rightarrow> 'e" and sm :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and lam :: "'b \<Rightarrow> 'k" and z :: 'e
  assumes factor: "\<And>b u. G b u = G b0 (C b u)"
    and homog: "\<And>t u c. G b0 (sm t u) c = t * G b0 u c"
    and eigen: "\<And>b. C b z = sm (lam b) z" and z_ne: "z \<noteq> 0"
    and inj: "\<And>u. (\<forall>b c. G b u c = 0) \<Longrightarrow> u = 0"
    and norank1: "\<And>u mu w. (\<forall>b c. G b u c = mu b * w c) \<Longrightarrow> (\<forall>b c. G b u c = 0)"
  shows False
proof -
  have "G b z c = lam b * G b0 z c" for b c
  proof -
    have "G b z c = G b0 (C b z) c" by (simp only: factor[of b z])
    also have "\<dots> = G b0 (sm (lam b) z) c" by (simp only: eigen)
    also have "\<dots> = lam b * G b0 z c" by (rule homog)
    finally show ?thesis .
  qed
  then have "\<forall>b c. G b z c = lam b * G b0 z c" by blast
  from norank1[OF this] inj z_ne show False by blast
qed

end
