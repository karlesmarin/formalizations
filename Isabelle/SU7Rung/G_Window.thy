(*  Title:      G_Window.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: su7-certified-gap, Proposition prop:mono (the G-window): mu decreasing, the admissible x an interval,
   dG/dx = -6 mu / x < 0; identity (I) for dG/dx is Part VII's and enters as a hypothesis *)
theory G_Window
  imports Complex_Main
begin

text \<open>Proposition \<open>prop:mono\<close> of the note on the certified gap of SU(7) gauge-Higgs unification. On a cell
  $(A_4,8D)$ with $8D>0$, write $z=\zeta(3)>0$ (any positive constant here) and $d=8D>0$. Identity (II) of Part VII
  gives $\mu(x)=z\,d/(4x^2)-A_4/6$; identity (I) of Part VII gives $G'(x)=A_4/x-K/x^3$ with $K=\tfrac{12}{8}z\,d$.
  The identities (I) and (II) are Part VII's; what this note claims, and what is proved here, is the consequence:
  $G'(x)=-6\mu(x)/x$, so $G$ decreases where $\mu>0$; $\mu$ is strictly decreasing, so the $x>0$ with
  $\mu(x)\in[\mu_-,\mu_+]$ form an interval; hence a target box pulls back to one interval of $G$ per cell.\<close>

definition mu :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "mu z d A x = z * d / (4 * x\<^sup>2) - A / 6"

lemma mu_strict_anti:
  assumes zd: "0 < z * d" and x: "0 < x" and xy: "x < y"
  shows "mu z d A y < mu z d A x"
proof -
  have sq: "x\<^sup>2 < y\<^sup>2" using x xy by (simp add: power_strict_mono)
  have "z * d / (4 * y\<^sup>2) < z * d / (4 * x\<^sup>2)"
    by (rule frac_less2) (use zd x sq in auto)
  then show ?thesis unfolding mu_def by simp
qed

text \<open>The admissible $x$ form an interval: membership is convex.\<close>
theorem mu_window_interval:
  assumes zd: "0 < z * d"
    and x1: "0 < x1" "a \<le> mu z d A x1" "mu z d A x1 \<le> b"
    and x2: "a \<le> mu z d A x2" "mu z d A x2 \<le> b"
    and x: "x1 \<le> x" "x \<le> x2"
  shows "0 < x \<and> a \<le> mu z d A x \<and> mu z d A x \<le> b"
proof -
  have xpos: "0 < x" using x1(1) x(1) by linarith
  have le2: "mu z d A x2 \<le> mu z d A x"
    using mu_strict_anti[OF zd xpos] x(2) by (cases "x = x2") (auto simp: less_eq_real_def)
  have le1: "mu z d A x \<le> mu z d A x1"
    using mu_strict_anti[OF zd x1(1)] x(1) by (cases "x1 = x") (auto simp: less_eq_real_def)
  show ?thesis using xpos le1 le2 x1 x2 by linarith
qed

text \<open>The identity of the proposition: with $K=\tfrac{12}{8}z d$, $A_4/x-K/x^3=-6\mu(x)/x$.\<close>
lemma G_derivative_identity:
  assumes x: "x \<noteq> 0"
  shows "A / x - (12 / 8 * z * d) / x ^ 3 = - 6 * mu z d A x / x"
  using x unfolding mu_def by (simp add: field_simps power2_eq_square power3_eq_cube)

text \<open>Hence $G$ is strictly decreasing on any interval of $x>0$ where $\mu>0$, given identity (I) of Part VII.\<close>
theorem G_strictly_decreasing:
  assumes I: "\<And>x. 0 < x \<Longrightarrow> (G has_real_derivative (A / x - (12 / 8 * z * d) / x ^ 3)) (at x)"
    and pos: "\<And>x. x1 \<le> x \<Longrightarrow> x \<le> x2 \<Longrightarrow> 0 < mu z d A x"
    and x1: "0 < x1" and lt: "x1 < x2"
  shows "G x2 < G x1"
proof -
  have "G x2 < G x1"
  proof (rule DERIV_neg_imp_decreasing[OF lt])
    fix x assume xx: "x1 \<le> x" "x \<le> x2"
    have xpos: "0 < x" using x1 xx(1) by linarith
    have "A / x - (12 / 8 * z * d) / x ^ 3 = - 6 * mu z d A x / x"
      using G_derivative_identity xpos by simp
    moreover have "- 6 * mu z d A x / x < 0" using pos[OF xx] xpos by (simp add: divide_neg_pos)
    ultimately show "\<exists>y. (G has_real_derivative y) (at x) \<and> y < 0" using I[OF xpos] by auto
  qed
  then show ?thesis .
qed

end
