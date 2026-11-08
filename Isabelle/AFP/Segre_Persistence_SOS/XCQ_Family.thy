(*  Title:      XCQ_Family.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: the family F_t = Q + t w^2 above the Xu-Cui-Qi form of length eight: 8 squares for t >= 1/2 *)
section \<open>A family above the Xu--Cui--Qi form of length eight\<close>

theory XCQ_Family
  imports Complex_Main
begin

text \<open>Let $Q$ be the $4\times3$ biquadratic form of Xu, Cui and Qi @{cite XCQ} (Theorem 4.1), which is
  a sum of eight squares of bilinear forms and of no fewer, and let $w = d + h + l$ with
  $d = x_1y_0$, $h = x_2y_1$, $l = x_3y_2$ (indices from $0$). For $t > 0$ the Gram matrix of
  $F_t = Q + t\,w^2$ built from its nine forms is an extreme point of rank nine of the Gram
  spectrahedron; this was checked by computation and is not formalized here. Nevertheless $F_t$ is a
  sum of eight squares for every $t \ge 1/2$, and of seven at $t = 1/2$. This theory proves the
  polynomial identity behind it and the resulting representations. The variables are
  $x\colon \mathbb{N}\to\mathbb{R}$ and $y\colon \mathbb{N}\to\mathbb{R}$, read on the indices
  $0..3$ and $0..2$.\<close>

definition xcq_z :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "xcq_z x y i j = x i * y j"

text \<open>The form $Q$ of @{cite XCQ}, Theorem 4.1.\<close>

definition xcq_Q :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "xcq_Q x y = (xcq_z x y 0 0)\<^sup>2 + (xcq_z x y 1 1)\<^sup>2 + (xcq_z x y 2 2)\<^sup>2 + (xcq_z x y 0 1)\<^sup>2
     + (xcq_z x y 1 2)\<^sup>2 + (xcq_z x y 2 0)\<^sup>2 + (xcq_z x y 3 0)\<^sup>2
     + (xcq_z x y 3 1 + xcq_z x y 0 2)\<^sup>2"

definition xcq_d :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where "xcq_d x y = xcq_z x y 1 0"
definition xcq_h :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where "xcq_h x y = xcq_z x y 2 1"
definition xcq_l :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where "xcq_l x y = xcq_z x y 3 2"

text \<open>The family $F_t = Q + t\,(d + h + l)^2$.\<close>

definition xcq_F :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "xcq_F x y t = xcq_Q x y + t * (xcq_d x y + xcq_h x y + xcq_l x y)\<^sup>2"

text \<open>Six squares.\<close>

definition xcq_S :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "xcq_S x y = (xcq_z x y 0 0)\<^sup>2 + (xcq_z x y 0 1)\<^sup>2 + (xcq_z x y 0 2 + xcq_z x y 3 1)\<^sup>2
     + (xcq_z x y 2 2)\<^sup>2 + (xcq_z x y 1 1 + xcq_z x y 2 0)\<^sup>2 + (xcq_z x y 1 2 + xcq_z x y 3 0)\<^sup>2"

text \<open>The scaled identity, valid for every real $t$.\<close>

theorem scaled_identity:
  "t * xcq_F x y t = t * xcq_S x y + (t * (xcq_h x y + xcq_l x y) + (t - 1) * xcq_d x y)\<^sup>2
     + (2 * t - 1) * (xcq_d x y)\<^sup>2"
  unfolding xcq_F_def xcq_Q_def xcq_S_def xcq_d_def xcq_h_def xcq_l_def xcq_z_def
  by (simp add: power2_eq_square algebra_simps)

text \<open>For $t \ge 1/2$, $F_t$ is a sum of eight squares of bilinear forms: the six of $S$, then
  $(t(h + l) + (t - 1)d)/\sqrt t$ and $\sqrt{(2t - 1)/t}\,d$.\<close>

theorem eight_squares:
  assumes ht: "1 / 2 \<le> t"
  shows "xcq_F x y t = xcq_S x y + ((t * (xcq_h x y + xcq_l x y) + (t - 1) * xcq_d x y) / sqrt t)\<^sup>2
     + (sqrt ((2 * t - 1) / t) * xcq_d x y)\<^sup>2"
proof -
  define A where "A = t * (xcq_h x y + xcq_l x y) + (t - 1) * xcq_d x y"
  have t0: "0 < t" using ht by simp
  have q0: "0 \<le> (2 * t - 1) / t" using ht t0 by simp
  have key: "t * xcq_F x y t = t * xcq_S x y + A\<^sup>2 + (2 * t - 1) * (xcq_d x y)\<^sup>2"
    unfolding A_def by (rule scaled_identity)
  have r1: "(A / sqrt t)\<^sup>2 = A\<^sup>2 / t"
    using t0 by (simp add: power_divide)
  have r2: "(sqrt ((2 * t - 1) / t) * xcq_d x y)\<^sup>2 = (2 * t - 1) / t * (xcq_d x y)\<^sup>2"
    using q0 by (simp add: power_mult_distrib)
  have "xcq_F x y t = (t * xcq_F x y t) / t" using t0 by simp
  also have "\<dots> = (t * xcq_S x y + A\<^sup>2 + (2 * t - 1) * (xcq_d x y)\<^sup>2) / t" by (simp only: key)
  also have "\<dots> = xcq_S x y + A\<^sup>2 / t + (2 * t - 1) / t * (xcq_d x y)\<^sup>2"
    using t0 by (simp add: field_simps)
  finally show ?thesis unfolding A_def[symmetric] r1 r2 .
qed

text \<open>At $t = 1/2$ the last square vanishes: seven squares.\<close>

theorem seven_squares_half:
  "xcq_F x y (1 / 2) = xcq_S x y + ((xcq_h x y + xcq_l x y) - xcq_d x y)\<^sup>2 / 2"
  unfolding xcq_F_def xcq_Q_def xcq_S_def xcq_d_def xcq_h_def xcq_l_def xcq_z_def
  by (simp add: power2_eq_square field_simps)

end
