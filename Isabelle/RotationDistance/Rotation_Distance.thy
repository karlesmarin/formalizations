(*  Title:      Rotation_Distance.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Every binary tree with n internal nodes reaches the right comb in at most n - 1 rotations, so rotation distance is at most 2n - 2
*)

theory Rotation_Distance
  imports Main
begin

section \<open>Upper bound 2n - 2 for the rotation distance between binary trees\<close>

datatype tree = Leaf | Node tree tree

text \<open>@{text "nodes t"} is the number of internal nodes.\<close>
fun nodes :: "tree \<Rightarrow> nat" where
  "nodes Leaf = 0"
| "nodes (Node l r) = nodes l + nodes r + 1"

inductive rot :: "tree \<Rightarrow> tree \<Rightarrow> bool" where
  rotR: "rot (Node (Node A B) C) (Node A (Node B C))"
| rotL: "rot (Node A (Node B C)) (Node (Node A B) C)"
| rot_left: "rot l l' \<Longrightarrow> rot (Node l r) (Node l' r)"
| rot_right: "rot r r' \<Longrightarrow> rot (Node l r) (Node l r')"

lemma rot_nodes: "rot t t' \<Longrightarrow> nodes t' = nodes t"
  by (induction rule: rot.induct) auto

lemma rot_sym: "rot t t' \<Longrightarrow> rot t' t"
proof (induction rule: rot.induct)
  case (rotR A B C) show ?case by (rule rot.rotL)
next
  case (rotL A B C) show ?case by (rule rot.rotR)
next
  case (rot_left l l' r)
  from rot_left.IH show ?case by (rule rot.rot_left)
next
  case (rot_right r r' l)
  from rot_right.IH show ?case by (rule rot.rot_right)
qed

text \<open>The comb (right spine) and the length of the right spine.\<close>

fun comb :: "nat \<Rightarrow> tree" where
  "comb 0 = Leaf"
| "comb (Suc n) = Node Leaf (comb n)"

fun rs :: "tree \<Rightarrow> nat" where
  "rs Leaf = 0"
| "rs (Node l r) = Suc (rs r)"

lemma nodes_comb: "nodes (comb n) = n"
  by (induction n) auto

lemma rs_le_nodes: "rs t \<le> nodes t"
  by (induction t) auto

lemma rs_full: "rs t = nodes t \<Longrightarrow> t = comb (nodes t)"
proof (induction t)
  case Leaf show ?case by simp
next
  case (Node l r)
  have "rs r \<le> nodes r" by (rule rs_le_nodes)
  with Node.prems have l0: "nodes l = 0" and e: "rs r = nodes r" by auto
  have "r = comb (nodes r)" by (rule Node.IH(2)[OF e])
  moreover from l0 have "l = Leaf" by (cases l) auto
  ultimately show ?case using l0 by simp
qed

lemma rot_step_exists:
  "rs t < nodes t \<Longrightarrow> \<exists>t'. rot t t' \<and> rs t' = Suc (rs t)"
proof (induction t)
  case Leaf thus ?case by simp
next
  case (Node l r)
  show ?case
  proof (cases l)
    case Leaf
    with Node.prems have "rs r < nodes r" by simp
    from Node.IH(2)[OF this] obtain r' where h1: "rot r r'" and h2: "rs r' = Suc (rs r)" by blast
    have "rot (Node l r) (Node l r')" by (rule rot.rot_right[OF h1])
    moreover have "rs (Node l r') = Suc (rs (Node l r))" using h2 by simp
    ultimately show ?thesis by blast
  next
    case (Node A B)
    have "rot (Node (Node A B) r) (Node A (Node B r))" by (rule rot.rotR)
    moreover have "rs (Node A (Node B r)) = Suc (rs (Node (Node A B) r))" by simp
    ultimately show ?thesis using Node by blast
  qed
qed

lemma to_comb: "nodes t - rs t = d \<Longrightarrow> (rot ^^ d) t (comb (nodes t))"
proof (induction d arbitrary: t)
  case 0
  hence "rs t = nodes t" using rs_le_nodes[where t = t] by simp
  thus ?case using rs_full by simp
next
  case (Suc e)
  hence lt: "rs t < nodes t" by simp
  from rot_step_exists[OF lt] obtain t' where r: "rot t t'" and s: "rs t' = Suc (rs t)" by blast
  have sz: "nodes t' = nodes t" by (rule rot_nodes[OF r])
  have "nodes t' - rs t' = e" using Suc.prems s sz by simp
  from Suc.IH[OF this] have h: "(rot ^^ e) t' (comb (nodes t))" using sz by simp
  show ?case by (rule relpowp_Suc_I2[OF r h])
qed

theorem comb_distance:
  assumes "nodes t = n" "1 \<le> n"
  shows "\<exists>k\<le>n - 1. (rot ^^ k) t (comb n)"
proof -
  have "t \<noteq> Leaf" using assms by auto
  then obtain l r where t: "t = Node l r" by (cases t) auto
  hence "1 \<le> rs t" by simp
  hence "nodes t - rs t \<le> n - 1" using assms by simp
  moreover have "(rot ^^ (nodes t - rs t)) t (comb n)"
    using to_comb[where t = t and d = "nodes t - rs t"] assms by simp
  ultimately show ?thesis by blast
qed

lemma relpowp_rot_sym: "(rot ^^ k) a b \<Longrightarrow> (rot ^^ k) b a"
proof (induction k arbitrary: a b)
  case 0 thus ?case by simp
next
  case (Suc k)
  from Suc.prems have "\<exists>c. rot a c \<and> (rot ^^ k) c b" by (rule relpowp_Suc_D2)
  then obtain c where h1: "rot a c" and h2: "(rot ^^ k) c b" by blast
  have "(rot ^^ k) b c" by (rule Suc.IH[OF h2])
  moreover have "rot c a" by (rule rot_sym[OF h1])
  ultimately show ?case by (rule relpowp_Suc_I)
qed

theorem rotation_distance_bound:
  assumes "nodes s = n" "nodes t = n" "1 \<le> n"
  shows "\<exists>k\<le>2 * n - 2. (rot ^^ k) s t"
proof -
  obtain k1 where k1: "k1 \<le> n - 1" "(rot ^^ k1) s (comb n)"
    using comb_distance[OF assms(1,3)] by blast
  obtain k2 where k2: "k2 \<le> n - 1" "(rot ^^ k2) t (comb n)"
    using comb_distance[OF assms(2,3)] by blast
  have "(rot ^^ k2) (comb n) t" by (rule relpowp_rot_sym[OF k2(2)])
  with k1(2) have "(rot ^^ (k1 + k2)) s t" by (auto simp: relpowp_add)
  moreover have "k1 + k2 \<le> 2 * n - 2" using k1(1) k2(1) by simp
  ultimately show ?thesis by blast
qed

end
