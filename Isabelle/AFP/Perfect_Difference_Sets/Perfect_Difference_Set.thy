(*  Title:      Perfect_Difference_Set.thy
    Author:     Carles Marin

    Existence of a perfect difference set of positive integers: a set A of positive integers such
    that every nonzero integer is a - b for exactly one pair (a, b) of distinct elements of A.
    This is erdos_1194.variants.exists_perfect_difference_set of google-deepmind/formal-conjectures
    (IsPerfectDifferenceSetInt A := 0 \<notin> A \<and> the map (a, b) \<mapsto> a - b is a bijection from the
    off-diagonal of A onto the nonzero integers).  Greedy construction as in V. F. Lev,
    Reconstructing integer sets from their representation functions, Electron. J. Combin. 11 (2004),
    Section 3, with an explicit (not minimal) choice of the new element.
*)

theory Perfect_Difference_Set
  imports Main
begin

section \<open>Positive differences and uniqueness\<close>

definition pdiffs :: "nat set \<Rightarrow> nat set" where
  "pdiffs A = {a - b | a b. a \<in> A \<and> b \<in> A \<and> b < a}"

definition uniq :: "nat set \<Rightarrow> bool" where
  "uniq A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>A. \<forall>c\<in>A. \<forall>e\<in>A.
      b < a \<longrightarrow> e < c \<longrightarrow> a - b = c - e \<longrightarrow> a = c \<and> b = e)"

lemma pdiffs_iff: "n \<in> pdiffs A \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> A \<and> b < a \<and> a - b = n)"
  unfolding pdiffs_def by auto

lemma pdiffs_mono: "A \<subseteq> B \<Longrightarrow> pdiffs A \<subseteq> pdiffs B"
  unfolding pdiffs_def by blast

lemma pdiffs_finite: "finite A \<Longrightarrow> finite (pdiffs A)"
proof -
  assume "finite A"
  have "pdiffs A \<subseteq> (\<lambda>p. fst p - snd p) ` (A \<times> A)"
    unfolding pdiffs_def by force
  then show ?thesis
    using \<open>finite A\<close> by (meson finite_SigmaI finite_imageI finite_subset)
qed

section \<open>One greedy step\<close>

definition gap :: "nat set \<Rightarrow> nat" where
  "gap A = (LEAST d. 0 < d \<and> d \<notin> pdiffs A)"

definition top :: "nat set \<Rightarrow> nat" where
  "top A = Max (insert 0 A)"

definition step :: "nat set \<Rightarrow> nat set" where
  "step A = (let d = gap A; z = 2 * top A + d + 1 in A \<union> {z, z + d})"

lemma gap: assumes "finite A" shows "0 < gap A \<and> gap A \<notin> pdiffs A"
proof -
  have "finite (insert 0 (pdiffs A))"
    using pdiffs_finite[OF assms] by simp
  then obtain d :: nat where "d \<notin> insert 0 (pdiffs A)"
    using ex_new_if_finite[OF infinite_UNIV_nat] by blast
  then have "\<exists>d. 0 < d \<and> d \<notin> pdiffs A" by auto
  then show ?thesis
    unfolding gap_def by (rule LeastI_ex)
qed

lemma gap_least: "0 < n \<Longrightarrow> n < gap A \<Longrightarrow> n \<in> pdiffs A"
  unfolding gap_def using not_less_Least by blast

lemma top: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> a \<le> top A"
  unfolding top_def by simp

lemma step_eq: "step A = A \<union> {2 * top A + gap A + 1, 2 * top A + gap A + 1 + gap A}"
  unfolding step_def Let_def by simp

lemma step_sub: "A \<subseteq> step A"
  unfolding step_eq by blast

lemma gap_in_step: assumes "finite A" shows "gap A \<in> pdiffs (step A)"
proof -
  define z where "z = 2 * top A + gap A + 1"
  have mem: "z \<in> step A" "z + gap A \<in> step A"
    unfolding step_eq z_def by auto
  have "0 < gap A" using gap[OF assms] by blast
  then have "z < z + gap A" "(z + gap A) - z = gap A" by auto
  then show ?thesis
    unfolding pdiffs_iff using mem by blast
qed

lemma step_uniq:
  assumes fin: "finite A" and u: "uniq A"
  shows "uniq (step A)"
proof -
  define d where "d = gap A"
  define M where "M = top A"
  define z where "z = 2 * M + d + 1"
  have st: "step A = A \<union> {z, z + d}"
    unfolding step_eq z_def d_def M_def by simp
  have dpos: "0 < d" and dnot: "d \<notin> pdiffs A"
    using gap[OF fin] by (auto simp: d_def)
  have le: "\<And>x. x \<in> A \<Longrightarrow> x \<le> M"
    using top[OF fin] by (simp add: M_def)
  have nd: "x \<noteq> y + d" if x: "x \<in> A" and y: "y \<in> A" for x y
  proof
    assume xy: "x = y + d"
    then have "y < x" "x - y = d" using dpos by auto
    then have "d \<in> pdiffs A"
      unfolding pdiffs_def using x y by blast
    then show False using dnot by blast
  qed
  have cls: "(a \<in> A \<and> b \<in> A) \<or> (a = z \<and> b \<in> A) \<or> (a = z + d \<and> b \<in> A) \<or> (a = z + d \<and> b = z)"
    if a: "a \<in> step A" and b: "b \<in> step A" and ba: "b < a" for a b
  proof -
    have "a \<in> A \<or> a = z \<or> a = z + d" using a st by auto
    moreover have "b \<in> A \<or> b = z \<or> b = z + d" using b st by auto
    ultimately show ?thesis
      using ba le[of a] unfolding z_def by auto
  qed
  show ?thesis
    unfolding uniq_def
  proof (intro ballI impI)
    fix a b c e
    assume mem: "a \<in> step A" "b \<in> step A" "c \<in> step A" "e \<in> step A"
      and ba: "b < a" and ec: "e < c" and eq: "a - b = c - e"
    have eq': "a + e = c + b" using eq ba ec by arith
    have uu: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> c \<in> A \<Longrightarrow> e \<in> A \<Longrightarrow> a = c \<and> b = e"
      using u ba ec eq unfolding uniq_def by blast
    note facts = eq' uu le[of a] le[of b] le[of c] le[of e]
      nd[of a b] nd[of c e] nd[of e b] nd[of b e] dpos
    from cls[OF mem(1,2) ba] cls[OF mem(3,4) ec]
    show "a = c \<and> b = e"
      using facts unfolding z_def by (elim disjE) auto
  qed
qed

section \<open>The greedy sequence and its union\<close>

primrec seq :: "nat \<Rightarrow> nat set" where
  "seq 0 = {}"
| "seq (Suc k) = step (seq k)"

lemma seq_props: "finite (seq k) \<and> uniq (seq k) \<and> 0 \<notin> seq k \<and> {1..k} \<subseteq> pdiffs (seq k)"
proof (induction k)
  case 0
  then show ?case by (simp add: uniq_def)
next
  case (Suc k)
  define A where "A = seq k"
  have fin: "finite A" and u: "uniq A" and z: "0 \<notin> A" and cov: "{1..k} \<subseteq> pdiffs A"
    using Suc by (auto simp: A_def)
  have "finite (step A)" using fin by (simp add: step_eq)
  moreover have "uniq (step A)" using step_uniq[OF fin u] .
  moreover have "0 \<notin> step A" using z by (simp add: step_eq)
  moreover have "{1..Suc k} \<subseteq> pdiffs (step A)"
  proof
    fix n assume n: "n \<in> {1..Suc k}"
    show "n \<in> pdiffs (step A)"
    proof (cases "n \<le> k")
      case True
      then have "n \<in> pdiffs A" using cov n by auto
      then show ?thesis using pdiffs_mono[OF step_sub] by blast
    next
      case False
      then have nk: "n = Suc k" using n by auto
      show ?thesis
      proof (cases "n < gap A")
        case True
        then have "n \<in> pdiffs A" using gap_least n by auto
        then show ?thesis using pdiffs_mono[OF step_sub] by blast
      next
        case False
        have "gap A \<notin> {1..k}" using gap[OF fin] cov by blast
        then have "Suc k \<le> gap A" using gap[OF fin] by auto
        then have "n = gap A" using False nk by simp
        then show ?thesis using gap_in_step[OF fin] by simp
      qed
    qed
  qed
  ultimately show ?case by (simp add: A_def)
qed

lemma seq_mono: "j \<le> k \<Longrightarrow> seq j \<subseteq> seq k"
  by (rule lift_Suc_mono_le[of seq]) (simp_all add: step_sub)

definition S :: "nat set" where
  "S = (\<Union>k. seq k)"

lemma S_zero: "0 \<notin> S"
  unfolding S_def using seq_props by blast

lemma S_cov: "0 < n \<Longrightarrow> n \<in> pdiffs S"
proof -
  assume "0 < n"
  then have "n \<in> pdiffs (seq n)" using seq_props[of n] by auto
  moreover have "seq n \<subseteq> S" unfolding S_def by blast
  ultimately show ?thesis using pdiffs_mono by blast
qed

text \<open>The union of an increasing chain of sets with unique differences has unique differences.\<close>

lemma uniq_chain:
  assumes mono: "\<And>k. f k \<subseteq> f (Suc k)" and u: "\<And>k. uniq (f k)"
  shows "uniq (\<Union>k. f k)"
  unfolding uniq_def
proof (intro ballI impI)
  fix a b c e
  assume "a \<in> (\<Union>k. f k)" "b \<in> (\<Union>k. f k)" "c \<in> (\<Union>k. f k)" "e \<in> (\<Union>k. f k)"
    and h: "b < a" "e < c" "a - b = c - e"
  then obtain i j k l where "a \<in> f i" "b \<in> f j" "c \<in> f k" "e \<in> f l"
    by blast
  define K where "K = max (max i j) (max k l)"
  have "i \<le> K" "j \<le> K" "k \<le> K" "l \<le> K"
    unfolding K_def by auto
  then have "f i \<subseteq> f K" "f j \<subseteq> f K" "f k \<subseteq> f K" "f l \<subseteq> f K"
    by (simp_all add: lift_Suc_mono_le[of f, OF mono])
  then have "a \<in> f K" "b \<in> f K" "c \<in> f K" "e \<in> f K"
    using \<open>a \<in> f i\<close> \<open>b \<in> f j\<close> \<open>c \<in> f k\<close> \<open>e \<in> f l\<close> by blast+
  then show "a = c \<and> b = e"
    using u[of K] h unfolding uniq_def by blast
qed

lemma S_uniq: "uniq S"
  unfolding S_def
  by (rule uniq_chain) (simp_all add: step_sub seq_props)

section \<open>The formal-conjectures statement\<close>

text \<open>\<open>IsPerfectDifferenceSet A 0\<close> of formal-conjectures is \<open>Set.BijOn (fun (a, b) => (a - b : \<int>))
  A.offDiag {x | x \<noteq> 0}\<close> (as \<open>ZMod 0 = \<int>\<close>); \<open>BijOn\<close> (maps into, injective on, onto) is
  \<open>bij_betw\<close>.\<close>

lemma bij_of_uniq:
  assumes u: "uniq A" and A_cov: "\<And>n. 0 < n \<Longrightarrow> n \<in> pdiffs A"
  shows "bij_betw (\<lambda>(a, b). int a - int b) {(a, b). a \<in> A \<and> b \<in> A \<and> a \<noteq> b} {x :: int. x \<noteq> 0}"
proof -
  let ?f = "\<lambda>(a, b). int a - int b"
  let ?D = "{(a, b). a \<in> A \<and> b \<in> A \<and> a \<noteq> b}"
  have inj: "inj_on ?f ?D"
  proof (rule inj_onI)
    fix p q assume p: "p \<in> ?D" and q: "q \<in> ?D" and pq: "?f p = ?f q"
    obtain a b where pab: "p = (a, b)" by (cases p)
    obtain c e where qce: "q = (c, e)" by (cases q)
    have m: "a \<in> A" "b \<in> A" "c \<in> A" "e \<in> A" "a \<noteq> b" "c \<noteq> e"
      using p q pab qce by auto
    have eqi: "int a - int b = int c - int e" using pq pab qce by simp
    show "p = q"
    proof (cases "b < a")
      case True
      then have "e < c" "a - b = c - e" using eqi by auto
      then show ?thesis using u m True pab qce unfolding uniq_def by blast
    next
      case False
      then have "a < b" "c < e" "b - a = e - c" using eqi m(5) by auto
      then show ?thesis using u m pab qce unfolding uniq_def by blast
    qed
  qed
  have img: "?f ` ?D = {x :: int. x \<noteq> 0}"
  proof
    show "?f ` ?D \<subseteq> {x. x \<noteq> 0}" by auto
    show "{x :: int. x \<noteq> 0} \<subseteq> ?f ` ?D"
    proof
      fix x :: int assume "x \<in> {x. x \<noteq> 0}"
      then have x: "x \<noteq> 0" by simp
      show "x \<in> ?f ` ?D"
      proof (cases "0 < x")
        case True
        then have "nat x \<in> pdiffs A" using A_cov by simp
        then obtain a b where ab: "a \<in> A" "b \<in> A" "b < a" "a - b = nat x"
          unfolding pdiffs_iff by blast
        then have h1: "(a, b) \<in> ?D" and h2: "?f (a, b) = x" using True by auto
        show ?thesis by (rule rev_image_eqI[where f = ?f, OF h1 h2[symmetric]])
      next
        case False
        then have "nat (- x) \<in> pdiffs A" using A_cov x by simp
        then obtain a b where ab: "a \<in> A" "b \<in> A" "b < a" "a - b = nat (- x)"
          unfolding pdiffs_iff by blast
        then have h1: "(b, a) \<in> ?D" and h2: "?f (b, a) = x" using False x by auto
        show ?thesis by (rule rev_image_eqI[where f = ?f, OF h1 h2[symmetric]])
      qed
    qed
  qed
  show "bij_betw ?f ?D {x :: int. x \<noteq> 0}"
    unfolding bij_betw_def using inj img by blast
qed

theorem perfect_difference_set_exists:
  "\<exists>A :: nat set. 0 \<notin> A \<and>
     bij_betw (\<lambda>(a, b). int a - int b) {(a, b). a \<in> A \<and> b \<in> A \<and> a \<noteq> b} {x :: int. x \<noteq> 0}"
  using S_zero bij_of_uniq[OF S_uniq S_cov] by blast

end
