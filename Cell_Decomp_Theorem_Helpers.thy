theory Cell_Decomp_Theorem_Helpers
imports Denef_Lemma_2_4 Denef_Lemma_2_3 Algebras_of_Cells
begin

locale common_decomp_proof_context = denef_I + denef_II

locale common_refinement_locale = common_decomp_proof_context +
  fixes \<C> A c a1 a2 I f m
  assumes f_closed: "f \<in> carrier (UP (SA m))" 
  assumes f_deg: " deg (SA m) f \<le> (Suc d)"
  assumes \<C>_def: "\<C> = Cond m A c a1 a2 I"
  assumes \<C>_cond: "is_cell_condition \<C>" 
  assumes f_taylor_cfs: "\<And> i. (taylor_expansion (SA m) c f i = \<zero>\<^bsub>SA m\<^esub>) \<or> 
                                  (taylor_expansion (SA m) c f i \<in> Units (SA m))"

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Partitions by Zero Sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context padic_fields 
begin

definition zero_set_partition where
"zero_set_partition m Fs = atoms_of (gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (SA_zero_set m ` Fs))"

lemma nonzero_set_as_diff:
"SA_nonzero_set m f = (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) - (SA_zero_set m f)"
  unfolding SA_nonzero_set_def SA_zero_set_def by auto 

lemma  zero_set_partition_semialg:
  assumes "Fs \<subseteq> carrier (SA m)"
  assumes "finite Fs"
  assumes "a \<in> zero_set_partition m Fs"
  shows "is_semialgebraic m a"
proof- 
  have 0: "(SA_zero_set m ` Fs) \<subseteq> semialg_sets m"
    apply(rule subsetI) 
    using SA_zero_set_is_semialg assms unfolding SA_zero_set_def is_semialgebraic_def by auto 
  have "zero_set_partition m Fs \<subseteq> semialg_sets m"
    unfolding semialg_sets_def zero_set_partition_def
    apply(rule atoms_of_gen_boolean_algebra, rule gen_boolean_algebra_subalgebra)
    using 0 unfolding semialg_sets_def apply blast 
    apply(rule gen_boolean_algebra_finite) using assms by auto 
  thus ?thesis using assms 
    using is_semialgebraicI by auto
qed

lemma partition_by_zero_sets:
  assumes "finite Fs"
  assumes "Fs \<subseteq> carrier (SA m)"
  assumes "a \<in> zero_set_partition m Fs"
  assumes "f \<in> Fs"
  shows "(\<forall> x \<in> a. f x = \<zero>) \<or> (\<forall> x \<in> a. f x \<noteq> \<zero>)"
proof(cases "a \<subseteq> SA_zero_set m f")
  case True
  then show ?thesis unfolding SA_zero_set_def by auto  
next
  case False
  have F0: "SA_zero_set m f \<in> (gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (SA_zero_set m ` Fs))"
    apply(rule generator_closed)
    using assms unfolding SA_zero_set_def by auto 
  then have F1:  "a \<inter> SA_zero_set m f = {}"
    using assms atoms_are_minimal[of a _ "SA_zero_set m f"] False 
    unfolding zero_set_partition_def by blast
  have "a \<subseteq> SA_nonzero_set m f"  
    unfolding nonzero_set_as_diff 
    apply(intro atom_in_comp[of "SA_zero_set m ` Fs" _ _  "SA_zero_set m f"]
                F1 F0)
    using assms unfolding zero_set_partition_def by auto 
  thus ?thesis unfolding SA_nonzero_set_def by auto     
qed

lemma of_gen_boolean_algebra_un:
"\<Union> (gen_boolean_algebra S Xs) = S"
  using gen_boolean_algebra_subset[of _ S Xs] 
        gen_boolean_algebra.universe[of S Xs]
  by auto 

lemma gen_boolean_algebra_atom_un:
  assumes "finite Xs"
  assumes "Y \<in> gen_boolean_algebra S Xs"
  shows "Y = \<Union> {a \<in> atoms_of (gen_boolean_algebra S Xs). a \<subseteq> Y}"
  by(intro gen_boolean_algebra_elem_uni_of_atoms[of "gen_boolean_algebra S Xs" S]
              gen_boolean_algebra_finite assms, 
      unfold of_gen_boolean_algebra_un gen_boolean_algebra_idempotent, auto simp: assms)

lemma gen_boolean_algebra_atoms_cover:
  assumes "finite Xs"
  shows "S = \<Union> (atoms_of (gen_boolean_algebra S Xs))"
  using assms gen_boolean_algebra_atom_un[of Xs S S] 
  by (simp add: atoms_of_covers' of_gen_boolean_algebra_un)

lemma induced_partition:
  assumes "Xs partitions S"
  assumes "Y \<subseteq> S"
  shows "(\<inter>) Y ` Xs partitions Y"
  apply(intro is_partitionI disjointI)
  using assms is_partitionE disjointE 
   apply (smt (verit, best) Sup_upper boolean_algebra_cancel.inf1 image_iff inf.absorb_iff1 
              inf_Sup inf_bot_right)
  using assms by (metis inf.orderE inf_Sup is_partitionE(2))

lemma partition_by_zero_sets_covers: 
  assumes "finite Fs"
  shows "carrier (Q\<^sub>p\<^bsup>m\<^esup>) = \<Union> (zero_set_partition m Fs)"
  unfolding zero_set_partition_def 
  apply(rule gen_boolean_algebra_atoms_cover)
  using assms by blast

lemma partition_by_zero_sets_disjoint: 
  assumes "finite Fs"
  shows "disjoint (zero_set_partition m Fs)"
  apply(rule disjointI)
  using assms unfolding zero_set_partition_def 
  by (simp add: atoms_of_disjoint)

lemma partition_by_zero_sets_partitions:
  assumes "finite Fs"
  shows "(zero_set_partition m Fs) partitions (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"
  apply(rule is_partitionI)
  using partition_by_zero_sets_covers partition_by_zero_sets_disjoint assms by auto 

definition poly_cfs_car_part where
"poly_cfs_car_part m f = zero_set_partition m (f ` {..deg (SA m) f})"

lemma poly_cfs_car_part_semialg: 
  assumes "f \<in> carrier (UP (SA m))"
  assumes "a \<in> poly_cfs_car_part m f"
  shows "is_semialgebraic m a"
  apply(rule zero_set_partition_semialg[of "f ` {..deg (SA m) f}"])
  using assms cfs_closed poly_cfs_car_part_def by auto

lemma poly_cfs_car_part_memE:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "a \<in> poly_cfs_car_part m f"
  shows "(\<forall> x \<in> a. f i x = \<zero>) \<or> (\<forall> x \<in> a. f i x \<noteq> \<zero>)"
proof(cases "i > deg (SA m) f")
  case True
  then have T0: "f i = \<zero>\<^bsub>SA m\<^esub>"
    using assms UPSA.deg_leE by blast
  have "a \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms poly_cfs_car_part_semialg  is_semialgebraic_closed by presburger
  then have T1: "(\<forall>x\<in>a. \<zero>\<^bsub>SA m\<^esub> x = \<zero>)"
    using SA_zeroE by auto 
  show ?thesis
    unfolding T0 using T1 by auto 
next
  case False
  show ?thesis
    apply(intro partition_by_zero_sets[of "f ` {..deg (SA m) f}" m])
    using False assms cfs_closed poly_cfs_car_part_def by auto
qed

lemma  poly_cfs_car_part_finite:
  "finite (poly_cfs_car_part m f)"
  unfolding poly_cfs_car_part_def zero_set_partition_def 
  apply(rule atoms_finite)
  by auto 

lemma poly_cfs_car_part_covers:
"carrier (Q\<^sub>p\<^bsup>m\<^esup>) = \<Union> (poly_cfs_car_part m f)"
  using gen_boolean_algebra_elem_uni_of_atoms
  unfolding poly_cfs_car_part_def zero_set_partition_def 
  using partition_by_zero_sets_covers zero_set_partition_def by force

definition poly_cfs_part where
"poly_cfs_part m f A = ((\<inter>) A ` (poly_cfs_car_part m f)) - {{}}"

lemma poly_cfs_part_subset:
"\<And> a. a \<in> poly_cfs_part m f A \<Longrightarrow> a \<subseteq> A"
  unfolding poly_cfs_part_def by auto 

lemma partition_minus_empty:
  assumes "As partitions A"
  shows "(As - {{}}) partitions A"
  apply(rule is_partitionI)
  using assms is_partitionE disjointE disjointI apply fastforce
  using assms is_partitionE(2) by auto[1]

lemma poly_cfs_part_partitions:
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "(poly_cfs_part m f A) partitions A"
  unfolding poly_cfs_part_def poly_cfs_car_part_def
  apply(intro partition_minus_empty)
  apply(intro induced_partition[of _ "carrier (Q\<^sub>p\<^bsup>m\<^esup>)"] )
  by(rule partition_by_zero_sets_partitions, auto simp: assms)

lemma poly_cfs_part_finite:
"finite (poly_cfs_part m f A)"
  unfolding poly_cfs_part_def using poly_cfs_car_part_finite by auto 

lemma poly_cfs_part_memE:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "a \<in> poly_cfs_part m f A"
  shows "(\<forall> x \<in> a. f i x = \<zero>) \<or> (\<forall> x \<in> a. f i x \<noteq> \<zero>)"
  using poly_cfs_car_part_memE[of f m _ i] assms
        unfolding poly_cfs_part_def  by auto 

lemma poly_cfs_part_semialg:
  assumes "is_semialgebraic m A"
  assumes "f \<in> carrier (UP (SA m))"
  assumes "a \<in> poly_cfs_part m f A"
  shows "is_semialgebraic m a"
proof- 
  obtain a' where a'_def: "a' \<in> poly_cfs_car_part m f \<and> a = A \<inter> a'"
    using assms poly_cfs_part_def by auto 
  thus ?thesis 
  using assms poly_cfs_part_def intersection_is_semialg poly_cfs_car_part_semialg
    by auto 
qed

definition poly_unit_replacement where
"poly_unit_replacement m f a = (\<lambda> i::nat. if (\<forall> x \<in> a \<inter> (carrier (Q\<^sub>p\<^bsup>m\<^esup>)). f i x = \<zero>) then \<zero>\<^bsub>SA m\<^esub>
                                     else to_fun_unit m (f i))"

lemma poly_unit_replacement_dichotomy: 
  assumes "f \<in> carrier (UP (SA m))"
  assumes "is_semialgebraic m a"
  shows "\<And>i. poly_unit_replacement m f a i = \<zero>\<^bsub>SA m\<^esub> \<or> poly_unit_replacement m f a i \<in> Units (SA m) "
  unfolding poly_unit_replacement_def using assms  to_fun_unit_is_unit cfs_closed by auto 

lemma poly_unit_replacement_cfs_closed:
  assumes "f \<in> carrier (UP (SA m))"
  shows "poly_unit_replacement m f a i \<in> carrier (SA m)"
  apply(cases "\<forall> x \<in> a \<inter> (carrier (Q\<^sub>p\<^bsup>m\<^esup>)). f i x = \<zero>", unfold poly_unit_replacement_def)
  using assms to_fun_unit_closed[of "f i" m] cfs_closed[of f m i] by auto 

lemma poly_unit_replacement_above_deg:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "i > deg (SA m) f"
  shows "poly_unit_replacement m f a i = \<zero>\<^bsub>SA m\<^esub>"
proof- 
  have "f i = \<zero>\<^bsub>SA m\<^esub>"
    using assms UPSA.deg_leE by blast
  hence "\<forall>x\<in>a \<inter> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x = \<zero>"
    using SA_zeroE by auto 
  thus ?thesis 
    unfolding poly_unit_replacement_def  by auto
qed

lemma poly_unit_replacement_closed: 
  assumes "f \<in> carrier (UP (SA m))"
  shows "poly_unit_replacement m f a \<in> carrier (UP (SA m))"
  apply(intro UP_car_memI[of "deg (SA m) f"])
   apply(intro poly_unit_replacement_above_deg assms, auto)
  by(rule poly_unit_replacement_cfs_closed, rule assms)

lemma poly_unit_replacement_cfs1: 
  assumes "f \<in> carrier (UP (SA m))"
  assumes "(\<forall> x \<in> a. f i x = \<zero>)"
  shows "poly_unit_replacement m f a i = \<zero>\<^bsub>SA m\<^esub>"
  using assms
  unfolding poly_unit_replacement_def by auto 

lemma poly_unit_replacement_deg: 
  assumes "f \<in> carrier (UP (SA m))"
  shows "deg (SA m) (poly_unit_replacement m f a) \<le> deg (SA m) f"
  apply(rule deg_leqI)
    apply (simp add: assms poly_unit_replacement_closed)
 by (simp add: UPSA.deg_leqI assms padic_fields.poly_unit_replacement_closed padic_fields_axioms poly_unit_replacement_above_deg)

lemma poly_unit_replacement_cfs2: 
  assumes "f \<in> carrier (UP (SA m))"
  assumes "(\<forall> x \<in> a. f i x \<noteq> \<zero>)"
  assumes "is_semialgebraic m a"
  assumes "a \<noteq> {}"
  shows "poly_unit_replacement m f a i = (to_fun_unit m (f i))"
proof- 
  have "\<not> (\<forall>x\<in>a \<inter> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x = \<zero>)"
    using assms is_semialgebraic_closed by blast 
  thus ?thesis 
    unfolding poly_unit_replacement_def by auto 
qed

lemma poly_unit_replacement_on_cfs_part:
  assumes "is_semialgebraic m A"
  assumes "f \<in> carrier (UP (SA m))"
  assumes "a \<in> poly_cfs_part m f A"
  shows "poly_unit_replacement m f a \<in> carrier (UP (SA m))"
        "\<And>x. x \<in> a \<Longrightarrow> poly_unit_replacement m f a i x = f i x"
        "\<And>x. x \<in> a \<Longrightarrow> SA_poly_to_Qp_poly m x f = 
                            SA_poly_to_Qp_poly m x (poly_unit_replacement m f a)"
proof- 
  have a_closed: "a \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms poly_cfs_part_subset is_semialgebraic_closed by blast 
  have a_nonempty: "a \<noteq> {}"
    using assms unfolding poly_cfs_part_def by auto 
  show 1: "poly_unit_replacement m f a \<in> carrier (UP (SA m))"
    using assms by (simp add: poly_unit_replacement_closed)
  show 2: "\<And>x i. x \<in> a \<Longrightarrow> poly_unit_replacement m f a i x = f i x"
  proof- fix x i assume A: "x \<in> a"
    show "poly_unit_replacement m f a i x = f i x"
    proof(cases "(\<forall> x \<in> a. f i x = \<zero>)")
      case True
      show ?thesis 
        using a_closed assms A True poly_unit_replacement_def SA_zeroE 
        by (simp add: Set.basic_monos(7))
    next
      case False
      hence "(\<forall> x \<in> a. f i x \<noteq> \<zero>)"
        using assms  by (meson poly_cfs_part_memE)
      have "\<not> (\<forall> x \<in> a \<inter> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f i x = \<zero>)"
        using a_nonempty a_closed by (simp add: False Int_absorb2)
      hence "poly_unit_replacement m f a i = to_fun_unit m (f i)"
        unfolding poly_unit_replacement_def by  auto 
      then show ?thesis 
        using a_closed assms poly_unit_replacement_cfs2 to_fun_unit_eq[of "f i" m]
              A UPSA.UP_car_memE(1) \<open>\<forall>x\<in>a. f i x \<noteq> \<zero>\<close> by auto
    qed
  qed
  show 3: "\<And>x. x \<in> a \<Longrightarrow> SA_poly_to_Qp_poly m x f = 
                            SA_poly_to_Qp_poly m x (poly_unit_replacement m f a)"
  proof- 
    fix x assume A: "x \<in> a"
    show "SA_poly_to_Qp_poly m x f = 
                            SA_poly_to_Qp_poly m x (poly_unit_replacement m f a)"
    proof(rule ext) fix j 
      have 30: "SA_poly_to_Qp_poly m x f j = f j x"
        using SA_poly_to_Qp_poly_coeff[of _ m f j] A assms(2) local.a_closed 
        by auto
      have 31: "SA_poly_to_Qp_poly m x (poly_unit_replacement m f a) j =  
                        (poly_unit_replacement m f a) j x"
        using a_closed assms 1 2 SA_poly_to_Qp_poly_coeff[of _ m f j] A
                  SA_poly_to_Qp_poly_coeff[of _ m "poly_unit_replacement m f a" j] 
        by blast
      show "SA_poly_to_Qp_poly m x f j = 
                            SA_poly_to_Qp_poly m x (poly_unit_replacement m f a) j"
        unfolding 30 31 using 1 2[of x j] A  by auto 
    qed
  qed
qed

lemma(in UP_cring) taylor_expansion_inv:
  assumes "f \<in> carrier (UP R)"
  assumes "c \<in> carrier R"
  shows "f = taylor_expansion R (\<ominus>c) (taylor_expansion R c f)"
        "f = taylor_expansion R c (taylor_expansion R (\<ominus>c) f)"
proof-
  have 0: "\<And> c. c \<in> carrier R \<Longrightarrow> f = taylor_expansion R (\<ominus>c) (taylor_expansion R c f)"
  proof-
    fix x c assume A: "c \<in> carrier R"
    have 0: "X_poly_minus R c = X_poly_plus R (\<ominus> c)"
      by (simp add: A UP_cring.X_minus_plus assms(2) is_UP_cring)
    have 1: "f = Cring_Poly.compose R (taylor c f) (X_poly_minus R c)"
      using A taylor_id[of c f] assms P_def by fastforce
    show "f = taylor_expansion R (\<ominus>c) (taylor_expansion R c f)"
      using 1 0 A
      unfolding taylor_expansion_def taylor_def by auto 
  qed
  show "f = taylor_expansion R (\<ominus>c) (taylor_expansion R c f)"
    by(intro 0 assms)
  show "f = taylor_expansion R c (taylor_expansion R (\<ominus>c) f)"
    using 0[of "\<ominus> c"] assms by auto 
qed

lemma(in UP_cring) taylor_expansion_closed:
  assumes "f \<in> carrier (UP R)"
  assumes "c \<in> carrier R"
  shows "taylor_expansion R c f \<in> carrier (UP R)"
  using assms taylor_closed[of f c]
    unfolding P_def taylor_def by auto   

lemma poly_unit_replacement_deg_lemma:
  assumes "is_semialgebraic m A"
  assumes "f \<in> carrier (UP (SA m))" 
  assumes "c \<in> carrier (SA m)"
  assumes "a \<in> poly_cfs_part m (taylor_expansion (SA m) c f) A"
  assumes "g = taylor_expansion (SA m) (\<ominus>\<^bsub>SA m\<^esub> c) 
                    (poly_unit_replacement m (taylor_expansion (SA m) c f) a)"
  shows "deg (SA m) g \<le> deg (SA m) f"
proof- 
  have 0: "deg (SA m) f = deg (SA m) (taylor_expansion (SA m) c f)"
    using assms UPSA.taylor_def UPSA.taylor_deg by presburger
  have 1: "deg (SA m) f \<ge> deg (SA m) (poly_unit_replacement m (taylor_expansion (SA m) c f) a)"
    unfolding 0 using assms 
    by (meson UPSA.taylor_expansion_closed poly_unit_replacement_deg)
  thus ?thesis 
    unfolding assms using  1 assms UPSA.taylor_deg UPSA.taylor_def UPSA.taylor_deg unfolding  UPSA.taylor_def
  using R.cring_simprules(3) UPSA.taylor_expansion_closed padic_fields.poly_unit_replacement_closed padic_fields_axioms by presburger
qed

lemma poly_unit_replacement_on_cfs_part_taylor:
  assumes "is_semialgebraic m A"
  assumes "f \<in> carrier (UP (SA m))" 
  assumes "c \<in> carrier (SA m)"
  assumes "a \<in> poly_cfs_part m (taylor_expansion (SA m) c f) A"
  assumes "g = taylor_expansion (SA m) (\<ominus>\<^bsub>SA m\<^esub> c) 
                    (poly_unit_replacement m (taylor_expansion (SA m) c f) a)"
  shows "g \<in> carrier (UP (SA m))"
        "\<And>x i . x \<in> a \<Longrightarrow> g i x = f i x"
        "\<And> x i. x \<in> a \<Longrightarrow> UPSA.pderiv m g i x = UPSA.pderiv m f i x"
        "\<And>x. x \<in> a \<Longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
        "\<And>x. x \<in> a \<Longrightarrow> SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = 
                        SA_poly_to_Qp_poly m x (UPSA.pderiv m f)"
        "\<And> i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or>
               taylor_expansion (SA m) c g i \<in> Units (SA m)"
proof- 
  obtain h where h_def: "h = (poly_unit_replacement m (taylor_expansion (SA m) c f) a)"
    by blast 
  show g_closed: "g \<in> carrier (UP (SA m))"
    unfolding assms apply(intro taylor_expansion_closed poly_unit_replacement_closed)
    using assms by auto 
  have taylor: "taylor_expansion (SA m) c f \<in> carrier (UP (SA m))"
    using assms UPSA.taylor_closed UPSA.taylor_def by force 
  have a_sub: "a \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms poly_cfs_part_subset[of a m "taylor_expansion (SA m) c f" A] taylor 
            is_semialgebraic_closed  by auto 
  have h_props: "h \<in> carrier (UP (SA m))"
                "\<And>x i. x \<in> a \<Longrightarrow> h i x = taylor_expansion (SA m) c f i x"
                "\<And>x i. x \<in> a \<Longrightarrow> SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f) = 
                            SA_poly_to_Qp_poly m x h"
  proof- 
    show "h \<in> carrier (UP (SA m))"
      unfolding h_def
      by(intro poly_unit_replacement_on_cfs_part[of m A "taylor_expansion (SA m) c f" a] 
          taylor assms)
    show " \<And>x i. x \<in> a \<Longrightarrow> h i x = taylor_expansion (SA m) c f i x"
      unfolding h_def
      by(intro poly_unit_replacement_on_cfs_part[of m A "taylor_expansion (SA m) c f" a] 
          taylor assms, auto)
    show "\<And>x i. x \<in> a \<Longrightarrow> SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f) = SA_poly_to_Qp_poly m x h"
      unfolding h_def
      by(intro poly_unit_replacement_on_cfs_part[of m A "taylor_expansion (SA m) c f" a] 
          taylor assms, auto)
  qed
  show 1: "\<And>x. x \<in> a \<Longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
  proof- fix x assume A: "x \<in> a"
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using a_sub A by auto 
    have 0: "SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f) = 
                            SA_poly_to_Qp_poly m x h"
      using h_props A by auto 
    have 1: "f = taylor_expansion (SA m) (\<ominus>\<^bsub>SA m\<^esub> c) (taylor_expansion (SA m) c f)"
      by(intro taylor_expansion_inv assms)
    have 2: "SA_poly_to_Qp_poly m x 
                  (taylor_expansion (SA m) (\<ominus>\<^bsub>SA m\<^esub> c) (taylor_expansion (SA m) c f)) = 
              taylor_expansion Q\<^sub>p ((\<ominus>\<^bsub>SA m\<^esub> c) x) (SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f))"
      apply(intro SA_poly_to_Qp_poly_taylor_poly taylor)
      using assms apply auto[1]
      using a_sub A by auto  
    hence 3: "SA_poly_to_Qp_poly m x f =  taylor_expansion Q\<^sub>p ((\<ominus>\<^bsub>SA m\<^esub> c) x) (SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f))"
      using 1 by auto 
    have 4: "SA_poly_to_Qp_poly m x g = taylor_expansion Q\<^sub>p ((\<ominus>\<^bsub>SA m\<^esub> c) x)  (SA_poly_to_Qp_poly m x
     (poly_unit_replacement m (taylor_expansion (SA m) c f) a))"
      unfolding assms 
      apply(intro SA_poly_to_Qp_poly_taylor_poly x_closed)
      using h_props assms unfolding h_def by auto 
    have 5: " (SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f)) =  (SA_poly_to_Qp_poly m x
     (poly_unit_replacement m (taylor_expansion (SA m) c f) a))"
      using A h_props h_def by auto 
    show "SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f "
      unfolding 3 4 5 by auto 
  qed
  show 2: "\<And>x i. x \<in> a \<Longrightarrow> g i x = f i x"
  proof- fix i x assume A: "x \<in> a"
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using a_sub by auto 
    show "g i x = f i x"
      using 1[of x] g_closed assms(2) x_closed A
             SA_poly_to_Qp_poly_coeff[of x m f i]
            SA_poly_to_Qp_poly_coeff[of x m g i] 
      by auto 
  qed
  have h_eq: "h = taylor_expansion (SA m) c g"
    unfolding h_def assms apply(rule taylor_expansion_inv)
    using assms h_props h_def by auto 
  show "\<And>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or> taylor_expansion (SA m) c g i \<in> Units (SA m)"
    using assms taylor_closed h_def h_eq poly_cfs_part_semialg
          poly_unit_replacement_dichotomy padic_fields_axioms taylor by presburger
  have derivs_closed: "UPSA.pderiv m g \<in> carrier (UP (SA m))"
                      "UPSA.pderiv m f \<in> carrier (UP (SA m))"
    by(auto simp:  UPSA.pderiv_closed g_closed assms(2))
  show 3: "\<And>x i. x \<in> a \<Longrightarrow> UPSA.pderiv m g i x = UPSA.pderiv m f i x"
  proof- fix i x assume A: "x \<in> a"
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using a_sub by auto 
    have p: "g (Suc i) x = f (Suc i) x"
      by(intro A 2)
    have q: "UPSA.pderiv m g i = [Suc i] \<cdot>\<^bsub>SA m\<^esub> g (Suc i)"
            "UPSA.pderiv m f i = [Suc i] \<cdot>\<^bsub>SA m\<^esub> f (Suc i)"
      using  g_closed assms(2) x_closed A derivs_closed 
            UPSA.pderiv_cfs[of g m i] UPSA.pderiv_cfs[of f m i]  by auto 
    have r: "([Suc i] \<cdot>\<^bsub>SA m\<^esub> g (Suc i)) x = [Suc i] \<cdot> g (Suc i) x"
            "([Suc i] \<cdot>\<^bsub>SA m\<^esub> f (Suc i)) x = [Suc i] \<cdot> f (Suc i) x"
      using p x_closed cfs_closed[of f m "Suc i"] SA_add_pow_apply[of "g (Suc i)" m x "Suc i"]
            cfs_closed[of g m "Suc i"] SA_add_pow_apply[of "f (Suc i)" m x "Suc i"] 
            g_closed assms by auto 
    show "UPSA.pderiv m g i x = UPSA.pderiv m f i x"
      unfolding p q r by auto 
  qed
  show "\<And>x. x \<in> a \<Longrightarrow>
               SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = SA_poly_to_Qp_poly m x (UPSA.pderiv m f)"
  proof fix x i
    assume A: "x \<in> a"
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using a_sub by auto 
    have p: "UPSA.pderiv m g i x = UPSA.pderiv m f i x"
      using A 3 by auto 
    show "SA_poly_to_Qp_poly m x (UPSA.pderiv m g) i =
             SA_poly_to_Qp_poly m x (UPSA.pderiv m f) i"
      using SA_poly_to_Qp_poly_coeff[of x m "UPSA.pderiv m g" i]
            SA_poly_to_Qp_poly_coeff[of x m "UPSA.pderiv m f" i] 
            derivs_closed x_closed
      unfolding p by auto 
  qed
qed

definition decomp_by_cfs where 
"decomp_by_cfs m f \<C> = (\<lambda> C. refine_fibres \<C> C) ` poly_cfs_part m f (fibre_set \<C>)"

lemma decomp_by_cfs_is_decomp:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "is_cell_condition \<C>"
  assumes "arity \<C> = m"
  shows "is_cell_decomp m (decomp_by_cfs m f \<C>) (condition_to_set \<C>)"
proof- 
  obtain C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using assms arity.simps by (meson equal_CondI)
  have C_semialg: "is_semialgebraic m C"
    using assms params is_cell_conditionE by smt 
  have C_closed: "C \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using C_semialg is_semialgebraic_closed by auto 
  have sa: "\<And> x. x \<in> poly_cfs_part m f C \<Longrightarrow> is_semialgebraic m x"
    by(rule poly_cfs_part_semialg[of _ C f], intro C_semialg, rule assms, auto)
  show ?thesis
    unfolding decomp_by_cfs_def 
    apply(intro partition_to_cell_decomp[of \<C> m C c a1 a2 I] assms params)
    unfolding params fibre_set.simps 
      apply(intro poly_cfs_part_partitions C_closed)
    unfolding are_semialgebraic_def using sa apply blast
    by(rule poly_cfs_part_finite)
qed

lemma decomp_by_cfs_params:
  assumes "\<B> \<in> (decomp_by_cfs m f (Cond m C c a1 a2 I))"
  shows "center \<B> = c"
        "l_bound \<B> = a1"
        "u_bound \<B> = a2"
        "boundary_condition \<B> = I"
  using assms unfolding decomp_by_cfs_def refine_fibres_def by auto 
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Cell Decomposition Properties are Hereditary (up to Common Centers)\<close>
(**************************************************************************************************)
(**************************************************************************************************)
context common_decomp_proof_context
begin

lemma SA_poly_ubounded_mono:
  assumes "SA_poly_ubounded p m f c A N"
  assumes "B \<subseteq> A"
  shows "SA_poly_ubounded p m f c B N"
  using assms 
proof -
  have f1: "\<forall>R Ra rs. (\<not> R \<subseteq> Ra \<or> (rs::((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list) \<notin> R) \<or> rs \<in> Ra"
    by blast
  have f2: "A \<subseteq> carrier (Frac (padic_int p)\<^bsup>Suc m\<^esup>)"
    by (meson SA_poly_ubounded.A_closed assms(1))
  have "\<forall>i n f fa R ia. SA_poly_ubounded_axioms i n f fa R ia = (f \<in> carrier (UP (padic_fields.SA i n)) \<and> fa \<in> carrier (padic_fields.SA i n) \<and> R \<subseteq> carrier (Frac (padic_int i)\<^bsup>Suc n\<^esup>) \<and> (\<forall>na rs r. r # rs \<notin> R \<or> padic_fields.val i (UP_cring.to_fun (Frac (padic_int i)) (padic_fields.SA_poly_to_Qp_poly i n rs f) r) \<le> padic_fields.val i (UP_cring.to_fun (Frac (padic_int i)) (UP_cring.taylor_term (Frac (padic_int i)) (fa rs) (padic_fields.SA_poly_to_Qp_poly i n rs f) na) r) + eint ia))"
    using SA_poly_ubounded_axioms_def by presburger
  then have "SA_poly_ubounded_axioms p m f c B N"
    using f2 f1 SA_poly_ubounded.P_closed SA_poly_ubounded.c_closed SA_poly_ubounded.ubounded assms(1) assms(2) by force
  then show ?thesis
    by (simp add: SA_poly_ubounded.intro padic_fields_axioms)
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Reducing the Proof to the Sets $A_0$ and its Complement\<close>
(**************************************************************************************************)
(**************************************************************************************************)
context common_refinement_locale
begin

lemma \<C>_memE: 
  assumes "x \<in> condition_to_set \<C>"
  shows "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        "hd x \<in> carrier Q\<^sub>p"
        "tl x \<in> A"
  using assms  unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq
    apply (meson cartesian_power_tail)
  apply (metis Qp_pow_ConsE(2) assms cell_condition_set_memE(1) common_refinement_locale.\<C>_cond common_refinement_locale.\<C>_def common_refinement_locale_axioms)
  using \<C>_cond \<C>_def assms condition_to_set_memE(1) by presburger

lemma c_closed: "c \<in> carrier (SA m)"
  using \<C>_cond is_cell_conditionE(2) unfolding \<C>_def 
  by blast

lemma a1_closed: "a1 \<in> carrier (SA m)"
  using \<C>_cond unfolding \<C>_def 
  by fastforce

lemma a2_closed: "a2 \<in> carrier (SA m)"
  using \<C>_cond unfolding \<C>_def 
  by (meson is_cell_conditionE''(7))

lemma A_semialg: "is_semialgebraic m A"
  using \<C>_cond unfolding \<C>_def 
  by simp

text\<open>For the sake of matching the text and brevity, we give a name to the taylor coefficients of f 
     expanded at c.\<close>
definition a where
"a = taylor_expansion (SA m) c f"

lemma a_closed: 
"a \<in> carrier (UP (SA m))"
  unfolding a_def 
  by (metis c_closed UPSA.taylor_def UP_cring.taylor_closed UP_cring_def f_closed padic_fields.SA_is_cring padic_fields_axioms)

lemma a_cfs_closed: "a i \<in> carrier (SA m)"
  by (meson UPSA.UP_car_memE(1) local.a_closed)

lemma a_deg: 
"deg (SA m) a = deg (SA m) f"
  unfolding a_def 
  using c_closed UPSA.taylor_def UPSA.taylor_deg  f_closed by force

lemma a_eval: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "a i x \<in> carrier Q\<^sub>p"
by(intro SA_car_closed[of _ m] a_cfs_closed assms)

text\<open>The set of indices for the nonzero taylor coefficients:\<close>
definition inds where 
"inds = {i. a i \<in> Units (SA m) }"

lemma inds_bounded:
"i \<in> inds \<Longrightarrow> i \<le> deg (SA m) f"
  unfolding inds_def mem_Collect_eq
  by (metis SA_units_not_zero UPSA.deg_eqI a_deg le_cases local.a_closed)

lemma inds_bounded':
"i \<in> inds \<Longrightarrow> i \<le> Suc d"
  by (meson f_deg inds_bounded le_trans)

lemma inds_finite:
  "finite inds"
  by (meson finite_nat_set_iff_bounded_le inds_bounded)

lemma inds_memE:
"i \<in> inds \<Longrightarrow> a i \<in> Units (SA m)"
  using inds_def by blast

lemma inds_non_memE:
"i \<notin> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> a i x = \<zero>"
  by (metis SA_zeroE a_def f_taylor_cfs inds_def mem_Collect_eq)

definition ind_pairs where
"ind_pairs = {(i, j) \<in> inds \<times> inds. i \<noteq> j}"

lemma finite_ind_pairs: "finite (ind_pairs)"
  apply(rule finite_subset[of ind_pairs "inds \<times>inds"])
  unfolding ind_pairs_def apply blast 
  using inds_finite by blast 

lemma a_quotient_closed: 
"\<And>i j. i \<in> inds \<Longrightarrow> j \<in> inds \<Longrightarrow>  (a j) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> (a i) \<in> carrier (SA m)"
using inds_memE by blast

lemma a_quotient_unit: "\<And>i j. i \<in> inds \<Longrightarrow> j \<in> inds \<Longrightarrow> (a j) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> (a i) \<in> Units (SA m)"
using inds_memE  by blast

lemma f_eval_formula: "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> t \<in> carrier Q\<^sub>p \<Longrightarrow> 
                      SA_poly_to_SA_fun m f (t#x) = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
proof-
  fix x t assume a: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p"
  have 0: "SA_poly_to_SA_fun m f (t#x) = (\<Oplus>i\<in>{..deg (SA m) f}. (a i (tl (t#x)))\<otimes>(hd (t#x) \<ominus> c (tl (t#x)))[^]i)"
    unfolding a_def
    apply(rule SA_poly_to_SA_fun_taylor_expansion)
      apply (simp add: f_closed)
     apply (simp add: c_closed)
    by (simp add: Qp_pow_ConsI a(1) a(2))
  show "SA_poly_to_SA_fun m f (t # x) = (\<Oplus>i\<in>inds. a i x \<otimes> (t \<ominus> c x) [^] i)" 
    unfolding 0 list_tl list_hd apply(rule Qp.finsum_mono_neutral_cong)
       apply(rule , intro Qp.ring_simprules Qp.nat_pow_closed a  SA_car_closed[of _ m] a_cfs_closed c_closed, simp)
    using inds_non_memE Qp.l_null Qp.minus_closed Qp.nat_pow_closed SA_car_closed a(1) a(2) c_closed apply presburger
    by (simp add: inds_bounded subset_eq)
qed    

lemma \<C>_mem_tl:
"\<And> x. x \<in> condition_to_set \<C> \<Longrightarrow> tl x \<in>A"
  by (metis cell_memE(2) condition_to_set.simps common_refinement_locale.\<C>_def common_refinement_locale_axioms)

lemma \<C>_mem_hd:
"\<And> x. x \<in> condition_to_set \<C> \<Longrightarrow> hd x \<in> carrier Q\<^sub>p"
  by (metis Qp_pow_ConsE(2) \<C>_def cell_condition_set_memE(1) common_refinement_locale.\<C>_cond common_refinement_locale_axioms)

lemma f_eval_formula': "\<And>x. x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_SA_fun m f x = (\<Oplus>i\<in>inds. (a i (tl x))\<otimes>((hd x) \<ominus> c (tl x))[^]i)"
proof- 
  fix x assume A: "x \<in> condition_to_set \<C>"
  have 0: "x = hd x # tl x"
    using A 
    by (metis \<C>_def cartesian_power_car_memE cell_memE(1) condition_to_set.simps list.exhaust_sel list.size(3) nat.simps(3))
  have " SA_poly_to_SA_fun m f (hd x # tl x) = (\<Oplus>i\<in>inds. (a i (tl x))\<otimes>((hd x) \<ominus> c (tl x))[^]i)"
    apply(rule f_eval_formula)
    using A unfolding \<C>_def  
    apply (simp add: cartesian_power_tail cell_memE(1))
    by (simp add: A \<C>_mem_hd)
  thus " SA_poly_to_SA_fun m f x = (\<Oplus>i\<in>inds. a i (tl x) \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] i)"
    using 0 by auto 
qed

end


locale one_val_point_decomp = common_refinement_locale + 
  fixes B\<^sub>0 Ls As Fs
  assumes subset: "B\<^sub>0 \<subseteq> condition_to_set \<C>"
  assumes Ls_finite: "finite Ls"
  assumes nonempty: "Ls \<noteq> {}"
  assumes semialg: "\<And>l. l \<in> Ls \<Longrightarrow> Fs l \<in> carrier (SA m)"
  assumes semialg_fibres: "\<And> l. l \<in> Ls \<Longrightarrow> is_semialgebraic m (As l)"
  assumes covers: "B\<^sub>0 = (\<Union>l \<in> Ls. condition_to_set (Cond m (As l) c (Fs l) (Fs l) closed_interval))"

context one_val_point_decomp
begin

lemma is_cell:
"l \<in> Ls \<Longrightarrow> is_cell_condition  (Cond m (As l) c (Fs l) (Fs l) closed_interval)"
  apply(rule is_cell_conditionI')
  using semialg_fibres c_closed semialg is_convex_condition_def by auto

lemma one_val_point_decomposable:
 "one_val_point_c_decomposable m c (Fs ` Ls) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))
       (\<Union>l \<in> Ls. condition_to_set (Cond m (As l) c (Fs l) (Fs l) closed_interval))"
    apply(rule finite_union_one_val_point_c_decomposable)
  using c_closed apply blast
  using Ls_finite apply blast 
  using nonempty apply blast
  using semialg apply blast
  proof(rule subsetI)
    fix x assume A: "x \<in> (\<lambda>l. condition_to_set (Cond m (As l) c (Fs l) (Fs l) closed_interval)) ` Ls"
    then obtain l where l_def: "l \<in> Ls" "x = condition_to_set (Cond m (As l) c (Fs l) (Fs l) closed_interval)"
      by blast
    have 00: "Cond m (As l) c (Fs l) (Fs l) closed_interval \<in>  c_cells_at_one_val_point m c (Fs ` Ls) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
      unfolding c_cells_at_one_val_point_def mem_Collect_eq condition_to_set.simps
        arity.simps center.simps u_bound.simps l_bound.simps boundary_condition.simps cell_def 
      using is_cell l_def by auto 
    thus "x \<in> condition_to_set ` c_cells_at_one_val_point m c (Fs ` Ls) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
      using l_def by blast
  qed

definition first_decomp where 
"first_decomp = (SOME S'. S' \<noteq> {} \<and> 
            is_cell_decomp m S' B\<^sub>0 \<and>
             S' \<subseteq> c_cells_at_one_val_point m c (Fs ` Ls) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)))"

lemma first_decomp_prop:
"first_decomp \<noteq> {} \<and> 
            is_cell_decomp m first_decomp B\<^sub>0 \<and>
             first_decomp \<subseteq> c_cells_at_one_val_point m c (Fs ` Ls) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
proof-
  obtain S' where S'_def: "S' \<noteq> {} \<and> 
            is_cell_decomp m S' B\<^sub>0 \<and>
             S' \<subseteq> c_cells_at_one_val_point m c (Fs ` Ls) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
    using one_val_point_decomposable nonempty semialg 
          one_val_point_c_decomposable_nonempty[of c m "(Fs ` Ls)"  "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
                                  B\<^sub>0]
          c_closed unfolding covers  by blast 
  show ?thesis unfolding first_decomp_def using S'_def SomeE by smt 
qed

lemma bounds: 
  assumes "C \<in> first_decomp"
  shows "u_bound C \<in> Fs ` Ls"
  using first_decomp_prop assms
  unfolding c_cells_at_one_val_point_def by auto 

lemma decomp:
"\<exists>S'. (is_cell_decomp m S' B\<^sub>0 \<and>
         (\<forall>B\<in>S'. (\<exists> \<phi>. \<phi> \<in> (Fs ` Ls) \<and>
             center B = c \<and> l_bound B = \<phi> \<and> u_bound B = \<phi> \<and>
             boundary_condition B = closed_interval)))"
  using first_decomp_prop unfolding c_cells_at_one_val_point_def 
  by (smt (verit, best) in_mono mem_Collect_eq)

end

context common_refinement_locale
begin


text\<open>This is just the set that denef also calls $A_0$. The proof proceeds by showing that both $A_0$ and its complement can be decomposed as desired.\<close>
definition A\<^sub>0 where 
"A\<^sub>0  = {x \<in> condition_to_set \<C>. (\<forall> i \<in> inds. (\<forall> j \<in> inds. i < j \<longrightarrow> val (a i (tl x))  \<noteq> val (a j (tl x) \<otimes> (hd x \<ominus> c (tl x))[^](j- i))))}"

lemma A\<^sub>0_closed: "A\<^sub>0 \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
unfolding A\<^sub>0_def using condition_to_set.simps[of m A c a1 a2 I] unfolding \<C>_def  cell_def 
  by blast 

definition ordered_ind_pairs where
"ordered_ind_pairs = {(i,j) \<in> ind_pairs. i < j}"

lemma ordered_ind_pairs_unit:
  assumes "i \<in> inds"
  assumes "j \<in> inds"
  assumes "i < j"
  shows "\<exists>\<eta>\<in>Units (SA m).  \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>).
          (int j - int i) * ord (\<eta> x) + ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - int i) =
                  ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) "
proof- 
  have 0: "(int j - int i) = int (j - i)"
    using assms by auto 
  show ?thesis 
    unfolding 0 
  apply(rule denef_lemma_2_4_floor[of d])
  apply (simp add: denef_II_axioms)
  apply (simp add: Suc_leI assms(3))
  using assms(2) diff_le_self inds_bounded' order.trans apply blast
  using a_quotient_unit assms(1) assms(2) by presburger
qed

lemma ordered_ind_pairs_unit':
 "\<And>ps. ps \<in> ordered_ind_pairs \<Longrightarrow> 
      \<exists>\<phi> \<in> Units (SA m). 
          (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (int (snd ps) - int (fst ps))*ord (\<phi> x)
                              +  ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x) 
                                                                    mod (int (snd ps) - int (fst ps))
                                = ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x))"
proof- 
  fix ps assume A: "ps \<in> ordered_ind_pairs"
  obtain i j where ij_def: "ps = (i,j)"
    using A unfolding ordered_ind_pairs_def mem_Collect_eq by auto 
  have i_closed: "i \<in> inds"
    using A unfolding ij_def mem_Collect_eq ordered_ind_pairs_def ind_pairs_def by auto 
  have j_closed: "j \<in> inds"
    using A unfolding ij_def mem_Collect_eq ordered_ind_pairs_def ind_pairs_def by auto 
  have le: "i < j"
    using A unfolding ij_def mem_Collect_eq ordered_ind_pairs_def ind_pairs_def by auto 
  show "\<exists>\<phi> \<in> Units (SA m).
          (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (int (snd ps) - int (fst ps))*ord (\<phi> x)
                              +  ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x) mod (int (snd ps) - (fst ps))
                                = ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x))"
    unfolding ij_def fst_conv snd_conv 
    by(intro ordered_ind_pairs_unit i_closed  j_closed le) 
qed

lemma ordered_ind_pairs_memE: 
  assumes "ps \<in> ordered_ind_pairs"
  shows "fst ps \<in> inds"
        "snd ps \<in> inds"
        "fst ps < snd ps"
  using assms unfolding ordered_ind_pairs_def ind_pairs_def mem_Collect_eq by auto 

lemma ordered_ind_pairs_finite: 
"finite ordered_ind_pairs"
  unfolding ordered_ind_pairs_def ind_pairs_def using inds_finite 
  by (metis (no_types, lifting) Collect_case_prod_mono case_prodD finite_ind_pairs ind_pairs_def 
      mem_Collect_eq predicate2I rev_finite_subset)

lemma semialg_ineq_set:
  assumes "(i,j) \<in> ordered_ind_pairs"
  assumes "F =  {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). val (a i (tl x))  \<noteq> 
                                        val (a j (tl x) \<otimes> (hd x \<ominus> c (tl x))[^](j- i))}"
  shows "is_semialgebraic (Suc m) F"
proof- 
  have i_in: "i \<in> inds"
    using assms ordered_ind_pairs_def ind_pairs_def by force
  have j_in: "j \<in>inds"
    using assms  ordered_ind_pairs_def ind_pairs_def by force
  have i_leq_j: "i < j"
    using assms  unfolding ordered_ind_pairs_def by blast 
  obtain Ai where Ai_def: "Ai = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). a i (tl x))"
    by blast 
  obtain Aj where Aj_def: "Aj = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). a j (tl x))"
    by blast
  obtain C where C_def: "C = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). c (tl x))"
    by blast 
  obtain Hd where Hd_def: "Hd = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). hd x)"
    by blast 
  have Hd_closed: "Hd \<in> carrier (SA (Suc m))"
    using hd_is_semialg_function[of "Suc m"]
    unfolding Hd_def using restrict_in_SA_car by blast
  have Ai_closed: "Ai \<in> carrier (SA (Suc m))"
    unfolding Ai_def  apply(rule  tl_comp_in_SA)
    using a_cfs_closed by blast  
  have Aj_closed: "Aj \<in> carrier (SA (Suc m))"
    unfolding Aj_def  apply(rule  tl_comp_in_SA)
    using a_cfs_closed by blast  
  have C_closed: "C \<in> carrier (SA (Suc m))"
    unfolding C_def apply(rule  tl_comp_in_SA)
    using c_closed by blast
  obtain G where G_def: "G = Aj \<otimes>\<^bsub>SA (Suc m)\<^esub> (Hd \<ominus>\<^bsub>SA (Suc m)\<^esub> C)[^]\<^bsub>SA (Suc m)\<^esub>(j-i)"
    by blast 
  have G_closed: "G \<in> carrier (SA (Suc m))"
    unfolding G_def by(rule R.ring_simprules, rule Aj_closed, rule R.nat_pow_closed, 
                    rule R.minus_closed, rule Hd_closed, rule C_closed)
  have G_eval_1: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> G x =  (Aj x \<otimes> (Hd x \<ominus> C x)[^](j- i))"
    unfolding G_def using Aj_closed Hd_closed C_closed SA_minus_eval SA_mult SA_nat_pow by presburger
  have G_eval_2: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> G x =  (a j (tl x) \<otimes> (hd x \<ominus> c (tl x))[^](j- i))"
    using G_eval_1  restrict_apply unfolding Aj_def Hd_def C_def by (smt restrict_apply)
  have 2: "F = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). val (Ai x) \<noteq> val (G x)}"
    apply(rule equalityI')
    unfolding assms mem_Collect_eq apply(rule conjI, blast)
  proof- 
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> val (a i (tl x)) \<noteq> val (a j (tl x) \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] (j - i))"
    have 00: "Ai x = a i (tl x)"
      using A restrict_apply unfolding Ai_def by metis 
    show "val (Ai x) \<noteq> val (G x)"
      unfolding 00 using G_eval_2[of x] A by smt 
  next
    show "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> val (Ai x) \<noteq> val (G x) \<Longrightarrow>
 x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> val (a i (tl x)) \<noteq> val (a j (tl x) \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] (j - i))"
      apply(rule conjI, blast)
    proof-
      fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> val (Ai x) \<noteq> val (G x)"
      have 00: "Ai x = a i (tl x)"
        unfolding Ai_def using A restrict_apply by smt 
      have 01: " G x =  (a j (tl x) \<otimes> (hd x \<ominus> c (tl x))[^](j- i))"
        apply(rule G_eval_2) using A by blast
      show "val (a i (tl x)) \<noteq> val (a j (tl x) \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] (j - i))"
        using A unfolding 00 01 by blast 
    qed
  qed
  have 3: "F = carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). val (Ai x) = val (G x)}"
    unfolding 2 by blast 
  show "is_semialgebraic (Suc m) F"
    unfolding 3 apply(rule diff_is_semialgebraic, rule carrier_is_semialgebraic)
    by(rule semialg_val_eq_set_is_semialg, rule Ai_closed, rule G_closed)
qed

definition term_ineq_set where
"term_ineq_set ps = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). val (a (fst ps) (tl x))  \<noteq> 
                                val (a (snd ps) (tl x) \<otimes> (hd x \<ominus> c (tl x))[^]((snd ps)- (fst ps)))}"

lemma term_ineq_set_semialg: 
  assumes "ps \<in> ordered_ind_pairs"
  shows "is_semialgebraic (Suc m) (term_ineq_set ps)"
proof-
  obtain i j where ij_def: "i \<in> inds \<and> j \<in> inds \<and> i< j" "ps = (i,j)"
    using assms unfolding ordered_ind_pairs_def ind_pairs_def by blast 
  show ?thesis 
    using semialg_ineq_set[of i j "term_ineq_set ps"] assms ij_def 
    unfolding ij_def ordered_ind_pairs_def term_ineq_set_def fst_conv snd_conv
    by auto 
qed

lemma A\<^sub>0_as_intersection: "A\<^sub>0 = condition_to_set \<C> \<inter> \<Inter> (term_ineq_set ` ordered_ind_pairs)"
proof(rule equalityI')
  show "\<And>x. x \<in> A\<^sub>0 \<Longrightarrow> x \<in> condition_to_set \<C> \<inter> \<Inter> (term_ineq_set ` ordered_ind_pairs)"
  proof(rule IntI)
    show " \<And>x. x \<in> A\<^sub>0 \<Longrightarrow> x \<in> condition_to_set \<C>"
      unfolding A\<^sub>0_def by blast
    show "\<And>x. x \<in> A\<^sub>0 \<Longrightarrow> x \<in> \<Inter> (term_ineq_set ` ordered_ind_pairs)"
    proof fix x ps assume A: "x \<in> A\<^sub>0" "ps \<in> ordered_ind_pairs"
      obtain i j where ij_def: "i \<in> inds \<and> j \<in> inds \<and> i< j \<and> ps = (i,j)"
        using A(2) unfolding ordered_ind_pairs_def ind_pairs_def by blast 
      have ps_eq: "ps = (i,j)"
        using ij_def by blast 
      have 0: "term_ineq_set ps = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). val (a i (tl x)) \<noteq> val (a j (tl x) \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] (j - i))}"
        unfolding ps_eq term_ineq_set_def by auto 
      show "x \<in> term_ineq_set ps"
        using  A\<^sub>0_closed ij_def unfolding A\<^sub>0_def unfolding 0 mem_Collect_eq
        using A(1) A\<^sub>0_def by blast
    qed
  qed
  show "\<And>x. x \<in> condition_to_set \<C> \<inter> \<Inter> (term_ineq_set ` ordered_ind_pairs) \<Longrightarrow> x \<in> A\<^sub>0"
  proof- fix x assume A: "x \<in> condition_to_set \<C> \<inter>\<Inter> (term_ineq_set ` ordered_ind_pairs)"
    show " x \<in> A\<^sub>0"
      unfolding A\<^sub>0_def mem_Collect_eq 
      apply(rule conjI) using A apply blast
    proof fix i assume i_inds: "i \<in> inds"
      show "\<forall>j\<in>inds. i < j \<longrightarrow> val (a i (tl x)) \<noteq> val (a j (tl x) \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] (j - i))"
      proof fix j assume j_inds: "j \<in> inds"
        show " i < j \<longrightarrow> val (a i (tl x)) \<noteq> val (a j (tl x) \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] (j - i))"
        proof assume le: "i < j"
          have ordered_ind_pairs_el: "(i,j) \<in> ordered_ind_pairs"
            unfolding ordered_ind_pairs_def ind_pairs_def using i_inds j_inds le by blast 
          show "val (a i (tl x)) \<noteq> val (a j (tl x) \<otimes> (lead_coeff x \<ominus> c (tl x)) [^] (j - i))"
            using A ordered_ind_pairs_el fst_conv snd_conv unfolding term_ineq_set_def by auto 
        qed
      qed
    qed
  qed
qed

lemma A\<^sub>0_semialg: "is_semialgebraic (Suc m) A\<^sub>0"
  unfolding A\<^sub>0_as_intersection
  apply(cases "ordered_ind_pairs = {}")
  apply auto[1] apply(intro condition_to_set_is_semialg[of \<C> m] \<C>_cond)
  using  \<C>_def arity.simps apply blast 
    apply(rule intersection_is_semialg, rule condition_to_set_is_semialg, rule \<C>_cond)
    unfolding \<C>_def arity.simps apply blast
    apply(rule finite_intersection_is_semialg, rule ordered_ind_pairs_finite, blast)
    using term_ineq_set_semialg unfolding is_semialgebraic_def by blast

lemma A\<^sub>0_closures: 
  assumes "t#x \<in> A\<^sub>0"
  assumes "i \<in> inds"
  assumes "j \<in> inds"
  shows "a i x \<in> Units Q\<^sub>p" 
        "a j x \<in> Units Q\<^sub>p"
        "t \<ominus> c x \<in> carrier Q\<^sub>p"
        "t \<ominus> c x \<noteq> \<zero> \<Longrightarrow> t \<ominus> c x \<in> Units Q\<^sub>p"
proof- 
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms A\<^sub>0_closed cartesian_power_head by force    
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms A\<^sub>0_closed cartesian_power_tail by fastforce
  show 0: "a i x \<in> Units Q\<^sub>p" 
       "a j x \<in> Units Q\<^sub>p"
       "(t \<ominus> c x) \<in> carrier Q\<^sub>p" 
      unfolding Units_eq_nonzero nonzero_def mem_Collect_eq
      using x_closed inds_memE  SA_Units_memE' a_eval assms  apply auto[1] 
      using x_closed inds_memE  SA_Units_memE' a_eval assms apply auto[1]
      using t_closed x_closed assms Qp.ring_simprules(4) c_closed SA_car_closed by auto[1]
  show "t \<ominus> c x \<noteq> \<zero> \<Longrightarrow> t \<ominus> c x \<in> Units Q\<^sub>p"
    using 0 assms Qp.nonzero_memI Units_eq_nonzero by presburger
qed

lemma A\<^sub>0_memE: 
  assumes "t#x \<in> A\<^sub>0"
  assumes "i \<in> inds"
  assumes "j \<in> inds"
  assumes "i < j"
  assumes "t \<ominus> c x \<noteq> \<zero>"
  shows "val (a i x \<otimes> (t \<ominus> c x)[^]i) \<noteq> val (a j x \<otimes> (t \<ominus> c x)[^]j)"
        "ord (a i x \<otimes> (t \<ominus> c x)[^]i) \<noteq> ord (a j x \<otimes> (t \<ominus> c x)[^]j)"
proof-
  have units: "a i x \<in> Units Q\<^sub>p" 
              "a j x \<in> Units Q\<^sub>p"
              "(t \<ominus> c x) \<in> Units Q\<^sub>p" 
    using assms A\<^sub>0_closures by auto 
  have 0: "val (a i x) \<noteq> val (a j x \<otimes> (t \<ominus> c x) [^] (j - i))"
    using assms unfolding A\<^sub>0_def mem_Collect_eq list_tl list_hd by auto 
  hence 1: "ord (a i x) \<noteq> ord (a j x \<otimes> (t \<ominus> c x) [^] (j - i))"
    using units unfolding val_def 
    by (simp add: Qp.Units_pow_closed Qp.ring_in_Units_imp_not_zero)
  have 2: "ord (a j x \<otimes> (t \<ominus> c x) [^] (j - i)) = ord (a j x) + (int j - int i)* ord (t \<ominus> c x)"
    using units assms Qp.Units_pow_closed Units_eq_nonzero nonzero_nat_pow_ord ord_mult
    by force
  hence 3: "ord (a i x) + int i*ord(t \<ominus> c x) \<noteq> ord (a j x) + int j* ord (t \<ominus> c x)"
    using 1 2 int_distrib(3) by force
  thus "ord (a i x \<otimes> (t \<ominus> c x) [^] i) \<noteq> ord (a j x \<otimes> (t \<ominus> c x) [^] j)"
    using units  Qp.Units_pow_closed Units_eq_nonzero nonzero_nat_pow_ord ord_mult by auto
  thus "val (a i x \<otimes> (t \<ominus> c x) [^] i) \<noteq> val (a j x \<otimes> (t \<ominus> c x) [^] j)"
    unfolding val_def using units by auto
qed

lemma A\<^sub>0_memE': 
  assumes "t#x \<in> A\<^sub>0"
  assumes "i \<in> inds"
  assumes "j \<in> inds"
  assumes "i < j"
  assumes "t \<ominus> c x = \<zero>"
  shows "i = 0 \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x)[^]i) \<noteq> val (a j x \<otimes> (t \<ominus> c x)[^]j)"
        "i > 0 \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x)[^]i) = \<infinity>"
        "val (a j x \<otimes> (t \<ominus> c x)[^]j) = \<infinity>"
proof-
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms A\<^sub>0_closed cartesian_power_head by force    
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms A\<^sub>0_closed cartesian_power_tail by fastforce
  have units: "a i x \<in> Units Q\<^sub>p" 
              "a j x \<in> Units Q\<^sub>p"
    using assms A\<^sub>0_closures by auto 
  show 0: "val (a j x \<otimes> (t \<ominus> c x)[^]j) = \<infinity>"
    using assms units unfolding assms(5) val_def 
    by (simp add: Qp.Units_closed Qp.nat_pow_zero)
  show "i > 0 \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x)[^]i) = \<infinity>"
    using assms units unfolding assms(5) val_def 
    by (simp add: Qp.Units_closed Qp.nat_pow_zero)
  show "i = 0 \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x)[^]i) \<noteq> val (a j x \<otimes> (t \<ominus> c x)[^]j)"
    unfolding 0 using units 
    by (metis (no_types, lifting) Group.nat_pow_0 Qp.Units_not_right_zero_divisor
        Qp.nat_pow_closed Qp.zero_closed Qp.zero_not_one eint.distinct(2) val_def)
qed

text\<open>This lemma formalizes equation (3) from Denef's proof of this result.\<close>
lemma val_f_on_A\<^sub>0: "\<And>x. x \<in> A\<^sub>0 \<Longrightarrow> inds \<noteq> {} \<Longrightarrow> 
                val (SA_poly_to_SA_fun m f x) = (MIN i\<in>inds. (val ( (a i (tl x))\<otimes>((hd x) \<ominus> c (tl x))[^]i)))"
proof- 
  fix xs assume A0: "xs \<in> A\<^sub>0" "inds \<noteq> {} "
  obtain t x where tx_def: "xs = t#x"
    using A0 A\<^sub>0_closed Qp_pow_ConsE 
    by (metis (mono_tags, lifting) Suc_n_not_n cartesian_power_car_memE list.exhaust_sel list.sel(2) subset_iff)
  have t_x_closed: "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using A0 A\<^sub>0_closed Qp_pow_ConsE unfolding tx_def apply force 
    using A0 A\<^sub>0_closed Qp_pow_ConsE unfolding tx_def by force 
  have diff_closed: "t \<ominus> c x \<in> carrier Q\<^sub>p"
    using t_x_closed Qp.ring_simprules c_closed SA_car_closed by auto 
  have 100: "SA_poly_to_SA_fun m f (t#x) = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
    by(rule f_eval_formula, auto simp: t_x_closed)
  have 101: "(\<lambda>i. a i x \<otimes> (t \<ominus> c x) [^] i) \<in> inds \<rightarrow> carrier Q\<^sub>p"
    using diff_closed t_x_closed by (simp add: a_eval)
  show "val (SA_poly_to_SA_fun m f xs) = (MIN i\<in>inds. val (a i (tl xs) \<otimes> (hd xs \<ominus> c (tl xs)) [^] i))"
    unfolding tx_def list_tl list_hd
  proof(cases "(t \<ominus> c x) = \<zero>")
    case True
    have T0: "\<And>i. i \<noteq> 0 \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x) [^] i) = \<infinity>"
      using Qp.nat_pow_zero Qp.r_null True a_eval local.val_zero t_x_closed(2) by presburger
    then have T1: "\<And>i. i \<in> inds \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x) [^] i) \<ge> val (a 0 x \<otimes> (t \<ominus> c x) [^] (0::nat))"
      by (metis basic_trans_rules(20) eint_ord_code(3) notin_closed)
    have T2: "\<And>i. i \<noteq> 0 \<Longrightarrow> a i x \<otimes> (t \<ominus> c x) [^] i = \<zero>"
      using Qp.nat_pow_zero Qp.r_null True a_eval t_x_closed(2) by presburger
    show "val (SA_poly_to_SA_fun m f (t # x)) = (MIN i\<in>inds. val (a i x \<otimes> (t \<ominus> c x) [^] i))" 
    proof(cases "(0::nat) \<in> inds")
      case True
      have T00: " (a 0 x \<otimes> (t \<ominus> c x) [^] (0::nat)) \<in> carrier Q\<^sub>p"
        by (simp add: a_eval t_x_closed(2))
      have T01: "\<And>i. i \<in> inds \<Longrightarrow> a i x \<otimes> (t \<ominus> c x) [^] i \<in> carrier (Q\<^sub>p)"
        using T00 T2 
        by (metis Qp.zero_closed)
      have T02: "inds = insert 0 (inds - {0})"
        using True by blast 
      have "(\<Oplus>i\<in>insert 0 (inds - {0}). a i x \<otimes> (t \<ominus> c x) [^] i) =
          a(0::nat) x \<otimes> (t \<ominus> c x)[^] (0::nat) \<oplus> (\<Oplus>i\<in>inds-{(0::nat)}. a i x \<otimes> (t \<ominus> c x) [^] i)"
        apply(rule Qp.finsum_insert[of "inds-{0}" "0::nat" "(\<lambda> i.  a i x \<otimes> (t \<ominus> c x) [^] i)"])
        using inds_finite apply blast
          apply blast
        using "101" apply blast
        using T00 by blast
      hence T03: "(SA_poly_to_SA_fun m f (t#x)) = (a 0 x \<otimes> (t \<ominus> c x) [^] (0::nat)) \<oplus>
                                (\<Oplus>i\<in>inds - {0}. a i x \<otimes> (t \<ominus> c x) [^] i)"
        using T02  unfolding 100 by auto
      have T04: "(MIN i\<in>inds. val (a i x \<otimes> (t \<ominus> c x) [^] i)) = 
                      val (a 0 x \<otimes> (t \<ominus> c x) [^] (0::nat))"
        apply(rule Min_eqI ) 
        using inds_finite apply blast 
        using  T1 apply blast 
        using True by blast 
      show "val (SA_poly_to_SA_fun m f (t#x)) = (MIN i\<in>inds. val (a i x \<otimes> (t \<ominus> c x) [^] i))"
        using T2 Qp.finsum_zero unfolding T03  T04 tx_def 
        by (smt (verit, best) DiffD2 Qp.add.finprod_one_eqI Qp.r_zero T00 insertI1)
    next
      case False
      then have F0:  "\<And>i. i \<in> inds \<Longrightarrow>  (a i x \<otimes> (t \<ominus> c x) [^] i) = \<zero>"
        using T2 by metis 
      hence F1: "(SA_poly_to_SA_fun m f (t#x))  = \<zero>"
        unfolding 100 using Qp.finsum_zero by (smt Qp.add.finprod_one_eqI Qp.r_zero singletonI)
      have F2: " (MIN i\<in>inds. val (a i x \<otimes> (t \<ominus> c x) [^] i)) = \<infinity>"
        apply(rule Min_eqI)
        using inds_finite apply blast 
        using F0 True local.val_zero apply force
        using A0(2) F0 local.val_zero by fastforce
      show "val (SA_poly_to_SA_fun m f (t # x)) = (MIN i\<in>inds. val (a i x \<otimes> (t \<ominus> c x) [^] i))"
        unfolding F1 F2 val_zero by blast 
    qed
  next
    case False
    show "val (SA_poly_to_SA_fun m f (t # x)) = (MIN i\<in>inds. val (a i x \<otimes> (t \<ominus> c x) [^] i))"           
      unfolding 100 
    proof(rule finsum_val_ultrametric_diff')
      show "(\<lambda>i. a i x \<otimes> (t \<ominus> c x) [^] i) \<in> inds \<rightarrow> carrier Q\<^sub>p"
        using 101 by blast 
      show "finite inds"
        using inds_def inds_finite by blast
      show " inds \<noteq> {}" 
        by (simp add: A0(2))
      show "\<And>i b. i \<in> inds \<Longrightarrow>
             b \<in> inds \<Longrightarrow> i \<noteq> b \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x) [^] i) \<noteq> val (a b x \<otimes> (t \<ominus> c x) [^] b)"
      proof- fix i b assume A: "i \<in> inds" "b \<in> inds" "i \<noteq> b"                 
        show "val (a i x \<otimes> (t \<ominus> c x) [^] i) \<noteq> val (a b x \<otimes> (t \<ominus> c x) [^] b)"
          apply(cases "i < b")
          using A A\<^sub>0_memE[of t x i b] A\<^sub>0_memE[of t x b i] A0 False unfolding tx_def by auto
      qed 
    qed
  qed
qed


text\<open>This lemma formalizes the statement from Denef's proof that ``The cells contained in $A \setminus A_0$ have the form \[
B = \{ (x,t) \mid x \in C \text{ and ord}(t - c(x)) = \text{ord}(\theta(x)) \}, ...
\]" \<close>

definition \<Theta> where \<Theta>_def: "\<Theta>  = (\<lambda>ps. (SOME \<phi> .\<phi> \<in> Units (SA m) \<and>
    (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (int (snd ps) - int (fst ps))*ord (\<phi> x)
                              +  ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x) 
                                                                    mod (int (snd ps) - int (fst ps))
                                = ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x))))"

lemma \<Theta>_unit: "\<And>ps. ps \<in> ordered_ind_pairs \<Longrightarrow> \<Theta> ps \<in> Units (SA m)"
 "\<And>ps. ps \<in> ordered_ind_pairs \<Longrightarrow>
                          (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (int (snd ps) - int (fst ps))*ord (\<Theta> ps x)
                              +  ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x) 
                                                                    mod (int (snd ps) - int (fst ps))
                                = ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x))"
proof- 
  fix ps assume A: "ps \<in> ordered_ind_pairs"
  then obtain i j where ij_def: "ps = (i,j)"
    using bezw.cases by blast
  have F10010: "(i,j) \<in> ordered_ind_pairs"
    using A unfolding ordered_ind_pairs_def mem_Collect_eq ij_def 
    by metis 
  obtain \<phi> where \<phi>_def: "\<phi>\<in>Units (SA m) \<and> (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (int (snd ps) - int (fst ps))*ord (\<phi> x)
                              +  ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x) 
                                                                    mod (int (snd ps) - int (fst ps))
                                = ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x))"
    using F10010 F_def ordered_ind_pairs_unit'[of "(i,j)"] ij_def by blast
  have a: "\<Theta> ps \<in> Units (SA m) \<and> (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (int (snd ps) - int (fst ps))*ord (\<Theta> ps x)
                              +  ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x) 
                                                                    mod (int (snd ps) - int (fst ps))
                                = ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x))"
    apply(rule SomeE[of "\<Theta> ps" _ \<phi> ])
    using F10010 \<phi>_def  SomeE unfolding \<Theta>_def ij_def by auto
  show "\<Theta> ps \<in> Units (SA m)"
        "(\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (int (snd ps) - int (fst ps))*ord (\<Theta> ps x)
                              +  ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x) 
                                                                    mod (int (snd ps) - int (fst ps))
                                = ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x))"
    using a unfolding ij_def by auto 
qed

lemma \<Theta>_ord: "\<And>i j x. (i, j) \<in> ordered_ind_pairs \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> 
                                 (int j - int i)*ord ((\<Theta> (i,j)) x)
                              +  ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - i)
                                = ord (((a i) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a j ) x)"
proof- 
    fix i j x assume F10010: "(i, j) \<in> ordered_ind_pairs" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" 
    have "\<exists>\<eta>\<in>Units (SA m). \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>).
          (int j - int i) * ord (\<eta> x) + ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - int i) =
                  ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) "
      apply(rule ordered_ind_pairs_unit)
      using ordered_ind_pairs_unit[of i j ] F10010(1)
      unfolding ordered_ind_pairs_def ind_pairs_def mem_Collect_eq by auto  
    then obtain \<phi> where \<phi>_def: "\<phi>\<in>Units (SA m) \<and>
       ( \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>).
          (int j - int i) * ord (\<phi> x) + ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - int i) =
                  ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x))"
      by blast
    have a:"(\<Theta> (i,j))\<in>Units (SA m) \<and>
       ( \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>).
          (int j - int i) * ord ((\<Theta> (i,j)) x) + ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - int i) =
                  ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x))"
      apply(rule SomeE[of "\<Theta> (i,j)" _ \<phi>])
      using F10010  unfolding \<Theta>_def fst_conv snd_conv apply blast
      using \<phi>_def by auto 
  have 000: "snd (case (i, j) of (x, y) \<Rightarrow> (x, int y)) = j"
    by auto
  have 001: "fst (case (i, j) of (x, xa) \<Rightarrow> (int x, xa)) = i"
    by auto
  have 002: "(\<Theta> (i,j)) \<in>Units (SA m) \<and>
     (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>).
          (int j - int i) * ord ((\<Theta> (i,j)) x) + ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - int i) =
                  ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x))"
    using a unfolding 000 001 fst_conv snd_conv by auto 
  show "(int j - int i) * ord (\<Theta>(i,j) x) + ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - int i) =
       ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x)"
    using 002  F10010 by auto                
qed

definition A\<^sub>0_comp_fibre_cover where
"A\<^sub>0_comp_fibre_cover ps = 
      {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). int (snd ps - fst ps)* ord ((\<Theta> ps) x) =  
                            ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) } 
\<inter>    {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<Theta> ps x) \<in> I (val (a1 x)) (val (a2 x))}
\<inter>    A "

lemma A\<^sub>0_comp_fibre_cover_semialg: 
  assumes "ps \<in> ordered_ind_pairs"
  shows "is_semialgebraic m (A\<^sub>0_comp_fibre_cover ps)"
proof-
  obtain i j where ij_def: "ps = (i,j)"
    using assms unfolding ordered_ind_pairs_def ind_pairs_def by auto 
  obtain G where G_def: "G = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). 
  int (snd ps - fst ps)* ord ((\<Theta> ps) x) =  ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) }"
    by blast
  have 0: "is_semialgebraic m G"
  proof- 
    have 0: "(a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) \<in> carrier (SA m)"
      using inds_memE[of "fst ps"] inds_memE[of "snd ps"] assms ordered_ind_pairs_memE
      by auto 
    have 1: "snd ps - fst ps > 0"
      using  assms ordered_ind_pairs_memE[of ps] by linarith 
    have 2: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x \<noteq>\<zero>"
     by(intro SA_Units_memE'[of _ m] a_quotient_unit ordered_ind_pairs_memE assms, auto )
    have 3: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x \<in> carrier Q\<^sub>p \<and> (a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x \<noteq> \<zero>"
      using 2 0 SA_car_memE by blast 
    have 4: " {x \<in> carrier (Q\<^sub>p\<^bsup>m + 0\<^esup>).
  (a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x \<in> nonzero Q\<^sub>p \<and> ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x) mod int (snd ps - fst ps) = 0} =
  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) mod (snd ps - fst ps) = 0}"
      apply(rule equalityI')
      unfolding mem_Collect_eq nonzero_def apply (metis add_cancel_left_right)
      using 3  add_cancel_left_right[of m 0] by metis 
    have 5: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). int (snd ps - fst ps)* ord ((\<Theta> ps) x) =  ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) }"
    proof- 
      have 50: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (\<Theta> ps x) \<in> nonzero Q\<^sub>p"
        using \<Theta>_unit assms SA_Units_memE' SA_Units_closed SA_car_memE unfolding nonzero_def 
        by (metis (mono_tags, lifting) function_ring_car_closed mem_Collect_eq)
      have 51: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (int (snd ps - fst ps))* ord ((\<Theta> ps) x) = ord ((\<Theta> ps [^] \<^bsub>SA m\<^esub> (snd ps - fst ps)) x)"
      proof- fix x assume AAA: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        have 510: "(\<Theta> ps [^] \<^bsub>SA m\<^esub> (snd ps - fst ps)) x = (\<Theta> ps x [^] (snd ps - fst ps))"
          using \<Theta>_unit AAA SA_Units_memE SA_Units_closed by (meson SA_nat_pow)
        show "int (snd ps - fst ps) * ord (\<Theta> ps x) = ord ((\<Theta> ps [^]\<^bsub>SA m\<^esub> (snd ps - fst ps)) x)"
          using 50 unfolding 510 using AAA nonzero_nat_pow_ord by presburger
      qed
      have 52: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (snd ps - fst ps)* ord ((\<Theta> ps) x) =  ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) }
      = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>).ord ((\<Theta> ps [^] \<^bsub>SA m\<^esub> (snd ps - fst ps)) x) =  ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) }"
        apply(rule equalityI') unfolding mem_Collect_eq  using 51 50 
        apply (metis SA_nat_pow mult_of_nat_commute)
         using 51 50 
         by presburger
       have 53: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (\<Theta> ps [^] \<^bsub>SA m\<^esub> (snd ps - fst ps)) x \<in> nonzero Q\<^sub>p"
         using 50 \<Theta>_unit Qp_nat_pow_nonzero SA_nat_pow by presburger
       have 54: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) \<in> nonzero Q\<^sub>p"
         using inds_memE by (meson "3" not_nonzero_Qp)
       have 55: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (snd ps - fst ps)* ord ((\<Theta> ps) x) =  ord (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) }
      = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val ((\<Theta> ps [^] \<^bsub>SA m\<^esub> (snd ps - fst ps)) x) =  val (((a (fst ps)) \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a (snd ps) ) x) }"
        unfolding 52 apply(rule equalityI')
        unfolding mem_Collect_eq using inds_memE 50 
         apply (metis "3" Qp.nonzero_memE(1) Qp.nonzero_memE(2) Qp_nat_pow_nonzero SA_nat_pow val_ord')
        using 53 54 unfolding val_def nonzero_def mem_Collect_eq 
        by (meson eint.simps(1))
      have 56: "(\<Theta> ps [^]\<^bsub>SA m\<^esub> (snd ps - fst ps)) \<in> carrier (SA m)"
        using assms \<Theta>_unit by blast
      have 57: "(a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) \<in> carrier (SA m)"
        using inds_memE ordered_ind_pairs_memE[of ps] assms by auto  
      show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). int (snd ps - fst ps) * ord (\<Theta> ps x) = ord ((a (fst ps) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a (snd ps)) x)}"
        unfolding 55 using 56 57 semialg_val_eq_set_is_semialg by blast
    qed 
    thus ?thesis unfolding G_def by auto 
  qed
  obtain G' where G'_def: "G' = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<Theta> ps x) \<in> I (val (a1 x)) (val (a2 x))} \<inter> G"
    by blast 
  have 1: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<Theta> ps x) \<in> I (val (a1 x)) (val (a2 x))}"
    apply(rule cell_cond_semialg) 
      using \<C>_def \<C>_cond is_cell_conditionE(5)  apply blast
      using \<Theta>_unit(1) assms SA_Units_closed apply auto[1]
      using \<C>_cond  unfolding \<C>_def by auto 
  show ?thesis 
    unfolding A\<^sub>0_comp_fibre_cover_def 
    apply(intro intersection_is_semialg)
    using 1 A_semialg 0 unfolding G_def by auto 
qed

lemma A\<^sub>0_comp_fibre_cover_covers: 
 "condition_to_set \<C> - A\<^sub>0 = 
    (\<Union> ps \<in> ordered_ind_pairs. condition_to_set 
                                (Cond m (A\<^sub>0_comp_fibre_cover ps) c (\<Theta> ps)(\<Theta> ps) closed_interval))"
proof(rule equalityI')
  fix xs assume A: "xs \<in> condition_to_set \<C> - A\<^sub>0"
  then obtain ps where ps_def: "ps \<in> ordered_ind_pairs" "xs \<notin> term_ineq_set ps"
    unfolding Diff_iff Int_iff A\<^sub>0_as_intersection Inter_iff by auto 
  obtain i j where ij_def: "i \<in> inds" "j \<in> inds" "i < j" "ps = (i,j)"
    using ps_def unfolding ordered_ind_pairs_def ind_pairs_def by auto 
  have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using A unfolding condition_to_set.simps \<C>_def cell_def by auto 
  obtain t x where tx_def: "xs = t#x" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using xs_closed 
    by (metis Qp_pow_ConsE(1) Qp_pow_ConsE(2) cartesian_power_car_memE
        list.exhaust_sel list.size(3) nat.distinct(2))
  have 0: "val (a i x) = val (a j x \<otimes> (t \<ominus> c x) [^] (j - i))"
    using xs_closed ps_def(2) 
    unfolding ij_def term_ineq_set_def fst_conv snd_conv mem_Collect_eq tx_def list_tl list_hd
    by auto 
  have 1: "a i x \<in> Units Q\<^sub>p" "a j x \<in> Units Q\<^sub>p"
    using tx_def ij_def SA_Units_nonzero  inds_memE 
    unfolding Units_eq_nonzero by auto  
  have 2: "t \<ominus> c x \<in> Units Q\<^sub>p"
    using tx_def 0 1 val_zero  Qp.Units_closed Qp.nat_pow_zero Qp.nonzero_memE(2)
          Units_eq_nonzero ij_def(3) c_closed SA_car_closed
    unfolding Units_eq_nonzero nonzero_def mem_Collect_eq 
    by (metis (no_types, opaque_lifting) Qp.cring_simprules(27) Qp.cring_simprules(4)
        Qp.pow_zero eint.simps(3) val_def zero_less_diff)
  have closures: "a i x \<in> carrier Q\<^sub>p" "a j x \<in> carrier Q\<^sub>p" "t \<ominus> c x \<in> carrier Q\<^sub>p" 
                  "(t \<ominus> c x) [^](j-i) \<in> carrier Q\<^sub>p" "\<Theta> ps x \<in> Units Q\<^sub>p"
  proof-
    show 0: "a i x \<in> carrier Q\<^sub>p" "a j x \<in> carrier Q\<^sub>p" "t \<ominus> c x \<in> carrier Q\<^sub>p" 
            "(t \<ominus> c x) [^](j-i) \<in> carrier Q\<^sub>p"
      using 1 using 2 by auto
    show "\<Theta> ps x \<in> Units Q\<^sub>p"
      by (metis SA_Units_nonzero Units_eq_nonzero \<Theta>_unit(1) ps_def(1) tx_def(3))
  qed
  have 3: "ord (a i x) = ord (a j x \<otimes> (t \<ominus> c x) [^] (j - i))"
    using 0 val_ord 1 2 Units_eq_nonzero 
    by (simp add: Qp.Units_closed equal_val_imp_equal_ord(1))
  have 4: "ord (a i x) = ord (a j x) + (j - i)*ord (t \<ominus> c x)"
    by (metis 1 2 3  Qp.Units_pow_closed Units_nonzero_Qp int_pow_int int_pow_ord ord_mult)
  have 5: "ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a j) x) = (j - i)*ord (t \<ominus> c x)"
    using 4 tx_def 1 SA_div_eval Units_eq_nonzero a_cfs_closed ij_def(2) inds_memE ord_fract 
    by force
  have 6: "ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - int i) = 0"
    using 5 ij_def by (simp add: of_nat_diff)
  have 7: " (int j - int i) * ord (\<Theta> (i, j) x) + 
            ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x) mod (int j - int i) =
            ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x)"
    using \<Theta>_unit[of "(i,j)"]  tx_def ij_def(4) ps_def(1) by auto
  have 8: "ord (t \<ominus> c x) = ord (\<Theta> ps x)"
    using 0 7 unfolding 6 unfolding 5  using ij_def 
    by (simp add: int_ops(6))
  hence 9: "val (\<Theta> ps x) = val (t \<ominus> c x)"
    using 7 closures 2 Units_eq_nonzero by force
  have 10: "x \<in> A\<^sub>0_comp_fibre_cover ps"
    unfolding A\<^sub>0_comp_fibre_cover_def mem_Collect_eq Int_iff  9
    unfolding fst_conv snd_conv ij_def 
    using tx_def 7 ij_def A unfolding 6 \<C>_def condition_to_set.simps cell_def mem_Collect_eq 
        tx_def Diff_iff 
    by (simp add: "5" "8")
  have "xs \<in> condition_to_set (Cond m (A\<^sub>0_comp_fibre_cover ps) c (\<Theta> ps) (\<Theta> ps) closed_interval)"
    unfolding condition_to_set.simps 
    by(intro cell_memI xs_closed, unfold tx_def list_tl list_hd closed_interval_def, intro 10, 
       auto simp: 9)
  thus "xs \<in> (\<Union>ps\<in>ordered_ind_pairs.
                  condition_to_set (Cond m (A\<^sub>0_comp_fibre_cover ps) c (\<Theta> ps) (\<Theta> ps) closed_interval))"
    using ps_def by auto 
next
  fix xs assume A: "xs \<in> (\<Union>ps\<in>ordered_ind_pairs.
               condition_to_set (Cond m (A\<^sub>0_comp_fibre_cover ps) c (\<Theta> ps) (\<Theta> ps) closed_interval))"
  then obtain ps where ps_def: "ps \<in> ordered_ind_pairs"
         "xs \<in> condition_to_set (Cond m (A\<^sub>0_comp_fibre_cover ps) c (\<Theta> ps) (\<Theta> ps) closed_interval)"
    by auto 
  obtain i j where ij_def: "i \<in> inds" "j \<in> inds" "i < j" "ps = (i,j)"
    using ps_def unfolding ordered_ind_pairs_def ind_pairs_def by auto 
  have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using ps_def unfolding condition_to_set.simps \<C>_def cell_def by auto 
  obtain t x where tx_def: "xs = t#x" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using xs_closed 
    by (metis Qp_pow_ConsE(1) Qp_pow_ConsE(2) cartesian_power_car_memE
        list.exhaust_sel list.size(3) nat.distinct(2))
  have props: "val (t \<ominus> c x) = val (\<Theta> ps x)" "x \<in> A\<^sub>0_comp_fibre_cover ps"
    using ps_def 
    unfolding tx_def condition_to_set.simps cell_def mem_Collect_eq list_tl
              list_hd closed_interval_def by auto 
  have closures: "\<Theta> ps x \<in> Units Q\<^sub>p" "t \<ominus> c x \<in> carrier Q\<^sub>p" "t \<ominus> c x \<in> Units Q\<^sub>p"
                 "a i x \<in> Units Q\<^sub>p" "a j x \<in> Units Q\<^sub>p" 
  proof- 
    show 0: "a i x \<in> Units Q\<^sub>p" "a j x \<in> Units Q\<^sub>p" 
      using ij_def 
      apply (metis SA_Units_nonzero Units_eq_nonzero inds_memE tx_def(3))
      using ij_def 
      by (metis SA_Units_nonzero Units_eq_nonzero inds_memE tx_def(3))
    show 1: "\<Theta> ps x \<in> Units Q\<^sub>p"
      by (metis SA_Units_nonzero Units_eq_nonzero \<Theta>_unit(1) ps_def(1) tx_def(3))
    show 2: "t \<ominus> c x \<in> carrier Q\<^sub>p"
      using tx_def c_closed Qp.cring_simprules(4) SA_car_closed by presburger
    show 3: "t \<ominus> c x \<in> Units Q\<^sub>p"
      using 1 2 props val_zero 
      by (metis Units_eq_nonzero equal_val_imp_equal_ord(2))
  qed
  have 1: "int (j - i) * ord (\<Theta> (i, j) x) = ord ((a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a j) x)"
    using props  
    unfolding A\<^sub>0_comp_fibre_cover_def  mem_Collect_eq ij_def snd_conv fst_conv Int_iff  by auto 
  hence 2: "int (j - i) * ord (t \<ominus> c x) = ord (a i x) - ord (a j x)"
    using props 1 closures 
    by (metis SA_div_eval Units_eq_nonzero a_cfs_closed equal_val_imp_equal_ord(1) ij_def(2) 
        ij_def(4) inds_memE ord_fract tx_def(3))
  hence 3: "val (a i x) = val (a j x \<otimes> (t \<ominus> c x) [^] (j - i))"
    using ij_def closures val_ord Qp.Units_m_closed Qp.nat_pow_nonzero Units_eq_nonzero 
      nonzero_nat_pow_ord ord_mult by auto
  have 4: "xs \<notin> A\<^sub>0"
    using props ij_def 3 
    unfolding A\<^sub>0_comp_fibre_cover_def  mem_Collect_eq ij_def snd_conv fst_conv Int_iff A\<^sub>0_def 
    by (metis list.sel(1) list.sel(3) tx_def(1))
  have 5: "xs \<in> condition_to_set \<C>"
    unfolding \<C>_def condition_to_set.simps
    apply(intro cell_memI xs_closed, unfold tx_def list_tl list_hd)
    using props unfolding A\<^sub>0_comp_fibre_cover_def Int_iff mem_Collect_eq props by auto 
  show "xs \<in> condition_to_set \<C> - A\<^sub>0"
    using 4 5 by auto 
qed

lemma A\<^sub>0_comp_decomp:
  "\<exists>S'. (is_cell_decomp m S' (condition_to_set \<C> - A\<^sub>0) \<and>
         (\<forall>B\<in>S'. (\<exists> \<phi>. \<phi> \<in> Units (SA m) \<and>
             center B = c \<and> l_bound B = \<phi> \<and> u_bound B = \<phi> \<and>
             boundary_condition B = closed_interval)))"
proof(cases "ordered_ind_pairs = {}")
  case True
  hence 0: "(condition_to_set \<C> - A\<^sub>0) = {}"
    unfolding A\<^sub>0_as_intersection True by auto 
  have "is_cell_decomp m {} (condition_to_set \<C> - A\<^sub>0)"
    unfolding 0 is_partition_def disjoint_def is_cell_decomp_def by auto 
  thus ?thesis by blast 
next
  case False
  interpret one_val_point_decomp _ _ _ _ _ _ _ _ _ _ _ _ _ "condition_to_set \<C> - A\<^sub>0"
                                                            ordered_ind_pairs A\<^sub>0_comp_fibre_cover
                                                            \<Theta>
    apply(intro one_val_point_decomp.intro one_val_point_decomp_axioms.intro  
              common_refinement_locale_axioms A\<^sub>0_comp_fibre_cover_semialg ordered_ind_pairs_finite 
              False)
          apply auto[1]
    using \<Theta>_unit unfolding A\<^sub>0_comp_fibre_cover_covers Q\<^sub>p_def Z\<^sub>p_def \<iota>_def
    by auto 
  show ?thesis 
    using decomp \<Theta>_unit(1)
    by (metis (no_types, opaque_lifting) image_iff)
qed
       
definition A\<^sub>0_comp_decomp where 
"A\<^sub>0_comp_decomp = (SOME S'. (is_cell_decomp m S' (condition_to_set \<C> - A\<^sub>0) \<and>
                           (\<forall>B\<in>S'. (\<exists> \<phi>. \<phi> \<in> Units (SA m) \<and> center B = c \<and> 
                        l_bound B = \<phi> \<and> u_bound B = \<phi> \<and> boundary_condition B = closed_interval))))"

lemma A\<^sub>0_comp_decompE:
"(is_cell_decomp m A\<^sub>0_comp_decomp (condition_to_set \<C> - A\<^sub>0) \<and>
 (\<forall>B \<in> A\<^sub>0_comp_decomp. 
        (\<exists> \<phi>. \<phi> \<in> Units (SA m) \<and> 
              center B = c \<and> l_bound B = \<phi> \<and> u_bound B = \<phi> \<and>
              boundary_condition B = closed_interval)))"
proof- 
  obtain S' where S'_def: "(is_cell_decomp m S' (condition_to_set \<C> - A\<^sub>0) \<and> (\<forall>B\<in>S'. (\<exists> \<phi>. \<phi> \<in> Units (SA m) \<and> center B = c \<and> l_bound B = \<phi> \<and> u_bound B = \<phi> \<and> boundary_condition B = closed_interval)))"
    using A\<^sub>0_comp_decomp by blast
  show ?thesis apply(rule SomeE[of "A\<^sub>0_comp_decomp" _ S'])
    unfolding A\<^sub>0_comp_decomp_def apply blast
    by(rule S'_def)
qed

text\<open>That $A_0$ can be decomposed as desired is relatively easy to show:\<close>
lemma A\<^sub>0_decomp:
  assumes "inds \<noteq> {}"
  shows "\<exists>S. is_cell_decomp m S A\<^sub>0 \<and> 
              (\<forall>B\<in>S. center B = c \<and> 
              (\<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N))"
proof-
  have 0: "\<exists>S. is_cell_decomp m S A\<^sub>0 \<and> (\<forall>B\<in>S. center B = c)" 
  proof- 
    have 0: "\<exists>S. is_cell_decomp m S (condition_to_set \<C> - (condition_to_set \<C> - A\<^sub>0)) \<and> (\<forall>A\<in>S. center A = c)"
      apply(rule cell_decomp_same_center[of \<C> m A c a1 a2 I "condition_to_set \<C> - A\<^sub>0"])
         apply (simp add: \<C>_cond)
      using \<C>_def apply blast 
      apply blast
      using           A\<^sub>0_comp_decompE
      by auto 
    have 1: "(condition_to_set \<C> - (condition_to_set \<C> - A\<^sub>0)) = A\<^sub>0"
      using A\<^sub>0_def by auto 
    show ?thesis  
      using "0" "1" by auto
  qed
  then obtain S where S_def: "is_cell_decomp m S A\<^sub>0 \<and> (\<forall>B\<in>S. center B = c)" 
    by blast 
  have "(\<forall>B\<in>S. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
  proof
    fix B
    assume A: "B \<in>  S"
    have center_B: "center B = c"
      using A S_def by blast 
    show "\<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N"
      apply(rule exI, rule SA_poly_uboundedI[of _ _ _ _ 0])
      using f_closed apply blast 
      unfolding center_B 
      apply (simp add: c_closed)
      using A S_def 
      apply (metis is_cellI is_cell_decompE(3) is_cell_decompE(4) is_cell_subset)
    proof-
     fix x t i assume B': " t # x \<in> condition_to_set B"
      then have P0: "t # x \<in> A\<^sub>0" 
        using A S_def  is_cell_decompE 
        by (meson in_mono is_cell_decomp_subset)
      hence P1: " val (SA_poly_to_SA_fun m f (t # x)) = (MIN i\<in>inds. (val ( (a i x)\<otimes>(t \<ominus> c x)[^]i)))"
        using val_f_on_A\<^sub>0[of "t#x"] assms P0 
        unfolding list_tl list_hd by auto 
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using P0 A\<^sub>0_def cartesian_power_head 
        by (metis (no_types, lifting) B' cell_memE(1) condition_to_set.simps list_hd padic_fields.condition_decomp' padic_fields_axioms)
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using P0 A\<^sub>0_def cartesian_power_tail[of "t#x" Q\<^sub>p m] 
        by (metis (no_types, lifting) A\<^sub>0_closed list_tl subsetD)
      have x_closed': "x \<in> A"
        using P0 A\<^sub>0_def  \<C>_memE(3) by fastforce        
      have P2: "val (SA_poly_to_Qp_poly m x f \<bullet> t) = (MIN i\<in>inds. (val ( (a i x)\<otimes>(t \<ominus> c x)[^]i)))"
        using P1 SA_poly_to_SA_fun_formula[of f m x t] A x_closed t_closed 
        using f_closed by force
      have P3: "i \<in> inds \<Longrightarrow> val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> (val ( (a i x)\<otimes>(t \<ominus> c x)[^]i))"
        apply(rule MinE''[of inds])
          using inds_finite apply blast 
            apply blast 
          using P2 apply blast 
          by blast  
      have P4: "UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t =
                  taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f) i \<otimes> (t \<ominus> c x) [^] i"
          using A UPQ.to_fun_taylor_term[of "SA_poly_to_Qp_poly m x f" t "c x" i]
          SA_poly_to_Qp_poly_closed[of x m f] t_closed c_closed x_closed
          SA_car_memE(3)[of c m]
          unfolding UPQ.taylor_def 
          using f_closed by blast
      have P5: "taylor_expansion (SA m) c f i x = taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f) i"
          using SA_poly_to_Qp_poly_taylor_cfs[of f m x c i] c_closed x_closed f_closed by blast 
      have P6: "i \<in> inds \<Longrightarrow> (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) =  (a i x)\<otimes>(t \<ominus> c x)[^]i"
          using a_eval a_def x_closed' unfolding P4 P5 a_def
          by auto 
      have P7: "i \<in> inds \<Longrightarrow> val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t)"
        using P6 unfolding UPQ.taylor_term_def 
        using P3 by presburger
      have P8: "i \<notin> inds \<Longrightarrow>   UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t = \<zero>"
        using x_closed'  inds_memE  c_closed x_closed t_closed SA_car_memE(3)[of c m]
        unfolding P4 P5     a_def   
        by (metis P5 Qp.cring_simprules(26) Qp.cring_simprules(4) Qp.nat_pow_closed SA_car_closed a_def inds_non_memE)
      have P9: "i \<notin> inds \<Longrightarrow>   val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) = \<infinity>"
        using val_zero unfolding P8 by blast    
      show "val (SA_poly_to_Qp_poly m x f \<bullet> t)
\<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint 0"
        apply(cases "i \<in> inds")
        using P7 apply (metis add.right_neutral eint_defs(1))
        unfolding P9 
        by (metis add.right_neutral eint_defs(1) eint_ord_code(3))
    qed
  qed
  thus ?thesis using S_def  by auto 
qed
end

locale A\<^sub>0_refinement = common_refinement_locale + 
  fixes B b b1 b2 J
  assumes B_cell: "is_cell_condition B"
  assumes B_eq: "B = Cond m b c b1 b2 J"
  assumes B_subset: "condition_to_set B \<subseteq> A\<^sub>0"

context A\<^sub>0_refinement
begin

text\<open>We wish to decompose the set $A_0$ into finer cells so that on each cell, there is always
     a fixed $i_0$ so that $val (a_{i_0}(x)(t- c(x))^{i_0})$ is minimal. This was easy to do on 
     the complement of $A_0$ because this value did not depend on $t$, but here this will take some
     extra work. Here we assume we already have obtained a cell in a decomposition of $A_0$, and
     will further decompose this cell until we have our desired property.\<close>

definition refinement_functions where
"refinement_functions = insert \<zero>\<^bsub>SA m\<^esub> (\<Theta> ` ordered_ind_pairs)"

definition refined_decomp where
"refined_decomp = (SOME S. is_cell_decomp m S (condition_to_set (Cond m b c b1 b2 J)) \<and>
            (\<forall>C\<in>S. center C = c \<and>
              (\<forall>f\<in>refinement_functions.
                  \<forall>g\<in>refinement_functions.
                     \<forall>I. is_convex_condition I \<longrightarrow>
                         condition_to_set C \<subseteq> condition_to_set (Cond m b c f g I) \<or>
                         condition_to_set C \<inter> condition_to_set (Cond m b c f g I) = {})))"

lemma refined_decomp_prop:
"is_cell_decomp m refined_decomp (condition_to_set (Cond m b c b1 b2 J)) \<and>
          (\<forall>C\<in> refined_decomp. center C = c \<and>
              (\<forall>f\<in>refinement_functions.
                  \<forall>g\<in>refinement_functions.
                     \<forall>I. is_convex_condition I \<longrightarrow>
                         condition_to_set C \<subseteq> condition_to_set (Cond m b c f g I) \<or>
                         condition_to_set C \<inter> condition_to_set (Cond m b c f g I) = {}))"
proof-
  have 0: "finite refinement_functions"
  proof- 
    have 0: "refinement_functions \<subseteq> insert \<zero>\<^bsub>SA m\<^esub> (\<Theta> ` ind_pairs)"
      unfolding refinement_functions_def ordered_ind_pairs_def 
      by auto 
    have "finite (insert \<zero>\<^bsub>SA m\<^esub> (\<Theta> ` ind_pairs))"
      using finite_ind_pairs by auto 
    thus ?thesis using 0 finite_subset by blast
  qed
  have 1: "refinement_functions \<subseteq> carrier (SA m)"
    unfolding refinement_functions_def 
    using \<Theta>_unit by blast
  have 0: " \<exists>S. is_cell_decomp m S (condition_to_set (Cond m b c b1 b2 J)) \<and>
        (\<forall>C\<in>S. center C = c \<and>
                (\<forall>f\<in>refinement_functions.
                    \<forall>g\<in>refinement_functions.
                       \<forall>I. is_convex_condition I \<longrightarrow>
                           condition_to_set C \<subseteq> condition_to_set (Cond m b c f g I) \<or>
                           condition_to_set C \<inter> condition_to_set (Cond m b c f g I) = {}))"
    using 0 1 semialg_boundary_cell_decomp[of refinement_functions m B b c b1 b2 J] 
          refinement_functions_def B_eq B_cell by auto  
  then obtain S where S_def: "is_cell_decomp m S (condition_to_set (Cond m b c b1 b2 J)) \<and>
        (\<forall>C\<in>S. center C = c \<and>
                (\<forall>f\<in>refinement_functions.
                    \<forall>g\<in>refinement_functions.
                       \<forall>I. is_convex_condition I \<longrightarrow>
                           condition_to_set C \<subseteq> condition_to_set (Cond m b c f g I) \<or>
                           condition_to_set C \<inter> condition_to_set (Cond m b c f g I) = {}))"
    by blast 
  thus ?thesis using refined_decomp_def SomeE[of refined_decomp _ S]  
    by blast
qed

lemma refined_decomp_subset:
  assumes "\<B> \<in> refined_decomp"
  shows "condition_to_set \<B> \<subseteq> condition_to_set B"
  using assms is_cell_decomp_subset[of m refined_decomp "condition_to_set B" \<B>] refined_decomp_prop
  unfolding B_eq by auto 

lemma refined_decomp_closure:
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  shows "t \<in> carrier Q\<^sub>p"
        "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        "t \<ominus> c x \<in> carrier Q\<^sub>p"
proof-
  show  "t \<in> carrier Q\<^sub>p"
          "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms B_cell refined_decomp_subset Qp_pow_ConsE[of "t#x" m]
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd
    by auto 
  thus "t \<ominus> c x \<in> carrier Q\<^sub>p"
    using Qp.cring_simprules(4) SA_car_closed c_closed by presburger
qed

lemma refined_decomp_static_order1: 
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  assumes "(i,j) \<in> ordered_ind_pairs"
  shows "\<And>s y.  s#y \<in> condition_to_set \<B> 
                \<Longrightarrow> val (t \<ominus> c x) \<le> val (\<Theta>(i,j) x)   \<Longrightarrow> val (s \<ominus> c y) \<le> val (\<Theta>(i,j) y)"
        "\<And>s y.   s#y \<in> condition_to_set \<B> 
                \<Longrightarrow> val (t \<ominus> c x) < val (\<Theta>(i,j) x)  \<Longrightarrow> val (s \<ominus> c y) < val (\<Theta>(i,j) y)"
proof- 
  fix s y assume a: "s#y \<in> condition_to_set \<B>"
  have sy_in: "s#y \<in> condition_to_set B"
    using a assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have s_closed: "s \<in> carrier Q\<^sub>p"
    using assms B_cell sy_in 
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(2) list.sel(1))
  have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms B_cell sy_in
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(1) list.sel(3))
  have tx_in: "t#x \<in> condition_to_set B"
    using assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms refined_decomp_closure by auto 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms refined_decomp_closure by auto 
  have i_le_j: "i < j"
    using assms ordered_ind_pairs_def by auto 
  have in_inds: "i \<in> inds" "j \<in> inds"
    using assms ordered_ind_pairs_def ind_pairs_def by auto 
  have F0: "t#x \<in> A\<^sub>0"
    using tx_in assms B_subset by blast
  show "val (\<Theta>(i,j) x) \<ge> val (t \<ominus> c x) \<Longrightarrow> val (\<Theta>(i,j) y) \<ge> val (s \<ominus> c y)"
    proof- 
    assume A: "val (\<Theta>(i,j) x) \<ge> val (t \<ominus> c x)"
    then have 0: "t#x \<in> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) closed_ray)"
      unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd closed_ray_def 
      using B_cell B_eq Qp_pow_ConsI padic_fields.condition_to_set_memE'(1) padic_fields_axioms
            t_closed tx_in x_closed by auto
    hence 1: "condition_to_set \<B> \<subseteq> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) closed_ray)"
      using assms refined_decomp_prop unfolding refinement_functions_def is_convex_condition_def
      by blast
    hence "s#y \<in> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) closed_ray)"
      using a by auto 
    thus "val (\<Theta>(i,j) y) \<ge> val (s \<ominus> c y)"
      unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd closed_ray_def 
      by auto 
  qed

  show "val (\<Theta>(i,j) x) > val (t \<ominus> c x) \<Longrightarrow> val (\<Theta>(i,j) y) > val (s \<ominus> c y)"
    proof- 
    assume A: "val (\<Theta>(i,j) x) > val (t \<ominus> c x)"
    then have 0: "t#x \<in> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) open_ray)"
      unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
       using A\<^sub>0_closed B_cell B_eq F0 condition_to_set_memE'(1) open_ray_memI tx_in by auto
    hence 1: "condition_to_set \<B> \<subseteq> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) open_ray)"
      using assms refined_decomp_prop unfolding refinement_functions_def is_convex_condition_def
      by blast
    hence "s#y \<in> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) open_ray)"
      using a by auto 
    thus "val (\<Theta>(i,j) y) > val (s \<ominus> c y)"
      unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd open_ray_def 
      by auto 
  qed
qed

lemma refined_decomp_static_order2: 
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  assumes "(i,j) \<in> ordered_ind_pairs"
  shows   "\<And>s y.  s#y \<in> condition_to_set \<B> 
                \<Longrightarrow> val (t \<ominus> c x) \<ge> val (\<Theta>(i,j) x) \<Longrightarrow> val (s \<ominus> c y) \<ge> val (\<Theta>(i,j) y)"
          "\<And>s y.  s#y \<in> condition_to_set \<B> 
                \<Longrightarrow> val (t \<ominus> c x) > val (\<Theta>(i,j) x) \<Longrightarrow> val (s \<ominus> c y) > val (\<Theta>(i,j) y)"
proof- 
  fix s y assume A: "s#y \<in> condition_to_set \<B> "
  have 0: "val (s \<ominus> c y) < val (\<Theta> (i, j) y) \<Longrightarrow> val (t \<ominus> c x) < val (\<Theta> (i, j) x)"
    using A assms refined_decomp_static_order1(2)[of \<B> s y i j t x] by auto 
  have 1: "val (s \<ominus> c y) \<le> val (\<Theta> (i, j) y) \<Longrightarrow> val (t \<ominus> c x) \<le> val (\<Theta> (i, j) x)"
    using A assms refined_decomp_static_order1(1)[of \<B> s y i j t x] by auto 
  have 2: "\<And> x y::eint. x < y \<longleftrightarrow> \<not> y \<le> x"
    by auto 
  show "val (t \<ominus> c x) \<ge> val (\<Theta>(i,j) x)   \<Longrightarrow> val (s \<ominus> c y) \<ge> val (\<Theta>(i,j) y)"
    using 0 unfolding 2 by auto   
  show "val (t \<ominus> c x) > val (\<Theta>(i,j) x)   \<Longrightarrow> val (s \<ominus> c y) > val (\<Theta>(i,j) y)"
    using 1 unfolding 2 by auto  
qed

lemma val_in_B_zero: 
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  assumes "(i,j) \<in> ordered_ind_pairs"
  assumes "t \<ominus> c x = \<zero>"
  shows "\<And>s y. s#y \<in> condition_to_set \<B> \<Longrightarrow> s \<ominus> c y = \<zero>"
proof- 
  fix s y assume A: "s#y \<in> condition_to_set \<B>"
  have sy_in: "s#y \<in> condition_to_set B"
    using A assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have s_closed: "s \<in> carrier Q\<^sub>p"
    using assms B_cell sy_in 
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(2) list.sel(1))
  have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms B_cell sy_in
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(1) list.sel(3))
  have tx_in: "t#x \<in> condition_to_set B"
    using assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms refined_decomp_closure by auto 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms refined_decomp_closure by auto 
  have F0: "t#x \<in> A\<^sub>0"
    using tx_in assms B_subset by blast
  have "t#x \<in> condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval)"
      unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
                closed_interval_def assms val_def 
      using A\<^sub>0_closed B_cell B_eq  SA_zeroE F0 padic_fields.condition_to_set_memE'(1) 
            padic_fields_axioms tx_in x_closed by auto
  then have "condition_to_set \<B> \<subseteq>condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval)"
    using assms refined_decomp_prop 
    unfolding is_convex_condition_def refinement_functions_def by blast
  hence "s#y \<in> condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval)"
    using A by auto 
  thus "s \<ominus> c y = \<zero>"
    unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd closed_interval_def
              val_def 
    by (smt (verit, best) Extended_Int.infinity_ileE SA_zeroE y_closed)
qed

lemma val_in_B_nonzero: 
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  assumes "(i,j) \<in> ordered_ind_pairs"
  assumes "t \<ominus> c x \<noteq> \<zero>"
  shows "\<And>s y. s#y \<in> condition_to_set \<B> \<Longrightarrow> s \<ominus> c y \<noteq> \<zero>"
proof- 
  fix s y assume A: "s#y \<in> condition_to_set \<B>"
  have sy_in: "s#y \<in> condition_to_set B"
    using A assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have s_closed: "s \<in> carrier Q\<^sub>p"
    using assms B_cell sy_in 
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(2) list.sel(1))
  have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms B_cell sy_in
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(1) list.sel(3))
  have tx_in: "t#x \<in> condition_to_set B"
    using assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms refined_decomp_closure by auto 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms refined_decomp_closure by auto 
  have F0: "t#x \<in> A\<^sub>0"
    using tx_in assms B_subset by blast
  have "t#x \<notin> condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval)"
      unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
                closed_interval_def  val_def 
      using A\<^sub>0_closed B_cell B_eq  SA_zeroE F0 padic_fields.condition_to_set_memE'(1) 
            padic_fields_axioms assms tx_in x_closed by auto
  then have "condition_to_set \<B>  \<inter> condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval) = {}"
    using assms refined_decomp_prop 
    unfolding is_convex_condition_def refinement_functions_def by blast
  hence "s#y \<notin> condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval)"
    using A by auto 
  thus "s \<ominus> c y \<noteq> \<zero>"
    unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd closed_interval_def
    by (metis A assms(1) assms(2) assms(3) assms(4) val_in_B_zero)
qed

lemma ineq_equivalence:
  assumes "\<alpha> \<in> Units Q\<^sub>p"
  assumes "\<beta> \<in> Units Q\<^sub>p"
  assumes "x \<in> Units Q\<^sub>p"
  shows "val (\<alpha> \<otimes> x[^](i::nat)) < val (\<beta> \<otimes> x[^](j::nat)) 
          \<Longrightarrow> ord \<alpha> - ord \<beta> < (int j- int i)*ord x"
        "ord \<alpha> - ord \<beta> < (int j- int i)*ord x
          \<Longrightarrow> val (\<alpha> \<otimes> x[^](i::nat)) < val (\<beta> \<otimes> x[^](j::nat))"
        "val (\<alpha> \<otimes> x[^](i::nat)) > val (\<beta> \<otimes> x[^](j::nat)) 
          \<Longrightarrow> ord \<alpha> - ord \<beta> > (int j- int i)*ord x"
        "ord \<alpha> - ord \<beta> > (int j- int i)*ord x
          \<Longrightarrow> val (\<alpha> \<otimes> x[^](i::nat)) > val (\<beta> \<otimes> x[^](j::nat))"
  by(auto simp: Qp.Units_pow_closed Units_nonzero_Qp assms(1) assms(2) assms(3)
                int_distrib(3) nonzero_nat_pow_ord ord_mult)

lemma val_ineq_theta_ineq1: 
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  assumes "(i,j) \<in> ordered_ind_pairs"
  assumes "t \<ominus> c x \<noteq> \<zero>"
  shows "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) < val ((a j x)\<otimes>(t \<ominus> c x)[^]j) 
            \<Longrightarrow> val (t \<ominus> c x) > val (\<Theta>(i,j) x)"
        "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j) 
            \<Longrightarrow> val (\<Theta> (i, j) x) \<ge> val (t \<ominus> c x)"
        "val (t \<ominus> c x) > val (\<Theta> (i, j) x) \<Longrightarrow> 
          val (a i x \<otimes> (t \<ominus> c x) [^] i) < val (a j x \<otimes> (t \<ominus> c x) [^] j)"
        "val (t \<ominus> c x) \<le> val (\<Theta>(i,j) x)  \<Longrightarrow> 
            val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
proof-  
  have tx_in: "t#x \<in> condition_to_set B"
    using assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have inA0: "t#x \<in> A\<^sub>0"
    using tx_in assms B_subset by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms refined_decomp_closure by auto
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms refined_decomp_closure by auto
  have i_le_j: "i < j"
    using assms ordered_ind_pairs_def by auto 
  have in_inds: "i \<in> inds" "j \<in> inds"
    using assms ordered_ind_pairs_def ind_pairs_def by auto 
  have 0: "(int j - int i) * ord (\<Theta>(i,j) x) 
            + (ord (a i x) - ord (a j x)) mod (int j - int i)
            =  ord (a i x) - ord (a j x)"
    using x_closed \<Theta>_ord[of i j x] assms 
    by (metis (mono_tags, opaque_lifting) SA_Units_nonzero SA_div_eval
                a_cfs_closed in_inds(1) in_inds(2) inds_memE ord_fract)
  have units: "a i x \<in> Units Q\<^sub>p" "a j x \<in> Units Q\<^sub>p" "t \<ominus> c x \<in> Units Q\<^sub>p"
    using i_le_j in_inds A\<^sub>0_closures assms inA0 by auto 
  have diff_pos: "(int j - int i) > 0"
    using i_le_j by auto 
  have mod_pos: "(ord (a i x) - ord (a j x)) mod (int j - int i) \<ge> 0"
    using assms by (simp add: i_le_j)
  have ineq: "val (a i x \<otimes> (t \<ominus> c x) [^] i) \<noteq> val (a j x \<otimes> (t \<ominus> c x) [^] j)"
             "ord (a i x \<otimes> (t \<ominus> c x) [^] i) \<noteq> ord (a j x \<otimes> (t \<ominus> c x) [^] j)"
    using inA0 assms in_inds i_le_j A\<^sub>0_memE[of t x i j] by auto 
  show g1: "val (a i x \<otimes> (t \<ominus> c x) [^] i) < val (a j x \<otimes> (t \<ominus> c x) [^] j) \<Longrightarrow>
           val (\<Theta> (i, j) x) < val (t \<ominus> c x)"
  proof-
    assume A: "val (a i x \<otimes> (t \<ominus> c x) [^] i) < val (a j x \<otimes> (t \<ominus> c x) [^] j)"
    have 1: "ord (a i x) - ord (a j x) < (int j- int i)*ord (t \<ominus> c x)"
      by(rule ineq_equivalence, auto simp: units A)         
    hence 2: "(int j - int i) * ord (\<Theta>(i,j) x) <  (int j - int i)* ord(t \<ominus> c x)"
      using mod_pos 1 0 by auto   
    hence 3: "ord (\<Theta>(i,j) x) <  ord(t \<ominus> c x)"
      by (simp add: i_le_j)
    thus "val (\<Theta> (i, j) x) < val (t \<ominus> c x)"
      by (metis (mono_tags, lifting) SA_Units_memE' \<Theta>_unit assms(3) assms(4) eint_ord_simps(2) 
            val_def x_closed)
  qed
  show g2: "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j) 
            \<Longrightarrow> val (\<Theta> (i, j) x) \<ge> val (t \<ominus> c x)"
  proof-
    assume A: "val (a i x \<otimes> (t \<ominus> c x) [^] i) > val (a j x \<otimes> (t \<ominus> c x) [^] j)"
    have 1: "ord (a i x) - ord (a j x) > (int j- int i)*ord (t \<ominus> c x)"
      by(rule ineq_equivalence, auto simp: units A)         
    hence 2: "(int j - int i) * ord (\<Theta>(i,j) x) + (ord (a i x) - ord (a j x)) mod (int j - int i)
               > (int j - int i)* ord(t \<ominus> c x)"
      using mod_pos 1 0 by auto   
    hence 3: "(ord (a i x) - ord (a j x)) mod (int j - int i)
               > (int j - int i)*( ord(t \<ominus> c x) - ord (\<Theta>(i,j) x))"
      by (smt (verit, ccfv_SIG) nat_distrib(2))
    have 4: "( ord(t \<ominus> c x) - ord (\<Theta>(i,j) x)) \<le> 0"
    proof- 
      have R: "\<And> m a b::int. m > 0 \<Longrightarrow> a mod m > m*b \<Longrightarrow> b \<le> 0"
        by (smt (verit, ccfv_SIG) Euclidean_Division.pos_mod_bound mod_mult_self1_is_0 mod_pos_pos_trivial mult_less_cancel_right mult_sign_intros(1))
      show ?thesis 
        apply(rule R[of "(int j - int i)" _  "(ord (a i x) - ord (a j x)) mod (int j - int i)"])
        using i_le_j 3 by auto 
    qed
    hence 3: "ord (\<Theta>(i,j) x) \<ge>  ord(t \<ominus> c x)"
      by (simp add: i_le_j)
    thus "val (\<Theta> (i, j) x) \<ge> val (t \<ominus> c x)"
      using Units_eq_nonzero eint_ord_simps(1) eint_ord_simps(3) units(3) val_def val_ord 
      by presburger
  qed
  have "val (t \<ominus> c x) > val (\<Theta> (i, j) x) \<Longrightarrow>
          val (a i x \<otimes> (t \<ominus> c x) [^] i) \<le> val (a j x \<otimes> (t \<ominus> c x) [^] j)"
    using g2 notin_closed by blast
  thus g3: "val (t \<ominus> c x) > val (\<Theta> (i, j) x) \<Longrightarrow>
          val (a i x \<otimes> (t \<ominus> c x) [^] i) < val (a j x \<otimes> (t \<ominus> c x) [^] j)"
    using g2 ineq using ineq by auto 
  have "val (t \<ominus> c x) \<le> val (\<Theta> (i, j) x) \<Longrightarrow>
        val (a j x \<otimes> (t \<ominus> c x) [^] j) \<le> val (a i x \<otimes> (t \<ominus> c x) [^] i)"
    using g1 notin_closed by blast  
  thus g4: "val (t \<ominus> c x) \<le> val (\<Theta> (i, j) x) \<Longrightarrow>
    val (a j x \<otimes> (t \<ominus> c x) [^] j) < val (a i x \<otimes> (t \<ominus> c x) [^] i)"
    using g1 ineq using ineq by auto 
qed

lemma val_in_B0: 
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  assumes "(i,j) \<in> ordered_ind_pairs"
  assumes "t \<ominus> c x \<noteq> \<zero>"
  assumes "val (t \<ominus> c x) = val (\<Theta> (i,j) x)"
  shows "\<And>s y. s#y \<in> condition_to_set \<B> \<Longrightarrow> 
              val (s \<ominus> c y) = val (\<Theta> (i,j) y)"
proof- 
  fix s y assume A: "s#y \<in> condition_to_set \<B>"
  have sy_in: "s#y \<in> condition_to_set B"
    using A assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have s_closed: "s \<in> carrier Q\<^sub>p"
    using assms B_cell sy_in 
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(2) list.sel(1))
  have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms B_cell sy_in
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(1) list.sel(3))
  have tx_in: "t#x \<in> condition_to_set B"
    using assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms refined_decomp_closure by auto
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms refined_decomp_closure by auto
  have i_le_j: "i < j"
    using assms ordered_ind_pairs_def by auto 
  have in_inds: "i \<in> inds" "j \<in> inds"
    using assms ordered_ind_pairs_def ind_pairs_def by auto 
  have F0: "t#x \<in> A\<^sub>0"
    using tx_in assms B_subset by blast
  have F1: "t#x \<in> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) closed_interval)"
    using assms tx_in 
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd closed_interval_def
    by (simp add: SA_zeroE val_def x_closed)
  hence "condition_to_set \<B> \<subseteq> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) closed_interval)"
    using assms refined_decomp_prop 
    unfolding is_convex_condition_def refinement_functions_def 
    by blast
  hence F3: "s#y \<in> condition_to_set (Cond m b c (\<Theta>(i,j)) (\<Theta>(i,j)) closed_interval)"
    using A by auto 
  thus "val (s \<ominus> c y) = val (\<Theta> (i, j) y)"
    unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd  closed_interval_def 
    by auto 
qed

lemma val_in_B1: 
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  assumes "(i,j) \<in> ordered_ind_pairs"
  assumes "t \<ominus> c x \<noteq> \<zero>"
  assumes "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) < val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
  shows "\<And>s y. s#y \<in> condition_to_set \<B> \<Longrightarrow> 
              val ((a i y)\<otimes>(s \<ominus> c y)[^]i) < val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
proof- 
  fix s y assume A: "s#y \<in> condition_to_set \<B>"
  have sy_in: "s#y \<in> condition_to_set B"
    using A assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have s_closed: "s \<in> carrier Q\<^sub>p"
    using assms B_cell sy_in 
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(2) list.sel(1))
  have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms B_cell sy_in
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(1) list.sel(3))
  have tx_in: "t#x \<in> condition_to_set B"
    using assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms refined_decomp_closure by auto
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms refined_decomp_closure by auto
  have i_le_j: "i < j"
    using assms ordered_ind_pairs_def by auto 
  have in_inds: "i \<in> inds" "j \<in> inds"
    using assms ordered_ind_pairs_def ind_pairs_def by auto 
  have F0: "t#x \<in> A\<^sub>0"
    using tx_in assms B_subset by blast
  have F1: "val (t \<ominus> c x) > val (\<Theta>(i,j) x)"
    using val_ineq_theta_ineq1 assms by auto 
  have F2: "t#x \<in> condition_to_set (Cond m b c (\<Theta>(i,j)) \<zero>\<^bsub>SA m\<^esub> left_closed_interval)"
    using assms tx_in F1
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd left_closed_interval_def
    by (simp add: SA_zeroE val_def x_closed)
  hence "condition_to_set \<B> \<subseteq>condition_to_set (Cond m b c (\<Theta>(i,j)) \<zero>\<^bsub>SA m\<^esub> left_closed_interval)"
    using assms refined_decomp_prop 
    unfolding is_convex_condition_def refinement_functions_def 
    by blast
  hence F3: "s#y \<in> condition_to_set (Cond m b c (\<Theta>(i,j)) \<zero>\<^bsub>SA m\<^esub> left_closed_interval)"
    using A by auto 
  hence F4: "val (s \<ominus> c y) \<ge> val (\<Theta>(i,j) y)"
    unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd left_closed_interval_def
    by auto 
  have F5: "s \<ominus> c y \<noteq> \<zero>"
    using F3  unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd left_closed_interval_def
    using local.val_zero by force
  have F6: "val (s \<ominus> c y) \<noteq> val (\<Theta>(i,j) y)"
    using val_in_B0[of \<B> s y i j t x] assms A F1 
    by (metis F5 basic_trans_rules(20))
  hence F7: "val (s \<ominus> c y) > val (\<Theta>(i,j) y)"
    using F4 F6 by auto 
  show "val (a i y \<otimes> (s \<ominus> c y) [^] i) < val (a j y \<otimes> (s \<ominus> c y) [^] j)"
    apply(rule val_ineq_theta_ineq1[of \<B>])
    using assms A F7 F5 by auto 
qed
      
lemma val_in_B2: 
  assumes "\<B> \<in> refined_decomp"
  assumes "t#x \<in> condition_to_set \<B>"
  assumes "(i,j) \<in> ordered_ind_pairs"
  assumes "t \<ominus> c x \<noteq> \<zero>"
  assumes "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
  shows "\<And>s y. s#y \<in> condition_to_set \<B> \<Longrightarrow> 
              val ((a i y)\<otimes>(s \<ominus> c y)[^]i) > val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
proof-
  fix s y assume A: "s#y \<in> condition_to_set \<B>"
  have sy_in: "s#y \<in> condition_to_set B"
    using A assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have s_closed: "s \<in> carrier Q\<^sub>p"
    using assms B_cell sy_in 
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(2) list.sel(1))
  have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms B_cell sy_in
    unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq
    by (metis Qp_pow_ConsE(1) list.sel(3))
  have tx_in: "t#x \<in> condition_to_set B"
    using assms refined_decomp_prop is_cell_decomp_subset B_eq by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms refined_decomp_closure by auto
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms refined_decomp_closure by auto
  have i_le_j: "i < j"
    using assms ordered_ind_pairs_def by auto 
  have in_inds: "i \<in> inds" "j \<in> inds"
    using assms ordered_ind_pairs_def ind_pairs_def by auto 
  have F0: "t#x \<in> A\<^sub>0" "s#y \<in> A\<^sub>0"
    using tx_in sy_in assms B_subset by auto 
  have F1: "val (a j y \<otimes> (s \<ominus> c y) [^] j) \<noteq> val (a i y \<otimes> (s \<ominus> c y) [^] i)"
           "val (a j x \<otimes> (t \<ominus> c x) [^] j) \<noteq> val (a i x \<otimes> (t \<ominus> c x) [^] i)"
    using F0 A\<^sub>0_memE assms 
     apply (metis A i_le_j in_inds(1) in_inds(2) val_in_B_nonzero)
    using F0 A\<^sub>0_memE assms by auto 
  show "val (a j y \<otimes> (s \<ominus> c y) [^] j) < val (a i y \<otimes> (s \<ominus> c y) [^] i)"
    using val_in_B1[of \<B> s y i j t x] F1 assms 
    by (metis A basic_trans_rules(20) notin_closed val_in_B_zero val_ineq_theta_ineq1(3) val_ineq_theta_ineq1(4))
qed

lemma pre_val_in_B: 
  assumes "\<B> \<in> refined_decomp"
  assumes "(i,j) \<in> ordered_ind_pairs"
  shows "\<And>s y t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                  val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j)
              \<longleftrightarrow> val ((a i y)\<otimes>(s \<ominus> c y)[^]i) > val ((a j y)\<otimes>(s \<ominus> c y)[^]j) "
proof- 
  fix s y t x
  assume A: " t#x \<in> condition_to_set \<B>" "s#y \<in> condition_to_set \<B>"
  have 0: "condition_to_set \<B> \<subseteq> condition_to_set B"
    using assms B_eq is_cell_decomp_subset refined_decomp_prop by blast
  have units: "a j x \<in> Units Q\<^sub>p" "a i x \<in> Units Q\<^sub>p"  "a i y \<in> Units Q\<^sub>p" "a j y \<in> Units Q\<^sub>p"
    using  A\<^sub>0_closures A  B_subset assms 0
    unfolding ordered_ind_pairs_def ind_pairs_def by auto 
  have 1: "i \<in> inds" "j \<in> inds" "i < j"
    using assms unfolding ordered_ind_pairs_def ind_pairs_def by auto 
  show "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j)
              \<longleftrightarrow> val ((a i y)\<otimes>(s \<ominus> c y)[^]i) > val ((a j y)\<otimes>(s \<ominus> c y)[^]j) "
  proof(cases "t \<ominus> c x = \<zero>")
    case True
    then have T0: "s \<ominus> c y = \<zero>"
      using A val_in_B_zero[of \<B> t x i j] assms by auto 
    have j_pos: "j > 0"
      using assms ordered_ind_pairs_def by auto 
    hence T1: "(a j y \<otimes> \<zero> [^] j) = \<zero>" "(a j x \<otimes> \<zero> [^] j) = \<zero>"
      using assms units Qp.Units_closed Qp.pow_zero Qp.r_null 
      by auto    
    show ?thesis 
      unfolding T1 val_def True 
      using T0 T1(1) eint_ord_code(6) by presburger
  next
    case False
    then have F0: "s \<ominus> c y \<noteq> \<zero>"
      using A val_in_B_nonzero[of \<B> t x i j] assms by auto
    have F1: "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<noteq> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
          "val ((a i y)\<otimes>(s \<ominus> c y)[^]i) \<noteq> val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
      using A\<^sub>0_memE[of _ _ i j] assms A 1 
       apply (meson 0 B_subset False subset_iff)
      using A\<^sub>0_memE[of _ _ i j] assms A 1 
      by (meson "0" B_subset F0 basic_trans_rules(31))
    show ?thesis 
    proof
      show 0: "val (a j x \<otimes> (t \<ominus> c x) [^] j) < val (a i x \<otimes> (t \<ominus> c x) [^] i) \<Longrightarrow>
    val (a j y \<otimes> (s \<ominus> c y) [^] j) < val (a i y \<otimes> (s \<ominus> c y) [^] i)"
        apply(rule  val_in_B2[of \<B> t x])
        using assms A False by auto 
      show 1: "val (a j y \<otimes> (s \<ominus> c y) [^] j) < val (a i y \<otimes> (s \<ominus> c y) [^] i) \<Longrightarrow>
    val (a j x \<otimes> (t \<ominus> c x) [^] j) < val (a i x \<otimes> (t \<ominus> c x) [^] i)"
        using assms F0 A val_in_B2[of \<B> s y i j] 0 F1 by blast
    qed
  qed
qed

lemma val_in_B: 
  assumes "\<B> \<in> refined_decomp"
  assumes "i \<in> inds"
  assumes "j \<in> inds"
  assumes "i \<noteq> j"
  shows "\<And>s y t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                  val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j)
              \<longleftrightarrow> val ((a i y)\<otimes>(s \<ominus> c y)[^]i) > val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
        "\<And>t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> t \<ominus> c x \<noteq> \<zero> \<Longrightarrow>
                  val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<noteq> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
        "\<And>s y t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                  t \<ominus> c x = \<zero>
              \<longleftrightarrow> s \<ominus> c y = \<zero>"
proof- 
  have sub: "condition_to_set \<B> \<subseteq> A\<^sub>0"
    using assms B_eq B_subset is_cell_decomp_subset refined_decomp_prop by blast
  show "\<And>t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> t \<ominus> c x \<noteq> \<zero> \<Longrightarrow>
                  val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<noteq> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
  proof(cases "i < j")
    case True
    show "\<And>t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> t \<ominus> c x \<noteq> \<zero> \<Longrightarrow>
                  val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<noteq> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
       using A\<^sub>0_memE(1)[of _ _ i j] sub assms True by auto 
  next
    case False
    show "\<And>t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> t \<ominus> c x \<noteq> \<zero> \<Longrightarrow>
                  val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<noteq> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
       using A\<^sub>0_memE(1)[of _ _ j i] sub assms False 
       by (smt (z3) nat_neq_iff subset_iff)
  qed
next 
  show "\<And>s y t x.
       t # x \<in> condition_to_set \<B> \<Longrightarrow>
       s # y \<in> condition_to_set \<B> \<Longrightarrow>
       (val (a j x \<otimes> (t \<ominus> c x) [^] j) < val (a i x \<otimes> (t \<ominus> c x) [^] i)) =
       (val (a j y \<otimes> (s \<ominus> c y) [^] j) < val (a i y \<otimes> (s \<ominus> c y) [^] i))"
  proof(cases "i < j")
    case True
    then have "(i,j) \<in> ordered_ind_pairs"
      unfolding ordered_ind_pairs_def ind_pairs_def using assms by auto 
    thus "\<And>s y t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                    val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j)
                \<longleftrightarrow> val ((a i y)\<otimes>(s \<ominus> c y)[^]i) > val ((a j y)\<otimes>(s \<ominus> c y)[^]j) "
      using assms pre_val_in_B by metis 
  next
    case False
    then have ind: "(j,i) \<in> ordered_ind_pairs"
      unfolding ordered_ind_pairs_def ind_pairs_def using assms by auto 
    hence F0: "\<And>s y t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                    val ((a j x)\<otimes>(t \<ominus> c x)[^]j) > val ((a i x)\<otimes>(t \<ominus> c x)[^]i)
                \<longleftrightarrow> val ((a j y)\<otimes>(s \<ominus> c y)[^]j) > val ((a i y)\<otimes>(s \<ominus> c y)[^]i) "
      using assms pre_val_in_B by metis
    fix t x s y assume A: " t # x \<in> condition_to_set \<B>" " s # y \<in> condition_to_set \<B>"
    have inA0: "t#x \<in> A\<^sub>0" "s#y \<in> A\<^sub>0"
      using A  B_subset assms is_cell_decomp_subset refined_decomp_prop B_eq basic_trans_rules(31)
      apply metis 
      using A  B_subset assms is_cell_decomp_subset refined_decomp_prop B_eq basic_trans_rules(31)
      by metis 
    have units: "a j x \<in> Units Q\<^sub>p" "a i x \<in> Units Q\<^sub>p"  "a i y \<in> Units Q\<^sub>p" "a j y \<in> Units Q\<^sub>p"
      using  A\<^sub>0_closures(1,2) A inA0  B_subset assms A ind 
      unfolding ordered_ind_pairs_def ind_pairs_def by auto 
    show "(val (a j x \<otimes> (t \<ominus> c x) [^] j) < val (a i x \<otimes> (t \<ominus> c x) [^] i)) =
         (val (a j y \<otimes> (s \<ominus> c y) [^] j) < val (a i y \<otimes> (s \<ominus> c y) [^] i))"
    proof(cases "t \<ominus> c x = \<zero>")
      case T: True
      then have T0: "s \<ominus> c y = \<zero>"
        using ind assms A val_in_B_zero[of \<B> t x j i  s y] by auto 
      have i_pos: "i > 0"
        using ind assms ordered_ind_pairs_def by auto 
      hence T1: "(a i y \<otimes> \<zero> [^] i) = \<zero>" "(a i x \<otimes> \<zero> [^] i) = \<zero>"
        using assms A units Qp.Units_closed Qp.pow_zero Qp.r_null by auto 
      hence T2: "val (a i y \<otimes> \<zero> [^] i) = \<infinity>" "val (a i x \<otimes> \<zero> [^] i) = \<infinity>"
        using val_def by auto 
      show ?thesis 
        using units 
        unfolding T0 T2 T  
        by (metis (no_types, opaque_lifting) Qp.Units_closed Qp.Units_not_right_zero_divisor 
            Qp.cring_simprules(2) Qp.cring_simprules(27) Qp.nat_pow_closed eint.distinct(2)
            eint_ord_simps(4) val_def)
    next
      case F: False
      then have 0: "s \<ominus> c y \<noteq> \<zero>"
        using ind assms A val_in_B_nonzero[of \<B> t x j i  s y] by auto 
      have 1: "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<noteq> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
               "val ((a i y)\<otimes>(s \<ominus> c y)[^]i) \<noteq> val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
        using False F 0 inA0 assms A\<^sub>0_memE[of s y j i] A\<^sub>0_memE[of t x j i] by auto 
      then show ?thesis
        using A F0[of t x s y] by auto 
    qed
  qed
next 
  have "\<And>s y t x.  t # x \<in> condition_to_set \<B> \<Longrightarrow> s # y \<in> condition_to_set \<B> 
                \<Longrightarrow> (t \<ominus> c x = \<zero>) \<Longrightarrow> (s \<ominus> c y = \<zero>)"
  proof-
    fix t x s y assume A: " t # x \<in> condition_to_set \<B>" " s # y \<in> condition_to_set \<B>"
    show "(t \<ominus> c x = \<zero>) \<Longrightarrow> (s \<ominus> c y = \<zero>)"
    proof-
      assume B: "t \<ominus> c x = \<zero>"
      then have "t#x\<in> condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval)"
        unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd closed_interval_def
        using A 
        by (metis (mono_tags, lifting) A\<^sub>0_closed B_cell B_eq B_subset SA_zeroE assms(1) 
            cartesian_power_tail eint_ord_simps(3) list.sel(3) local.val_zero 
            padic_fields.condition_to_set_memE'(1) padic_fields.is_cell_decomp_subset 
            padic_fields_axioms refined_decomp_prop subset_iff)
      hence "condition_to_set \<B> \<subseteq> condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval)"
        using assms A refined_decomp_prop 
        unfolding is_convex_condition_def refinement_functions_def
        by blast 
      hence "s#y\<in> condition_to_set (Cond m b c \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_interval)"
        using A by auto 
      thus "s \<ominus> c y = \<zero>"
        unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd closed_interval_def
        by (metis Qp.cring_simprules(4) Qp_pow_ConsE(2) SA_car_closed SA_zeroE c_closed 
                  cartesian_power_tail list.sel(1) list.sel(3) val_ineq)
    qed
  qed
  thus "\<And>s y t x.
       t # x \<in> condition_to_set \<B> \<Longrightarrow> s # y \<in> condition_to_set \<B> \<Longrightarrow>
               (t \<ominus> c x = \<zero>) = (s \<ominus> c y = \<zero>)"
    by metis  
qed

lemma static_order: 
  assumes "\<B> \<in> refined_decomp"
  assumes "i \<in> inds"
  assumes "j \<in> inds"
  shows "\<And>s y t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                  val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<ge> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)
              \<longleftrightarrow> val ((a i y)\<otimes>(s \<ominus> c y)[^]i) \<ge> val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
proof(cases "i = j")
  case True
  then show "\<And>s y t x . t#x \<in> condition_to_set \<B> \<Longrightarrow> s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                  val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<ge> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)
              \<longleftrightarrow> val ((a i y)\<otimes>(s \<ominus> c y)[^]i) \<ge> val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
    by auto 
next
  case ne: False
  fix s y t x assume A: "t#x \<in> condition_to_set \<B>" "s#y \<in> condition_to_set \<B>"
  show "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<ge> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)
              \<longleftrightarrow> val ((a i y)\<otimes>(s \<ominus> c y)[^]i) \<ge> val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
  proof(cases "t \<ominus> c x = \<zero>")
    case True
    then have T0: "s \<ominus> c y = \<zero>"
      using A assms val_in_B(3)[of \<B> i j t x s y] ne by auto  
    show ?thesis 
      unfolding T0 True 
      apply(cases "i = 0")
       apply (smt (z3) A(1) A(2) A\<^sub>0_memE'(3) B_eq B_subset ne T0 True assms(1)
          assms(2) assms(3) bot_nat_0.not_eq_extremum eint_ord_simps(4) notin_closed
          padic_fields.is_cell_decomp_subset padic_fields_axioms refined_decomp_prop
          subset_iff val_in_B(1))
      apply(cases "j = 0")
       apply (smt (verit) A(1) A(2) A\<^sub>0_memE'(3) B_eq B_subset T0 True assms(1) assms(2)
          assms(3) basic_trans_rules(31) bot_nat_0.not_eq_extremum eint_ord_simps(3) 
          padic_fields.is_cell_decomp_subset padic_fields_axioms refined_decomp_prop)
      by (smt (z3) A(1) A(2) A\<^sub>0_closures(2) B_eq B_subset Qp.Units_closed 
          Qp.cring_simprules(27) Qp.nat_pow_zero assms(1) assms(2) assms(3) 
          padic_fields.is_cell_decomp_subset padic_fields_axioms refined_decomp_prop subset_iff)
  next
    case False
    have F0: "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) > val ((a j x)\<otimes>(t \<ominus> c x)[^]j)
              \<longleftrightarrow> val ((a i y)\<otimes>(s \<ominus> c y)[^]i) > val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
      using A assms val_in_B(1)[of \<B> i j t x s y] by auto 
    have F1: "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) \<noteq> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
      using ne False A assms val_in_B(2)[of \<B> i j t x] by auto 
    have F2: "val ((a i y)\<otimes>(s \<ominus> c y)[^]i) \<noteq> val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
      using False A ne assms val_in_B(3)[of \<B> i j t x s y] val_in_B(2)[of \<B> i j s y] by auto
    show ?thesis 
      using F1 F2 F0 by auto 
  qed
qed

lemma exists_uniform_i0:
  assumes "\<B> \<in> refined_decomp"
  assumes "inds \<noteq> {}"
  shows "\<exists>i\<^sub>0 \<in> inds . (\<forall>j. \<forall>t. \<forall>x. t#x \<in> condition_to_set \<B> 
          \<longrightarrow> val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j))"
proof(cases "condition_to_set \<B> = {}")
  case True
  then show ?thesis using assms by blast  
next
  case False
  have R: "\<And> xs. xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> \<exists> t x. xs = t#x"
  proof- 
    have "\<And> xs. xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> length xs > 0"
      by (simp add: cartesian_power_car_memE)
    thus "\<And> xs. xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> \<exists> t x. xs = t#x"
      by (meson cartesian_power_car_memE length_Suc_conv)
  qed
  have bsub: "condition_to_set \<B> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using assms refined_decomp_prop 
    by (metis is_cellI is_cell_decompE(3) is_cell_decompE(4) is_cell_subset)
  then obtain t x where tx_def: "t#x \<in> condition_to_set \<B>"
    using False R by blast 
  have "\<exists>i\<^sub>0 \<in> inds. val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) = (MIN i\<in>inds. (val ( (a i x)\<otimes>(t \<ominus> c x)[^]i)))"
    using assms Min_in inds_finite 
    by (smt (verit, best) finite_imageI imageE image_is_empty)
  then obtain i\<^sub>0 where i\<^sub>0_def: "i\<^sub>0 \<in> inds \<and>
        val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) = (MIN i\<in>inds. (val ( (a i x)\<otimes>(t \<ominus> c x)[^]i)))"
    by blast 
  have i\<^sub>0_in: "i\<^sub>0 \<in> inds"
    using i\<^sub>0_def by auto 
  have i\<^sub>0_min: "\<And> j. j \<in> inds \<Longrightarrow> val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ( (a j x)\<otimes>(t \<ominus> c x)[^]j)"
    using inds_finite i\<^sub>0_in i\<^sub>0_def by auto 
  have d: "\<forall>j .
          \<forall>s y. s # y \<in> condition_to_set \<B> \<longrightarrow>
                val (a i\<^sub>0 y \<otimes> (s \<ominus> c y) [^] i\<^sub>0) \<le> val (a j y \<otimes> (s \<ominus> c y) [^] j)"
  proof- 
    have d0: "\<And> j s y. j \<notin> inds \<Longrightarrow>  s # y \<in> condition_to_set \<B> \<Longrightarrow>
                val (a i\<^sub>0 y \<otimes> (s \<ominus> c y) [^] i\<^sub>0) \<le> val (a j y \<otimes> (s \<ominus> c y) [^] j)"
    proof- 
      fix j s y assume A: " j \<notin> inds" "s # y \<in> condition_to_set \<B>"
      have diff: "s \<ominus> c y \<in> carrier Q\<^sub>p"
        using A 
        by (metis (no_types, lifting) Qp.cring_simprules(4) Qp_pow_ConsE(2) SA_car_closed bsub
            c_closed cartesian_power_tail list.sel(1) list.sel(3) subsetD)
      have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A bsub cartesian_power_tail by fastforce
      have zero: "a j y = \<zero>"
        using A y_closed inds_non_memE[of j y] y_closed by auto 
      have inf: "val (a j y \<otimes> (s \<ominus> c y) [^] j) = \<infinity>"
        using diff unfolding zero val_def by auto 
      show "val (a i\<^sub>0 y \<otimes> (s \<ominus> c y) [^] i\<^sub>0) \<le> val (a j y \<otimes> (s \<ominus> c y) [^] j)"
        unfolding inf by auto 
    qed
    have d1: "\<And> j s y. j \<in>  inds \<Longrightarrow>  s # y \<in> condition_to_set \<B> \<Longrightarrow>
                val (a i\<^sub>0 y \<otimes> (s \<ominus> c y) [^] i\<^sub>0) \<le> val (a j y \<otimes> (s \<ominus> c y) [^] j)"
      using assms i\<^sub>0_min tx_def i\<^sub>0_in static_order[of \<B> _ i\<^sub>0] i\<^sub>0_in by smt  
    show ?thesis 
      using d0 d1 by smt  
  qed
  show ?thesis
    by(rule bexI[of _ i\<^sub>0], rule d, rule i\<^sub>0_in)
qed

lemma exists_uniform_i:
  assumes "\<B> \<in> refined_decomp"
  shows "\<exists>i\<^sub>0 . (\<forall>j. \<forall>t. \<forall>x. t#x \<in> condition_to_set \<B> 
          \<longrightarrow> val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j))"
proof(cases "inds = {}")
  case True
  have "\<And> j t x. t#x \<in> condition_to_set \<B> \<Longrightarrow> val ((a j x)\<otimes>(t \<ominus> c x)[^]j) = \<infinity>"
  proof- 
    fix j t x assume A: "t#x \<in> condition_to_set \<B>"
    have 0: "t \<ominus> c x \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p"
      using A assms refined_decomp_closure by auto
    have 1: "a j x = \<zero>"
      using A True inds_non_memE 0 by auto 
    show "val (a j x \<otimes> (t \<ominus> c x) [^] j) = \<infinity> "
      using 0 unfolding 1 val_def  by auto 
  qed
  thus ?thesis by auto 
next
  case False
  then show ?thesis using assms exists_uniform_i0 by blast  
qed
end

context common_refinement_locale
begin


definition has_minimal_i where
"has_minimal_i \<B> = (\<exists>i\<^sub>0 . (\<forall>j. \<forall>t. \<forall>x. t#x \<in> condition_to_set \<B> 
          \<longrightarrow> val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)))"

text\<open>This lemma statement is long-winded because we need to simultaneously extract a piece of
      information relevant to the proof of cell decomposition theorem $I$ as well as one relevant
      to theorem II.\<close>

lemma A\<^sub>0_comp_minimal_i_decomp:
  assumes "inds \<noteq> {}"
  shows "\<exists> S. is_cell_decomp m S (condition_to_set \<C> - A\<^sub>0) \<and> 
              (\<forall> \<B> \<in> S. has_minimal_i \<B> \<and> 
                        (\<exists> \<phi> i\<^sub>0. \<phi> \<in> Units (SA m) \<and> center \<B> = c \<and> l_bound \<B> = \<phi>  \<and>
                                     u_bound \<B> = \<phi> \<and> boundary_condition \<B> = closed_interval \<and> 
                                   (\<forall>j. \<forall>t. \<forall>x.
                                   t#x \<in> condition_to_set \<B> \<longrightarrow>
                                   val ((a i\<^sub>0 x)\<otimes>(\<phi> x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(\<phi> x)[^]j))))"
proof-
  obtain S where S_def: "(is_cell_decomp m S (condition_to_set \<C> - A\<^sub>0) \<and>
                           (\<forall>B\<in>S. (\<exists> \<phi>. \<phi> \<in> Units (SA m) \<and> center B = c \<and> l_bound B = \<phi>  \<and>
                                         u_bound B = \<phi> \<and> boundary_condition B = closed_interval)))"
    using A\<^sub>0_comp_decomp by blast 
  show ?thesis 
    apply(rule refine_each_cell[of _ S])
    using S_def apply blast  
  proof- 
    fix B assume A: "B \<in> S"
    obtain b where b_def: "b = fibre_set B"
      by blast 
    obtain \<phi> where \<phi>_def: " \<phi> \<in> Units (SA m) \<and> center B = c \<and> l_bound B = \<phi> \<and> u_bound B = \<phi> \<and>
                             boundary_condition B = closed_interval"
      using A S_def by blast 
    have B_eq: "B = Cond m b c \<phi> \<phi> closed_interval"
      using A \<phi>_def b_def condition_decomp' S_def is_cell_decompE(4) 
      by metis 
    have  \<phi>_closed: "\<phi> \<in> carrier (SA m)"
      using \<phi>_def SA_Units_closed by blast 
    have \<phi>_nonzero: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<phi> x \<noteq> \<zero>"
      using \<phi>_def SA_Units_memE' by blast
    have \<phi>_nonzero': "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<phi> x \<in> nonzero Q\<^sub>p"
      using \<phi>_closed \<phi>_nonzero SA_car_memE(3) unfolding nonzero_def by blast 
    have B_cell_cond: "is_cell_condition B"
      using A S_def is_cell_decompE by meson 
    have B0_semialg: "is_semialgebraic m b"
      using B_eq B_cell_cond is_cell_conditionE by blast
    obtain H where H_def: "H = (\<lambda>i. a i \<otimes>\<^bsub>SA m\<^esub>\<phi>[^]\<^bsub>SA m\<^esub> i)"
      by blast 
    have H_closed: "\<And> i. i \<in> inds \<Longrightarrow>  H i \<in> carrier (SA m)"
      unfolding H_def using inds_memE \<phi>_closed SA_Units_closed[of _ m]
      by blast
    have H_unit: "\<And>i. i \<in> inds \<Longrightarrow> H i \<in> Units (SA m)"
      unfolding H_def using inds_memE \<phi>_def R.Units_pow_closed by blast
    have H_eval: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x = a i x \<otimes> (\<phi> x [^] i)"
      unfolding H_def using \<phi>_closed inds_memE a_closed SA_mult SA_nat_pow by presburger
    have H_nonzero: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x \<noteq> \<zero>"
      using H_unit SA_Units_memE' by blast            
    have H_nonzero': "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x \<in> nonzero Q\<^sub>p"
      unfolding nonzero_def mem_Collect_eq using SA_car_memE(3) H_closed H_nonzero by blast 
    have H_ord: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (H i x) = ord (a i x) + i*ord(\<phi> x)"
      using H_eval \<phi>_nonzero inds_memE ord_mult nonzero_nat_pow_ord 
      by (metis Qp_nat_pow_nonzero SA_Units_nonzero \<phi>_nonzero')
    have H_val: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> val (H i x) = val (a i x) + val (\<phi> x [^] i)"
      using  \<phi>_nonzero inds_memE  H_eval val_mult 
      by (metis Qp_nat_pow_nonzero SA_Units_nonzero \<phi>_nonzero' val_mult0)
    have b_semialg: "is_semialgebraic m b"
      using b_def B0_semialg by linarith
    have "\<exists>Bs. finite Bs \<and> Bs partitions b \<and> (\<forall>b\<in>Bs. is_semialgebraic m b \<and> static_order_type (H ` inds) b)"
      apply(rule static_order_type_decomp[of "H ` inds" m b])
      using inds_finite apply blast 
      using H_unit apply blast
      using b_semialg  by auto 
    then obtain Bs0 where Bs0_def: 
      "finite Bs0 \<and> Bs0 partitions b \<and> (\<forall>b\<in>Bs0. is_semialgebraic m b \<and>
                                 static_order_type (H ` inds) b)"
      by blast 
    obtain Bs where Bs_def: "Bs = Bs0 - {{}}"
      by blast 
    have Bs_finite: "finite Bs"
      using Bs_def Bs0_def  by blast
    have Bs_semialg: "\<And>b. b \<in> Bs \<Longrightarrow> is_semialgebraic m b"
      using Bs_def Bs0_def  by blast 
    have Bs_partitions: "Bs partitions b"
      unfolding Bs_def apply(rule is_partitionI)
      using Bs0_def is_partitionE Generated_Boolean_Algebra.disjoint_def apply fastforce
      using Bs0_def is_partitionE(2)[of Bs0 b] by auto 
    have Bs_covers: "\<Union> Bs = b"
      using Bs_partitions is_partitionE[of Bs b] by auto 
    have Bs_static_order_type: "\<And>b'. b' \<in> Bs \<Longrightarrow> static_order_type (H ` inds) b'"
      using Bs_def Bs0_def by auto 
    have B_vals: "\<And>x. x \<in> condition_to_set B \<Longrightarrow> val (hd x \<ominus> c (tl x)) = val (\<phi> (tl x))"
      apply(rule basic_trans_rules(24))
      unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq closed_interval_def
       apply blast by blast 
    obtain S' where S'_def: "S' = refine_fibres B ` Bs"
      by blast 
    have S'_decomp: "is_cell_decomp m S' (condition_to_set B)"
      apply(unfold S'_def, rule partition_to_cell_decomp[of B m b c \<phi> \<phi> closed_interval] )
      unfolding are_semialgebraic_def 
      using B_cell_cond B_eq Bs_partitions Bs_finite Bs_semialg by auto 
    have "(\<forall>\<B>\<in>S'. has_minimal_i \<B> \<and>
                     (\<exists>\<phi> i\<^sub>0. \<phi> \<in> Units (SA m) \<and>
                           center \<B> = c \<and>
                           l_bound \<B> = \<phi> \<and> u_bound \<B> = \<phi> \<and> boundary_condition \<B> = closed_interval \<and> 
                            (\<forall>j. \<forall>t. \<forall>x.
                                   t#x \<in> condition_to_set \<B> \<longrightarrow>
                                   val ((a i\<^sub>0 x)\<otimes>(\<phi> x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(\<phi> x)[^]j))))"
    proof
      fix \<B> assume a: "\<B> \<in> S'"
      obtain b0 where b0_def: "b0 = fibre_set \<B>"
        by blast 
      have b0_in: "b0 \<in> Bs"
        using b0_def a unfolding S'_def refine_fibres_def by auto 
      have \<phi>_fact:  " \<phi> \<in> Units (SA m) \<and>  center \<B> = c \<and> l_bound \<B> = \<phi> \<and> u_bound \<B> = \<phi> \<and>
                     boundary_condition \<B> = closed_interval"
        using a S'_def \<phi>_def unfolding B_eq refine_fibres_def 
        by auto
      show "has_minimal_i \<B> \<and> (\<exists>\<phi> i\<^sub>0. \<phi> \<in> Units (SA m) \<and>
                           center \<B> = c \<and>
                           l_bound \<B> = \<phi> \<and> u_bound \<B> = \<phi> \<and> boundary_condition \<B> = closed_interval \<and> 
                            (\<forall>j. \<forall>t. \<forall>x.
                                   t#x \<in> condition_to_set \<B> \<longrightarrow>
                                   val ((a i\<^sub>0 x)\<otimes>(\<phi> x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(\<phi> x)[^]j)))"
      proof(cases "condition_to_set \<B> = {}")
        case True
        show ?thesis
          using \<phi>_fact unfolding has_minimal_i_def True  by auto
      next
        case False
        obtain xs where xs_def: "xs \<in> condition_to_set \<B>"
          using False by blast 
        have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
          by (meson xs_def a S'_decomp is_cell_decompE is_cell_decomp_subset subset_iff)
        obtain t x where tx_def: "xs = t#x"
          by (metis xs_closed Suc_length_conv cartesian_power_car_memE)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using tx_def xs_closed Qp_pow_ConsE(1) by force
        have x_in_b0: "x \<in> b0"
          using xs_def b0_def unfolding tx_def 
          by (metis cell_formula(2) condition_decomp' condition_to_set.simps)
        have ex: "\<exists>i\<^sub>0 \<in> inds. val ((a i\<^sub>0 x)\<otimes>(\<phi> x)[^]i\<^sub>0) = 
                        (MIN i\<in>inds. (val ((a i x)\<otimes>(\<phi> x)[^]i)))"
          by (smt (verit, best) assms Min_in inds_finite finite_imageI imageE image_is_empty)
        then obtain i\<^sub>0 where i\<^sub>0_def: "i\<^sub>0 \<in> inds \<and> val ((a i\<^sub>0 x)\<otimes>(\<phi> x)[^]i\<^sub>0) = 
                        (MIN i\<in>inds. (val ((a i x)\<otimes>(\<phi> x)[^]i)))"
          by blast 
        have i\<^sub>0_ineq: "\<And> j. j \<in> inds \<Longrightarrow>  val ((a i\<^sub>0 x)\<otimes>(\<phi> x)[^]i\<^sub>0) \<le>  val ((a j x)\<otimes>(\<phi> x)[^]j)"
        proof- fix j assume inds: "j \<in> inds"
          show " val (a i\<^sub>0 x \<otimes> \<phi> x [^] i\<^sub>0) \<le> val (a j x \<otimes> \<phi> x [^] j)"
            using inds i\<^sub>0_def MinE inds_finite by auto 
        qed
        have i\<^sub>0_ineq': "\<And> j s y. s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                   val ((a i\<^sub>0 y)\<otimes>(s \<ominus> c y)[^]i\<^sub>0) \<le>  val ((a j y)\<otimes>(s \<ominus> c y)[^]j)"
                      "\<And> j s y. s#y \<in> condition_to_set \<B> \<Longrightarrow> 
                               val ((a i\<^sub>0 y)\<otimes>(\<phi> y)[^]i\<^sub>0) \<le>  val ((a j y)\<otimes>(\<phi> y)[^]j)"
        proof- 
          fix j s y assume b: " s#y \<in> condition_to_set \<B>"
          have sy_closed: "s#y \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
            by (meson b a S'_decomp is_cell_decompE is_cell_decomp_subset subset_iff)
          have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
            using sy_closed Qp_pow_ConsE(1) by force
          have y_in_b0: "y \<in> b0"
            by (metis b b0_def cell_formula(2) condition_decomp' condition_to_set.simps)
          have diff: "s \<ominus> c y \<in> carrier Q\<^sub>p"
              using y_closed b 
              by (metis Qp.cring_simprules(4) Qp_pow_ConsE(2) SA_car_closed list.sel(1) 
                  sy_closed common_refinement_locale.c_closed common_refinement_locale_axioms)
          have phiy: "\<phi> y \<in> carrier Q\<^sub>p"
            using y_closed SA_car_closed \<phi>_closed by auto
          have "val (a i\<^sub>0 y \<otimes> (s \<ominus> c y) [^] i\<^sub>0) \<le> val (a j y \<otimes> (s \<ominus> c y) [^] j) \<and>
                  val ((a i\<^sub>0 y)\<otimes>(\<phi> y)[^]i\<^sub>0) \<le>  val ((a j y)\<otimes>(\<phi> y)[^]j)"
          proof(cases "j \<in> inds")
            case True
            have 0: "val (H i\<^sub>0 x) \<le> val (H j x)"
              unfolding H_def using True i\<^sub>0_ineq[of j] x_closed 
              using H_def H_eval i\<^sub>0_def by fastforce
            hence i\<^sub>0_inds: "i\<^sub>0 \<in> inds"
              using i\<^sub>0_def True x_closed inds_non_memE[of i\<^sub>0 x] unfolding H_def
              by force
            hence 1: "val (H i\<^sub>0 y) \<le> val (H j y)"
              using Bs_static_order_type[of b0] b0_in i\<^sub>0_inds True 
              by (smt (z3) 0 basic_trans_rules(20) image_eqI notin_closed 
                              static_order_type_def x_in_b0 y_in_b0)
            have 2: "val (s \<ominus> c y) = val (\<phi> y)"
              using B_vals[of "t#x"] B_vals[of "s#y"] b xs_def a S'_decomp
              unfolding list_tl list_hd tx_def 
              by (meson basic_trans_rules(31) is_cell_decomp_subset)
            have 3: "H i\<^sub>0 y = (a i\<^sub>0 y)\<otimes>(\<phi> y)[^]i\<^sub>0" "H j y = (a j y)\<otimes>(\<phi> y)[^]j"
              using H_eval i\<^sub>0_inds y_closed True by auto 
            have un: "\<phi> y \<in> Units Q\<^sub>p"
              using y_closed Units_eq_nonzero \<phi>_nonzero' by blast
            show "val (a i\<^sub>0 y \<otimes> (s \<ominus> c y) [^] i\<^sub>0) \<le> val (a j y \<otimes> (s \<ominus> c y) [^] j) \<and>
                  val ((a i\<^sub>0 y)\<otimes>(\<phi> y)[^]i\<^sub>0) \<le>  val ((a j y)\<otimes>(\<phi> y)[^]j)"
              using 1 2 diff H_val H_ord un 
              by (smt (verit, ccfv_SIG) "3"(1) "3"(2) Qp.nat_pow_closed True Units_eq_nonzero
                  a_eval equal_val_imp_equal_ord(2) i\<^sub>0_inds val_mult val_of_power y_closed)
          next
            case False
            have F1: "a j y = \<zero>"
              using False inds_non_memE y_closed by auto 
            show "val (a i\<^sub>0 y \<otimes> (s \<ominus> c y) [^] i\<^sub>0) \<le> val (a j y \<otimes> (s \<ominus> c y) [^] j) \<and>
                  val ((a i\<^sub>0 y)\<otimes>(\<phi> y)[^]i\<^sub>0) \<le>  val ((a j y)\<otimes>(\<phi> y)[^]j)"
              using diff phiy unfolding F1 val_def by auto 
          qed
          thus "val (a i\<^sub>0 y \<otimes> (s \<ominus> c y) [^] i\<^sub>0) \<le> val (a j y \<otimes> (s \<ominus> c y) [^] j)"
               " val ((a i\<^sub>0 y)\<otimes>(\<phi> y)[^]i\<^sub>0) \<le>  val ((a j y)\<otimes>(\<phi> y)[^]j)"
            by auto 
        qed
        thus "has_minimal_i \<B> \<and>
       (\<exists>\<phi> i\<^sub>0. \<phi> \<in> Units (SA m) \<and> center \<B> = c \<and> l_bound \<B> = \<phi> \<and> u_bound \<B> = \<phi> \<and>
                                   boundary_condition \<B> = closed_interval \<and>
              (\<forall>j t x. t # x \<in> condition_to_set \<B> \<longrightarrow> 
                          val (a i\<^sub>0 x \<otimes> \<phi> x [^] i\<^sub>0) \<le> val (a j x \<otimes> \<phi> x [^] j)))"
          by (metis \<phi>_fact has_minimal_i_def)
      qed
    qed
    thus "\<exists>S. is_cell_decomp m S (condition_to_set B) \<and>
             (\<forall>\<B>\<in>S. has_minimal_i \<B> \<and>
                     (\<exists>\<phi> i\<^sub>0. \<phi> \<in> Units (SA m) \<and>
                           center \<B> = c \<and>
                           l_bound \<B> = \<phi> \<and> u_bound \<B> = \<phi> \<and> boundary_condition \<B> = closed_interval \<and> 
                            (\<forall>j. \<forall>t. \<forall>x.
                                   t#x \<in> condition_to_set \<B> \<longrightarrow>
                                   val ((a i\<^sub>0 x)\<otimes>(\<phi> x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(\<phi> x)[^]j))))"
      using S'_decomp by auto 
  qed
qed

lemma A\<^sub>0_minimal_i_decomp:
  assumes "inds \<noteq> {}"
  shows "\<exists> S. is_cell_decomp m S A\<^sub>0 \<and> (\<forall> \<B> \<in> S. center \<B> = c \<and> has_minimal_i \<B>)"
proof- 
  obtain S where S_def: " is_cell_decomp m S A\<^sub>0 \<and> 
              (\<forall>B\<in>S. center B = c \<and> 
              (\<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N))"
    using A\<^sub>0_decomp assms by auto 
  show ?thesis 
  proof(rule refine_each_cell[of m S])
    show " is_cell_decomp m S A\<^sub>0"
      using S_def by auto 
    fix B assume A: "B \<in> S"
    have B_center: "center B = c"
      using S_def A by auto 
    have sub: "condition_to_set B \<subseteq> A\<^sub>0"
      using A S_def is_cell_decomp_subset[of m S A\<^sub>0] by auto 
    have cell: "is_cell_condition B"
      using A S_def is_cell_decompE by auto 
    obtain b b1 b2 J where params: "B = Cond m b c b1 b2 J"
      using A S_def B_center condition_decomp' is_cell_decompE(4) by blast
    have 0: "A\<^sub>0_refinement p d \<C> A c a1 a2 I f m B b b1 b2 J"
      using sub cell params 
      by (meson A\<^sub>0_refinement.intro A\<^sub>0_refinement_axioms.intro common_refinement_locale_axioms)
    show "\<exists>S. is_cell_decomp m S (condition_to_set B) \<and> (\<forall>\<B>\<in>S. center \<B> = c \<and> has_minimal_i \<B>)"
      using 0 A\<^sub>0_refinement.exists_uniform_i Q\<^sub>p_def Z\<^sub>p_def A\<^sub>0_refinement.refined_decomp_prop
      by (smt (z3) params common_refinement_locale.has_minimal_i_def common_refinement_locale_axioms)
  qed
qed

lemma \<C>_comp_minimal_i_decomp:
  shows "\<exists> S. is_cell_decomp m S (condition_to_set \<C>) \<and> (\<forall> \<B> \<in> S. center \<B> = c \<and> has_minimal_i \<B>)"
proof- 
  have A: "is_cell_decomp m {\<C>} (condition_to_set \<C>)"
    using \<C>_cond \<C>_def arity.simps condition_to_set_cell_decomp by blast
  show ?thesis 
  proof(cases "inds = {}")
    case True
    have "\<And> t x j. t # x \<in> condition_to_set \<C> ==>
               val (a j x \<otimes> (t \<ominus> c x) [^] j) = \<infinity>"
    proof- 
      fix t x j
      assume A: "t#x \<in> condition_to_set \<C>"
      have 0: "a j x = \<zero>"
        using inds_non_memE  A unfolding True 
        by (metis \<C>_memE(1) empty_iff list.sel(3))
      have 1: "(t \<ominus> c x) \<in> carrier Q\<^sub>p"
        using A 
        by (metis Qp.cring_simprules(4) SA_car_closed \<C>_cond \<C>_def \<C>_mem_hd cartesian_power_tail
            cell_condition_set_memE(1) list.sel(1) list.sel(3) common_refinement_locale.c_closed common_refinement_locale_axioms)
      show "val (a j x \<otimes> (t \<ominus> c x) [^] j) = \<infinity>"
        using 1 unfolding 0 val_def by auto 
    qed
    hence "has_minimal_i \<C>"
      unfolding has_minimal_i_def by auto 
    thus "\<exists>S. is_cell_decomp m S (condition_to_set \<C>) \<and> (\<forall>\<B>\<in>S. center \<B> = c \<and> has_minimal_i \<B>)"
      using A \<C>_def center.simps by auto 
  next
    case False
    show ?thesis 
    proof(rule binary_refinement[of _ "{\<C>}"], rule A)
      have "is_semialgebraic (Suc m) A\<^sub>0 \<and>
              A\<^sub>0 \<subseteq> condition_to_set \<C> \<and>
              (\<exists>S. is_cell_decomp m S A\<^sub>0 \<and> (\<forall>\<B>\<in>S. center \<B> = c \<and> has_minimal_i \<B>)) \<and>
              (\<exists>S. is_cell_decomp m S (condition_to_set \<C> - A\<^sub>0) \<and>
                   (\<forall>\<B>\<in>S. center \<B> = c \<and> has_minimal_i \<B>))"
        using A\<^sub>0_semialg A\<^sub>0_def A\<^sub>0_minimal_i_decomp A\<^sub>0_comp_minimal_i_decomp False by auto
      thus "\<And>C. C \<in> {\<C>} \<Longrightarrow>
         \<exists>C0. is_semialgebraic (Suc m) C0 \<and>
              C0 \<subseteq> condition_to_set C \<and>
              (\<exists>S. is_cell_decomp m S C0 \<and> (\<forall>\<B>\<in>S. center \<B> = c \<and> has_minimal_i \<B>)) \<and>
              (\<exists>S. is_cell_decomp m S (condition_to_set C - C0) \<and>
                   (\<forall>\<B>\<in>S. center \<B> = c \<and> has_minimal_i \<B>))" by auto 
    qed
  qed
qed
end
end

