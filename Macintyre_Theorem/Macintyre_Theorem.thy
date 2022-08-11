theory Macintyre_Theorem
  imports Denef_Cell_Decomp_Theorem_II_Induct
begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Macintyre's Theorem\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context padic_fields
begin

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Preliminary Lemmas for the Proof of Macintyre's Theorem\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma pow_res_classes_disjoint:
  "\<And>n. n > 0 \<Longrightarrow>  disjoint (pow_res_classes n \<union> {{\<zero>}})"  
proof(rule disjointI)
  fix n A B assume A: "n > 0" "A \<in> pow_res_classes n \<union> {{\<zero>}}" "B \<in> pow_res_classes n \<union> {{\<zero>}}" "A \<noteq> B"
  show "A \<inter> B = {}"
  proof(cases "A = {\<zero>}")
    case True
    then have T0: "B \<in> pow_res_classes n"
      using A by blast 
    then show ?thesis using pow_res_nonzero
      unfolding True pow_res_classes_def 
      by (metis (no_types, lifting) A(1) A(4) Int_emptyI T0 True pow_res_classes_mem_eq pow_res_zero singletonD)
  next
    case False
    show ?thesis 
    proof(cases "B = {\<zero>}")
      case True
      then have T0: "A \<in> pow_res_classes n"
        using A by blast 
      then show ?thesis using pow_res_nonzero
        unfolding True pow_res_classes_def 
        by (metis (no_types, lifting) A(1) A(4) Int_emptyI T0 True pow_res_classes_mem_eq pow_res_zero singletonD)
    next
      case F: False
      have F0: "A \<in> pow_res_classes n"
        using False A by blast 
      have F1: "B \<in> pow_res_classes n"
        using F A by blast 
      obtain a where a_def: "a \<in> nonzero Q\<^sub>p \<and> A = pow_res n a"
        using F0 A unfolding pow_res_classes_def by blast 
      obtain b where b_def: "b \<in> nonzero Q\<^sub>p \<and> B = pow_res n b"
        using F1 A unfolding pow_res_classes_def by blast 
      have F2: "pow_res n a \<inter> pow_res n b = {}"
        using a_def b_def A(4) pow_res_refl 
        by (metis A(1) F0 F1 Int_emptyI pow_res_classes_mem_eq)
      then show ?thesis using a_def b_def by blast 
    qed
  qed
qed

lemma denef_cell_decomp_II:
  assumes "finite Fs"
  assumes "Fs \<subseteq> carrier (UP (SA m))"
  assumes "n > 0"
  shows "\<exists> S. (is_cell_decomp m S (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))) \<and> 
                           (\<forall>A \<in> S. \<forall>P \<in> Fs. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k)"
proof- 
  obtain d where d_def: "d = Max (deg (SA m) ` Fs)"
    by blast 
  have dE: "\<And>f. f \<in> Fs \<Longrightarrow> deg (SA m) f \<le> d"
    unfolding d_def apply(rule Max_ge) using assms apply blast
    by blast 
  have 0: "denef_II p d"
    using denef_cell_decomp_II by blast 
  have 1: " finite Fs \<and> (\<forall>P\<in>Fs. P \<in> carrier (UP (SA m)) \<and> deg (SA m) P \<le> d) \<and> 0 < n"
    using assms dE by blast 
  have 2: "\<exists>S. is_cell_decomp m S (carrier (Frac (padic_int p)\<^bsup>Suc m\<^esup>)) \<and>
             (\<forall>A\<in>S. \<forall>P\<in>Fs. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k)"
  proof-
    have "finite Fs \<and> (\<forall>P\<in>Fs. P \<in> carrier (UP (SA m)) \<and> deg (SA m) P \<le> d) \<and> 0 < n \<longrightarrow>
        (\<exists>S. is_cell_decomp m S (carrier (Frac (padic_int p)\<^bsup>Suc m\<^esup>)) \<and>
             (\<forall>A\<in>S. \<forall>P\<in>Fs. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k))"
    using 1 0 assms  unfolding denef_II_def denef_II_axioms_def by blast 
    thus ?thesis using 1 by blast 
  qed
  show ?thesis 
    using 2  unfolding denef_II_def denef_II_axioms_def Q\<^sub>p_def Zp_def by blast 
qed

lemma SA_poly_factors_div: 
  assumes "\<exists>u h k. SA_poly_factors p m n P c A u h k"
  assumes "n mod l = 0"
  assumes "n > 0"
  shows  "\<exists>u h k. SA_poly_factors p m l P c A u h k"
proof-
  obtain u h k where uhk_def: "SA_poly_factors p m n P c A u h k"
    using assms by blast 
  hence 1: "l dvd n"
    using assms(2) 
    by blast
  obtain j where j_def: "l*j = n"
    using  1  by blast 
  obtain v where v_def: "v = (\<lambda>xs. (u xs)[^]j)"
    by blast 
  have u_closed: "u \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    using uhk_def unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  by blast 
  have u_val: "\<And>t x. t#x \<in> A \<Longrightarrow> val (u (t#x)) = 0"
    using uhk_def SA_poly_factorsE by blast 
  have v_val: "\<And>t x. t#x \<in> A \<Longrightarrow> val (v (t#x)) = 0"
    unfolding v_def apply(rule val_zero_imp_val_pow_zero)
    using uhk_def SA_poly_factorsE(3) apply blast
    by(rule u_val)
  have v_closed: "v \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    unfolding v_def apply(rule )
    using u_closed by blast 
  have "SA_poly_factors p m l P c A v h k"
    apply(rule SA_poly_factorsI)
    using uhk_def  SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def apply metis 
       apply(rule v_closed)
    using uhk_def  SA_poly_factors_closure(3) apply blast
    using uhk_def  SA_poly_factors_closure(4) apply blast
    apply(rule conjI)
    using v_val apply blast
  proof- fix t x assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p" "t # x \<in> A"
    have 0: "SA_poly_to_Qp_poly m x P \<bullet> t = u (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> c x) [^] k"
      using uhk_def SA_poly_factorsE(2)[of m n P c A u h k] A by blast 
    have 1: "u (t # x) [^] (j*l) = v (t # x) [^] l"
      unfolding v_def 
      using A uhk_def SA_poly_factorsE(3)[of m n P c A u h k t x] j_def Qp_nat_pow_pow by blast
    have 2: "j*l = l * j"
      by auto 
    have 3: "u (t # x) [^] n = v (t # x) [^] l"
      using 1  unfolding v_def j_def 2 by blast 
    show "SA_poly_to_Qp_poly m x P \<bullet> t = v (t # x) [^] l \<otimes> h x \<otimes> (t \<ominus> c x) [^] k"
      unfolding 0 3 by blast 
  qed
  thus ?thesis by blast 
qed

lemma div: 
  assumes "finite (Fs::nat set)"
  assumes "l = Lcm Fs"
  shows "\<And>a. a \<in> Fs \<Longrightarrow> l mod a = 0"
proof- 
  fix a assume A: "a \<in> Fs"
  have 0: "a dvd l"
    unfolding assms using assms 
    using A dvd_Lcm by blast
  show "l mod a = 0"
    using 0 
    by simp
qed

lemma macintyre_union:
  assumes "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> A)}"
  assumes "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> B)}"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> (A \<union> B))}"
proof- 
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> (A \<union> B))} = 
       {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> A)} \<union> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> B)}"
    apply(rule equalityI') unfolding mem_Collect_eq apply blast
    by blast 
  show ?thesis unfolding 0
    apply(rule union_is_semialgebraic)
     apply(rule assms)
    by(rule assms)
qed

lemma macintyre_finite_union:
  assumes "\<And>a. a \<in> A \<Longrightarrow> is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> a)}"
  assumes "finite A"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> (\<Union> A))}"
proof- 
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> (\<Union> A))} = (\<Union> a \<in> A. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> a)})"
    by blast 
  show ?thesis unfolding 0 
    apply(rule finite_union_is_semialgebraic')
    using assms apply blast
    using assms unfolding is_semialgebraic_def by blast 
qed

definition P_pows where 
"P_pows (n::nat) = {x \<in> carrier Q\<^sub>p. (\<exists>y \<in> carrier Q\<^sub>p. x = y[^]n)}"

lemma P_pows_un: 
  assumes "n > 0"
  shows "P_pows n = P_set n \<union> {\<zero>}"
  unfolding P_pows_def P_set_def apply(rule equalityI')
  unfolding mem_Collect_eq nonzero_def Un_iff singleton_mem apply blast
  apply(erule disjE) apply blast
  using Qp.pow_zero assms by blast

lemma basic_semialg_set_def'':
  assumes "n \<noteq> 0"
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
  shows "basic_semialg_set (m::nat) (n::nat) P = {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). Qp_ev P q \<in> P_pows n}"
proof- 
  have 0: "P_pows n =P_set n \<union> {\<zero>}"
    using assms P_pows_un by blast 
  have 1: " basic_semialg_set m n P = {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). eval_at_point Q\<^sub>p q P = \<zero> \<or> eval_at_point Q\<^sub>p q P \<in> P_set n}"
    using basic_semialg_set_def'[of n P m] assms by blast 
  show ?thesis unfolding 1 0 by blast 
qed

lemma P_set_cong: 
  assumes "a \<in> P_set n"
  assumes "c \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "a = c[^]n \<otimes> b"
  shows "b \<in> P_set n"
proof- 
  obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> a = y[^]n"
    using assms unfolding P_set_def by blast 
  have c_inv: "inv (c[^]n) = (inv c) [^]n"
    using assms Qp.nonzero_memE(1) Qp.nonzero_memE(2) field_nat_pow_inv by blast
  have 0: "(inv c) [^]n \<otimes> a = b"
    unfolding assms using assms c_inv     
    by (metis Qp.cring_simprules(11) Qp.l_one Qp.nat_pow_closed Qp.nonzero_memE(1) Qp.nonzero_memE(2) Qp.nonzero_pow_nonzero field_inv(1) inv_in_frac(1))
  have 1: "b = (inv c) [^]n \<otimes>y[^]n"
    using 0 y_def by metis 
  have 2: "(inv c) [^]n \<otimes>y[^]n = (inv c \<otimes> y)[^]n"
    using assms y_def Qp.nat_pow_distrib Qp.nonzero_memE(1) Qp.nonzero_memE(2) inv_in_frac(1) by presburger
  have 3: "a \<in> nonzero Q\<^sub>p"
    using assms P_set_def by blast 
  have 4: "b \<in> nonzero Q\<^sub>p"
    using 3 assms 
    by (metis Qp.nat_pow_closed Qp.nonzero_memE(1) Qp.not_nonzero_memE Qp.r_null)
  show " b \<in> P_set n"
    using 4 2 assms y_def 
    by (metis "1" P_set_memI Qp.cring_simprules(5) Qp.nonzero_closed Qp.not_nonzero_memI inv_in_frac(1))
qed

lemma P_set_cong': 
  assumes "b \<in> P_set n"
  assumes "c \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "a = c[^]n \<otimes> b"
  shows "a \<in> P_set n"
proof- 
  obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> b = y[^]n"
    using assms unfolding P_set_def by blast 
  have c_inv: "inv (c[^]n) = (inv c) [^]n"
    using assms Qp.nonzero_memE(1) Qp.nonzero_memE(2) field_nat_pow_inv by blast
  have 0: "a = c[^]n \<otimes> y[^]n"
    unfolding assms using y_def by blast 
  have 1: "c[^]n \<otimes> y[^]n = (c \<otimes> y)[^]n"
    using assms y_def Qp.nat_pow_distrib Qp.nonzero_memE(1) by blast
  have 2: "a \<in> nonzero Q\<^sub>p"
    using assms unfolding P_set_def mem_Collect_eq  
    by (metis (no_types, opaque_lifting) "1"  Qp.cring_simprules(5) Qp.integral_iff Qp.nat_pow_closed Qp.nonzero_memE(1) Qp.nonzero_memI Qp.nonzero_pow_nonzero  local.nat_power_eq y_def)
  have 3: "c \<otimes> y \<in> carrier Q\<^sub>p"
    using assms y_def Qp.nonzero_memE(1) by blast
  show ?thesis using 0 2 3 unfolding 1 P_set_def mem_Collect_eq by blast 
qed

lemma P_pows_cong:
  assumes "n > 0"
  assumes "a \<in> P_pows n"
  assumes "c \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "a = c[^]n \<otimes> b"
  shows "b \<in> P_pows n"
proof- 
  have 0: "P_pows n = P_set n \<union> {\<zero>}"
    using assms P_pows_un by blast 
  show ?thesis 
    apply(cases "a \<in> P_set n")
    using P_set_cong[of a n c b] assms unfolding 0 apply blast
    using assms unfolding 0 
    by (metis Qp.integral Qp.nonzero_memE(1) Qp.not_nonzero_memI Qp_nat_pow_nonzero Un_iff singleton_mem)
qed

lemma P_pows_cong':
  assumes "n > 0"
  assumes "b \<in> P_pows n"
  assumes "c \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "a = c[^]n \<otimes> b"
  shows "a \<in> P_pows n"
proof- 
  have 0: "P_pows n = P_set n \<union> {\<zero>}"
    using assms P_pows_un by blast 
  show ?thesis 
    apply(cases "b \<in> P_set n")
    using P_set_cong'[of b n c a] assms unfolding 0 apply blast
    using assms unfolding 0 
    using Qp.nonzero_memE(1) Qp.r_null Un_insert_right by blast
qed

lemma family_intersect_SA:
  assumes "is_semialgebraic m A"
  assumes "\<And>Ps. Ps \<in> parts \<Longrightarrow> Ps partitions A"
  assumes "\<And>Ps. Ps \<in> parts \<Longrightarrow> finite Ps"
  assumes "\<And>Ps P. Ps \<in> parts \<Longrightarrow> P \<in> Ps \<Longrightarrow> is_semialgebraic m P"
  assumes "finite parts"
  assumes "parts \<noteq> {}"
  shows "\<And>P. P \<in> family_intersect parts \<Longrightarrow> is_semialgebraic m P"
proof- 
  fix P assume A: "P \<in> family_intersect parts"
  have 0: "P \<in> atoms_of (\<Union> parts)"
    using A unfolding family_intersect_def by blast 
  have 1: "finite (\<Union> parts)"
    using assms by blast 
  have 2: "\<Union> parts \<subseteq> semialg_sets m"
    using assms unfolding is_semialgebraic_def by blast 
  obtain Ps where Ps_def: "Ps \<in> parts"
    using assms by blast 
  have 3: "\<Union> (\<Union> parts) = A"
    apply(rule equalityI')
    using assms is_partitionE(2)[of _ A] apply blast 
    using assms is_partitionE(2)[of Ps A] Ps_def by blast 
  have 4: "atoms_of (\<Union> parts) = atoms_of (gen_boolean_algebra A (\<Union> parts))"
    apply(rule atoms_of_sets_eq_atoms_of_algebra[of "\<Union> parts" A])
     apply(rule 1)
    unfolding 3 by blast 
  have 5: "atoms_of (\<Union> parts) \<subseteq>  (gen_boolean_algebra A (\<Union> parts))"
    apply(rule atoms_of_gen_boolean_algebra)
    using 3 gen_boolean_algebra.generator[of _ "\<Union> parts" A] 
     apply (meson Sup_upper gen_boolean_algebra_generators subsetI)
    by(rule 1)
  have 6: "A \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms is_semialgebraic_closed by blast
  have 7: "(gen_boolean_algebra A (\<Union> parts)) \<subseteq> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (\<Union> parts)"
    apply(rule gen_boolean_algebra_univ_mono) 
    using 3 gen_boolean_algebra_finite_union[of "\<Union> parts" "carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "\<Union> parts"]
          gen_boolean_algebra.generator[of _ "\<Union> parts" "carrier (Q\<^sub>p\<^bsup>m\<^esup>)" ] 6 1 
    by (meson Sup_le_iff gen_boolean_algebra_generators)
  have 8: "gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (\<Union> parts) \<subseteq> semialg_sets m"
    unfolding semialg_sets_def apply(rule gen_boolean_algebra_subalgebra)
    using 2 unfolding semialg_sets_def by blast 
  show "is_semialgebraic m P"
    using 0 5 6 7 8 unfolding is_semialgebraic_def by blast 
qed

lemma low_multiple: 
  assumes "(l::int) > 0"
  shows "\<exists> j. j*l < i"
proof(cases "i > 0")
  case True
  have T0: "0*l < i"
    using True by auto 
  then show ?thesis by blast 
next
  case False
  have "l \<ge> 1"
    using assms by linarith 
  hence "i*l \<le> i" 
    using False mult_le_cancel_left2 by blast
  hence "i*l - l < i"
    using assms by linarith 
  hence "(i-1)*l < i"
    using assms 
    by (metis False diff_ge_0_iff_ge more_arith_simps(6) mult_left_mono_neg mult_zero_left rel_simps(46) zero_le_mult_iff zle_diff1_eq)
  then show ?thesis by blast 
qed

lemma high_multiple: 
  assumes "(l::int) > 0"
  shows "\<exists> j. j*l > i"
proof(cases "i > 0")
  case True
  have T0: "(i+1)*l > i"
    using assms True 
    by (meson discrete int.lless_eq int_one_le_iff_zero_less mult_le_cancel_left1 verit_comp_simplify1(3))
  then show ?thesis by blast 
next
  case False
  have "1*l > i"
    using False assms by auto 
 then show ?thesis by blast 
qed

lemma SA_fun_ord_floor: 
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  shows "\<exists>\<eta>\<in>Units (SA m). \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x)"
  apply(rule denef_lemma_2_4_floor[of k])
  apply (simp add: padic_fields.denef_cell_decomp_II padic_fields_axioms) 
    apply(rule assms)
   apply linarith 
  using assms by blast 

lemma SA_fun_ord_ceiling: 
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  shows "\<exists>\<eta>\<in>Units (SA m). \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x) + k"
  apply(rule denef_lemma_2_4_ceiling[of k])
  apply (simp add: padic_fields.denef_cell_decomp_II padic_fields_axioms)
    apply(rule assms)
   apply linarith 
  using assms by blast 

definition ceiling_fun where 
"ceiling_fun m k \<phi> = (SOME \<eta>. \<eta> \<in> Units (SA m) \<and> ( \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x) + k))"

lemma ceiling_funE: 
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  shows "(ceiling_fun m k \<phi>) \<in> Units (SA m) \<and> (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). 
              int k * ord ((ceiling_fun m k \<phi>) x) + ord (\<phi> x) mod int k = ord (\<phi> x) + int k)"
proof-
  obtain \<eta> where \<eta>_def: "\<eta>\<in>Units (SA m) \<and> (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x) + k)"
    using SA_fun_ord_ceiling[of k \<phi> m] assms by blast 
  show ?thesis 
    apply(rule SomeE[of "ceiling_fun m k \<phi>" _  \<eta> ])
    unfolding ceiling_fun_def apply blast
    by(rule \<eta>_def)
qed

definition floor_fun where 
"floor_fun m k \<phi> = (SOME \<eta>. \<eta> \<in> Units (SA m) \<and> (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x)))"

lemma floor_funE: 
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  shows "(floor_fun m k \<phi>) \<in> Units (SA m) \<and> 
        (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord ((floor_fun m k \<phi>) x) + ord (\<phi> x) mod int k = ord (\<phi> x))"
proof-
  obtain \<eta> where \<eta>_def: "\<eta>\<in>Units (SA m) \<and> (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x))"
    using SA_fun_ord_floor[of k \<phi> m] assms by blast 
  show ?thesis 
    apply(rule SomeE[of "floor_fun m k \<phi>" _  \<eta> ])
    unfolding floor_fun_def apply blast
    by(rule \<eta>_def)
qed

lemma ceiling_fun_geq: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  assumes "ord (\<phi> x) mod int k \<noteq> 0"
  shows "\<And> j::int. (val (\<phi> x) \<ge> j*k) \<Longrightarrow> (val (ceiling_fun m k \<phi> x) > j)"
proof- 
  obtain c where c_def: "c = ceiling_fun m k \<phi>"
    by blast 
  have c_closed: "c \<in> Units (SA m)"
    unfolding c_def using ceiling_funE assms by blast 
  obtain n where n_def: "n = ord (\<phi> x)"
    by blast 
  have c_ord: "int k * ord (c x) + ord (\<phi> x) mod int k = ord (\<phi> x) + k"
    unfolding c_def using ceiling_funE[of k \<phi> m] assms by blast 
  have 0: "int k * ord (c x) =  ord (\<phi> x) - ( ord (\<phi> x) mod int k) + k"
    using c_ord by linarith 
  have 1: "\<phi> x \<in> nonzero Q\<^sub>p"
    using assms SA_Units_nonzero by blast
  have 2: "c x \<in> nonzero Q\<^sub>p"
    using c_closed assms SA_Units_nonzero by blast
  have 3: " ord (\<phi> x) = int k * ord (c x) + ( ord (\<phi> x) mod int k) - k "
    using 0 by linarith 
  show "\<And>j::int. (val (\<phi> x) \<ge> j*k) \<Longrightarrow> (val (ceiling_fun m k \<phi> x) > j)"
  proof-
    fix j 
    show " val (\<phi> x) \<ge> eint (j * int k) \<Longrightarrow> val (ceiling_fun m k \<phi> x) > eint j"
    proof-
      assume A: "val (\<phi> x) \<ge> eint (j * int k)"
      have a0: "ord (\<phi> x) \<ge> j* k"
        using A 1 val_ord  by (metis eint_ord_simps(1))       
      have a1: "int k * ord (c x) + ( ord (\<phi> x) mod int k) - k \<ge> j*k"
        using a0 0 by linarith
      have R: "\<And> m (n::int). n > 0 \<Longrightarrow> (m mod n) < n"
        by (meson int.lless_eq pos_mod_conj)
      have a2: "( ord (\<phi> x) mod int k) < k"
        apply(rule R)
        using assms by linarith 
      have R0: "\<And>m (n::int) a b. n > 0 \<Longrightarrow> m >0 \<Longrightarrow>  m < n \<Longrightarrow> n*a + m - n \<ge>  b*n \<Longrightarrow> a > b"
      proof- 
        fix m n a b::int assume A: "n > 0" " m >0" "m < n" " n*a + m - n \<ge> b*n "
        have 0:  " n*a  \<ge>  b*n + n - m "
          using A by linarith 
        have 1:  " n*a  - b*n \<ge> n - m "
          using 0 by linarith 
        have 2: "n*(a - b) \<ge> n - m"
          using 1 int_distrib(4) by auto
        hence "n*(a - b) -  n \<ge> - m"
          by linarith 
        have 3: "n*(a - b - 1) \<ge> - m"
          using 2 by (metis \<open>n * (a - b) - n \<ge> - m\<close> more_arith_simps(6) right_diff_distrib')
        have 4: "n*(1 - a + b) \<le> m"
        proof -
          have "- m \<le> n * - (b - (a - 1))"
            using "3" unfolding minus_diff_eq 
            by (metis add.commute add_diff_cancel_left diff_add_cancel diff_minus_eq_add plus_int_code(1) uminus_add_conv_diff)
          then have "n * (b - (a - 1)) \<le> m"
            by linarith
          then show ?thesis
            by (metis (no_types) add.commute diff_minus_eq_add minus_diff_eq)
        qed
        have 5: "(1 - a + b) \<le> 0"
        proof-
          have R: "\<And>j. n*j \<le> m \<Longrightarrow> j \<le> 0"
          proof- fix j show "n*j \<le> m \<Longrightarrow> j \<le> 0"
              using A(1) A(2) less_le_trans[of m n "n*j"]
          proof -
            assume a1: "n * j \<le> m"
            have f2: "\<not> (1::int) \<le> 0"
              by auto
            have f3: "\<not> n + - 1 * (n * j) \<le> 0"
              using a1 A(2) 
              using A(3) by linarith
            have f4: "\<forall>x1. ((0::int) < x1) = (\<not> x1 \<le> 0)"
              by linarith
            have f5: "\<forall>x2 x3. ((x3::int) < x2) = (\<not> x2 + - 1 * x3 \<le> 0)"
              by linarith
            have f6: "0 \<le> n"
              using A(1) by linarith
            have "n * (j * 1) + - 1 * (n * j * 1) \<le> 0"
              by linarith
            then have "\<not> 1 \<le> j * 1 \<or> \<not> 0 \<le> n * j"
              using f5 f4 f3 f2 by (metis (no_types) mult_less_le_imp_less)
            moreover
            { assume "\<not> 0 \<le> n * j"
              then have "\<not> 0 \<le> j"
                using f6 by (meson split_mult_pos_le)
              then have ?thesis
                by linarith }
            ultimately show ?thesis
              by linarith
          qed
          qed
          show ?thesis 
            by(rule R, rule 4)
        qed
        show "a > b"
          using 5 by linarith 
      qed
      have a3: "j < ord (c x)"  
        apply(rule R0[of k "ord (\<phi> x) mod int k"] )
        using assms apply linarith 
        using assms(2) assms(4) 
        apply (smt Euclidean_Division.pos_mod_sign of_nat_1 of_nat_mono)       
         apply(rule a2)
        using a1 by linarith 
      show "eint j < val (ceiling_fun m k \<phi> x)"
        using a3 2 val_ord 
        unfolding c_def 
        using eint_ord_code by presburger
    qed
  qed
qed

lemma ceiling_fun_geq': 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  assumes "ord (\<phi> x) mod int k \<noteq> 0"
  shows "\<And> j::int. (val (ceiling_fun m k \<phi> x) > j) \<Longrightarrow> (val (\<phi> x) > eint (j*k))"
proof- 
  fix j::int assume A: "val (ceiling_fun m k \<phi> x) > j"
  obtain A where A_def: "A = ord (\<phi> x)"
    by blast 
  obtain B where B_def: "B = ord (ceiling_fun m k \<phi> x)"
    by blast 
  have 0: "int k * B + ord (\<phi> x) mod int k = A + int k"
    unfolding B_def A_def using assms floor_funE 
    by (meson ceiling_funE)
  have 1: "ord (\<phi> x) mod int k > 0"
    using assms(2) assms(4) 
    by (smt Euclidean_Division.pos_mod_sign of_nat_1 of_nat_mono) 
  have 2: "int k > 0"
    using assms by linarith 
  have 3: "k - (ord (\<phi> x) mod int k) < k"
    using assms(1) 1 2 by linarith
  obtain M where M_def: "M = k - (ord (\<phi> x) mod int k)"
    by blast 
  have 4: "k*B = A + M"
    unfolding M_def using 0 by linarith 
  have 5: "ceiling_fun m k \<phi> x \<in> nonzero Q\<^sub>p"
    apply(rule SA_Units_nonzero[of _ m])
    using assms ceiling_funE apply blast
    by(rule assms)
  have 6: "B = val (ceiling_fun m k \<phi> x)"
    using 5 val_ord unfolding B_def 
    by presburger
  have 7: "B > j"
    using A unfolding 6 
    by (metis "6" eint_ord_simps(2))
  have 8: "B \<ge>  j + 1"
    using 7 by linarith 
  have 9: "k*B \<ge> k*(j+1)"
    using 8 4 assms 2 mult_le_cancel_left_pos by blast
  have 9: "k*B \<ge> k*j + k"
    using 9 
    by (metis mult.commute semiring_normalization_rules(2))
  have 10: "k*B - k \<ge> k*j"
    using 9 2 by linarith 
  have 11: "M < k"
    unfolding M_def  using "1" by linarith
  have 12: "k*B - M > k*B - k"
    using 11 by linarith
  have 13: "k*B - M > k*j"
    using 12 10 by linarith
  have 14: "A > k*j"
    using 13 unfolding 4   by linarith 
  have 15: "A > j*k"
    using 14 by (metis mult_of_nat_commute)
  show "val (\<phi> x) > j*k"
    using 15 SA_Units_nonzero assms 
    unfolding A_def 
    using eint_ord_code val_ord by presburger
qed

lemma floor_fun_geq: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  assumes "ord (\<phi> x) mod int k \<noteq> 0"
  shows "\<And> j::int. (val (\<phi> x) \<le> j*k) \<Longrightarrow> (val (floor_fun m k \<phi> x) < j)"
        "\<And> j::int. (val (floor_fun m k \<phi> x) <  j \<Longrightarrow> (val (\<phi> x) < j*k))" 
proof- 
  obtain A where A_def: "A = ord (\<phi> x)"
    by blast 
  obtain B where B_def: "B = ord (floor_fun m k \<phi> x)"
    by blast 
  have 0: "int k * B + ord (\<phi> x) mod int k = A"
    unfolding B_def A_def using assms floor_funE 
    by (meson floor_funE)
  have 1: "\<phi> x \<in> nonzero Q\<^sub>p"
    using assms  SA_Units_nonzero by blast
  have 2: "floor_fun m k \<phi> x \<in> nonzero Q\<^sub>p"
    apply(rule SA_Units_nonzero[of _ m])
    using assms floor_funE apply blast
    by(rule assms)
  obtain M where M_def: "M = ord (\<phi> x) mod int k"
    by blast 
  have M_pos: "M > 0"
    unfolding M_def 
    using assms(2) assms(4) 
    by (smt Euclidean_Division.pos_mod_sign of_nat_1 of_nat_mono) 
  have 3: "int k > 0"
    using assms by linarith 
  have M_less: "M < k"
    unfolding M_def using 3 Euclidean_Division.pos_mod_bound by blast
  have 4: "val (floor_fun m k \<phi> x) = B"
    unfolding B_def using 2 val_ord 
    by blast
  have 5: "val (\<phi> x) = A"
    unfolding A_def using 1 val_ord 
    by blast 
  have 6: "A = k*B + M"
    using 0  unfolding A_def B_def M_def  by linarith 
  show "\<And>j. val (floor_fun m k \<phi> x) < eint j \<Longrightarrow> val (\<phi> x) < eint (j * int k)"
  proof-
  fix j::int assume A: "val (floor_fun m k \<phi> x) < j"
  then have 7: "B < j"
    unfolding 4 
    by simp
  hence 8: "B \<le> j - 1"
    using 7 by linarith 
  hence "k*B \<le> k*(j-1)"
    using 3 
    by (meson mult_left_mono of_nat_0_le_iff)
  hence 9: "k*B \<le> k*j - k"
     by (simp add: Rings.ring_distribs(4))    
  hence 10: "k*B < k*j - M"
    using M_less by linarith 
  hence 11: "k*B + M < k*j"
    by linarith 
  show "(val (\<phi> x) < j*k)"
    unfolding 5 6
    using 11 by (metis eint_ord_simps(2) mult.commute)
  qed
  show "\<And>j. val (\<phi> x) \<le> eint (j * int k) \<Longrightarrow> val (floor_fun m k \<phi> x) < eint j"
  proof-
    fix j assume A: "val (\<phi> x) \<le> eint (j * int k)"
    then have 7: "A \<le> j*int k"
      using val_ord 1 eint_ord_code unfolding A_def 
      by metis 
    hence 8: "k*B + M \<le> k*j"
      unfolding 6  by (metis mult.commute)
    hence 9: "k*B < k*j"
      using M_pos by linarith 
    hence 10: "B < j"
      using 3 mult_less_cancel_left_pos by blast
    show "val (floor_fun m k \<phi> x) < eint j"
      using 10 unfolding 4 
      using eint_ord_code(2) by blast
  qed
qed

lemma unit_ord_mod_neq_0: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  assumes "ord (\<phi> x) mod int k \<noteq> 0"
  shows "\<And> j::int. (val (\<phi> x) \<le> j*k) = (val (\<phi> x) < j*k)"
        "\<And> j::int. (val (\<phi> x) \<ge> j*k) = (val (\<phi> x) > j*k)"
proof- 
  have 0: "\<And>j::int. val (\<phi> x) \<noteq> j*k"
  proof- 
    fix j::int
    have 0: "\<phi> x \<in> nonzero Q\<^sub>p"
      using assms SA_Units_nonzero by blast
    have 1: "ord (\<phi> x) \<noteq> j*k"
      using assms(3) 
      by (metis assms(4) mod_mult_self2_is_0)
    have 2: "val(\<phi> x) = ord (\<phi> x)"
      using 0 val_ord by blast
    show "val (\<phi> x) \<noteq> j*k"
      unfolding 2 using 1 by blast
  qed
  show  "\<And> j::int. (val (\<phi> x) \<le> j*k) = (val (\<phi> x) < j*k)"
    using 0 
    by (smt eint_ile eint_iless eint_ord_simps(1) eint_ord_simps(2))
  have R: "\<And> a b::eint. a < b \<Longrightarrow> a \<le> b"
    by auto 
  show "\<And> j::int. (val (\<phi> x) \<ge> j*k) = (val (\<phi> x) > j*k)"
    apply(rule ) using 0  eint_ord_simps(1) eint_ord_simps(2) 
    using \<open>\<And>j. (val (\<phi> x) \<le> eint (j * int k)) = (val (\<phi> x) < eint (j * int k))\<close> notin_closed apply blast
    by(rule R)
qed

lemma ceiling_fun_equiv: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  assumes "ord (\<phi> x) mod int k \<noteq> 0"
  shows "(val (\<phi> x) > j*int k) = (val (ceiling_fun m k \<phi> x) > j)"
        "(val (\<phi> x) \<ge> j*k) = (val (ceiling_fun m k \<phi> x) > j)"
proof-
  show 0: "(val (\<phi> x) > j*k) = (val (ceiling_fun m k \<phi> x) > j)"
    apply(rule )
  using ceiling_fun_geq assms unit_ord_mod_neq_0
  apply (metis (no_types, lifting) Num.of_nat_simps(5))
     using ceiling_fun_geq' assms unit_ord_mod_neq_0 
     by (metis (no_types, lifting) Num.of_nat_simps(5))
   show 1: "(val (\<phi> x) \<ge> j*k) = (val (ceiling_fun m k \<phi> x) > j)"
     using 0 assms unit_ord_mod_neq_0 
     by (metis (no_types, lifting) Num.of_nat_simps(5))
qed

lemma floor_fun_equiv: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "k \<ge> 1"
  assumes "\<phi> \<in> Units (SA m)"
  assumes "ord (\<phi> x) mod int k \<noteq> 0"
  shows "(val (\<phi> x) < j* int k) = (val (floor_fun m k \<phi> x) < j)"
        "(val (\<phi> x) \<le> j* int k) = (val (floor_fun m k \<phi> x) < j)"
proof-
  show 0: "(val (\<phi> x) < j*int k) = (val (floor_fun m k \<phi> x) < j)"
    apply(rule )
    using assms 
    apply (metis (no_types, lifting) Num.of_nat_simps(5) floor_fun_geq(1) unit_ord_mod_neq_0(1))
    using assms floor_fun_geq unit_ord_mod_neq_0(1) 
    by (metis (no_types, opaque_lifting) Num.of_nat_simps(5))
  show 1: "(val (\<phi> x) \<le> eint (j * int k)) = (val (floor_fun m k \<phi> x) < eint j) "
    using 0 assms unit_ord_mod_neq_0 
    by (metis (no_types, lifting) Num.of_nat_simps(5))
qed

lemma interval_translation:
  assumes "is_convex_condition I"
  shows "\<And> a b c d. ((c::eint) + eint d \<in> I (b::eint) (a::eint)) = (c \<in> I (eint (-d) + b) (eint (-d) + a))"
proof-
  fix a::eint fix b::eint fix c ::eint fix d::int
  have 0: "(c + d < a) = (c < (-d) + a)"
    by(induction c,induction a, auto )
  have 1: "(c + d \<le> a) = (c \<le> (-d) + a)"
    by(induction c,induction a,  auto, induction a, auto)
  have 2: "(c + d > b) = (c > (-d) + b)"
    apply(induction c,induction b, auto)
    by (metis not_eint_eq plus_eint_simps(3))
  have 3: "(c + d \<ge> b) = (c \<ge> (-d) + b)"
    by(induction c,induction b, auto )
  show " (c + eint d \<in> I b a) = (c \<in> I ((-d) + b) ((-d) + a))"
    apply(rule convex_condition_induct, rule assms)
    unfolding closed_interval_def left_closed_interval_def open_ray_def closed_ray_def
              mem_Collect_eq
    0 1 2 3 by auto 
qed

lemma pow_res_reduce:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "n dvd m"
  assumes "pow_res m a = pow_res m b"
  shows "pow_res n a = pow_res n b"
proof- 
  obtain k where k_def: "m = k*n"
    using assms Groups.mult_ac(2) by blast
  have 0: "a \<in> pow_res m b"
    using pow_res_refl assms by auto 
  then obtain y where y_def: "y \<in> nonzero Q\<^sub>p" "a = b \<otimes> y[^]m"
    unfolding pow_res_def mem_Collect_eq by auto 
  have "a = b \<otimes> (y[^]k)[^]n"
    unfolding y_def k_def 
    by (simp add: Qp.nat_pow_pow Qp.nonzero_closed y_def(1))
  hence "a \<in> pow_res n b"
    using y_def unfolding pow_res_def 
    using Qp.nat_pow_nonzero assms(1) by blast
  thus ?thesis 
    using assms 
    by (simp add: pow_res_eq_statement)
qed
end


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Intervals with Rational Endpoints are Semialgebraic\<close>
(**************************************************************************************************)
(**************************************************************************************************)


text\<open>A key fact in Denef's proof of Macintyre's Theorem is that relations of the form

\[
\exists l \in \mathbb{Z} \frac{\text{ord}(b_1 x)}{n} \leq l \leq  \frac{\text{ord}(b_2 x)}{n}
\]

are semialgebraic for any positive natural number $n$. In this section we prove a variant of this 
fact in its own locale.
\<close>

locale rational_cell_interval = padic_fields + 
  fixes W and n and b1 and b2 and m and I
  assumes convex: "is_convex_condition I"
  assumes W_def: "W = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>l::int. l*n \<in> I (val (b1 x)) (val (b2 x))}"
  assumes n_pos: "(n::nat) > 0"
  assumes b1_closed: "b1 \<in> carrier (SA m)"
  assumes b2_closed: "b2 \<in> carrier (SA m)"


context rational_cell_interval
begin

lemma b1_non: "\<And>x. x \<in> W \<Longrightarrow> I = closed_interval \<or> I = left_closed_interval \<Longrightarrow> b1 x \<in> nonzero Q\<^sub>p"
proof- 
 fix x assume A: "x \<in> W" "I = closed_interval \<or> I = left_closed_interval"
 obtain j::int where j_def: " j*n \<in> I (val (b1 x)) (val (b2 x))"
   using A unfolding W_def by blast 
 have b1_in: "b1 x \<in> carrier Q\<^sub>p"
   using A b1_closed SA_car_closed 
   unfolding W_def mem_Collect_eq by blast 
 show "b1 x \<in> nonzero Q\<^sub>p"
   apply(rule nonzero_memI, rule b1_in)
   using j_def 
   apply(cases "I = left_closed_interval")
   unfolding left_closed_interval_def 
    apply (metis (no_types, lifting) infinity_ileE local.val_zero mem_Collect_eq)
   apply(cases "I = closed_interval")
   unfolding closed_interval_def 
    apply (metis (no_types, lifting) infinity_ileE local.val_zero mem_Collect_eq)
   using A
   unfolding is_convex_condition_def left_closed_interval_def closed_interval_def 
   by blast 
qed

definition c1 where c1_def: "c1 = to_fun_unit m b1"

lemma c1_closed: "c1 \<in> carrier (SA m)"
  unfolding c1_def by(rule to_fun_unit_closed, rule b1_closed)

lemma c1_Unit: "c1 \<in> Units (SA m)"
  unfolding c1_def by(rule to_fun_unit_is_unit, rule b1_closed)

definition c2 where c2_def: "c2 = to_fun_unit m b2"

lemma c2_closed: "c2 \<in> carrier (SA m)"
  unfolding c2_def by(rule to_fun_unit_closed, rule b2_closed)

lemma c2_Unit: "c2 \<in> Units (SA m)"
  unfolding c2_def by(rule to_fun_unit_is_unit, rule b2_closed)

definition W0 where W0_def: "W0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). b2 x = \<zero>} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). b1 x \<noteq> \<zero>}"

lemma W0_semialg: "is_semialgebraic m W0"
   unfolding W0_def apply(rule intersection_is_semialg)
   using b2_closed SA_zero_set_is_semialg apply presburger 
   using b1_closed SA_nonzero_set_is_semialg by presburger

lemma b1_eq: "\<And>x. x \<in> W \<Longrightarrow> I = closed_interval \<or> I = left_closed_interval \<Longrightarrow> c1 x = b1 x"
proof- 
 fix x assume A: "x \<in> W" "I = closed_interval \<or> I = left_closed_interval"
 have b1_non: "b1 x \<in> nonzero Q\<^sub>p"
   using b1_non A by auto 
 show "c1 x = b1 x"
   unfolding c1_def apply(rule to_fun_unit_eq[of b1 m x], rule b1_closed)
   using A unfolding W_def apply blast
   using b1_non nonzero_memE by blast   
qed 

lemma universal_interval_criterion:
  assumes "\<alpha> > \<beta>"
  assumes "\<alpha> < \<gamma>"
  shows "\<alpha> \<in> I \<beta> \<gamma>"
  using assms convex 
  unfolding is_convex_condition_def closed_interval_def 
  left_closed_interval_def closed_ray_def open_ray_def by auto 

lemma W0_sub_W: 
  assumes "x \<in> W0"
  shows "x \<in> W"
proof- 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms W0_def by blast 
  have b1_nonzero: "b1 x \<in> nonzero Q\<^sub>p"
    apply(intro nonzero_memI SA_car_closed[of _ m] b1_closed x_closed)
    using assms unfolding W0_def by auto 
  obtain j where j_def: "j*int n > ord (b1 x)"
    using high_multiple[of n] n_pos by auto 
  hence 0: "eint (j* int n) > val (b1 x)"
    using val_ord b1_nonzero by auto 
  have 1: "eint (j* int n) \<in> I (val (b1 x)) (val (b2 x))"
    apply(intro universal_interval_criterion 0)
    using assms W0_def val_zero by auto 
  show ?thesis 
    unfolding W_def mem_Collect_eq
    using 1 x_closed by auto 
qed

lemma W0_int_W: 
"W \<inter> W0 = W0"
  using W0_sub_W by blast

lemma t0: "\<And>x. x \<in> W - W0 \<Longrightarrow> I = closed_interval \<or> I = left_closed_interval \<Longrightarrow> c2 x = b2 x"
  unfolding c2_def 
  apply(rule to_fun_unit_eq, rule b2_closed)
  using W_def apply blast using b1_non
  unfolding Diff_iff W0_def mem_Collect_eq Int_iff W_def nonzero_def by blast    

lemma t1: "\<And>x. x \<in> W - W0 \<Longrightarrow> I = closed_interval \<or> I = left_closed_interval \<Longrightarrow> b2 x = c2 x"
  unfolding t0 by blast 

lemma t2: "\<And>x. x \<in> W - W0 \<Longrightarrow> I = closed_interval \<or> I = left_closed_interval \<Longrightarrow> b1 x = c1 x"
  using b1_eq by blast 

lemma t3: "\<And>x. x \<in> W - W0 \<Longrightarrow> I = closed_interval \<or> I = left_closed_interval \<Longrightarrow> c1 x = b1 x"
  unfolding t2 by blast

lemmas W0_comp_eqs = t0 t1 t2 t3

lemma t4: "\<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). b1 x \<noteq> \<zero>} \<inter> 
                    ({x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j*n \<in> I (val (c1 x)) (val (c2 x))} - W0) \<Longrightarrow> 
          c2 x = b2 x"
  unfolding c2_def apply(rule to_fun_unit_eq, rule b2_closed, blast)
  unfolding W0_def Diff_iff mem_Collect_eq Int_iff by blast  

lemma t5: "\<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). b1 x \<noteq> \<zero>} \<inter> 
                    ({x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j*n \<in> I (val (c1 x)) (val (c2 x))} - W0) \<Longrightarrow> 
          b2 x = c2 x"
  unfolding t4 by blast 

lemma t6: "\<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). b1 x \<noteq> \<zero>} \<inter> 
                    ({x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j*n \<in> I (val (c1 x)) (val (c2 x))} - W0) \<Longrightarrow> 
          b1 x = c1 x"
  unfolding c1_def using to_fun_unit_eq[of b1 m] b1_closed by blast 

definition Y where Y_def: "Y = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint (j * int n) \<in> I (val (c1 x)) (val (c2 x))}"

definition Y0 where Y0_def: "Y0 = Y \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n = 0}"

definition d2 where d2_def: "d2 = \<pp>[^](-1::int)\<odot>\<^bsub>SA m\<^esub>c2"

lemma d2_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> d2 x = \<pp>[^](-1::int) \<otimes> c2 x"
  unfolding d2_def 
  by (meson SA_smult_formula c2_closed p_intpow_closed(1))

lemma p_inv: "\<pp>[^](-1::int) \<in> nonzero Q\<^sub>p"
  using Qp_int_pow_nonzero p_nonzero by blast

lemma d2_Unit: "d2 \<in> Units (SA m)"
  apply(rule SA_Units_memI) 
  unfolding d2_def using nonzero_def  c2_Unit 
  using SA_smult_closed c2_closed p_intpow_closed(1) apply presburger
  using p_inv c2_Unit SA_Units_nonzero 
  using Qp.integral_iff Qp.nonzero_memE(2) SA_Units_closed_fun d2_def d2_eval p_intpow_closed(1) by presburger
   
lemma d2_val: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> val (d2 x) = ord (d2 x)"
  using d2_Unit SA_Units_nonzero val_ord  by blast

lemma d2_ord: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>ord (d2 x) = ord (c2 x) - 1"
  unfolding d2_eval using ord_mult c1_Unit SA_Units_nonzero 
  using  p_inv c2_Unit ord_p_pow_int by auto

lemma 1: "\<And>x \<alpha>. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<alpha> < val (c2 x) \<Longrightarrow> \<alpha> \<le> val (d2 x)"
proof- 
 fix x \<alpha> assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" " \<alpha> < val (c2 x)"
 obtain j where j_def: "\<alpha> = eint j"
   using A by (metis eint_ord_code(6) eint_ord_simps(4) less_infinityE)
 have 00: "val (c2 x) = ord (c2 x)"
   using A c2_Unit val_ord SA_Units_nonzero by blast  
 have 01: "j \<le> ord (d2 x)"
   using A d2_ord unfolding j_def 00 
   by (metis eint_ord_simps(2) zle_diff1_eq)
 show 02: "\<alpha> \<le> val (d2 x)"
   unfolding j_def using 01 d2_val A eint_ord_simps(1) by presburger
qed

lemma 2: "\<And>x \<alpha>. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  \<alpha> \<le> val (d2 x) \<Longrightarrow>\<alpha> < val (c2 x)"
proof- 
 fix x \<alpha> assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" " \<alpha> \<le> val (d2 x)"
 have 0: "val (d2 x) = ord (d2 x)"
   apply(rule d2_val)
   using A by blast 
 obtain j where j_def: "\<alpha> = eint j"
   using A 0 by (metis eint_ord_code  eint_ord_simps  less_infinityE)
 have 00: "val (c2 x) = ord (c2 x)"
   using A c2_Unit val_ord SA_Units_nonzero by blast  
 have a: "ord (d2 x) = ord (c2 x) - 1" 
   apply(rule d2_ord)
   using A by blast
 have b: "j \<le> ord (d2 x)"
   using A unfolding 0 
   using eint_ord_code(1) j_def by blast
 have 01: "j < ord (c2 x)"
   using A a b unfolding 0 j_def 00 by linarith 
 show 02: "\<alpha> < val (c2 x)"
   unfolding j_def using 01 d2_val A b 
   using "00" eint_ord_code(2) by presburger
qed

lemma Y_diff: "Y - Y0 = Y \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
  unfolding Y_def Y0_def apply(rule equalityI')
  unfolding Diff_iff Int_iff 
  apply (metis (mono_tags, lifting) mem_Collect_eq)
  unfolding mem_Collect_eq 
  by meson 

definition e1 where e1_def: "e1 = \<pp>[^](1::int) \<odot>\<^bsub>SA m\<^esub>floor_fun m n c1"

lemma smult_Unit: "\<And>f. f \<in> Units (SA m) \<Longrightarrow> \<pp>[^](1::int)\<odot>\<^bsub>SA m\<^esub>f \<in> Units (SA m)"
   apply(rule SA_Units_memI)
   using SA_smult_closed p_intpow_closed(1) apply blast
   using SA_Units_nonzero Qp_int_pow_nonzero p_nonzero
   by (metis p_inv Qp.integral Qp.nonzero_memE(2) SA_Units_closed SA_car_closed SA_smult_formula p_intpow_closed(1))
  
lemma e1_Unit: "e1 \<in> Units (SA m)"
   unfolding e1_def 
   apply(rule smult_Unit)
   using floor_funE c1_Unit  n_pos  of_nat_0_less_iff of_nat_1 of_nat_le_iff
   by auto

definition Y1 where Y1_def: "Y1 = Y - Y0"

lemma Y_un: "Y = Y1 \<union> Y0"
  unfolding Y1_def using Y0_def by blast 

lemma ray_mem_criterion:
  assumes "I = open_ray \<or> I = closed_ray"
  assumes "\<alpha> < \<gamma>"
  shows "\<alpha> \<in> I \<beta> \<gamma>"
  using assms unfolding open_ray_def closed_ray_def 
  by auto 

lemma ray_imp_Y_semialg: 
  assumes "I = open_ray \<or> I = closed_ray"
  shows "is_semialgebraic m Y"
proof- 
  have "Y = carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    apply(rule equalityI',unfold Y_def, blast, unfold mem_Collect_eq, rule conjI, blast)
  proof- 
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    have 0: "c2 x \<in> nonzero Q\<^sub>p"
      by (meson A SA_Units_nonzero c2_Unit)
    hence 1: "val (c2 x) = eint (ord (c2 x))"
      using val_ord by auto 
    obtain j where j_def: "j * int n < ord (c2 x)"
      using low_multiple[of n] n_pos by auto 
    hence 2: "eint (j * int n) < val (c2 x)"
      unfolding 1 by auto 
    have 3: "eint (j * int n) \<in> I (val (c1 x)) (val (c2 x))"
      by(intro ray_mem_criterion assms 2)
    thus "\<exists>j. eint (j * int n) \<in> I (val (c1 x)) (val (c2 x))"
      by auto 
  qed
  thus ?thesis using carrier_is_semialgebraic by auto 
qed

lemma closed_interval_imp_Y1_semialg: 
  assumes closed_interval: "I = closed_interval"
  shows "is_semialgebraic m Y1"
 proof-
   obtain Y2 where Y2_def: "Y2 = Y1 \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c2 x) mod n = 0}"
     by blast 
   have Y2_eq: "Y2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (c2 x) } \<inter> 
                      {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c2 x) mod n = 0} \<inter> 
                       {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
   proof(rule equalityI') 
     fix x assume A: "x \<in> Y2"
     have q0: "val (c1 x) \<le> val (c2 x)"
       using A unfolding Y2_def Y1_def Y_def unfolding mem_Collect_eq Int_iff  closed_interval closed_interval_def 
       using eint_ord_trans[of "val (c1 x)" _ "val (c2 x)"] 
       by blast 
     have q1: "ord (c1 x) mod int n \<noteq> 0"
       using A unfolding Y2_def Y1_def Y_diff Int_iff mem_Collect_eq by metis 
     show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (c2 x) } \<inter> 
                {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c2 x) mod n = 0} \<inter> 
                 {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
       unfolding Int_iff mem_Collect_eq using A q0 q1 unfolding Y2_def Y1_def Y0_def Diff_iff  by blast 
   next
     fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (c2 x)} \<inter>
                            {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c2 x) mod int n = 0} \<inter> 
                              {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
     then obtain j::int where j_def: "ord (c2 x) = j*n"
       unfolding Int_iff mem_Collect_eq 
       using mod_zeroE by presburger
     have q1: "(c1 x) \<in> nonzero Q\<^sub>p"
       using c1_Unit A SA_Units_nonzero by blast  
     have q2: "c2 x \<in> nonzero Q\<^sub>p"
       using c2_Unit A SA_Units_nonzero by blast  
     have q3: "val (c1 x) = ord (c1 x)"
       using q1 val_ord by metis
     have q4: "val (c2 x) = ord (c2 x)"
       using q2 val_ord by metis
     have q5: "j*n = val (c2 x)"
       unfolding q4 j_def by blast 
     have q5: "j*n \<in> closed_interval (val (c1 x)) (val (c2 x))"
       apply(rule closed_interval_memI)
       unfolding q5 using A  apply blast
       using A unfolding mem_Collect_eq Int_iff unfolding q5 by blast 
     show "x \<in> Y2"
       unfolding Y2_def apply(rule IntI)
       unfolding Y1_def Y_diff using A  unfolding Y_def unfolding mem_Collect_eq Int_iff closed_interval
       using q5  closed_interval apply metis                                
       using A  by blast 
   qed
   have Y2_semialg: "is_semialgebraic m Y2"
     unfolding Y2_eq apply(rule intersection_is_semialg)
   proof -
     have "is_semialgebraic m {rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 rs) \<le> val (c2 rs)}"
       using R.Units_closed c1_closed c2_Unit semialg_val_ineq_set_is_semialg by presburger
     then show "is_semialgebraic m ({rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 rs) \<le> val (c2 rs)} \<inter> 
                                    {rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c2 rs) mod int n = 0})"
       using SA_unit_cong_set_is_semialg c2_Unit intersection_is_semialg by blast
   next
     have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0} = 
              carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n = 0}"
       apply(rule equalityI') 
       unfolding Diff_iff mem_Collect_eq apply linarith
       by linarith 
     show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0}"
       unfolding 0 
       apply(rule diff_is_semialgebraic)
        apply (simp add: carrier_is_semialgebraic)
       using c1_Unit SA_unit_cong_set_is_semialg by blast
   qed
   have smult_Unit: "\<And>f. f \<in> Units (SA m) \<Longrightarrow> \<pp>[^](1::int)\<odot>\<^bsub>SA m\<^esub>f \<in> Units (SA m)"
     apply(rule SA_Units_memI)
     using SA_smult_closed p_intpow_closed(1) apply blast
     using SA_Units_nonzero Qp_int_pow_nonzero p_nonzero
     by (metis  Qp.integral Qp.nonzero_memE(2) SA_Units_closed SA_car_closed SA_smult_formula p_intpow_closed(1))
   obtain Y3 where Y3_def: "Y3 = Y1 - Y2"
     by blast 
   have Y3_semialg: "is_semialgebraic m Y3"
   proof-
     have Y3_eq: "Y3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint (j * int n) \<in> I (val (c1 x)) (val (c2 x)) } \<inter> 
                        {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c2 x) mod n \<noteq> 0} \<inter> 
                          {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
       apply(rule equalityI')
       unfolding Int_iff 
        apply(rule conjI, rule conjI)
       unfolding Y_def Y1_def Y3_def Y0_def Y2_def unfolding assms apply blast
       unfolding mem_Collect_eq Diff_iff Int_iff by auto 
     have r0: "\<And>x j. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  ord (c2 x) mod n \<noteq> 0 \<Longrightarrow>  ord (c1 x) mod n \<noteq> 0 \<Longrightarrow> 
                 ( eint (j * int n) \<in> I (val (c1 x)) (val (c2 x))) = (val (ceiling_fun m n c2 x) > j  \<and> val (floor_fun m n c1 x) < j)"
     proof- 
       fix x j assume A0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "ord (c2 x) mod n \<noteq> 0" "ord (c1 x) mod n \<noteq> 0"
       have r1: "(eint (j * int n) \<le> val (c2 x)) = (eint j < val (ceiling_fun m n c2 x))"
         using ceiling_fun_equiv[of x m n c2 j] c2_Unit n_pos A0 by linarith 
       have r2: "(val (c1 x) \<le> eint (j * int n)) = (val (floor_fun m n c1 x) < eint j)"
         using floor_fun_equiv[of x m n c1 j]   n_pos c2_Unit c1_Unit A0 by linarith 
       show r3: "( eint (j * int n) \<in> I (val (c1 x)) (val (c2 x))) = 
                    (val (ceiling_fun m n c2 x) > j  \<and> val (floor_fun m n c1 x) < j)"
         unfolding assms closed_interval_def r1 r2 mem_Collect_eq by blast 
     qed
     have r1: "\<And>x j::int. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  ord (c2 x) mod n \<noteq> 0 \<Longrightarrow>  ord (c1 x) mod n \<noteq> 0 \<Longrightarrow> 
          (val (floor_fun m n c1 x) < j) = (val (e1 x) \<le> j) "
     proof- 
       fix x fix j::int  assume A0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "ord (c2 x) mod n \<noteq> 0" "ord (c1 x) mod n \<noteq> 0"
       have t0: " (floor_fun m n c1) \<in> Units (SA m)"
         using floor_funE c1_Unit assms n_pos A0
         by (metis Suc_eq_plus1 Suc_le_eq add_leE)
       have t2: " (floor_fun m n c1 x) \<in> nonzero Q\<^sub>p"
         using t0 A0(1)  SA_Units_nonzero by blast
       have t1: "e1 x = \<pp>[^](1::int) \<otimes>  (floor_fun m n c1 x)"
         unfolding e1_def using t0 t1 A0(1) Qp_int_pow_nonzero p_nonzero
         SA_Units_closed SA_smult_formula p_intpow_closed(1) by presburger
       have t3: "val  (floor_fun m n c1 x) = ord  (floor_fun m n c1 x)"
         by(rule val_ord ,rule t2)
       have t4: "\<pp> [^] (1::int) \<in> nonzero Q\<^sub>p"
         using Qp_int_pow_nonzero p_nonzero by blast
       have t5: "local.ord (\<pp> [^] (1 ::int)) = 1"
         using ord_p_pow_int by blast
       have t6: "val (\<pp>[^](1::int) \<otimes>  (floor_fun m n c1 x)) = ord (\<pp>[^](1::int) \<otimes>  (floor_fun m n c1 x))"
         apply(rule val_ord)
         using t2 t4 Units_eq_nonzero by blast
       have t7: "ord (\<pp>[^](1::int) \<otimes>  (floor_fun m n c1 x)) = ord (floor_fun m n c1 x) + 1"
         using ord_mult[of "\<pp>[^](1::int)" "floor_fun m n c1 x"] t4 t2 unfolding t5
         by linarith
       show " (val (floor_fun m n c1 x) < j) = (val (e1 x) \<le> j)"
         unfolding  t1 t3 t6 t7 eint_ord_code by linarith 
     qed
     obtain e2 where e2_def: "e2 = ceiling_fun m n c2"
       by blast 
     have e2_Unit: "e2 \<in> Units (SA m)"
       unfolding e2_def using ceiling_funE[of n c2 m] c2_Unit n_pos  by linarith 
     have r2: "\<And>x j::int. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  ord (c2 x) mod n \<noteq> 0 \<Longrightarrow>  ord (c1 x) mod n \<noteq> 0 \<Longrightarrow> 
          ( eint (j * int n) \<in> I (val (c1 x)) (val (c2 x))) = (j \<in> left_closed_interval (val (e1 x)) (val (e2 x)))"
       unfolding r0 unfolding r1 left_closed_interval_def mem_Collect_eq unfolding e2_def  by auto 
     have Y3_eq': 
        "Y3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x)) } \<inter>
               {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c2 x) mod n \<noteq> 0} \<inter> 
                {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
     proof(rule equalityI')
       fix x assume A: "x \<in> Y3"
       have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
         using A Y3_def Y1_def Y_def by blast 
       have 1: "ord (c2 x) mod n \<noteq> 0"
         using A unfolding Y3_eq Int_iff mem_Collect_eq by metis  
       have 2: "ord (c1 x) mod n \<noteq> 0"
         using A unfolding Y3_eq Int_iff mem_Collect_eq by metis  
       obtain j where j_def: " eint (j * int n) \<in> I[val (c1 x) val (c2 x)]"
         using A unfolding Y3_eq assms by blast 
       have 3: " ( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (c2 x))) = (j \<in> left_closed_interval (val (e1 x)) (val (e2 x)))"
         using 0 1 2 r2 assms by blast 
       have 4: "j \<in> left_closed_interval (val (e1 x)) (val (e2 x))"
         using j_def unfolding 3 by blast 
       have 5: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x))}"
         using A Y3_eq 4 by blast 
       show " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x))} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c2 x) mod int n \<noteq> 0} \<inter>
{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0}"
         using 5 A unfolding Y3_eq closed_interval by auto 
     next
       fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x))} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c2 x) mod int n \<noteq> 0} \<inter>
      {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0}"
       have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
         using A Y3_def Y1_def Y_def by blast 
       have 1: "ord (c2 x) mod n \<noteq> 0"
         using A unfolding Y3_eq Int_iff mem_Collect_eq by metis  
       have 2: "ord (c1 x) mod n \<noteq> 0"
         using A unfolding Y3_eq Int_iff mem_Collect_eq by metis  
       obtain j::int where j_def: " j \<in> left_closed_interval (val (e1 x)) (val (e2 x))"
         using A by blast 
       have 3: " ( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (c2 x))) = (j \<in> left_closed_interval (val (e1 x)) (val (e2 x)))"
         using 0 1 2 r2 assms by blast 
       have 4: "( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (c2 x)))"
         unfolding 3 using j_def by blast 
       show "x \<in> Y3"
         unfolding Y3_eq Int_iff 
         apply(rule conjI, rule conjI)
         using 4 0 assms apply blast
         using 1 0 apply blast
         using 2 0 by blast 
     qed
     have r3: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x)) } =   
               {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>).(val (e1 x)) < (val (e2 x)) }"
     proof(rule equalityI')
       fix x assume A: " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>xa. eint xa \<in> left_closed_interval (val (e1 x)) (val (e2 x))} "
       then obtain j::int where j_def: "eint j \<in> left_closed_interval (val (e1 x)) (val (e2 x))"
         by blast 
       have " val (e1 x) < val (e2 x)"
         using le_less_trans[of _ "eint j"] j_def unfolding left_closed_interval_def by blast 
       thus " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (e1 x) < val (e2 x)}"
         using A by blast 
     next
       fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (e1 x) < val (e2 x)}"
       have r0: "e1 x \<in> nonzero Q\<^sub>p"
         using e1_Unit A SA_Units_nonzero by blast 
       have r1: "val (e1 x) = ord (e1 x)"
         by(rule val_ord, rule r0)
       have r2: "val (e1 x) \<in> left_closed_interval (val (e1 x)) (val (e2 x))"
         apply(rule left_closed_interval_memI)
         apply blast
         using A  by blast 
       show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>xa. eint xa \<in> left_closed_interval (val (e1 x)) (val (e2 x))}"
         unfolding mem_Collect_eq 
         using A r2 unfolding r1 by blast 
     qed
     have r4: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c2 x) mod int n \<noteq> 0} =    
                carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c2 x) mod int n = 0}"
       by fastforce
     have r5: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0} =    
                carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n = 0}"
       by fastforce
     have Y3_eq'': "Y3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>).(val (e1 x)) < (val (e2 x)) }\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c2 x) mod n \<noteq> 0}\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
       unfolding Y3_eq' r3 by blast 
     show ?thesis unfolding Y3_eq''
       apply(rule intersection_is_semialg, rule intersection_is_semialg)
       using e1_Unit e2_Unit semialg_val_strict_ineq_set_is_semialg apply blast
       unfolding r4 apply(rule diff_is_semialgebraic)
       apply(rule carrier_is_semialgebraic)
       using c2_Unit SA_unit_cong_set_is_semialg apply blast
       unfolding r5 apply(rule diff_is_semialgebraic)
       apply(rule carrier_is_semialgebraic)
       using c1_Unit SA_unit_cong_set_is_semialg by blast
   qed
   have Y1_un: "Y1 = Y2 \<union> Y3"
     unfolding Y3_def using Y2_def by blast 
   show ?thesis unfolding Y1_un
     apply(rule union_is_semialgebraic, rule Y2_semialg)
     using Y3_semialg by blast 
 qed

lemma closed_interval_imp_Y_semialg:
  assumes closed_interval: "I = closed_interval"
  shows "is_semialgebraic m Y"
  proof- 
   have Y0_eq: "Y0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (c2 x) } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n = 0}"
   proof(rule equalityI')
     fix x assume A: "x \<in> Y0"
     have q0: "val (c1 x) \<le> val (c2 x)"
       using A unfolding Y0_def Y_def
               unfolding mem_Collect_eq Int_iff closed_interval closed_interval_def 
       using eint_ord_trans[of "val (c1 x)" _ "val (c2 x)"] 
       by blast                           
     show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (c2 x) } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n = 0}"
       using A unfolding Y0_def using q0 by blast 
   next
     fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (c2 x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n = 0}"
     then obtain j::int where j_def: "ord (c1 x) = j*n"
       unfolding Int_iff mem_Collect_eq 
       using mod_zeroE by presburger
     have q1: "(c1 x) \<in> nonzero Q\<^sub>p"
       using c1_Unit A SA_Units_nonzero by blast  
     have q2: "c2 x \<in> nonzero Q\<^sub>p"
       using c2_Unit A SA_Units_nonzero by blast  
     have q3: "val (c1 x) = ord (c1 x)"
       using q1 val_ord by metis
     have q4: "val (c2 x) = ord (c2 x)"
       using q2 val_ord by metis
     have q5: "val (c1 x) = j*n"
       unfolding q3 j_def by blast 
     have q5: "j*n \<in> I (val (c1 x)) (val (c2 x))"
       unfolding closed_interval apply(rule closed_interval_memI)
       unfolding q5 apply blast
       using A unfolding mem_Collect_eq Int_iff unfolding q5 by blast 
     show "x \<in> Y0"
       unfolding Y0_def Y_def using A q5 by blast 
   qed
   have Y0_semialg: "is_semialgebraic m Y0"
     unfolding Y0_eq 
     apply(rule intersection_is_semialg)
     using c1_closed c2_closed semialg_val_ineq_set_is_semialg apply blast
     using c1_Unit SA_unit_cong_set_is_semialg by blast                          
   have Y_un: "Y = Y1 \<union> Y0"
     unfolding Y1_def using Y0_def by blast 
   have Y_semialg: "is_semialgebraic m Y"
     unfolding Y_un by(intro union_is_semialgebraic closed_interval_imp_Y1_semialg assms Y0_semialg)
   thus ?thesis unfolding Y_def by blast 
  qed

lemma left_closed_interval_imp_Y1_semialg: 
  assumes left_closed: "I = left_closed_interval"
  shows "is_semialgebraic m Y1"
proof-
 have Y_alt_def: "Y = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint (j * int n) \<in> closed_interval (val (c1 x)) (val (d2 x))}" 
   apply(rule equalityI')
   unfolding Y_def unfolding mem_Collect_eq assms closed_interval_def left_closed_interval_def using 1 apply blast
   using 2 by blast
 obtain Y2 where Y2_def: "Y2 = Y1 \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (d2 x) mod n = 0}"
   by blast 
 have Y2_eq: "Y2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (d2 x) } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (d2 x) mod n = 0}\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
 proof(rule equalityI')
   fix x assume A: "x \<in> Y2"
   have q0: "val (c1 x) \<le> val (d2 x)"
     using A unfolding Y2_def Y1_def mem_Collect_eq Int_iff Y_alt_def  closed_interval_def 
     using eint_ord_trans[of "val (c1 x)" _ "val (d2 x)"] 
     by blast 
   have q1: "ord (c1 x) mod int n \<noteq> 0"
     using A unfolding Y2_def Y1_def Y_diff Int_iff mem_Collect_eq by metis 
   show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (d2 x) } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (d2 x) mod n = 0}\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
     unfolding Int_iff mem_Collect_eq using A q0 q1 unfolding Y2_def Y1_def Y0_def Diff_iff  by blast 
 next
   fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) \<le> val (d2 x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (d2 x) mod int n = 0}\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
   then obtain j::int where j_def: "ord (d2 x) = j*n"
     unfolding Int_iff mem_Collect_eq 
     using mod_zeroE by presburger
   have q1: "(c1 x) \<in> nonzero Q\<^sub>p"
     using c1_Unit A SA_Units_nonzero by blast  
   have q2: "d2 x \<in> nonzero Q\<^sub>p"
     using d2_Unit A SA_Units_nonzero by blast  
   have q3: "val (c1 x) = ord (c1 x)"
     using q1 val_ord by metis
   have q4: "val (d2 x) = ord (d2 x)"
     using q2 val_ord by metis
   have q5: "j*n = val (d2 x)"
     unfolding q4 j_def by blast 
   have q5: "j*n \<in> closed_interval (val (c1 x)) (val (d2 x))"
     unfolding assms apply(rule closed_interval_memI)
     unfolding q5 using A  apply blast
     using A unfolding mem_Collect_eq Int_iff unfolding q5 by blast 
   show "x \<in> Y2"
     unfolding Y2_def apply(rule IntI)
     unfolding Y1_def Y_diff using A unfolding Y_alt_def  mem_Collect_eq Int_iff
     using q5  apply meson
     using A by blast 
 qed
 have Y2_semialg: "is_semialgebraic m Y2"
   unfolding Y2_eq apply(rule intersection_is_semialg)
 proof -
   have "is_semialgebraic m {rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 rs) \<le> val (d2 rs)}"
     using R.Units_closed c1_closed d2_Unit semialg_val_ineq_set_is_semialg by presburger
   then show "is_semialgebraic m ({rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 rs) \<le> val (d2 rs)} \<inter> {rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (d2 rs) mod int n = 0})"
     using SA_unit_cong_set_is_semialg d2_Unit intersection_is_semialg by blast
 next
   have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0} = carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n = 0}"
     apply(rule equalityI') 
     unfolding Diff_iff mem_Collect_eq apply linarith
     by linarith 
   show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0}"
     unfolding 0 
     apply(rule diff_is_semialgebraic)
      apply (simp add: carrier_is_semialgebraic)
     using c1_Unit SA_unit_cong_set_is_semialg by blast
 qed
 obtain Y3 where Y3_def: "Y3 = Y1 - Y2"
   by blast 
 have Y3_semialg: "is_semialgebraic m Y3"
 proof-
   have Y3_eq: "Y3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint (j * int n) \<in> closed_interval (val (c1 x)) (val (d2 x)) } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (d2 x) mod n \<noteq> 0}\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
     apply(rule equalityI')
     unfolding Int_iff 
      apply(rule conjI, rule conjI)
     unfolding Y3_def Y1_def Y_alt_def Y2_def Y0_def by auto 
   have r0: "\<And>x j. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  ord (d2 x) mod n \<noteq> 0 \<Longrightarrow>  ord (c1 x) mod n \<noteq> 0 \<Longrightarrow> 
               ( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (d2 x))) =  (val (ceiling_fun m n d2 x) > j  \<and> val (floor_fun m n c1 x) < j)"
   proof- 
     fix x j assume A0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "ord (d2 x) mod n \<noteq> 0" "ord (c1 x) mod n \<noteq> 0"
     have r1: "(eint (j * int n) \<le> val (d2 x)) = (eint j < val (ceiling_fun m n d2 x))"
       using ceiling_fun_equiv[of x m n d2 j] d2_Unit n_pos A0 by linarith 
     have r2: "(val (c1 x) \<le> eint (j * int n)) = (val (floor_fun m n c1 x) < eint j)"
       using floor_fun_equiv[of x m n c1 j]   n_pos d2_Unit c1_Unit A0 by linarith 
     show r3: "( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (d2 x))) = 
                  (val (ceiling_fun m n d2 x) > j  \<and> val (floor_fun m n c1 x) < j)"
       unfolding closed_interval_def r1 r2 mem_Collect_eq by blast 
   qed
   have r1: "\<And>x j::int. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  ord (d2 x) mod n \<noteq> 0 \<Longrightarrow>  ord (c1 x) mod n \<noteq> 0 \<Longrightarrow> 
        (val (floor_fun m n c1 x) < j) = (val (e1 x) \<le> j) "
   proof- 
     fix x fix j::int  assume A0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "ord (d2 x) mod n \<noteq> 0" "ord (c1 x) mod n \<noteq> 0"
     have t0: " (floor_fun m n c1) \<in> Units (SA m)"
       using floor_funE c1_Unit assms n_pos A0
       by (metis Suc_eq_plus1 Suc_le_eq add_leE)
     have t1: "e1 x = \<pp>[^](1::int) \<otimes>  (floor_fun m n c1 x)"
       unfolding e1_def using t0 A0(1) Qp_int_pow_nonzero p_nonzero
       by (meson  Qp.nonzero_memE(1) SA_Units_closed SA_smult_formula)
     have t2: " (floor_fun m n c1 x) \<in> nonzero Q\<^sub>p"
       using t0 A0(1)  SA_Units_nonzero by blast
     have t3: "val  (floor_fun m n c1 x) = ord  (floor_fun m n c1 x)"
       by(rule val_ord ,rule t2)
     have t4: "\<pp> [^] (1::int) \<in> nonzero Q\<^sub>p"
       using Qp_int_pow_nonzero p_nonzero by blast
     have t5: "local.ord (\<pp> [^] (1 ::int)) = 1"
       using ord_p_pow_int by blast
     have t6: "val (\<pp>[^](1::int) \<otimes>  (floor_fun m n c1 x)) = ord (\<pp>[^](1::int) \<otimes>  (floor_fun m n c1 x))"
       apply(rule val_ord)
       using t2 t4 Units_eq_nonzero by blast
     have t7: "ord (\<pp>[^](1::int) \<otimes>  (floor_fun m n c1 x)) = ord (floor_fun m n c1 x) + 1"
       using ord_mult[of "\<pp>[^](1::int)" "floor_fun m n c1 x"] t4 t2 unfolding t5
       by linarith
     show " (val (floor_fun m n c1 x) < j) = (val (e1 x) \<le> j)"
       unfolding  t1 t3 t6 t7 eint_ord_code by linarith 
   qed
   obtain e2 where e2_def: "e2 = ceiling_fun m n d2"
     by blast 
   have smult_Unit: "\<And>f. f \<in> Units (SA m) \<Longrightarrow> \<pp>[^](1::int)\<odot>\<^bsub>SA m\<^esub>f \<in> Units (SA m)"
     apply(rule SA_Units_memI)
     using SA_smult_closed p_intpow_closed(1) apply blast
     using SA_Units_nonzero Qp_int_pow_nonzero p_nonzero
     by (metis  Qp.integral Qp.nonzero_memE(2) SA_Units_closed SA_car_closed SA_smult_formula p_intpow_closed(1))
   have e2_Unit: "e2 \<in> Units (SA m)"
     unfolding e2_def using ceiling_funE[of n d2 m] d2_Unit n_pos assms by linarith 
   have r2: "\<And>x j::int. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  ord (d2 x) mod n \<noteq> 0 \<Longrightarrow>  ord (c1 x) mod n \<noteq> 0 \<Longrightarrow> 
        ( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (d2 x))) = (j \<in> left_closed_interval (val (e1 x)) (val (e2 x)))"
     unfolding r0 r1 e2_def left_closed_interval_def by blast 
   have Y3_eq': "Y3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x)) } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (d2 x) mod n \<noteq> 0}\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
   proof(rule equalityI')
     fix x assume A: "x \<in> Y3"
     have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
       using A Y3_def Y1_def Y_def by blast 
     have 1: "ord (d2 x) mod n \<noteq> 0"
       using A unfolding Y3_eq Int_iff mem_Collect_eq by metis  
     have 2: "ord (c1 x) mod n \<noteq> 0"
       using A unfolding Y3_eq Int_iff mem_Collect_eq by metis  
     obtain j where j_def: " eint (j * int n) \<in> I[val (c1 x) val (d2 x)]"
       using A unfolding Y3_eq by blast 
     have 3: " ( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (d2 x))) = (j \<in> left_closed_interval (val (e1 x)) (val (e2 x)))"
       using 0 1 2 r2 by blast 
     have 4: "j \<in> left_closed_interval (val (e1 x)) (val (e2 x))"
       using j_def unfolding 3 by blast 
     have 5: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x))}"
       using A Y3_eq 4 by blast 
     show " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x))} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (d2 x) mod int n \<noteq> 0} \<inter>
{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0}"
       using 5 A unfolding Y3_eq 
     proof -
       assume "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint (j * int n) \<in> I[val (c1 x) val (d2 x)]} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (d2 x) mod int n \<noteq> 0} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0}"
       have "x \<in> {rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ((\<exists>i. eint i \<in> left_closed_interval (val (e1 rs)) (val (e2 rs))) \<and> local.ord (d2 rs) mod int n \<noteq> 0) \<and> local.ord (c1 rs) mod int n \<noteq> 0}"
         using "5" "1" "2" by blast
       then show ?thesis
         by (metis mem_Collect_inter)
     qed                                 
   next
     fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x))} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (d2 x) mod int n \<noteq> 0} \<inter>
    {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0}"
     have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
       using A Y3_def Y1_def Y_def by blast 
     have 1: "ord (d2 x) mod n \<noteq> 0"
       using A unfolding Y3_eq Int_iff mem_Collect_eq by metis  
     have 2: "ord (c1 x) mod n \<noteq> 0"
       using A unfolding Y3_eq Int_iff mem_Collect_eq by metis  
     obtain j::int where j_def: " j \<in> left_closed_interval (val (e1 x)) (val (e2 x))"
       using A by blast 
     have 3: " ( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (d2 x))) = (j \<in> left_closed_interval (val (e1 x)) (val (e2 x)))"
       using 0 1 2 r2 by blast 
     have 4: "( eint (j * int n) \<in> closed_interval (val (c1 x)) (val (d2 x)))"
       unfolding 3 using j_def by blast 
     show "x \<in> Y3"
       unfolding Y3_eq Int_iff 
       apply(rule conjI, rule conjI)
       using 4 0 apply blast
       using 1 0 apply blast
       using 2 0 by blast 
   qed
   have r3: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> left_closed_interval (val (e1 x)) (val (e2 x)) } =   
             {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>).(val (e1 x)) < (val (e2 x)) }"
   proof(rule equalityI')
     fix x assume A: " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>xa. eint xa \<in> left_closed_interval (val (e1 x)) (val (e2 x))} "
     then obtain j::int where j_def: "eint j \<in> left_closed_interval (val (e1 x)) (val (e2 x))"
       by blast 
     have " val (e1 x) < val (e2 x)"
       using le_less_trans[of _ "eint j"] j_def unfolding left_closed_interval_def by blast 
     thus " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (e1 x) < val (e2 x)}"
       using A by blast 
   next
     fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (e1 x) < val (e2 x)}"
     have r0: "e1 x \<in> nonzero Q\<^sub>p"
       using e1_Unit A SA_Units_nonzero by blast 
     have r1: "val (e1 x) = ord (e1 x)"
       by(rule val_ord, rule r0)
     have r2: "val (e1 x) \<in> left_closed_interval (val (e1 x)) (val (e2 x))"
       apply(rule left_closed_interval_memI)
       apply blast
       using A  by blast 
     show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>xa. eint xa \<in> left_closed_interval (val (e1 x)) (val (e2 x))}"
       unfolding mem_Collect_eq 
       using A r2 unfolding r1 by blast 
   qed
   have r4: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (d2 x) mod int n \<noteq> 0} =    
              carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (d2 x) mod int n = 0}"
     by fastforce
   have r5: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n \<noteq> 0} =    
              carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n = 0}"
     by fastforce
   have Y3_eq'': "Y3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>).(val (e1 x)) < (val (e2 x)) }\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (d2 x) mod n \<noteq> 0}\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
     unfolding Y3_eq' r3 by blast 
   show ?thesis unfolding Y3_eq''
     apply(rule intersection_is_semialg, rule intersection_is_semialg)
     using e1_Unit e2_Unit semialg_val_strict_ineq_set_is_semialg apply blast
     unfolding r4 apply(rule diff_is_semialgebraic)
     apply(rule carrier_is_semialgebraic)
     using d2_Unit SA_unit_cong_set_is_semialg apply blast
     unfolding r5 apply(rule diff_is_semialgebraic)
     apply(rule carrier_is_semialgebraic)
     using c1_Unit SA_unit_cong_set_is_semialg by blast
 qed
 have Y1_un: "Y1 = Y2 \<union> Y3"
   unfolding Y3_def using Y2_def by blast 
 show ?thesis unfolding Y1_un
   by(rule union_is_semialgebraic, rule Y2_semialg, rule Y3_semialg)
qed

lemma left_closed_interval_imp_Y_semialg:
  assumes left_closed: "I = left_closed_interval"
  shows "is_semialgebraic m Y"
proof-
   have Y0_eq: "Y0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) < val (c2 x) } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n = 0}"
   proof(rule equalityI')
     fix x assume A: "x \<in> Y0"
     have q0: "val (c1 x) < val (c2 x)"
       using A unfolding Y0_def Y_def unfolding assms mem_Collect_eq Int_iff left_closed_interval_def 
       using le_less_trans[of "val (c1 x)" _ "val (c2 x)"] 
       by blast                           
     show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) < val (c2 x) } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n = 0}"
       using A unfolding Y0_def using q0 by blast 
   next
     fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (c1 x) < val (c2 x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). local.ord (c1 x) mod int n = 0}"
     then obtain j::int where j_def: "ord (c1 x) = j*n"
       unfolding Int_iff mem_Collect_eq 
       using mod_zeroE by presburger
     have q1: "(c1 x) \<in> nonzero Q\<^sub>p"
       using c1_Unit A SA_Units_nonzero by blast  
     have q2: "c2 x \<in> nonzero Q\<^sub>p"
       using c2_Unit A SA_Units_nonzero by blast  
     have q3: "val (c1 x) = ord (c1 x)"
       using q1 val_ord by metis
     have q4: "val (c2 x) = ord (c2 x)"
       using q2 val_ord by metis
     have q5: "val (c1 x) = j*n"
       unfolding q3 j_def by blast 
     have q5: "j*n \<in> I (val (c1 x)) (val (c2 x))"
       unfolding assms apply(rule left_closed_interval_memI)
       unfolding q5 apply blast
       using A unfolding mem_Collect_eq Int_iff unfolding q5 by blast 
     show "x \<in> Y0"
       unfolding Y0_def Y_def using A q5 by blast 
   qed
   have Y0_semialg: "is_semialgebraic m Y0"
     unfolding Y0_eq 
     apply(rule intersection_is_semialg)
     using c1_closed c2_closed semialg_val_strict_ineq_set_is_semialg apply blast
     using c1_Unit SA_unit_cong_set_is_semialg by blast                          
   have Y_diff: "Y - Y0 = Y \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (c1 x) mod n \<noteq> 0}"
     unfolding Y_def Y0_def apply(rule equalityI')
     unfolding Diff_iff Int_iff 
     apply (metis (mono_tags, lifting) mem_Collect_eq)
     unfolding mem_Collect_eq 
     by meson  
   have Y_un: "Y = Y1 \<union> Y0"
     unfolding Y1_def using Y0_def by blast 
   have Y_semialg: "is_semialgebraic m Y"
     unfolding Y_un by(intro union_is_semialgebraic assms left_closed_interval_imp_Y1_semialg Y0_semialg)
   thus ?thesis unfolding Y_def by blast 
qed

lemma Y_semialg: 
"is_semialgebraic m Y"
using convex ray_imp_Y_semialg closed_interval_imp_Y_semialg left_closed_interval_imp_Y_semialg 
  unfolding is_convex_condition_def by auto 

lemma W0_upper_val: 
  assumes "x \<in> W0"
  shows "val (b2 x) = \<infinity>"
  using assms val_zero unfolding W0_def mem_Collect_eq Int_iff
  by auto 

lemma W_min_W0: 
  assumes "I = closed_interval \<or> I = left_closed_interval"
  shows "W - W0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). b1 x \<noteq> \<zero>} \<inter> (Y - W0)"
proof- 
  have 0: "\<And>x. x \<in> W - W0 \<Longrightarrow>  c1 x = b1 x"
    using assms t2 by auto 
  have 1: "\<And>x. x \<in> W - W0 \<Longrightarrow>  c2 x = b2 x"
    using assms t0 by auto 
  show ?thesis 
  unfolding Y_def
   apply(rule equalityI')
   apply(rule IntI) 
   using assms b1_non W_def nonzero_memE apply blast                       
   apply(rule DiffI) unfolding mem_Collect_eq
   unfolding 0 1 unfolding  W_def apply blast 
   apply( blast, rule DiffI)
   unfolding mem_Collect_eq t5 t6 apply blast
   by blast 
qed

lemma ray_imp_W_semialg: 
  assumes "I = open_ray \<or> I = closed_ray"
  shows "is_semialgebraic m W"
proof- 
  have "W = carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    apply(rule equalityI',unfold W_def, blast, unfold mem_Collect_eq, rule conjI, blast)
  proof- 
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    obtain k where k_def: "eint k < val (b2 x)"
      by (metis eint_ord_simps(6) ex_val_less not_eint_eq)
    obtain j where j_def: "j * int n < k"
      using low_multiple[of n] n_pos by auto 
    hence 2: "eint (j * int n) < val (b2 x)"
      using k_def 
      by (meson eint_ord_code(1) int.lless_eq le_less_trans)
    have 3: "eint (j * int n) \<in> I (val (b1 x)) (val (b2 x))"
      by(intro ray_mem_criterion assms 2)
    thus "\<exists>j. eint (j * int n) \<in> I (val (b1 x)) (val (b2 x))"
      by auto 
  qed
  thus ?thesis using carrier_is_semialgebraic by auto 
qed

lemma W_as_union: "W = W0 \<union> (W - W0)"
  using W0_int_W by auto 

lemma W_semialg: "is_semialgebraic m W"
proof(cases "I = open_ray \<or> I = closed_ray")
  case True
  then show ?thesis by(rule ray_imp_W_semialg)
next
  case False
  hence 0: "W - W0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). b1 x \<noteq> \<zero>} \<inter> (Y - W0)"
    using W_min_W0 convex is_convex_condition_def by blast 
  have "is_semialgebraic m (W0 \<union> (W - W0))"
    unfolding 0
    by(intro union_is_semialgebraic W0_semialg diff_is_semialgebraic intersection_is_semialg
                SA_nonzero_set_is_semialg b1_closed Y_semialg)    
  thus ?thesis using W_as_union by auto 
qed
end


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Partitions by $n^{th}$ Power Residues\<close>
(**************************************************************************************************)
(**************************************************************************************************)


locale h_partition = padic_fields +
  fixes l::nat
  fixes h 
  fixes Is:: "'c set"
  fixes C m
  assumes Is_finite: "finite Is"
  assumes Is_nonempty: "Is \<noteq> {}"
  assumes n_pos: "l > 0"
  assumes h_semialg: "\<And>i. i \<in> Is \<Longrightarrow> (h i) \<in> carrier (SA m)"
  assumes C_semialg: "is_semialgebraic m C"

context h_partition
begin

definition h_res where h_res_def: "h_res b a   = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res l (h b x) = a } \<inter> C"

lemma p3: "\<And> a b. b \<in> Is \<Longrightarrow> a \<in> pow_res_classes l \<union> {{\<zero>}} \<Longrightarrow> (h_res b a) = h b  \<inverse>\<^bsub>m\<^esub> a \<inter> C"
proof-
  fix a b assume A0: "b \<in> Is" "a \<in> pow_res_classes l \<union> {{\<zero>}}"
  show 0: "(h_res b a) = h b  \<inverse>\<^bsub>m\<^esub> a \<inter> C"
    unfolding h_res_def evimage_def 
  proof(rule equalityI')
    fix x assume A1: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res l (h b x) = a} \<inter> C"
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A1 by blast 
    have pow_res: "pow_res l (h b x) = a"
      using A1 by blast 
    have hbx_closed: "h b x \<in> carrier Q\<^sub>p"
      using A0 h_semialg x_closed SA_car_closed by blast
    have 0: "h b x \<in> pow_res l (h b x)"
      using hbx_closed pow_res_refl by blast 
    show "x \<in> h b -` a \<inter> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<inter> C"
      using A1 using 0 unfolding pow_res by blast 
  next
    fix x assume A1: "x \<in> h b -` a \<inter> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<inter> C "
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A1 by blast 
    have hbx_closed: "h b x \<in> carrier Q\<^sub>p"
      using A0 h_semialg x_closed SA_car_closed by blast
    have 0: "h b x \<in> pow_res l (h b x)"
      using hbx_closed pow_res_refl by blast 
    have 1: "pow_res l (h b x) \<in> pow_res_classes l \<union> {{\<zero>}}"
      apply(cases "h b x = \<zero>")
      using pow_res_of_zero[of "l"] 
      apply (metis Un_iff singletonI)           
      using hbx_closed pow_res_classes_def unfolding nonzero_def by blast 
    have 2: "h b x \<in> a"
      using A1 by blast 
    have 3: "pow_res l (h b x) = a"
      using  A0 1 pow_res_classes_disjoint[of l] n_pos disjointE[of "(pow_res_classes l \<union> {{\<zero>}})"] 0 2 
      by (metis (no_types, lifting) IntI all_not_in_conv disjointE gr0I)
    show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res l (h b x) = a} \<inter> C"
      unfolding 3 mem_Collect_eq  Int_iff using A1 by blast 
  qed
qed

lemma p4: "\<And> a.  a \<in> pow_res_classes l \<union> {{\<zero>}} \<Longrightarrow> is_univ_semialgebraic a"
proof- 
fix a assume A0: "a \<in> pow_res_classes l \<union> {{\<zero>}}"
  show 1: "is_univ_semialgebraic a"
    apply(cases "a \<in> pow_res_classes l")
    using pow_res_is_univ_semialgebraic unfolding pow_res_classes_def nonzero_def apply blast
  proof- 
    assume A: "a \<notin> {S. \<exists>x\<in>{a \<in> carrier Q\<^sub>p. a \<noteq> \<zero>}. S = pow_res l x}"
    then have 0: "a  = {\<zero>}"
      using A0 unfolding pow_res_classes_def nonzero_def by blast 
    show "is_univ_semialgebraic a"
      unfolding 0 
      by (metis Qp.zero_closed pow_res_is_univ_semialgebraic pow_res_of_zero)
  qed
qed

lemma h_res_closed: "\<And> a b. b \<in> Is \<Longrightarrow> a \<in> pow_res_classes l \<union> {{\<zero>}} \<Longrightarrow> is_semialgebraic m (h_res b a)"
  unfolding p3  apply(rule intersection_is_semialg)
 apply(rule evimage_is_semialg)
  apply(rule h_semialg, blast)
  using p4 apply blast
  using C_semialg by auto 

definition Rs where Rs_def: "Rs b =  h_res b `(pow_res_classes l \<union> {{\<zero>}})" 

lemma Rs_disjoint: "\<And> b. b \<in> Is \<Longrightarrow> disjoint (Rs b)"
proof-
 fix x assume A0: "x \<in> Is"
 show "disjoint (Rs x)"
 proof(rule disjointI)
   fix A B assume A: "A \<in> Rs x" "B \<in> Rs x" "A \<noteq> B "
   obtain  a where a_def: "a \<in> (pow_res_classes l \<union> {{\<zero>}}) \<and> A = h_res x a"
     using A A0 unfolding Rs_def by blast 
   obtain  b where b_def: "b \<in> (pow_res_classes l \<union> {{\<zero>}}) \<and> B = h_res x b"
     using A A0 unfolding Rs_def by blast 
   have 0: "a \<inter> b = {}"
     apply(rule disjointE[of "(pow_res_classes l \<union> {{\<zero>}})"])
        apply(rule pow_res_classes_disjoint)
     using A0 n_pos apply blast
     using a_def apply blast
     using b_def apply blast using A a_def b_def by blast 
   have 1: "(h_res x a) = h x  \<inverse>\<^bsub>m\<^esub> a \<inter> C"
     using A0 p3[of x a] a_def by metis 
   have 2: "(h_res x b) = h x  \<inverse>\<^bsub>m\<^esub> b \<inter> C"
     using A0 p3[of x b] b_def by metis 
   show "A \<inter> B = {}"
     using a_def b_def 0 
     unfolding 1 2 evimage_def by blast 
 qed
qed

lemma Rs_covers: "\<And>b. b \<in> Is \<Longrightarrow> C = (\<Union> (Rs b))"
proof- 
 fix x assume A0: "x \<in> Is"
 show "C = \<Union> (Rs x)"
 proof(rule equalityI')
   fix y assume A: "y \<in> C"
   have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
     using A C_semialg is_semialgebraic_closed by blast 
   have 0: "h x y \<in> carrier Q\<^sub>p"
     using A0 h_semialg SA_car_closed y_closed by blast 
   obtain a where a_def: "a = pow_res l (h x y)"
     by blast 
   have a_in: "a \<in> (pow_res_classes l \<union> {{\<zero>}})"
     apply(cases "h x y = \<zero>")
     unfolding a_def using pow_res_zero[of "l"]  A0 
      apply (metis UnCI pow_res_of_zero singletonI)
     unfolding pow_res_classes_def nonzero_def using 0 by blast 
   have 1: "y \<in> h x  \<inverse>\<^bsub>m\<^esub> a \<inter> C"
     using A unfolding a_def evimage_def using pow_res_refl 0 
     using y_closed by blast
   have 2: "h_res x a = h x \<inverse>\<^bsub>m\<^esub> a \<inter> C"
     by(rule p3, rule A0, rule a_in)
   have 3: "y \<in> h_res x a"
     unfolding 2 using 1 by blast 
   show "y \<in>  \<Union> (Rs x)"
     unfolding Rs_def using 3 a_in by blast 
 next
   fix y assume A: "y \<in> \<Union> (Rs x)"
   show "y \<in> C"
     using A unfolding Rs_def h_res_def by blast 
 qed
qed

lemma Rs_partitions: "\<And>b. b \<in> Is \<Longrightarrow> Rs b partitions C"
   apply(rule is_partitionI)
    apply(rule Rs_disjoint, blast)
  using Rs_covers by blast 

definition parts where parts_def: "parts = Rs ` Is"

definition Ps where Ps_def: "Ps = family_intersect parts"

lemma Rs_finite: "\<And>b. b \<in> Is \<Longrightarrow> finite (Rs b)"
proof- fix b assume A: "b \<in> Is"
 have 0: "finite (pow_res_classes l)"
   apply(rule pow_res_classes_finite)
   using  n_pos A by linarith  
 show "finite (Rs b)"
   using A 0 unfolding Rs_def by blast 
qed

lemma Ps_partitions: "Ps partitions C"
   unfolding Ps_def apply(rule family_intersect_partitions)
   unfolding parts_def using Rs_partitions apply blast
   using Rs_finite apply blast
   using Is_finite apply blast
   using Is_nonempty by blast 

lemma Ps_semialg: "\<And>Y. Y \<in> Ps \<Longrightarrow> is_semialgebraic m Y"
   apply(rule family_intersect_SA[of m C "parts"])
   using C_semialg apply blast
   using Rs_partitions unfolding parts_def apply blast
   using Rs_finite apply blast
   using h_res_closed unfolding Rs_def apply blast
   using Is_finite apply blast
   using Is_nonempty apply blast
   unfolding Ps_def parts_def Rs_def  by blast 

lemma Ps_finite: "finite Ps"
   unfolding Ps_def unfolding family_intersect_def 
   apply(rule finite_set_imp_finite_atoms)
   unfolding parts_def using Rs_finite Is_finite by blast 

lemma Ps_pow_res: 
  assumes "A \<in> Ps"
  assumes "i \<in> Is"
  shows "\<exists> Cl \<in> pow_res_classes l \<union> {{\<zero>}}. (\<forall> x \<in> A. pow_res l (h i x) = Cl)"
proof- 
  have "\<exists>P\<in>Rs i. A \<subseteq> P"
    apply(intro family_intersect_memE[of parts C A "Rs i"])
    using Rs_partitions Rs_finite Is_finite Is_nonempty assms 
    unfolding parts_def Ps_def by auto 
  then obtain R where R_def: "R \<in> Rs i" "A \<subseteq> R"
    by blast 
  then obtain Cl where Cl_def: "Cl \<in> (pow_res_classes l \<union> {{\<zero>}})" "R = h_res i Cl"
    unfolding Rs_def by blast 
  have "(\<forall> x \<in> A. pow_res l (h i x) = Cl)"
  proof fix x assume A: "x \<in> A"
    hence 0: "x \<in> R"
      using R_def by auto 
    thus "pow_res l (h i x) = Cl"
      unfolding Cl_def h_res_def by auto 
  qed
  thus ?thesis using Cl_def by auto 
qed
end


lemma(in padic_fields) h_partition:
  assumes Is_finite: "finite Is"
  assumes Is_nonempty: "Is \<noteq> {}"
  assumes N_pos: "\<And> i. i \<in> Is \<Longrightarrow> (N i ::nat) > 0"
  assumes h_semialg: "\<And>i. i \<in> Is \<Longrightarrow> (h i) \<in> carrier (SA m)"
  assumes C_semialg: "is_semialgebraic m C"
  assumes l_def: "l = Lcm (N ` Is)"
  shows "\<exists> Ps. Ps partitions C \<and> 
               finite Ps \<and> 
               (\<forall>A \<in> Ps. is_semialgebraic m A) \<and>
               (\<forall> A \<in> Ps. (\<forall> i \<in> Is. (\<exists>Cl \<in> pow_res_classes l \<union> {{\<zero>}}. (\<forall> x \<in> A.
                                 pow_res l (h i x) = Cl))))"
proof-  
  have l_neq_0: "l \<noteq> 0"
    using Is_finite N_pos Lcm_0_iff_nat[of "N ` Is"] finite_imageI image_iff
    unfolding l_def by (metis not_less_zero)
  hence n_pos: "l > 0"
    by blast 
  interpret h_partition _ _ _ _ l
    by(unfold_locales, intro Is_finite, intro Is_nonempty,
              intro n_pos, intro h_semialg, auto,  intro C_semialg)
  have 0: "Ps partitions C \<and>
         finite Ps \<and> (\<forall>A\<in>Ps. is_semialgebraic m A) \<and>
          (\<forall>A\<in>Ps. \<forall>i\<in>Is. \<exists>Cl\<in>pow_res_classes l \<union> {{\<zero>}}. \<forall>x\<in>A. pow_res l (h i x) = Cl)"
    using Ps_partitions Ps_finite Ps_semialg Ps_pow_res by auto 
  thus ?thesis by auto 
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>The Proof of Macintyre's Theorem\<close>
(**************************************************************************************************)
(**************************************************************************************************)

locale macintyre_reduction_i = padic_fields +
  fixes Bs m 
  assumes Bs_sub: "Bs \<subseteq> basic_semialgs (Suc m)"
  assumes Bs_finite: "finite Bs"
  assumes Bs_un: "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) = \<Union> Bs"
  assumes Bs_nonempty: "Bs \<noteq> {}"

context macintyre_reduction_i
begin

definition F where F_def: "F = (\<lambda>b. (SOME f. f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc m\<^esub>]) \<and> (\<exists>(N::nat). N \<noteq> 0 \<and>
                                   b = basic_semialg_set (Suc m) N f)))"

lemma Bs_memE: 
  assumes "b \<in> Bs"
  shows "\<exists> f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc m\<^esub>]). (\<exists> (n::nat). n \<noteq> 0 \<and> b = basic_semialg_set (Suc m) n f)"
  using Bs_sub assms unfolding is_basic_semialg_def by auto 

lemma F_prop: 
  assumes "b \<in> Bs" 
  shows "F b \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc m\<^esub>]) \<and> (\<exists>(N::nat).N \<noteq> 0 \<and> b = basic_semialg_set (Suc m) N (F b))"
proof- 
  obtain f where " f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc m\<^esub>]) \<and> (\<exists> (n::nat). n \<noteq> 0 \<and> b = basic_semialg_set (Suc m) n f)"
    using assms Bs_memE by auto 
  thus ?thesis 
    using assms F_def Bs_memE SomeE by smt   
qed

lemma F_closed: "\<And>b. b \<in> Bs \<Longrightarrow> F b \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc m\<^esub>])"
  using F_prop by auto 

definition N where N_def: "N = (\<lambda>b. (SOME N. N \<noteq> 0 \<and> b = basic_semialg_set (Suc m) N (F b)))"

lemma N_prop: "\<And>b. b \<in> Bs \<Longrightarrow> N b \<noteq> 0 \<and> b = basic_semialg_set (Suc m) (N b) (F b)"
    using F_prop N_def SomeE by smt 

lemma N_nonzero: "\<And>b. b \<in> Bs \<Longrightarrow> N b > 0"
  using N_prop by auto 

lemma F_N_eval: "\<And> b. b \<in> Bs \<Longrightarrow>  b = basic_semialg_set (Suc m) (N b) (F b)"
  using N_prop by auto 


definition l::nat where l_def: "l = Lcm (N` Bs)"

lemma n_pos: "l > 0"
proof- 
  have 0: "(Lcm (N ` Bs) = 0) = (\<exists>x\<in>Bs. 0 = N x)"
    using Bs_finite Lcm_0_iff_nat[of "N ` Bs"] 
          finite_imageI[of Bs N]  not_less_zero[of l] by auto 
  have l_neq_0: "l \<noteq> 0"
    using N_nonzero 
    unfolding l_def image_iff[of 0 N Bs] 0 
    by auto     
  thus ?thesis by blast 
qed
end


locale macintyre_reduction_ii = macintyre_reduction_i + 
  fixes \<nu>:: "padic_tuple set \<Rightarrow> nat"
  fixes  Xs \<C> h H
  assumes \<C>_cell: "is_cell_condition \<C>"
  assumes \<C>_arity: "arity \<C> = m"
  assumes Xs_def: "Xs \<subseteq> Bs"
  assumes h_closed: "\<And> b. b \<in> Bs \<Longrightarrow> h b \<in> carrier (SA m)"
  assumes H_Xs: 
      "\<And>b. b \<in> Xs \<Longrightarrow> 
          H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> center \<C> (tl xs)) [^] (\<nu> b) \<in> P_pows (N b)}"
  assumes H_notXs:    
      "\<And>b. b \<notin> Xs \<Longrightarrow> 
          H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> center \<C> (tl xs)) [^] (\<nu> b) \<notin> P_pows (N b)}"


context macintyre_reduction_ii
begin

definition c where c_def: "c = center \<C>"
definition C where C_def: "C = fibre_set \<C>"
definition a1 where a1_def: "a1 = l_bound \<C>"
definition a2 where a2_def: "a2 = u_bound \<C>"
definition I where I_def: "I = boundary_condition \<C>"

lemma params: "\<C> = Cond m C c a1 a2 I"
  unfolding c_def C_def a1_def a2_def I_def using \<C>_arity condition_decomp' by auto

lemma c_closed: "c \<in> carrier (SA m)"
  using \<C>_cell is_cell_conditionE params by metis  

lemma a1_closed: "a1 \<in> carrier (SA m)"
  using \<C>_cell is_cell_conditionE params by metis  

lemma a2_closed: "a2 \<in> carrier (SA m)"
  using \<C>_cell is_cell_conditionE params by metis  

lemma I_convex: "is_convex_condition I"
  using \<C>_cell is_cell_conditionE params by metis  

lemma C_closed: "is_semialgebraic m C"
  using \<C>_cell is_cell_conditionE params by metis  

text\<open>The set B is one of the sets in the disjunction described by Denef at the beginning of his
proof. That is, B is a set of the form: 
    \[
    \ord[a_1(x)] \square_1 \ord[t - c(x)] \square_2 \ord[a_2(x)] \text{ and } x \in C \text{ and} 
    \]
    \[
    h_i(x)(t - c(x))^{\nu_i} \text{ is (is not) an } n_i\text{-th power, for } i = 1, \dots, k
    \]
\<close>

definition red_i where red_i_def: "red_i = (\<Inter>x\<in>Bs. H x \<inter> condition_to_set \<C>)"

lemma C_part: 
 "\<exists> Ps. Ps partitions C \<and> finite Ps \<and> (\<forall>A \<in> Ps. is_semialgebraic m A) \<and>
               (\<forall> A \<in> Ps. (\<forall> i \<in> Bs. (\<exists>Cl \<in> pow_res_classes l \<union> {{\<zero>}}. (\<forall> x \<in> A.
                                 pow_res l (h i x) = Cl))))"
  by(intro h_partition[of _ N] Bs_finite Bs_nonempty l_def h_closed C_closed N_nonzero, auto)

definition Ps where Ps_def: 
  "Ps = (SOME Ps. Ps partitions C \<and> finite Ps \<and> (\<forall>A \<in> Ps. is_semialgebraic m A) \<and>
               (\<forall> A \<in> Ps. (\<forall> i \<in> Bs. (\<exists>Cl \<in> pow_res_classes l \<union> {{\<zero>}}. (\<forall> x \<in> A.
                                 pow_res l (h i x) = Cl)))))"

lemma Ps_prop: "Ps partitions C \<and> finite Ps \<and> (\<forall>A \<in> Ps. is_semialgebraic m A) \<and>
               (\<forall> A \<in> Ps. (\<forall> i \<in> Bs. (\<exists>Cl \<in> pow_res_classes l \<union> {{\<zero>}}. (\<forall> x \<in> A.
                                 pow_res l (h i x) = Cl))))"
  unfolding Ps_def by(rule someI_ex, rule C_part)

lemma Ps_partitions:
"Ps partitions C"  using Ps_prop by auto 

lemma Ps_finite:
"finite Ps"  using Ps_prop by auto 

lemma Ps_semialg: 
"\<And> A. A \<in> Ps \<Longrightarrow> is_semialgebraic m A"  using Ps_prop by auto 

lemma Ps_pow_res: 
"\<And> A i. \<lbrakk>A \<in> Ps; i \<in> Bs\<rbrakk> \<Longrightarrow>
        \<exists>Cl \<in> pow_res_classes l \<union> {{\<zero>}}. (\<forall> x \<in> A. pow_res l (h i x) = Cl)"
  using Ps_prop by auto 

lemma \<C>_decomp: "is_cell_decomp m (refine_fibres \<C> ` Ps) (condition_to_set \<C>)"
   apply(rule  partition_to_cell_decomp[of \<C> m C c a1 a2 I Ps])
       apply(rule \<C>_cell)
      apply(rule params)
     apply(rule Ps_partitions)
   unfolding are_semialgebraic_def using Ps_semialg apply blast
   by(rule Ps_finite)

lemma red_i_inter: "red_i = (\<Inter>x\<in>Bs. H x) \<inter> condition_to_set \<C>"
    unfolding red_i_def using Bs_nonempty by blast 

lemma red_i_un: "red_i = (\<Union> A \<in> (refine_fibres \<C> ` Ps). (\<Inter> x \<in> Bs. H x) \<inter> condition_to_set A)"
   unfolding red_i_inter 
   using \<C>_decomp is_cell_decompE(2)[of m "refine_fibres \<C> ` Ps" "condition_to_set \<C>"]
          is_partitionE(2)[of "condition_to_set ` refine_fibres \<C> ` Ps" "condition_to_set \<C>"]
   by blast 
end


locale macintyre_reduction_iii = macintyre_reduction_ii + 
  fixes \<B> b 
  assumes b_def: "b \<in> Ps"
  assumes \<B>_def: "\<B> = refine_fibres \<C> b"


context macintyre_reduction_iii
begin

lemma b_semialg: "is_semialgebraic m b"
  using b_def Ps_semialg by auto 

lemma b_sub: "b \<subseteq> C"
  using b_def Ps_partitions is_partitionE(2) by auto 

definition \<alpha> where \<alpha>_def: 
"\<alpha> = (\<lambda> a. (SOME y. y \<in> insert \<zero> (nth_pow_wits l) \<and> 
             (\<forall>x \<in> b. pow_res l (h a x) = pow_res l y)))"

lemma \<alpha>_props: 
  assumes "i \<in> Bs"
  shows "\<alpha> i \<in> insert \<zero> (nth_pow_wits l)"
        "\<And> x. \<lbrakk>x \<in> b\<rbrakk> \<Longrightarrow> pow_res l (h i x) = pow_res l (\<alpha> i)"
proof- 
  obtain Cl where Cl_def:  "Cl \<in> pow_res_classes l \<union> {{\<zero>}} \<and> (\<forall> x \<in> b. pow_res l (h i x) = Cl)"
    using Ps_pow_res[of b i] b_def assms by blast 
  have 0: "\<exists> y \<in> insert \<zero> (nth_pow_wits l). Cl = pow_res l y"
  proof(cases "Cl = {\<zero>}")
    case True
    then show ?thesis unfolding True using pow_res_zero n_pos by auto 
  next
    case False
    then have "Cl \<in> pow_res_classes l"
      using Cl_def by auto 
    thus ?thesis using nth_pow_wits_covers[of l ]  False n_pos 
      by (smt (verit, del_insts) F.not_nonzero_memE Int_iff Q\<^sub>p_def equal_pow_resI insertCI 
          nth_pow_wits_exists pow_res_classes_mem_eq val_ring_memE(2))
  qed
  have "\<alpha> i \<in> insert \<zero> (nth_pow_wits l) \<and> 
             (\<forall>x \<in> b. pow_res l (h i x) = pow_res l (\<alpha> i) )"
    unfolding \<alpha>_def apply(rule someI_ex)
    by (metis Cl_def 0)
  thus "\<alpha> i \<in> insert \<zero> (nth_pow_wits l)"
        "\<And> x. \<lbrakk>x \<in> b\<rbrakk> \<Longrightarrow> pow_res l (h i x) = pow_res l (\<alpha> i)"
    using b_def assms by auto 
qed

lemma \<alpha>_closed: 
  assumes "i \<in> Bs"
  shows "\<alpha> i \<in> carrier Q\<^sub>p"
  using \<alpha>_props assms nth_pow_wits_closed 
  by (metis insert_iff n_pos val_ring_memE(2) zero_in_val_ring)

lemma \<B>_cond: 
"is_cell_condition \<B>"
  by(unfold \<B>_def, intro refine_fibres_is_cell[of \<C> m C c a1 a2 I b] params \<C>_cell b_semialg b_sub)

lemma \<B>_arity: 
"arity \<B> = m"
  using \<B>_def \<C>_arity refine_fibres_def arity.simps by auto 

lemma \<B>_params: 
"\<B> = Cond m b c a1 a2 I"
  unfolding \<B>_def using params refine_fibres_def 
  by (simp add: I_def \<C>_arity a1_def a2_def c_def)

lemma iib: "macintyre_reduction_ii p Bs m \<nu> Xs \<B> h H"
     apply(unfold_locales) 
  using Xs_def \<B>_cond h_closed H_Xs H_notXs Q\<^sub>p_def Z\<^sub>p_def \<B>_arity unfolding \<B>_params c_def by auto 

definition H1 where H1_def: "H1 = (\<lambda>a. center_term m c  \<inverse>\<^bsub>Suc m\<^esub> a)"


lemma H1_subset: "\<And>a. H1 a \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  unfolding H1_def evimage_def by blast 

lemma H1_covers: "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) = (\<Union> a \<in> pow_res_classes l \<union> {{\<zero>}}. H1 a)"
proof(rule equalityI')
 fix x assume x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
 have 0: "center_term m c x \<in> carrier Q\<^sub>p"
   using center_term_closed SA_car_closed c_closed x_closed by blast 
 have 1: "pow_res l (center_term m c x) \<in> pow_res_classes l \<union> {{\<zero>}}"
   apply(cases "center_term m c x = \<zero>")
   using pow_res_zero n_pos apply(metis UnCI singletonI)
   unfolding pow_res_classes_def using 0 Qp.nonzero_memI by blast
 have 2: "center_term m c x \<in> pow_res l (center_term m c x)"
   using pow_res_refl 0 by blast 
 thus "x \<in> \<Union> (H1 ` (pow_res_classes l \<union> {{\<zero>}}))"
   using x_closed 2 1 unfolding H1_def evimage_def by blast 
next
 show " \<And>x. x \<in> \<Union> (H1 ` (pow_res_classes l \<union> {{\<zero>}})) \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
   using H1_subset by blast 
qed

lemma H1_disjoint: "disjoint (H1 ` (pow_res_classes l \<union> {{\<zero>}}))"
proof(rule disjointI) 
 fix b A B assume A: "A \<in> H1 ` (pow_res_classes l \<union> {{\<zero>}})" "B \<in> H1 ` (pow_res_classes l \<union> {{\<zero>}})" "A \<noteq> B"
 obtain x where x_def: "x \<in> (pow_res_classes l \<union> {{\<zero>}}) \<and> A = H1 x"
   using A by blast 
 obtain y where y_def: "y \<in> (pow_res_classes l \<union> {{\<zero>}}) \<and> B = H1 y"
   using A by blast 
 have x_neq_y: "x \<noteq> y"
   using A x_def y_def by blast 
 have A_eq: "A = H1 x"
   using x_def by blast 
 have B_eq: "B = H1 y"
   using y_def by blast 
 show "A \<inter> B = {}"
   using A pow_res_classes_disjoint[of l]  x_neq_y  n_pos disjointE[of "pow_res_classes l \<union> {{\<zero>}}" x y] 
   unfolding H1_def evimage_def A_eq B_eq 
 proof -
   have "x \<inter> y = {}"
     using \<open>0 < l \<Longrightarrow> disjoint (pow_res_classes l \<union> {{\<zero>}})\<close> \<open>0 < l\<close> \<open>\<lbrakk>disjoint (pow_res_classes l \<union> {{\<zero>}}); x \<in> pow_res_classes l \<union> {{\<zero>}}; y \<in> pow_res_classes l \<union> {{\<zero>}}; x \<noteq> y\<rbrakk> \<Longrightarrow> x \<inter> y = {}\<close> \<open>x \<noteq> y\<close> x_def y_def by fastforce
   then show "center_term m c -` x \<inter> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<inter> (center_term m c -` y \<inter> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) = {}"
     by blast
 qed
qed

definition red_ii where red_ii_def: 
"red_ii = (\<Inter>x\<in>Bs. H x \<inter> condition_to_set \<B>)"

lemma \<alpha>_pow_res: "\<And>b t x. b \<in> Bs \<Longrightarrow> t#x \<in> condition_to_set \<B> \<Longrightarrow> 
                                              pow_res l (h b x) = pow_res l (\<alpha> b)"
   apply(rule \<alpha>_props , blast)
  unfolding \<B>_params condition_to_set.simps cell_def mem_Collect_eq list_tl by blast 

lemma red_ii_finite_union: 
"red_ii = (\<Union> a \<in> pow_res_classes l \<union> {{\<zero>}}. (\<Inter> b \<in> Bs. H b \<inter> H1 a \<inter> condition_to_set \<B>))"
proof- 
  have red_ii_inter: "red_ii = (\<Inter>x\<in>Bs. H x) \<inter> condition_to_set \<B>"
    unfolding red_ii_def using Bs_nonempty by auto 
  have red_ii_subset: "red_ii \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using Bs_nonempty unfolding red_ii_def unfolding \<B>_params condition_to_set.simps cell_def 
    by auto 
  have red_ii_inter': "red_ii = carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<inter> \<Inter> (H ` Bs) \<inter> condition_to_set \<B>"
    using red_ii_def red_ii_subset  Bs_nonempty  by blast 
  have 0: 
    "red_ii = (\<Union> a \<in> pow_res_classes l \<union> {{\<zero>}}. H1 a \<inter> (\<Inter> b \<in> Bs. H b) \<inter> condition_to_set \<B>)"
    unfolding red_ii_inter' H1_covers by blast 
  have 1: "\<And> a. a \<in> pow_res_classes l \<union> {{\<zero>}} \<Longrightarrow> 
     H1 a \<inter> (\<Inter> b \<in> Bs. H b) \<inter> condition_to_set \<B> = (\<Inter> b \<in> Bs. H b \<inter> H1 a \<inter> condition_to_set \<B>)"
    using Bs_nonempty by auto 
  show ?thesis unfolding 0 using 1 by auto 
qed
end


locale macintyre_reduction_iv = macintyre_reduction_iii + 
  fixes a :: "padic_number set"
  assumes a_def: "a \<in> pow_res_classes l \<union> {{\<zero>}}"


context macintyre_reduction_iv
begin

lemma pow_res_class_closure: "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> pow_res l x \<in> (pow_res_classes l \<union> {{\<zero>}})"
proof- fix x assume A: "x \<in> carrier Q\<^sub>p"
 show "pow_res l x \<in> (pow_res_classes l \<union> {{\<zero>}})"
   apply(cases "x = \<zero>")
   using pow_res_zero n_pos apply blast
   unfolding pow_res_classes_def nonzero_def using A by blast 
qed

lemma pow_res_eq_lemma:
 "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> x \<in> a \<Longrightarrow> pow_res l x = a"
 using pow_res_class_closure pow_res_classes_disjoint[of l] n_pos a_def
      Un_iff padic_fields.pow_res_classes_mem_eq  padic_fields_axioms pow_res_of_zero singleton_mem
  by metis 

lemma \<gamma>_ex: "\<And>b. b \<in> Bs \<Longrightarrow> 
      \<exists>\<gamma> \<in> carrier Q\<^sub>p. (\<forall>xs \<in>  H1 a \<inter> condition_to_set \<B>. 
                pow_res l (h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b) = pow_res l \<gamma>)"
proof- fix b assume A0: "b \<in> Bs"
 have sub: "H1 a \<inter> condition_to_set \<B> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
   unfolding H1_def evimage_def by blast 
 have e1: "\<And>xs. xs \<in>  H1 a \<Longrightarrow> (center_term m c xs) \<in> a"
   unfolding H1_def unfolding evimage_def by blast 
 have e2: "\<And>xs. xs \<in> H1 a \<Longrightarrow> center_term m c xs \<in> pow_res l (center_term m c xs)"
   apply(rule pow_res_refl)
   using center_term_closed c_closed SA_car_closed
   unfolding H1_def evimage_def by blast 
 have e3: "\<And>xs. xs \<in> H1 a \<Longrightarrow> pow_res l (center_term m c xs) = a"
   apply(rule pow_res_eq_lemma)
   using center_term_closed c_closed SA_car_closed
   unfolding H1_def evimage_def apply blast
   by blast 
 obtain \<beta> where \<beta>_def: "\<beta> \<in> a"
   using a_def unfolding pow_res_classes_def 
   by (smt Qp.nonzero_memE(1) mem_Collect_eq mem_simps(3) pow_res_refl singleton_mem)
 have e4: "\<And>xs. xs \<in>  H1 a \<inter> condition_to_set \<B> \<Longrightarrow> pow_res l (h b (tl xs)) = pow_res l (\<alpha> b)"
 proof- fix xs assume A: "xs \<in> H1 a \<inter> condition_to_set \<B>"              
   have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
     using A unfolding H1_def evimage_def by blast  
   obtain t x where tx_def: "xs = t#x"
     using xs_closed Qp_pow_Suc_decomp by blast  
   have t_closed: "t \<in> carrier Q\<^sub>p"
     using xs_closed unfolding tx_def  
     by (metis Qp_pow_ConsE list_hd)
   have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
     using xs_closed unfolding tx_def 
     by (metis Qp_pow_ConsE(1) list_tl)
   have 0: "pow_res l (h b x) = pow_res l (\<alpha> b)"
     apply(rule \<alpha>_pow_res[of  _ t])
     using A0 Xs_def apply blast
     using A unfolding tx_def by blast 
   thus "pow_res l (h b (tl xs)) = pow_res l (\<alpha> b)"
     unfolding tx_def list_tl by blast 
 qed
 obtain \<gamma> where \<gamma>_def: "\<gamma> = \<alpha> b \<otimes> \<beta>[^]\<nu> b"
   by blast 
 have b_in: "b \<in> Bs"
   using A0 Xs_def by blast 
 have e5: "\<alpha> b \<in> carrier Q\<^sub>p"
   apply(cases "\<alpha> b = \<zero>")
   using Qp.zero_closed apply metis 
   using A0 \<alpha>_props b_in nth_pow_wits_closed[of l "\<alpha> b"] Xs_def n_pos Qp.zero_closed 
   by blast 
 have e6: "a \<subseteq> carrier Q\<^sub>p"
   apply(cases "a = {\<zero>}")
   using zero_closed apply blast
   using a_def unfolding pow_res_classes_def pow_res_def Un_iff mem_Collect_eq by blast 
 have \<beta>_closed: "\<beta> \<in> carrier Q\<^sub>p"
   using \<beta>_def e6 by blast 
 have \<gamma>_closed: "\<gamma> \<in> carrier Q\<^sub>p"
   unfolding \<gamma>_def using \<beta>_closed e5 
   by blast
 have e7: " pow_res l \<beta> = a"
   by(rule pow_res_eq_lemma, rule \<beta>_closed, rule \<beta>_def)
 have e8: "\<And>xs. xs \<in> H1 a \<inter> condition_to_set \<B> \<Longrightarrow>  
                                   lead_coeff xs \<ominus> c (tl xs) = center_term m c xs"
   using center_term_eval  c_closed sub by blast 
 have e9: "\<And>xs. xs \<in> H1 a \<inter> condition_to_set \<B> \<Longrightarrow> 
             pow_res l (h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b) = pow_res l \<gamma>"
   unfolding \<gamma>_def 
   apply(intro pow_res_mult  n_pos SA_car_closed[of "h b" m] h_closed cartesian_power_tail 
               \<alpha>_closed b_in e4 Qp.nat_pow_closed Qp.ring_simprules cartesian_power_head[of _ _  m]
               SA_car_closed[of c m] c_closed \<beta>_closed pow_res_nat_pow, unfold e7, unfold e8)
   using sub \<beta>_closed e3 by auto 
 show " \<exists>\<gamma> \<in> carrier Q\<^sub>p. (\<forall>xs \<in>  H1 a \<inter> condition_to_set \<B>. 
                            pow_res l (h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b) = pow_res l \<gamma>)"
   using e9 \<gamma>_closed by blast 
qed

lemma same_pow_res: "\<And>a b \<gamma>. b \<in> Bs \<Longrightarrow> a \<in> carrier Q\<^sub>p \<Longrightarrow> \<gamma> \<in> carrier Q\<^sub>p \<Longrightarrow> 
       pow_res l a = pow_res l \<gamma> \<Longrightarrow>   a \<in> P_pows (N b) \<longleftrightarrow> \<gamma> \<in> P_pows (N b)"
proof-
 fix a b \<gamma>
 assume A0: "b \<in> Bs" "a \<in> carrier Q\<^sub>p" "\<gamma> \<in> carrier Q\<^sub>p" " pow_res l a = pow_res l \<gamma> "
 have p0: "a \<in> pow_res l \<gamma>"
   using A0 pow_res_refl by blast 
 obtain y0 where y0_def: "y0 \<in> nonzero Q\<^sub>p \<and> a = \<gamma> \<otimes> y0 [^] l"
     using p0 unfolding pow_res_def by blast 
 have p1: "\<gamma> \<in> pow_res l a"
   using A0 pow_res_refl by blast 
 obtain y1 where y1_def: "y1 \<in> nonzero Q\<^sub>p \<and> \<gamma> = a \<otimes> y1 [^] l"
     using p1 unfolding pow_res_def by blast 
 have p2: "l mod (N b) = 0"
   unfolding l_def 
   apply(rule div[of "N ` Bs"])
   using Bs_finite apply blast
   apply blast
   using A0 by blast 
 obtain j where j_def: "N b * j = l"
   using p2  by (metis mod_eq_0D)
 have l_eq: "l = j * N b"
   using j_def 
   by (simp add: Groups.mult_ac(2))           
 have p3: "y0 [^] l = (y0 [^] j)[^](N b)"
   using y0_def unfolding l_eq nonzero_def mem_Collect_eq  
   using Qp_nat_pow_pow by blast
 have p4: "y1 [^] l = (y1 [^] j)[^](N b)"
   using y1_def unfolding l_eq nonzero_def mem_Collect_eq  
   using Qp_nat_pow_pow by blast
 show "(a \<in> P_pows (N b)) = (\<gamma> \<in> P_pows (N b))"
 proof
   assume A1: "a \<in> P_pows (N b)"
   obtain a0 where a0_def: "a0 \<in> carrier Q\<^sub>p \<and> a = a0[^](N b)"
     using A1 unfolding P_pows_def by blast 
   have p5: "\<gamma> = a0[^](N b) \<otimes> (y1 [^] j)[^](N b)"
     using y1_def a0_def unfolding p4 by blast 
   have p6: "\<gamma> = (a0 \<otimes> y1 [^] j)[^](N b)"
     unfolding p5 using a0_def y1_def 
       Qp.nat_pow_closed Qp.nat_pow_distrib Qp.nonzero_memE(1) by presburger
   have p7: "a0 \<otimes> y1 [^] j \<in> carrier Q\<^sub>p"
     using a0_def y1_def Qp.nonzero_memE(1) by blast
   show "\<gamma> \<in> P_pows (N b)"
     unfolding P_pows_def mem_Collect_eq 
     using p6 a0_def y1_def p7 by blast 
 next 
   assume A1: "\<gamma> \<in> P_pows (N b)"
   obtain a0 where a0_def: "a0 \<in> carrier Q\<^sub>p \<and> \<gamma> = a0[^](N b)"
     using A1 unfolding P_pows_def by blast 
   have p5: "a = a0[^](N b) \<otimes> (y0 [^] j)[^](N b)"
     using y0_def a0_def unfolding p3 by blast 
   have p6: "a = (a0 \<otimes> y0 [^] j)[^](N b)"
     unfolding p5 using a0_def y0_def 
       Qp.nat_pow_closed Qp.nat_pow_distrib Qp.nonzero_memE(1) by presburger
   have p7: "a0 \<otimes> y0 [^] j \<in> carrier Q\<^sub>p"
     using a0_def y0_def Qp.nonzero_memE(1) by blast
   show "a \<in> P_pows (N b)"
     unfolding P_pows_def mem_Collect_eq 
     using p6 a0_def y1_def p7 by blast 
 qed
qed

definition \<gamma> where \<gamma>_def:
    "\<gamma> = (\<lambda>b. (SOME \<gamma>. \<gamma> \<in> carrier Q\<^sub>p \<and> (\<forall>xs \<in>  H1 a \<inter> condition_to_set \<B>. 
                       pow_res l (h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b) = pow_res l \<gamma>)))"
 
lemma \<gamma>_eval: "\<And>b. b \<in> Bs \<Longrightarrow> 
  \<gamma> b \<in> carrier Q\<^sub>p \<and> (\<forall>xs \<in> H1 a \<inter> condition_to_set \<B>. 
  pow_res l (h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b) = pow_res l (\<gamma> b))"
  unfolding \<gamma>_def apply(rule someI_ex) by (meson \<gamma>_ex)

lemma h_term_closed:
  assumes "xs \<in> H1 a \<inter> condition_to_set \<B>"
  assumes "i \<in> Bs"
  shows "h i (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> i \<in> carrier Q\<^sub>p"
        "(h i (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> i \<in> P_pows (N i)) = (\<gamma> i \<in> P_pows (N i))"
proof- 
  show 0: "h i (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> i \<in> carrier Q\<^sub>p"
  apply(intro Qp.nat_pow_closed Qp.ring_simprules SA_car_closed[of "h i" m] cartesian_power_head[of _ _ m]
                  SA_car_closed[of c m] c_closed h_closed cartesian_power_tail )
     using assms unfolding \<B>_params condition_to_set.simps cell_def by auto
   show "(h i (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> i \<in> P_pows (N i)) = (\<gamma> i \<in> P_pows (N i))"
     apply(intro same_pow_res 0 assms)
     using  Xs_def \<gamma>_eval[of i] assms Xs_def  by auto
qed

lemma H_inter_reduce_on_Xs: "\<And>b. b \<in> Xs \<Longrightarrow> \<gamma> b \<in> P_pows (N b) \<Longrightarrow>
             H b \<inter> H1 a \<inter> condition_to_set \<B> = H1 a \<inter> condition_to_set \<B>"
proof- 
 fix b assume A0: "b \<in> Xs" "\<gamma> b \<in> P_pows (N b)"
 have e1: "H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)}"
   using H_Xs[of b] A0 unfolding c_def by blast
 show " H b \<inter> H1 a \<inter> condition_to_set \<B> = H1 a \<inter> condition_to_set \<B>"
 proof(rule equalityI', blast)
   fix xs assume A: "xs \<in> H1 a \<inter> condition_to_set \<B>"
   have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
     using A unfolding H1_def evimage_def by blast 
   have 1: "(h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)) = (\<gamma> b \<in> P_pows (N b))"
     apply(intro h_term_closed)
     using A0 A Xs_def by auto
   show "xs \<in> H b \<inter> H1 a \<inter> condition_to_set \<B>"
     unfolding e1 Int_iff
     apply(rule conjI)
     unfolding mem_Collect_eq 1 using A0 A xs_closed apply blast
     using A by blast 
 qed
qed

lemma H_inter_empty: "\<And>b. b \<in> Xs \<Longrightarrow> \<gamma> b \<notin> P_pows (N b) \<Longrightarrow>  H b \<inter> H1 a \<inter> condition_to_set \<B> = {}"
proof-
 fix b assume A0: "b \<in> Xs" "\<gamma> b \<notin> P_pows (N b)"
 have e1: "H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)}"
   using H_Xs[of b] A0 unfolding c_def by blast 
 show " H b \<inter> H1 a \<inter> condition_to_set \<B>= {}"
 proof(rule equalityI')
   fix xs assume A: "xs \<in> H b \<inter> H1 a \<inter> condition_to_set \<B>"
   have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
     using A unfolding H1_def evimage_def by blast 
   have 1: "(h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)) = (\<gamma> b \<in> P_pows (N b))"
     apply(intro h_term_closed) using A0 A Xs_def by auto
   have 2: "h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)"
     using A H_Xs A0 unfolding c_def by blast 
   show "xs \<in> {}"
     using 2 A0 unfolding 1 by blast 
 next
   show "\<And>x. x \<in> {} \<Longrightarrow> x \<in> H b \<inter> H1 a \<inter> condition_to_set \<B>"
     by blast 
 qed
qed

lemma H_inter_empty': 
  "\<And>b. b \<in> Bs \<Longrightarrow> b \<notin> Xs \<Longrightarrow> \<gamma> b \<in> P_pows (N b) \<Longrightarrow>  H b \<inter> H1 a \<inter> condition_to_set \<B> = {}"
proof- 
 fix b assume A0: "b \<in> Bs" "b \<notin> Xs" "\<gamma> b \<in> P_pows (N b)"
  have e1: "H b = 
      {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<notin> P_pows (N b)}"
   using H_notXs[of b] A0 unfolding c_def by blast 
 show " H b \<inter> H1 a \<inter> condition_to_set \<B> = {}"
 proof(rule equalityI')
   fix xs assume A: "xs \<in> H b \<inter> H1 a \<inter> condition_to_set \<B>"
   have 1: "(h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)) = (\<gamma> b \<in> P_pows (N b))"
     apply(rule h_term_closed)
     using A Xs_def A0 by auto 
   show "xs  \<in> {}"
     using 1 A A0 unfolding e1 1 mem_Collect_eq  e1 Int_iff by blast 
 next
   show "\<And>x. x \<in> {} \<Longrightarrow> x \<in> H b \<inter> H1 a \<inter> condition_to_set \<B>"
     by blast 
 qed
qed

lemma H_inter_reduce_on_Xs': "\<And>b. b \<in> Bs \<Longrightarrow> b \<notin> Xs \<Longrightarrow>  \<gamma> b \<notin> P_pows (N b) \<Longrightarrow> 
                 H b \<inter> H1 a \<inter> condition_to_set \<B> =  H1 a \<inter> condition_to_set \<B>"
proof- 
 fix b assume A0: "b \<in> Bs" "b \<notin> Xs" "\<gamma> b \<notin> P_pows (N b)"
 have e1: "H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<notin>  P_pows (N b)}"
   using H_notXs[of b] A0 unfolding c_def by blast 
 show " H b \<inter> H1 a \<inter> condition_to_set \<B> =  H1 a \<inter> condition_to_set \<B>"
 proof(rule equalityI', blast)
   fix xs assume A: "xs \<in> H1 a \<inter> condition_to_set \<B>"
   have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
     using A unfolding H1_def evimage_def by blast 
   have 1: "(h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)) = (\<gamma> b \<in> P_pows (N b))"
     apply(rule h_term_closed)
     using A0 A Xs_def by auto
   show "xs \<in> H b \<inter> H1 a \<inter> condition_to_set \<B>"
     using 1 A A0 xs_closed unfolding e1 1 mem_Collect_eq  e1 Int_iff by blast 
 qed
qed

lemma reduction_iv:
  assumes A_def: "A = center_term m c  \<inverse>\<^bsub>Suc m\<^esub> a"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). 
            \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> A \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
proof(cases "a = {\<zero>}")
  case True
  have T0: "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  t \<in> carrier Q\<^sub>p \<Longrightarrow> t#x \<in> A \<longleftrightarrow> t = c x"
  proof- fix x t assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p"
    show "(t # x \<in> A) = (t = c x)"
    proof
     assume a0: "t # x \<in> A"
     have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
       using a0 unfolding A_def evimage_def by blast 
     have 0: "center_term m c (t#x) = t \<ominus> c x"
       using center_term_eval[of c m "t#x"] tx_closed c_closed 
       unfolding list_tl list_hd
       by blast 
     have 1: "t \<ominus> c x = \<zero>"
       using a0 unfolding A_def True using 0 
       unfolding evimage_def by blast 
     show "t = c x"
       using A c_closed SA_car_closed 1  Qp.r_right_minus_eq by blast
    next
     assume a0: "t = c x"
     then have "t \<ominus> c x = \<zero>"
       using A c_closed SA_car_closed Qp.r_right_minus_eq by blast
     have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
       using a0 A Qp_pow_ConsI by blast  
     have 0: "center_term m c (t#x) = t \<ominus> c x"
       using center_term_eval[of c m "t#x"] tx_closed c_closed 
       unfolding list_tl list_hd
       by blast 
     show "t # x \<in> A"
       unfolding True A_def evimage_def using 0 tx_closed 
       using \<open>t \<ominus> c x = \<zero>\<close> by blast
    qed
  qed
  have T1: "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  t \<in> carrier Q\<^sub>p \<Longrightarrow> t#x \<in> A \<longleftrightarrow> t \<ominus> c x = \<zero>"
    unfolding  T0 using c_closed SA_car_closed  Qp.r_right_minus_eq by blast
  obtain W where W_def: "W = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> A \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
    by blast 
  have T2: "\<And>x. x \<in> W \<Longrightarrow> val \<zero> \<in>  I (val (a1 x)) (val (a2 x))"
    unfolding W_def mem_Collect_eq using T1 
    by metis
  have T3: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> val \<zero> \<in>  I (val (a1 x)) (val (a2 x)) \<Longrightarrow> x \<in> W"
    unfolding W_def mem_Collect_eq apply(rule conjI, blast)
  proof-
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" " val \<zero> \<in> I (val (a1 x)) (val (a2 x))"
    obtain t where t_def: "t = c x"
      by blast 
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using A SA_car_closed c_closed unfolding t_def by blast 
    have 0: "t \<ominus> c x = \<zero>"
      using t_closed unfolding t_def 
      using Qp.r_right_minus_eq by blast
    have 1: "t#x \<in> A"
      using T1 0 t_closed A by blast 
    have "t # x \<in> A \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))"
      using 1 A t_closed T2 T1 unfolding 0 by blast  
    thus "\<exists>t\<in>carrier Q\<^sub>p. t # x \<in> A \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))"
      using t_closed by blast 
  qed
  have T4: "W = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val \<zero> \<in>  I (val (a1 x)) (val (a2 x))}"
    apply(rule equalityI')
    using T2 W_def apply blast
    using T3 by blast 
  have T5: "W = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<zero>\<^bsub>SA m\<^esub> x) \<in>  I (val (a1 x)) (val (a2 x))}"
    apply(rule equalityI')
    unfolding T4 mem_Collect_eq using SA_zeroE[of _ m] apply metis 
    using SA_zeroE[of _ m] by metis 
  have T6: "is_semialgebraic m W"
    unfolding T5 by(intro cell_cond_semialg I_convex a1_closed a2_closed, auto )
  show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> A \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
    using T6 unfolding W_def by blast 
next
  case False
  have f0: "a \<in> pow_res_classes l"
   using False a_def by blast 
  obtain \<beta> where \<beta>_def: "\<beta> \<in> a"
   using a_def unfolding pow_res_classes_def 
   by (smt Qp.nonzero_memE(1) mem_Collect_eq mem_simps(3) pow_res_refl singleton_mem)
  have a_closed: "a \<subseteq> carrier Q\<^sub>p"
   using a_def False unfolding pow_res_classes_def pow_res_def 
   by fastforce
  have \<beta>_closed: "\<beta> \<in> carrier Q\<^sub>p"
   using \<beta>_def a_closed by auto  
  have f1: "a = pow_res l \<beta>"
   using \<beta>_def 
   by (simp add: \<beta>_def f0 n_pos pow_res_classes_mem_eq)
  have f2: "\<beta> \<in> nonzero Q\<^sub>p"
   using \<beta>_def f0 pow_res_nonzero[of l] f1
   unfolding pow_res_classes_def mem_Collect_eq 
   using \<beta>_closed n_pos by blast
  obtain W where W_eq: "W = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> A \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
   by blast 
  have W_alt_def: "W = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j \<in> I (val (a1 x)) (val (a2 x)) \<and> j mod l = ord \<beta> mod l }"
  proof(rule equalityI')
    fix x assume A: "x \<in> W"
    then obtain t where t_def: "t\<in>carrier Q\<^sub>p \<and> t # x \<in> A \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))"
     unfolding W_eq by blast 
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
     using W_eq A by blast 
    have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
     using t_def x_closed Qp_pow_ConsI by blast
    have 0: "center_term m c (t#x) = t \<ominus> c x"
     using center_term_eval[of c m "t#x"] tx_closed c_closed
     unfolding list_tl list_hd by blast 
    have 1: "t \<ominus> c x \<in> a"
     using t_def unfolding A_def evimage_def using 0 
     by (metis A_def evimageD t_def)
    have 2: "t \<ominus> c x \<in> pow_res l \<beta>"
     using 1 unfolding f1 by blast 
    obtain y where y_def: "y \<in> nonzero Q\<^sub>p \<and> t \<ominus> c x =\<beta> \<otimes> y[^]l"
     using 2 unfolding pow_res_def mem_Collect_eq by blast 
    have tc_eq: "t \<ominus> c x = \<beta> \<otimes> y[^]l"
     using y_def by blast 
    have "y [^] l \<in> nonzero Q\<^sub>p"
     using y_def Qp_nat_pow_nonzero by blast
    hence 3: "t \<ominus> c x \<in> nonzero Q\<^sub>p"
     unfolding tc_eq using f2  
     by (meson Localization.submonoid.m_closed Qp.nonzero_is_submonoid)
    obtain j where j_def: "j = ord (t \<ominus> c x)"
     by blast 
    have j_val: "j = val (t \<ominus> c x)"
     using j_def val_ord 3 by presburger
    have 4: "j = ord \<beta> + l*ord y"
     unfolding j_def using ord_mult f2 y_def  monom_term_ord' by presburger
    have 5: "j mod int l = ord \<beta> mod l "
     unfolding 4 using n_pos  mod_mult_self2 by blast
    show " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint j \<in> I (val (a1 x)) (val (a2 x)) \<and> j mod int l = ord \<beta> mod l }"
     using 4 5 t_def x_closed 
     by (metis (mono_tags, lifting) j_val mem_Collect_eq)
  next
  fix x assume A: " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint j \<in> I (val (a1 x)) (val (a2 x)) \<and> j mod int l = ord \<beta> mod l }"
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
   using A by blast 
  obtain j where j_def: "eint j \<in> I (val (a1 x)) (val (a2 x)) \<and> j mod int l = ord \<beta> mod l"
   using A by blast 
  obtain e where e_def: "e = \<beta> \<otimes> \<pp>[^](j - ord \<beta>)"
   by blast 
  have 0: "\<pp>[^](j - ord \<beta>) \<in> nonzero Q\<^sub>p"
   using Qp_int_pow_nonzero p_nonzero by blast
  have 1: "ord (\<pp>[^](j - ord \<beta>)) = j - ord \<beta>"
   using ord_p_pow_int by blast
  have e_nonzero: "e \<in> nonzero Q\<^sub>p"
   unfolding e_def using 0 f2                      
   by (meson Localization.submonoid.m_closed Qp.nonzero_is_submonoid)
  have e_ord0: "ord e = ord \<beta> + (j - ord \<beta>)"
   unfolding e_def 
   using ord_mult[of \<beta> " \<pp>[^](j - ord \<beta>)"] f2 0 unfolding 1 
   by blast 
  have e_ord: "ord e = j"
   unfolding e_ord0 by linarith 
  have e_val: "val e = j"
   using e_nonzero e_ord val_ord by blast 
  have 1: "c x \<in> carrier Q\<^sub>p"
   using c_closed x_closed SA_car_closed by blast 
  obtain t where t_def: "t = e \<oplus> c x"
   by blast 
  have t_closed: "t \<in> carrier Q\<^sub>p"
   unfolding t_def apply(rule Qp.ring_simprules)
   using e_nonzero unfolding nonzero_def apply blast
   by(rule 1)
  have 2: "center_term m c (t#x) = t \<ominus> c x"
   using center_term_eval[of c m "t#x"] c_closed x_closed t_def
   unfolding list_tl list_hd 
   using Qp_pow_ConsI t_closed by blast
  have 3: "t \<ominus> c x = e"
   unfolding t_def using 1 e_def unfolding nonzero_def mem_Collect_eq a_minus_def
   by (metis "0" Qp.add.inv_solve_right' Qp.nonzero_mult_closed f2 t_closed t_def)
  have 4: "(j - ord \<beta>) mod l = 0"
   using A unfolding mem_Collect_eq 
   by (metis group_add_class.right_minus_eq j_def mod_0 mod_diff_cong mod_diff_left_eq mod_mod_trivial)
  then obtain i::int where i_def: "j - ord \<beta> = i*l"
   using n_pos mod_zeroE by presburger                    
  have 4: "\<pp>[^](j - ord \<beta>) = (\<pp>[^]i)[^]l"
   unfolding i_def 
   using Qp_p_int_nat_pow_pow by blast
  have 5: "e \<in> a"
   using e_nonzero Qp_int_pow_nonzero p_nonzero 
   unfolding e_def f1 pow_res_def mem_Collect_eq nonzero_def 4 
   by (metis (mono_tags, lifting) mem_Collect_eq)
  have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
   using x_closed t_def
   unfolding list_tl list_hd 
   using Qp_pow_ConsI t_closed by blast
  have 4: " t # x \<in> A \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))"
   apply(rule conjI) 
   unfolding A_def using tx_closed 2 5 unfolding 3 
    apply blast
   using j_def unfolding e_val by blast 
  show "x \<in> W"
   unfolding W_eq using t_closed 4 x_closed by blast 
  qed
  have W_alt_def': "W = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. eint (j* int l) + eint (ord \<beta>) \<in> I (val (a1 x)) (val (a2 x))}"
    unfolding W_alt_def
  proof(rule equalityI')
   fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint j \<in> I (val (a1 x)) (val (a2 x)) \<and> j mod int l = local.ord \<beta> mod int l}"
   obtain j where j_def: " eint j \<in> I (val (a1 x)) (val (a2 x)) \<and> j mod int l = local.ord \<beta> mod int l"
     using A by blast 
   have 4: "(j - ord \<beta>) mod l = 0"
     using A unfolding mem_Collect_eq 
     by (metis group_add_class.right_minus_eq j_def mod_0 mod_diff_cong mod_diff_left_eq mod_mod_trivial)
   then obtain i::int where i_def: "j - ord \<beta> = i*l"
     using n_pos mod_zeroE by presburger 
   have j_eq: "j = i*l + ord \<beta>"
     using i_def by linarith 
   hence j_eq: "eint j = eint(i*l) + eint (ord \<beta>)"
     by auto 
   show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j*l + eint (ord \<beta>) \<in> I (val (a1 x)) (val (a2 x))}"
     unfolding mem_Collect_eq using j_def unfolding j_eq using A by blast 
  next
   fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j*l + eint(ord \<beta>) \<in> I (val (a1 x)) (val (a2 x))}"
   then obtain i::int where i_def: " i*l + eint(ord \<beta>) \<in> I (val (a1 x)) (val (a2 x))"
     using A unfolding mem_Collect_eq  by blast 
   obtain j where j_def: "j =  i*l + ord \<beta>"
     by blast 
   have j_mod: "j mod l = ord \<beta> mod l"
     unfolding j_def 
     using mod_mult_self3 by blast
   have " eint j \<in> I (val (a1 x)) (val (a2 x))"
     unfolding j_def using i_def by auto 
   thus " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j. eint j \<in> I (val (a1 x)) (val (a2 x)) \<and> j mod int l = local.ord \<beta> mod int l}"
     unfolding mem_Collect_eq 
     using A j_def i_def j_mod by blast 
  qed
  obtain b1 where b1_def: "b1 = (inv \<beta>) \<odot>\<^bsub>SA m\<^esub> a1"
    by blast 
  obtain b2 where b2_def: "b2 = (inv \<beta>) \<odot>\<^bsub>SA m\<^esub> a2"
    by blast 
  have b1_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> b1 x = inv \<beta> \<otimes> a1 x"
    unfolding b1_def using a1_closed f2 
    using Qp.nonzero_memE(1) SA_smult_formula nonzero_inverse_Qp by blast
  have b2_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> b2 x = inv \<beta> \<otimes> a2 x"
    unfolding b2_def using a2_closed f2 
    using Qp.nonzero_memE(2) SA_smult_formula \<beta>_closed inv_in_frac(1) by blast
  have b1_closed: "b1 \<in> carrier (SA m)"
    using f2 a1_closed unfolding b1_def 
    using Qp.nonzero_memE(1) SA_smult_closed nonzero_inverse_Qp by blast
  have b2_closed: "b2 \<in> carrier (SA m)"
    using f2 a2_closed unfolding b2_def 
    using Qp.nonzero_memE(1) SA_smult_closed nonzero_inverse_Qp by blast
  have inv_\<beta>_val: "val (inv \<beta>) = eint (-ord(\<beta>))"
    using f2 
    by (simp add: Qp.nonzero_memE(2) \<beta>_closed nonzero_inverse_Qp ord_of_inv)
  have b1_val: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> val (b1 x) = eint (-ord \<beta>) + val (a1 x)"
    using val_mult[of "inv \<beta>" ] a1_closed SA_car_closed[of a1 m] \<beta>_closed f2
    unfolding b1_eval inv_\<beta>_val 
    by (meson Qp.nonzero_memE(1) nonzero_inverse_Qp)
  have b2_val: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> val (b2 x) = eint (-ord \<beta>) + val (a2 x)"
    using val_mult[of "inv \<beta>" ] a2_closed SA_car_closed[of a2 m] \<beta>_closed f2
    unfolding b2_eval inv_\<beta>_val 
    by (meson Qp.nonzero_memE(1) nonzero_inverse_Qp)
  have W_alt_def'': "W = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>j::int. j*l \<in> I (val (b1 x)) (val (b2 x))}"
    unfolding W_alt_def' apply(rule equalityI')
    unfolding mem_Collect_eq using I_convex b1_val b2_val interval_translation 
    apply metis  
    using I_convex b1_val b2_val interval_translation 
    by metis   
  interpret rational_cell_interval _ _ _ _ W l b1 b2 _ I
       apply(intro rational_cell_interval.intro rational_cell_interval_axioms.intro I_convex
                    padic_fields_axioms)
    using W_alt_def'' n_pos b1_closed b2_closed unfolding Q\<^sub>p_def Z\<^sub>p_def \<iota>_def by auto 
  have W_semialg: "is_semialgebraic m W"
    by(rule W_semialg)
  thus ?thesis unfolding W_eq by blast 
qed
end


context macintyre_reduction_iii
begin

lemma reduction_iii:
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> red_ii}"
proof(unfold red_ii_finite_union, rule macintyre_finite_union)
 fix Y assume d0: "Y \<in> (\<lambda>a. \<Inter>b\<in>Bs. H b \<inter> H1 a \<inter> condition_to_set \<B>)` (pow_res_classes l \<union> {{\<zero>}})"
 obtain a where a_def: "a \<in> (pow_res_classes l \<union> {{\<zero>}}) \<and> Y = (\<Inter>b\<in>Bs. H b \<inter> H1 a \<inter> condition_to_set \<B>)"
   using d0 by blast  
 have Y_eq: "Y = (\<Inter> (H ` Bs) \<inter> H1 a \<inter> condition_to_set \<B>)" 
   using a_def Bs_nonempty by blast 
 have Y_inter: "Y=  (\<Inter>b\<in>Bs. H b \<inter> H1 a \<inter> condition_to_set \<B>)"
   using a_def Bs_nonempty by blast 
 have a_closed: "a \<in> (pow_res_classes l \<union> {{\<zero>}})"
   using a_def by blast 
 have Y_sub: "Y \<subseteq> red_ii"
   using d0 red_ii_finite_union by blast 
  interpret macintyre_reduction_iv _ _ _ _ _ _ _ _ _ _ _ _ _ a
       apply(unfold_locales)
    using a_def Q\<^sub>p_def Z\<^sub>p_def by auto 
 have d7: "\<exists>b \<in> Xs. \<gamma> b \<notin> P_pows (N b) \<Longrightarrow> Y = {}"
   using H_inter_empty Y_inter Bs_nonempty Xs_def by blast 
 have d8: "\<exists>b \<in> Bs - Xs. \<gamma> b \<in>  P_pows (N b) \<Longrightarrow> Y = {}"
   using H_inter_empty' Y_inter Bs_nonempty Xs_def by blast 
 show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> Y}"
 proof(cases "\<exists>b \<in> Xs. \<gamma> b \<notin> P_pows (N b)")
   case True
   then have T0: "Y = {}"
     using d7 by blast 
   have T1: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> {}} = {}"
     by blast 
   show ?thesis 
     using empty_is_semialgebraic[of m] unfolding T0 T1 by blast 
 next
   case False
   show ?thesis 
   proof(cases "\<exists>b \<in> Bs - Xs. \<gamma> b \<in>  P_pows (N b)")
     case True
     then have T0: "Y = {}"
       using d8 by blast 
     have T1: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> {}} = {}"
       by blast 
     show ?thesis 
       using empty_is_semialgebraic[of m] unfolding T0 T1 by blast 
   next
     case F: False
     have F0: "\<And>b. b \<in> Xs \<Longrightarrow> H b \<inter> H1 a \<inter> condition_to_set \<B> = H1 a \<inter> condition_to_set \<B>"
       apply(rule H_inter_reduce_on_Xs, blast)
       using False by blast 
     have F1: "\<And>b. b \<in> Bs \<Longrightarrow> b \<notin> Xs \<Longrightarrow>  H b \<inter> H1 a \<inter> condition_to_set \<B> =  H1 a \<inter> condition_to_set \<B>"
       apply(rule H_inter_reduce_on_Xs', blast, blast)
       using F by blast
     have F2: "\<And>b. b \<in> Bs \<Longrightarrow> H b \<inter> H1 a \<inter> condition_to_set \<B> =  H1 a \<inter> condition_to_set \<B>"
       using F0 F1 by blast 
     have Y_inter': "Y  = (\<Inter> b \<in> Bs. H1 a \<inter> condition_to_set \<B>)"
       unfolding Y_eq using F2 Bs_nonempty 
       using Y_eq Y_inter by force
     have Y_eq: "Y =  H1 a \<inter> condition_to_set \<B>"
       using Bs_nonempty unfolding Y_inter' by blast 
     have F3: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> Y} = 
                {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> H1 a \<and> x \<in> b \<and> val(t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
       unfolding Y_eq condition_to_set.simps refine_fibres_def cell_def \<B>_params
                 arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
                 Int_iff mem_Collect_eq list_tl list_hd 
       apply(rule equalityI')
       unfolding mem_Collect_eq apply blast 
       using Qp_pow_ConsI by blast 
     have F4: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> Y} = 
                b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> H1 a \<and>  val(t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
       unfolding F3 by blast 
     show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> Y}"
       unfolding F4
       apply(rule intersection_is_semialg)
       apply(rule is_cell_conditionE[of m b c a1 a2 I])
       using \<B>_cond unfolding \<B>_params apply blast             
     proof- 
       obtain \<beta> where \<beta>_def: "\<beta> \<in> a"
         using a_def unfolding pow_res_classes_def 
         by (smt Qp.nonzero_memE(1) mem_Collect_eq mem_simps(3) pow_res_refl singleton_mem)
       have a_closed: "a \<subseteq> carrier Q\<^sub>p"
         apply(cases "a = {\<zero>}")
         using zero_closed apply blast
         using a_def unfolding pow_res_classes_def pow_res_def Un_iff mem_Collect_eq by blast 
       have \<beta>_closed: "\<beta> \<in> carrier Q\<^sub>p"
         using \<beta>_def a_closed  by blast 
       show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> H1 a \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
         apply(intro reduction_iv[of ])
         unfolding H1_def by blast 
     qed
   qed
 qed
next
 have "finite (pow_res_classes l \<union> {{\<zero>}})"
   using pow_res_classes_finite[of l] n_pos 
   by fastforce
 thus "finite ((\<lambda>a. \<Inter>b\<in>Bs. H b \<inter> H1 a \<inter> condition_to_set \<B>) ` (pow_res_classes l \<union> {{\<zero>}}))"
   by blast 
qed
end


context macintyre_reduction_ii
begin

lemma reduction_ii: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> red_i}"
unfolding red_i_un 
proof(rule macintyre_finite_union)
 fix D assume c0: "D \<in> (\<lambda>A. \<Inter> (H ` Bs) \<inter> condition_to_set A) ` refine_fibres \<C> ` Ps"
 then obtain E where E_def: "E \<in> Ps \<and> D = \<Inter> (H ` Bs) \<inter> condition_to_set (refine_fibres \<C> E)"
   by blast 
 have c1: "(refine_fibres \<C> E) = Cond m E c a1 a2 I"
   unfolding refine_fibres_def 
   using \<C>_arity c_def a1_def a2_def I_def by auto 
 interpret macintyre_reduction_iii _ _ _ _ _ _ _ _ _ _ _ "refine_fibres \<C> E" E
   apply(unfold_locales)
   using E_def by auto 
 show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> D}"
   using reduction_iii E_def Bs_nonempty unfolding red_ii_def by auto 
next
 show "finite ((\<lambda>A. \<Inter> (H ` Bs) \<inter> condition_to_set A) ` refine_fibres \<C> ` Ps)"
   using Ps_finite by auto 
qed
end


context padic_fields
begin

lemma reduction_i:
  assumes Bs_sub: "Bs \<subseteq> basic_semialgs (Suc m)"
  assumes Bs_finite: "finite Bs"
  assumes Bs_un: "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) = \<Union> Bs"
  assumes a_def: "a \<in> atoms_of Bs"
  assumes Bs_nonempty: "Bs \<noteq> {}"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> a}"
proof-
  obtain Xs where Xs_def: "Xs \<subseteq> Bs \<and> a = subset_to_atom Bs Xs \<and> Xs \<noteq> {}"
    using assms unfolding  atoms_of_def by blast
  have Bs_closed: "\<And>b. b \<in> Bs \<Longrightarrow> b \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using Bs_sub unfolding is_basic_semialg_def basic_semialg_set_def by blast 
  have Bs_inter: "\<And>b. b \<in> Bs \<Longrightarrow> b \<inter> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) = b"
    using Bs_closed by blast 
  have 0: "\<And>b. b \<in> Bs \<Longrightarrow> \<exists>f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>Suc m\<^esub>]). \<exists>(N::nat). N \<noteq> 0 \<and>  b = basic_semialg_set (Suc m) N f"
    using Bs_sub unfolding is_basic_semialg_def by blast 
  interpret macintyre_reduction_i 
       apply(unfold_locales)
    using assms Q\<^sub>p_def Z\<^sub>p_def by auto 
  have a_eq: "a = \<Inter> Xs \<inter> (\<Inter> y \<in> (Bs - Xs). carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) - y)"
  proof- 
    have 0: "a = subset_to_atom Bs Xs"
      using Xs_def by blast 
    show ?thesis unfolding 0 subset_to_atom_def 
    proof(rule equalityI')
      fix x assume a0: " x \<in> \<Inter> Xs - \<Union> (Bs - Xs)"
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
        using a0 Xs_def Bs_closed by blast 
      have x_int: "x \<in>  \<Inter> ((-) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) ` (Bs - Xs))"
        using x_closed a0 by blast 
      thus "x \<in> \<Inter> Xs \<inter> \<Inter> ((-) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) ` (Bs - Xs))"
        using a0 by blast 
    next
      fix x assume a0: "x \<in> \<Inter> Xs \<inter> \<Inter> ((-) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) ` (Bs - Xs))"
      have 0: "x \<notin> \<Union> (Bs - Xs)"
        using a0 by blast 
      thus "x \<in> \<Inter> Xs - \<Union> (Bs - Xs)"
        using a0 by blast 
    qed
  qed
  obtain Fs where Fs_def: "Fs = coord_ring_to_UP_SA m ` (F ` Bs)"
    by blast
  have Fs_closed: "Fs \<subseteq> carrier (UP (SA m))"
  proof(rule subsetI)
    fix x assume A: "x \<in> Fs"
    obtain b where b_def: "b \<in> Bs \<and> x = coord_ring_to_UP_SA m (F b)"
      using Fs_def A by blast 
    have 0: "x = coord_ring_to_UP_SA m (F b)"
      using b_def by blast 
    show "x \<in> carrier (UP (SA m)) "
      unfolding 0 
      apply(rule coord_ring_to_UP_SA_closed) 
      using F_closed[of b] b_def by blast
  qed
  have Fs_finite: "finite Fs"
    unfolding Fs_def using Bs_finite by blast 
  obtain S where S_def: "(is_cell_decomp m S (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))) \<and> 
                         (\<forall>A \<in> S. \<forall>P \<in> Fs. \<exists>u h k. SA_poly_factors p m l P (center A) (condition_to_set A) u h k)"
    using denef_cell_decomp_II[of Fs m l] n_pos Fs_closed Fs_finite by blast
  have 0: "\<And>b. b \<in> Bs \<Longrightarrow> (\<forall>A \<in> S. \<forall>P \<in> Fs. \<exists>u h k. SA_poly_factors p m (N b) P (center A) (condition_to_set A) u h k)"
    apply(rule , rule, rule SA_poly_factors_div[of _ l]) using S_def apply blast
    using div[of "N ` Bs" l] Bs_finite unfolding l_def apply blast
    using n_pos unfolding l_def by blast
  obtain G where G_def: "G = (\<lambda>b. if b \<in> Xs then b else carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) - b)"
    by blast 
  have G_Xs: "\<And>b. b \<in> Xs \<Longrightarrow> G b = b"
    using G_def by metis 
  have G_notXs: "\<And>b. b \<in> Bs - Xs \<Longrightarrow> G b = carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) - b"
    using G_def by (meson mem_simps(6))
  have a_inter: "a = (\<Inter> b \<in> Bs. G b)"
    apply(rule equalityI', rule InterI)
    using G_Xs G_notXs unfolding a_eq 
     apply (smt InterE mem_simps(10) mem_simps(4) mem_simps(6))
    apply(rule IntI)
    using G_Xs G_notXs Xs_def unfolding a_eq  
    apply (metis (no_types, opaque_lifting) INT_iff InterI Xs_def basic_trans_rules(31))
    using G_Xs G_notXs Xs_def unfolding a_eq  
    by auto
  have Q\<^sub>p_un: "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) = (\<Union> (condition_to_set ` S))"
    using S_def is_cell_decompE(2)[of m S "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"] is_partitionE(2)  
    by blast 
  have a_semialg: "is_semialgebraic (Suc m) a"
    unfolding is_semialgebraic_def semialg_sets_def     
    apply(rule gen_boolean_algebra_generator_subset[of _ _ Bs], rule atoms_closed)
    using Bs_finite apply blast 
    using a_def Bs_un Bs_finite atoms_of_sets_eq_atoms_of_algebra apply fastforce
    unfolding Bs_un apply blast 
    using Bs_sub by auto 
  have a_sub: "a \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using a_semialg is_semialgebraic_closed by blast  
  have a_un: "(\<Union> \<C> \<in> S. a \<inter> condition_to_set \<C> ) = a"
    using a_sub Q\<^sub>p_un by blast  
  obtain F1 where F1_def: "F1 = (\<lambda>b. coord_ring_to_UP_SA m (F b))"
    by blast 
  have F1_closed: "\<And>b. b \<in> Bs \<Longrightarrow> F1 b \<in> carrier (UP (SA m))"
    unfolding F1_def apply(rule coord_ring_to_UP_SA_closed)
    using F_closed by blast 
  have Fs_eq: "Fs = F1 ` Bs"
    unfolding Fs_def F1_def by blast 
  have F1_eval: "\<And>t x b. b \<in>  Bs \<Longrightarrow>  t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> 
                         Qp_ev (F b) (t#x) =  SA_poly_to_Qp_poly m x (F1 b) \<bullet> t "
    unfolding F1_def apply(rule coord_ring_to_UP_SA_eval) 
    using F_closed apply blast
    apply (metis cartesian_power_tail list_tl)
    by (metis cartesian_power_head list_hd)
  have 1: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> (\<Union> \<C> \<in> S. a \<inter> condition_to_set \<C> )}"
    apply(rule macintyre_finite_union)
  proof- 
    fix B assume C: "B \<in> (\<lambda>\<C>. a \<inter> condition_to_set \<C>) ` S"
    obtain \<C> where \<C>_def: "\<C> \<in> S \<and> B = a \<inter> condition_to_set \<C>"
      using C by blast 
    have \<C>_arity: "arity \<C> = m"
      using S_def \<C>_def is_cell_decompE(4)[of m S "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" \<C>] by blast 
    obtain C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
      using condition_decomp'[of \<C>] unfolding \<C>_arity by blast 
    have B_inter: "B =  (\<Inter> x \<in> Bs. G x \<inter> condition_to_set \<C>)"
      using \<C>_def Bs_nonempty unfolding a_inter  by blast
    have c_eq: "c = center \<C>"
      unfolding params center.simps by blast
    have \<C>_cell: "is_cell_condition \<C>"
      using \<C>_def S_def is_cell_decompE by blast 
    have c_closed: "c \<in> carrier (SA m)"
      unfolding c_eq using \<C>_cell unfolding params 
      by (metis c_eq is_cell_conditionE(2) params)
    have p0: "\<And>b. b \<in> Bs \<Longrightarrow>  \<exists>u h k. SA_poly_factors p m (N b) (F1 b) c (condition_to_set \<C>) u h k"
      using 0 Fs_eq \<C>_def c_eq by blast 
    obtain u where u_def: "u = (\<lambda>b. (SOME u. \<exists> h k. SA_poly_factors p m (N b) (F1 b) c (condition_to_set \<C>) u h k ))"
      by blast 
    have uE: "\<And>b. b \<in> Bs \<Longrightarrow> \<exists> h k. SA_poly_factors p m (N b) (F1 b) c (condition_to_set \<C>) (u b) h k "
      using u_def p0 SomeE by smt 
    obtain h where h_def: "h = (\<lambda>b. (SOME h. \<exists> k. SA_poly_factors p m (N b) (F1 b) c (condition_to_set \<C>) (u b) h k ))"
      by blast 
    have hE: "\<And>b. b \<in> Bs \<Longrightarrow> \<exists> k. SA_poly_factors p m (N b) (F1 b) c (condition_to_set \<C>) (u b) (h b) k "
      using uE h_def p0 SomeE by smt 
    obtain \<nu> where \<nu>_def: "\<nu> = (\<lambda>b. (SOME k. SA_poly_factors p m (N b) (F1 b) c (condition_to_set \<C>) (u b) (h b) k))"
      by blast 
    have kE: "\<And>b. b \<in> Bs \<Longrightarrow> SA_poly_factors p m (N b) (F1 b) c (condition_to_set \<C>) (u b) (h b) (\<nu> b)"
      using hE \<nu>_def p0 SomeE by smt 
    have Bs_eq: "\<And>b t x. b \<in> Bs \<Longrightarrow> t#x \<in> condition_to_set \<C> \<Longrightarrow> 
              SA_poly_to_Qp_poly m x (F1 b) \<bullet> t = (u b) (t # x) [^] (N b) \<otimes> (h b) x \<otimes> (t \<ominus> c x) [^] (\<nu> b)"
      apply(rule SA_poly_factorsE[of _ _ _ _ "condition_to_set \<C>"] )
       apply(rule kE, blast)
      by blast 
    have Bs_eq': "\<And>b t x. b \<in> Bs \<Longrightarrow> t#x \<in> condition_to_set \<C> \<Longrightarrow> 
              Qp_ev (F b) (t#x)  = (u b) (t # x) [^] (N b) \<otimes> (h b) x \<otimes> (t \<ominus> c x) [^] (\<nu> b)"      
      using Bs_eq F1_eval unfolding params condition_to_set.simps cell_def by blast 
    have u_closed: "\<And>b t x. b \<in> Bs \<Longrightarrow> t#x \<in> condition_to_set \<C> \<Longrightarrow> (u b) (t # x) \<in> carrier Q\<^sub>p"
      using kE  SA_poly_factors_closure by blast 
    have h_closed: "\<And>b . b \<in> Bs \<Longrightarrow>  h b \<in> carrier (SA m)"
      using kE  SA_poly_factors_closure by meson
    have u_val: "\<And>b t x. b \<in> Bs \<Longrightarrow> t#x \<in> condition_to_set \<C> \<Longrightarrow> val (u b (t#x)) = 0"
      using kE  SA_poly_factorsE by blast 
    have u_nonzero: "\<And>b t x. b \<in> Bs \<Longrightarrow> t#x \<in> condition_to_set \<C> \<Longrightarrow> (u b (t#x)) \<in> nonzero Q\<^sub>p"
      unfolding nonzero_def using u_closed u_val val_zero 
      by (metis (mono_tags, lifting) i0_ne_infinity mem_Collect_eq)
    have p1: "\<And>b. b \<in> Bs \<Longrightarrow> b \<inter> condition_to_set \<C> = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> c (tl xs)) [^] (\<nu> b) \<in> P_pows (N b)} \<inter> condition_to_set \<C>"
    proof- 
      fix b assume b_in: "b \<in> Bs"
      show "  b \<inter> condition_to_set \<C> = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)} \<inter> condition_to_set \<C>"
      proof(rule equalityI')
        fix xs assume A: "xs \<in> b \<inter> condition_to_set \<C>"
        have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
          using A unfolding params condition_to_set.simps cell_def by blast  
        obtain t x where tx_def: "xs = t#x"
          using xs_closed Qp_pow_Suc_decomp by blast  
        have t_closed: "t \<in> carrier Q\<^sub>p"
          using xs_closed unfolding tx_def  
          by (metis Qp_pow_ConsE list_hd)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using xs_closed unfolding tx_def 
          by (metis Qp_pow_ConsE(1) list_tl)
        have 0: "Qp_ev (F b) (t#x)  = (u b) (t # x) [^] (N b) \<otimes> (h b) x \<otimes> (t \<ominus> c x) [^] (\<nu> b)"
          using Bs_eq' A b_in unfolding tx_def by blast 
        have 1: "b = basic_semialg_set (Suc m) (N b) (F b)"
          using F_N_eval b_in by blast 
        have 2: "xs \<in> basic_semialg_set (Suc m) (N b) (F b)"
          using A 1 by blast 
        have 3: "basic_semialg_set (Suc m) (N b) (F b) = {q \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). eval_at_point Q\<^sub>p q (F b) \<in> P_pows (N b)}"
          using 2 basic_semialg_set_def''[of "N b" "F b" "Suc m"] b_in F_closed F_N_eval 
          by (meson N_prop)
        have 3: "(h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b) \<in> P_pows (N b)"
          apply(rule P_pows_cong[of _ "Qp_ev (F b) (t#x)" "(u b) (t # x)"]) 
          using F_N_eval F_closed b_in N_nonzero apply blast
          using 2 unfolding 3 mem_Collect_eq tx_def apply blast 
            apply(rule u_nonzero)
             apply(rule b_in)
          using A unfolding tx_def apply blast
          unfolding list_tl  list_hd apply(rule Qp.ring_simprules)
          using h_closed b_in x_closed SA_car_closed apply blast
            apply(rule Qp.nat_pow_closed, rule Qp.ring_simprules, rule t_closed)
          using c_closed b_in x_closed SA_car_closed apply blast 
          unfolding 0 apply(rule Qp.m_assoc)
             apply(rule Qp.nat_pow_closed, rule u_closed, rule b_in)
          using A unfolding tx_def apply blast
          using h_closed b_in x_closed SA_car_closed apply blast
           apply(rule Qp.nat_pow_closed, rule Qp.ring_simprules, rule t_closed)
          using c_closed b_in x_closed SA_car_closed by blast
        show "xs \<in> {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows(N b)} \<inter> condition_to_set \<C>"
          using 3 1 A xs_closed unfolding tx_def
          by blast 
      next
        fix xs assume A: " xs \<in> {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). h b (tl xs) \<otimes> (lead_coeff xs \<ominus> c (tl xs)) [^] \<nu> b \<in> P_pows (N b)} \<inter> condition_to_set \<C>"
        have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
          using A unfolding params condition_to_set.simps cell_def by blast  
        obtain t x where tx_def: "xs = t#x"
          using xs_closed Qp_pow_Suc_decomp by blast  
        have t_closed: "t \<in> carrier Q\<^sub>p"
          using xs_closed unfolding tx_def  
          by (metis Qp_pow_ConsE list_hd)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using xs_closed unfolding tx_def 
          by (metis Qp_pow_ConsE(1) list_tl)
        have 0: "Qp_ev (F b) (t#x)  = (u b) (t # x) [^] (N b) \<otimes> (h b) x \<otimes> (t \<ominus> c x) [^] (\<nu> b)"
          using Bs_eq' A b_in unfolding tx_def by blast 
        have 1: "b = basic_semialg_set (Suc m) (N b) (F b)"
          using F_N_eval b_in by blast 
        have 2: "basic_semialg_set (Suc m) (N b) (F b) = {q \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). eval_at_point Q\<^sub>p q (F b) \<in> P_pows (N b)}"
          using  basic_semialg_set_def''[of "N b" "F b" "Suc m"] b_in F_closed N_prop F_N_eval by blast
        have 3: "Qp_ev (F b) (t#x) \<in> P_pows (N b)"
          apply(rule P_pows_cong'[of "N b" "(h b) x \<otimes> (t \<ominus> c x) [^] (\<nu> b)" "(u b) (t # x)"])
          using F_N_eval N_prop b_in apply blast
          using A unfolding Int_iff tx_def mem_Collect_eq list_tl list_hd apply blast
            apply(rule u_nonzero)
             apply(rule b_in)
          using A unfolding tx_def apply blast
           apply(rule Qp.ring_simprules)
          using h_closed b_in x_closed SA_car_closed apply blast
            apply(rule Qp.nat_pow_closed, rule Qp.ring_simprules, rule t_closed)
          using c_closed b_in x_closed SA_car_closed apply blast 
          unfolding 0 apply(rule Qp.m_assoc)
             apply(rule Qp.nat_pow_closed, rule u_closed, rule b_in)
          using A unfolding tx_def apply blast
          using h_closed b_in x_closed SA_car_closed apply blast
           apply(rule Qp.nat_pow_closed, rule Qp.ring_simprules, rule t_closed)
          using c_closed b_in x_closed SA_car_closed by blast
        show "xs \<in> b \<inter> condition_to_set \<C>"
          using 1 A 3 unfolding 2 tx_def by blast 
      qed
    qed
    obtain H where H_def: "H = (\<lambda> b. if b \<in> Xs then 
            {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> c (tl xs)) [^] (\<nu> b) \<in> P_pows (N b)} 
       else {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> c (tl xs)) [^] (\<nu> b) \<notin> P_pows (N b)} )"
      by blast 
    have H_Xs_inter: "\<And>b. b \<in> Xs \<Longrightarrow> G b \<inter> condition_to_set \<C> = H b \<inter> condition_to_set \<C>"
    proof- 
      fix b  assume A: "b \<in> Xs"
      then have 0: "b \<in> Bs"
        using Xs_def by blast
      have 1: "G b = b"
        using A G_Xs by blast 
      have 2: "H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> c (tl xs)) [^] (\<nu> b) \<in> P_pows (N b)}"
        using A H_def by presburger
      show "G b \<inter> condition_to_set \<C> = H b \<inter> condition_to_set \<C>"
        unfolding 1 2 using p1 0 by blast 
    qed
    have H_not_Xs_inter: "\<And>b. b \<in> Bs \<Longrightarrow> b \<notin>Xs  \<Longrightarrow> G b \<inter> condition_to_set \<C> = H b \<inter> condition_to_set \<C>"
    proof-
      fix b  assume A: "b \<in> Bs" "b \<notin> Xs"
      then have 0: "b \<in> Bs"
        using Xs_def by blast
      have 1: "G b = carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) -  b"
        using A G_notXs by blast 
      have 2: "H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> c (tl xs)) [^] (\<nu> b) \<notin> P_pows (N b)}"
        using A H_def by presburger
      show "G b \<inter> condition_to_set \<C> = H b \<inter> condition_to_set \<C>"
        unfolding 1 2 using p1 0 by blast 
    qed
    have H_Xs: "\<And>b. b \<in> Xs \<Longrightarrow> H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> c (tl xs)) [^] (\<nu> b) \<in> P_pows (N b)}"
      using H_def by presburger 
    have H_notXs: "\<And>b. b \<notin> Xs \<Longrightarrow>  H b = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (h b) (tl xs) \<otimes> (hd xs \<ominus> c (tl xs)) [^] (\<nu> b) \<notin> P_pows (N b)}"
      using H_def by presburger 
    interpret macintyre_reduction_ii _ _ _ _ _ _ \<nu> Xs \<C> h H
      apply(unfold_locales)
      using \<C>_cell \<C>_arity Xs_def h_closed unfolding Q\<^sub>p_def Z\<^sub>p_def  H_Xs H_notXs c_eq by auto
    have B_inter': "B = (\<Inter>x\<in>Bs. H x \<inter> condition_to_set \<C>)"
      unfolding B_inter using H_Xs_inter H_not_Xs_inter by blast 
    show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> B}"
      using reduction_ii unfolding red_i_def B_inter' by auto 
  next
    show "finite ((\<lambda>\<C>. a \<inter> condition_to_set \<C>) ` S)"
      using S_def is_cell_decompE by auto 
  qed
  show ?thesis 
    using 1 unfolding a_un by auto 
qed

theorem macintyre_theorem:
  assumes "is_semialgebraic (Suc m) A"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (\<exists>t \<in> carrier Q\<^sub>p. (t#x) \<in> A)}"
  using assms unfolding basic_semialg_set_def 
proof- 
  obtain Bs0 where Bs0_def: "finite Bs0 \<and> Bs0 \<subseteq> basic_semialgs (Suc m)  \<and> 
                          A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) Bs0"
    using assms(1) gen_boolean_algebra_finite_gen_wits[of A "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "basic_semialgs (Suc m)"]
    unfolding is_semialgebraic_def semialg_sets_def 
    by blast 
  obtain y where y_def: "y = basic_semialg_set (Suc m) 1 \<one>\<^bsub>Q\<^sub>p[\<X>\<^bsub>Suc m\<^esub>]\<^esub>"
    by blast 
  have y_car: "y = carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    apply(rule equalityI')
    unfolding y_def basic_semialg_set_def apply blast
    unfolding mem_Collect_eq apply(rule conjI, blast)
  proof-
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    have 0: "eval_at_point Q\<^sub>p x \<one>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc m\<^esub>]\<^esub> = \<one>"
      using A Qp_ev_one by blast
    show " \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p x \<one>\<^bsub>Q\<^sub>p [\<X>\<^bsub>Suc m\<^esub>]\<^esub> = y [^] (1::nat)"
      using 0 Qp.nat_pow_eone by blast
  qed
  obtain Bs where Bs_def: "Bs = insert y Bs0"
    by blast 
  have y_in: "y \<in> basic_semialgs (Suc m)"
    unfolding y_def unfolding mem_Collect_eq is_basic_semialg_def 
    by blast
  have Bs_sub: "Bs \<subseteq> basic_semialgs (Suc m)"
    unfolding Bs_def using Bs0_def y_in by blast 
  have Bs_finite: "finite Bs"
    unfolding Bs_def using Bs0_def by blast 
  have A_in: "A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) Bs"
    apply(rule gen_boolean_algebra_generator_subset[of _ _ Bs0 ])
    using Bs0_def apply blast unfolding Bs_def by blast 
  obtain As where As_def: "As = atoms_of Bs"
    by blast 
  have Bs_closed: "\<And>b. b \<in> Bs \<Longrightarrow> b \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using Bs_sub unfolding is_basic_semialg_def basic_semialg_set_def by blast 
  have Bs_inter: "\<And>b. b \<in> Bs \<Longrightarrow> b \<inter> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) = b"
    using Bs_closed by blast 
  have Bs_un: "\<Union> Bs = carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    apply(rule equalityI')
    using Bs_closed apply blast
    unfolding Bs_def y_car by blast 
  have As_sub: "As \<subseteq> (gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) Bs)"
    unfolding As_def apply(rule atoms_of_gen_boolean_algebra)
     apply(rule subsetI)
    using  gen_boolean_algebra.generator[of _ Bs "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"]  Bs_inter
     apply metis 
    using Bs_finite by blast 
  have As_closed: "\<And>a. a \<in> As \<Longrightarrow> is_semialgebraic (Suc m) a"
    using As_sub unfolding is_semialgebraic_def semialg_sets_def 
    using gen_boolean_algebra_generator_subset Bs_sub by blast 
  have As_proj: "\<And>a. a \<in> As \<Longrightarrow>  is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> a}"
    apply(intro reduction_i[of Bs] Bs_sub Bs_finite)
    unfolding As_def Bs_un 
    unfolding Bs_def by auto 
  obtain Xs where Xs_def: "Xs = {a \<in> As. a \<subseteq> A}"
    by blast 
  have A_covered: "A = \<Union> Xs"
    unfolding Xs_def As_def
    apply(rule gen_boolean_algebra_elem_uni_of_atoms[of Bs "\<Union> Bs" ])
      apply(rule Bs_finite, blast)
    using gen_boolean_algebra.generator[of A "Bs" "\<Union> Bs"] unfolding Bs_un using A_in
    by (meson Sup_upper gen_boolean_algebra_generators)
  have As_finite: "finite As"
    unfolding As_def apply(rule finite_set_imp_finite_atoms)
    by(rule Bs_finite)
  show "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>t\<in>carrier Q\<^sub>p. t # x \<in> A}"
    unfolding A_covered
    apply(rule macintyre_finite_union)
     apply(rule As_proj)
    unfolding Xs_def apply blast
    apply(rule finite_subset[of _ As], blast)
    by(rule As_finite)
qed

end

end 
 