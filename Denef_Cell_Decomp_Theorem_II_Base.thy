theory Denef_Cell_Decomp_Theorem_II_Base
  imports Denef_Cell_Decomp_Theorem_I

begin

section\<open>The Proof of Cell Decomposition Theorem \texttt{II\_{d}} Assuming Theorem \texttt{I\_{d}}\<close>

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Preliminary Lemmas\<close>
(**************************************************************************************************)
(**************************************************************************************************)
context padic_fields
begin

lemma SA_Units_smult:
  assumes "f \<in> Units (SA m)"
  assumes "c \<in> Units Q\<^sub>p"
  shows "c \<odot>\<^bsub>SA m\<^esub> f \<in> Units (SA m)"
  apply(intro SA_Units_memI SA_smult_closed)
  using assms apply auto 
  using assms SA_Units_memE'[of f m] Qp.Units_closed Qp.Units_not_right_zero_divisor SA_Units_closed 
      SA_Units_closed_fun SA_smult_formula  by metis 

lemma Qp_pow_Suc_decomp: 
  assumes "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "\<exists> t \<in> carrier Q\<^sub>p. \<exists> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). xs = t#x"
proof- 
  obtain t x where tx_def: "xs = t#x"
    using assms cartesian_power_car_memE 
    by (metis length_Suc_conv)
  show ?thesis using assms unfolding tx_def 
    by (metis Qp_pow_ConsE(1) Qp_pow_ConsE(2) list.sel(1) list.sel(3))
qed

lemma nonempty_fibre_replacement: 
  assumes "is_cell_condition (Cond m C c f g I)"
  assumes "is_cell_condition (Cond m A d a1 a2 J)"
  assumes "condition_to_set (Cond m A d a1 a2 J) \<subseteq> condition_to_set (Cond m C c f g I)"
  shows "is_cell_condition (Cond m (A \<inter> C) d a1 a2 J)"
        "condition_to_set (Cond m A d a1 a2 J) = condition_to_set (Cond m (A \<inter> C) d a1 a2 J)"
   apply(rule is_cell_conditionI', rule intersection_is_semialg, 
            rule is_cell_conditionE[of m A d a1 a2 J], rule assms)
  apply(  rule is_cell_conditionE[of m C c f g I], rule assms, 
            rule is_cell_conditionE[of m A d a1 a2 J], rule assms , 
            rule is_cell_conditionE[of m A d a1 a2 J], rule assms,
            rule is_cell_conditionE[of m A d a1 a2 J], rule assms, 
            rule is_cell_conditionE[of m A d a1 a2 J], rule assms)
  apply(rule equalityI') 
  unfolding condition_to_set.simps 
  apply(rule cell_memI, rule cell_memE[of _ m A d a1 a2 J], blast, rule IntI, rule cell_memE[of _ m A d a1 a2 J], blast,
        rule cell_memE[of _ m C c f g I]) 
  using assms unfolding condition_to_set.simps apply blast
  apply(rule cell_memE[of _ m A d a1 a2 J], blast)
  apply(rule cell_memI, rule cell_memE[of _ m "A \<inter> C" d a1 a2 J], blast)
  using  cell_memE(2)[of _ m "A \<inter> C" d a1 a2 J] apply blast
  by(rule cell_memE[of _ m "A \<inter> C" d a1 a2 J], blast)

lemma nonempty_fibre_replacement': 
  assumes "is_cell_condition (Cond m C c f g I)"
  assumes "is_cell_condition \<C>"
  assumes "arity \<C> = m"
  assumes "condition_to_set \<C> \<subseteq> condition_to_set (Cond m C c f g I)"
  shows  "is_cell_condition (refine_fibres \<C> (fibre_set \<C> \<inter> C))"
"condition_to_set \<C> = condition_to_set (refine_fibres \<C> (fibre_set \<C> \<inter> C))"        
proof- 
  obtain A d a1 a2 J where params: "\<C> = Cond m A d a1 a2 J"
    using assms condition_decomp' by blast
  show "condition_to_set \<C> = condition_to_set (refine_fibres \<C> (fibre_set \<C> \<inter> C))" 
    unfolding params refine_fibres_def fibre_set.simps center.simps u_bound.simps arity.simps l_bound.simps boundary_condition.simps
    apply(rule nonempty_fibre_replacement[of m C c f g I], rule assms)
    using assms unfolding params apply blast
    using assms unfolding params by blast
  show "is_cell_condition (refine_fibres \<C> (fibre_set \<C> \<inter> C))"
    unfolding params refine_fibres_def fibre_set.simps center.simps u_bound.simps arity.simps l_bound.simps boundary_condition.simps
    apply(rule nonempty_fibre_replacement[of m C c f g I], rule assms)
    using assms unfolding params apply blast
    using assms unfolding params by blast
qed
 
lemma nonempty_fibre_replacement_cell_decomp: 
  assumes "is_cell_condition (Cond m C c f g I)"
  assumes "Y \<subseteq> condition_to_set (Cond m C c f g I)"
  assumes "is_cell_decomp m S Y"
  shows "is_cell_decomp m ((\<lambda> \<C>. refine_fibres \<C> (fibre_set \<C> \<inter> C )) ` S) Y "
proof- 
  have 0: "\<And>\<C>. \<C> \<in> S \<Longrightarrow> condition_to_set \<C> = condition_to_set (refine_fibres \<C> (fibre_set \<C> \<inter> C ))"
  proof- 
    fix \<C> assume A: "\<C> \<in> S"
    obtain A d a1 a2 J where params: "\<C> = Cond m A d a1 a2 J"
      using A assms(2) is_cell_decompE(4)[of m S Y \<C>] 
      using arity.cases  by (metis assms(3) equal_CondI)
    have P0: "condition_to_set (refine_fibres \<C> (fibre_set \<C> \<inter> C )) = condition_to_set (Cond m (A \<inter> C) d a1 a2 J)"
      unfolding refine_fibres_def params arity.simps fibre_set.simps l_bound.simps u_bound.simps boundary_condition.simps center.simps 
      by blast 
    have P1: "is_cell_condition (Cond m A d a1 a2 J)"
      using A assms is_cell_decompE(3)[of m S Y \<C>] unfolding params by blast 
    show "condition_to_set \<C> = condition_to_set (refine_fibres \<C> (fibre_set \<C> \<inter> C))"
      unfolding P0 unfolding params 
      apply(rule nonempty_fibre_replacement[of m C c f g I], rule assms, rule P1)
      using is_cell_decomp_subset assms params A by blast
  qed
  have 1: "\<Union> (condition_to_set ` S) =( \<Union> \<C> \<in> S. condition_to_set (refine_fibres \<C> (fibre_set \<C> \<inter> C )))"
    using 0 by blast 
  have 2: "condition_to_set ` (\<lambda>\<C>. refine_fibres \<C> (fibre_set \<C> \<inter> C)) ` S = condition_to_set ` S"
    using 0 by blast 
  have 3: "\<And>\<C>. \<C> \<in> S \<Longrightarrow> arity (refine_fibres \<C> (fibre_set \<C> \<inter> C )) = m"
  proof- 
    fix \<C> assume A: "\<C> \<in> S"
    obtain A d a1 a2 J where params: "\<C> = Cond m A d a1 a2 J"
      using A assms(2) is_cell_decompE(4)[of m S Y \<C>] 
      using arity.cases by (metis assms(3) equal_CondI)
    have P0: "(refine_fibres \<C> (fibre_set \<C> \<inter> C )) = (Cond m (A \<inter> C) d a1 a2 J)"
      unfolding refine_fibres_def params arity.simps fibre_set.simps l_bound.simps u_bound.simps boundary_condition.simps center.simps 
      by blast 
    show "arity (refine_fibres \<C> (fibre_set \<C> \<inter> C )) = m"
      unfolding P0 arity.simps by blast
  qed
  have 4: "\<And>\<C>. \<C> \<in> S \<Longrightarrow> is_cell_condition (refine_fibres \<C> (fibre_set \<C> \<inter> C ))"
  proof- 
    fix \<C> assume A: "\<C> \<in> S"
    obtain A d a1 a2 J where params: "\<C> = Cond m A d a1 a2 J"
      using A assms(2) is_cell_decompE(4)[of m S Y \<C>] 
      using arity.cases  by (metis assms(3) equal_CondI)
    have P0: "(refine_fibres \<C> (fibre_set \<C> \<inter> C )) = (Cond m (A \<inter> C) d a1 a2 J)"
      unfolding refine_fibres_def params arity.simps fibre_set.simps l_bound.simps u_bound.simps boundary_condition.simps center.simps 
      by blast 
    have P1: "is_cell_condition (Cond m A d a1 a2 J)"
      using A assms is_cell_decompE(3)[of m S Y \<C>] unfolding params by blast 
    show "is_cell_condition (refine_fibres \<C> (fibre_set \<C> \<inter> C ))"
      unfolding P0  apply(rule nonempty_fibre_replacement[of m C c f g I], rule assms, rule P1)
      using is_cell_decomp_subset assms A params by blast       
  qed
  show ?thesis
    apply(rule is_cell_decompI)
    using assms is_cell_decompE[of m S Y] apply blast
    unfolding 2 apply(rule is_cell_decompE[of m S Y], rule assms, rule conjI)
    using 4 apply blast using 3 apply blast using assms unfolding condition_to_set.simps cell_def apply blast
    using is_cell_decompE(5)[of m S Y] 0 
    using assms(3) by blast
qed

lemma monom_term_ord: 
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>"
  assumes "c \<noteq> \<zero>"
  shows "ord(a \<otimes> c[^](i::nat)) = ord a + i*ord c"
  using assms ord_mult[of a "c[^]i"] 
  by (metis Qp_nat_pow_nonzero nonzero_nat_pow_ord not_nonzero_Qp)

lemma monom_term_ord': 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "c \<in> nonzero Q\<^sub>p"
  shows "ord(a \<otimes> c[^](i::nat)) = ord a + i*ord c"
  apply(rule monom_term_ord)
  using assms unfolding nonzero_def apply blast
  using assms unfolding nonzero_def apply blast
  using assms unfolding nonzero_def apply blast
  using assms unfolding nonzero_def by blast

lemma taylor_monom_term_ord: 
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>"
  assumes "t \<noteq> c"
  shows "ord(a \<otimes> (t \<ominus> c)[^](i::nat)) = ord a + i*ord (t \<ominus> c)"
  apply(rule monom_term_ord, rule assms)
  using assms  apply blast
  using assms  apply blast
  using Qp.r_right_minus_eq assms(2) assms(3) assms(5) by blast

lemma taylor_monom_term_ord': 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "t \<ominus> c \<in> nonzero Q\<^sub>p"
  shows "ord(a \<otimes> (t \<ominus> c)[^](i::nat)) = ord a + i*ord (t \<ominus> c)"
  by(rule monom_term_ord', rule assms, rule assms)

lemma semialg_ord_ineq_set_closed: 
  assumes "f \<in> carrier (SA m)"
  assumes "g \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f x \<noteq> \<zero> \<and> g x \<noteq> \<zero> \<and> ord (f x) \<le> ord (g x)}"
proof- 
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f x \<noteq> \<zero> \<and> g x \<noteq> \<zero> \<and> ord (f x) \<le> ord (g x)} = 
            {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f x \<noteq> \<zero> } \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). g x \<noteq> \<zero>} \<inter> 
              {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (f x) \<le> val (g x)}"
    apply(rule equalityI')
     apply(rule IntI) 
    unfolding mem_Collect_eq Int_iff apply blast
     apply(rule conjI, blast)
    using SA_car_closed[of f m] SA_car_closed[of g m] 
          val_ord assms(1) assms(2) eint_ord_simps(1) val_ord' apply presburger
    apply(rule conjI, blast, rule conjI, blast, rule conjI, blast)
   using SA_car_closed[of f m] SA_car_closed[of g m] 
          val_ord assms(1) assms(2) eint_ord_simps(1) val_ord' 
   by metis 
  show ?thesis unfolding 0 apply(rule intersection_is_semialg,rule intersection_is_semialg)
    apply(rule SA_nonzero_set_is_semialg, rule assms, rule SA_nonzero_set_is_semialg, rule assms)
    by(rule semialg_val_ineq_set_is_semialg, rule assms, rule assms )
qed

lemma semialg_ord_eq_set_closed: 
  assumes "f \<in> carrier (SA m)"
  assumes "g \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). g x \<noteq> \<zero> \<and> f x \<noteq> \<zero> \<and> ord (f x) = ord (g x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). g x \<noteq> \<zero> \<and> f x \<noteq> \<zero> \<and> ord (f x) = ord (g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>).f x \<noteq> \<zero> \<and> g x \<noteq> \<zero>   \<and> ord (f x) \<le> ord (g x)} \<inter>
{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>).  g x \<noteq> \<zero> \<and> f x \<noteq> \<zero> \<and> ord (f x) \<ge> ord (g x)}"
    apply(rule equalityI')
    unfolding mem_Collect_eq Int_iff 
    apply linarith by linarith
  show ?thesis unfolding 0 
    by(intro intersection_is_semialg semialg_ord_ineq_set_closed assms)
qed

lemma semialg_Unit_ord_eq_set_closed: 
  assumes "f \<in> Units (SA m)"
  assumes "g \<in> Units (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (f x) = ord (g x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (f x) = ord (g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). g x \<noteq> \<zero> \<and> f x \<noteq> \<zero> \<and>  ord (f x) = ord (g x)}"
  apply(rule Collect_cong)
    using assms SA_Units_memE' by blast
  show ?thesis unfolding 0 apply(rule semialg_ord_eq_set_closed)
    using assms apply blast
    using assms by blast 
qed

lemma semialg_ord_ineq_set_plus_closed: 
  assumes "f \<in> carrier (SA m)"
  assumes "g \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f x \<noteq> \<zero> \<and> g x \<noteq> \<zero> \<and> ord (f x) + N \<le> ord (g x)}"
proof- 
  obtain h where h_def: "h = \<pp>[^]N \<odot>\<^bsub>SA m\<^esub> f"
    by blast 
  have h_closed: "h \<in> carrier (SA m)"
    unfolding h_def using assms SA_smult_closed p_intpow_closed(1) by blast
  have h_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> h x = \<pp>[^]N \<otimes> f x"
    unfolding h_def using assms SA_smult_formula p_intpow_closed(1) by blast
  have h_eval_ord: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> f x \<noteq> \<zero> \<Longrightarrow>  ord (h x) = N + ord (f x)"
    using h_eval assms ord_mult 
    by (metis SA_car_closed not_nonzero_Qp ord_p_pow_int p_intpow_closed(2))
  have h_nonzero: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> h x \<noteq> \<zero> \<longleftrightarrow> f x \<noteq> \<zero>"
    using h_eval 
    by (metis Qp.integral_iff Qp.zero_not_one SA_car_closed assms(1) p_intpow_closed(1) p_intpow_inv')
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). f x \<noteq> \<zero> \<and> g x \<noteq> \<zero> \<and> ord (f x) + N \<le> ord (g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). h x \<noteq> \<zero> \<and> g x \<noteq> \<zero> \<and> ord (h x) \<le> ord (g x)}"
    apply(rule equalityI')
    unfolding mem_Collect_eq using h_eval_ord h_nonzero  apply (metis add.commute)
    using h_eval_ord h_nonzero by (metis add.commute)
  show ?thesis unfolding 0 
    by(rule semialg_ord_ineq_set_closed, rule h_closed, rule assms)
qed

lemma singleton_cell_decomp: 
  assumes "is_cell_condition \<C>"
  assumes "arity \<C> = m"
  shows "is_cell_decomp m {\<C>} (condition_to_set \<C>)"
  apply(rule is_cell_decompI, blast, rule is_partitionI, rule disjointI, blast, blast, rule conjI)
  using assms apply blast using assms apply blast
  using assms apply (meson cell_condition_to_set_subset)
  by blast 

lemma(in UP_cring) taylor_zero_imp_zero:
  assumes "f \<in> carrier (UP R)"
  assumes "c \<in> carrier R"
  assumes "\<And>j. taylor c f j = \<zero>"
  shows "f = \<zero>\<^bsub>UP R\<^esub>"
proof-
  have 0: "taylor c f = \<zero>\<^bsub>UP R\<^esub>"
    apply(rule )
    using assms P_def cfs_zero by presburger
  have 1: "(Cring_Poly.compose R (X_plus c) (X_plus (\<ominus> c))) = X_poly R"
    using X_minus_plus assms(2) plus_minus_sub by presburger
  have 2: "Cring_Poly.compose R f (X_poly R) = f"
    using UP_cring.X_sub assms(1) is_UP_cring by blast
  have 3: "taylor (\<ominus>c) (taylor c f) = f"
    unfolding taylor_def taylor_expansion_def 
    using assms sub_assoc[of f "X_plus c" "X_plus (\<ominus>c)"] unfolding 1 2 
    using P_def R.add.inv_closed X_plus_closed by presburger
  show ?thesis 
    using 3 unfolding 0
    unfolding taylor_def taylor_expansion_def 
    using P_def R.add.inv_closed UP_zero_closed X_plus_closed assms(2) deg_zero sub_const by blast
qed

lemma(in UP_cring) taylor_zero_imp_zero':
  assumes "f \<in> carrier (UP R)"
  assumes "c \<in> carrier R"
  assumes "\<And>j. taylor_expansion R c f j = \<zero>"
  shows "f = \<zero>\<^bsub>UP R\<^esub>"
  apply(rule  taylor_def taylor_zero_imp_zero, rule assms, rule assms)
  using assms(3) unfolding taylor_def by blast 

lemma taylor_term_eval_zero_imp_zero:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "\<And>j. UPQ.taylor_term c f j \<bullet> t = \<zero> "
  shows "f \<bullet> t= \<zero>" 
proof-
  have 0: "f = finsum (UP Q\<^sub>p) (UPQ.taylor_term c f) {..deg Q\<^sub>p f}"
    using UPQ.taylor_term_sum[of f "deg Q\<^sub>p f" c] assms by blast 
  have 1: "(finsum (UP Q\<^sub>p) (UPQ.taylor_term c f) {..deg Q\<^sub>p f}) \<bullet> t = finsum Q\<^sub>p (\<lambda>j. UPQ.taylor_term c f j \<bullet> t) {..deg Q\<^sub>p f}"
    by(rule UPQ.to_fun_finsum, blast, rule, rule UPQ.taylor_term_closed, rule assms, rule assms, rule assms)
  have 2: "finsum Q\<^sub>p (\<lambda>j. UPQ.taylor_term c f j \<bullet> t) {..deg Q\<^sub>p f} = \<zero>"
    using assms Qp.finsum_zero 
    by (smt Qp.add.finprod_one_eqI)
  show ?thesis using 0 1 2 by smt  
qed

lemma Suc_pow_mem_decomp: 
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "as = (hd as)#(tl as)"
  using cartesian_power_car_memE assms 
  by (metis Zero_not_Suc list.exhaust_sel list.size(3))

lemma cell_conditon_mem_decomp: 
  assumes "xs \<in> condition_to_set \<C>"
  shows "xs = (hd xs)#(tl xs)"
  apply(rule Suc_pow_mem_decomp[of xs "arity \<C>"])
  using condition_to_set.simps unfolding cell_def 
  by (metis (mono_tags, lifting) assms cell_memE(1) condition_to_set.simps padic_fields.condition_decomp' padic_fields_axioms)

lemma cell_hd_closed: 
  assumes "xs \<in> condition_to_set \<C>"
  shows "hd xs \<in> carrier Q\<^sub>p"
  using assms  condition_to_set.simps unfolding cell_def 
  by (smt Qp_pow_ConsE(2) cell_memE(1) condition_to_set.elims)

lemma(in cring) finsum_cancel:
  assumes "finite Fs"
  assumes "f \<in> Fs \<rightarrow> carrier R"
  assumes "S \<subseteq> Fs"
  assumes "\<And>i. i \<in> Fs \<Longrightarrow> f i \<noteq> \<zero> \<Longrightarrow> i \<in> S"
  shows "finsum R f Fs = finsum R f S"
  using finsum_partition[of Fs f S]
        finsum_zero[of "Fs - S"]
        assms finsum_eq_parition
  by (metis Diff_iff )       

lemma ac_mod_0:
  assumes "u \<in> nonzero Q\<^sub>p"
  assumes "(N::nat) > k"
  shows "ac k u = ac N u mod (p^k)"
proof- 
  have 0: "ac k u = angular_component u k"
    unfolding ac_def using assms nonzero_memE 
    by presburger
  have 1: "ac N u = angular_component u N"
    unfolding ac_def using assms nonzero_memE    
    by presburger
  show ?thesis unfolding 0 1 
    using angular_component_closed[of u] assms less_or_eq_imp_le p_residue_alt_def p_residue_padic_int
    by presburger
qed

lemma ac_mod:
  assumes "u \<in> carrier Q\<^sub>p"
  assumes "(N::nat) > k"
  assumes "k > 0"
  shows "ac k u = ac N u mod (p^k)"
  apply(cases "u \<in> nonzero Q\<^sub>p", rule ac_mod_0, blast, rule assms)
proof- 
  assume A: "u \<notin>nonzero Q\<^sub>p"
  then have 0: "u = \<zero>"
    using assms unfolding nonzero_def by blast 
  show ?thesis unfolding ac_def 0 
    by presburger
qed

lemma nth_power_fact'':
  assumes "1 \<le> n" 
  shows "\<exists>m>1. \<forall>u\<in>carrier Q\<^sub>p. ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
proof- 
  obtain m where m_def: "m > 0 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
    using assms nth_power_fact by blast 
  have 0: "(\<forall>u\<in>carrier Q\<^sub>p. ac (Suc m) u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  proof(rule, rule) 
    fix u assume A: "u \<in> carrier Q\<^sub>p" "ac (Suc m) u = 1 \<and> val u = 0 "
    have 1: "ac m u = (ac (Suc m) u) mod p^m"
      apply(rule ac_mod, rule A, auto)
      using m_def by blast 
    have 2: "ac (Suc m) u = (1::int) "
      using A by blast
    have "(1::int) mod p ^ m = (1::int)"
    proof- 
      have "p^m > (1::int)"
      proof- 
        have 0: "m > (0::nat)"
          using m_def by blast 
        have 1: "p > 1"
          by (simp add: prime prime_gt_1_int)
        have "p^m > p^0"
          using 0 1 power_strict_increasing by blast
        thus ?thesis 
          by (metis int.nat_pow_0)
      qed
      thus ?thesis 
        using mod_pos_pos_trivial by presburger
    qed
    hence 3: "ac m u = (1::int)"
      unfolding 1 2 using m_def by blast 
    have 4: "\<And>u. u \<in> carrier Q\<^sub>p \<Longrightarrow> ac m u = (1::int) \<Longrightarrow> val u = 0 \<Longrightarrow>  u \<in> P_set n"
      using m_def by blast 
    show "u \<in> P_set n"
      apply(rule 4, rule A, rule 3)
      using A by blast
  qed
  have 1: "Suc m > 1"
    using m_def  by linarith
  show ?thesis using m_def 0 1 
    by blast
qed

text\<open>The cell \texttt{(constant\_res m b l k)} is of the form: \[ 
\{(t,x) \in \mathbb{Q}_p^(m+1) \mid x \in b \text{ and val}(t - k) \geq  p^l  \}
\]
Membership of a point $(t,x)$ in this cell will ensure that the degree $l$ residue of $t$ is equal to $k$.\<close>

definition constant_res where
"constant_res m b l k = Cond m b ([(k::int)]\<cdot>\<^bsub>SA m\<^esub>\<one>\<^bsub>SA m\<^esub>) ([(p^(l::nat))]\<cdot>\<^bsub>SA m\<^esub>\<one>\<^bsub>SA m\<^esub>) (\<zero>\<^bsub>SA m\<^esub>) closed_interval"

lemma cell_cond_mem_decomp: 
  assumes "xs \<in> condition_to_set (Cond m C c a1 a2 I)"
  shows "xs = hd xs # tl xs"
  using assms  unfolding condition_to_set.simps cell_def mem_Collect_eq 
  using Suc_pow_mem_decomp by blast

lemma cell_cond_head_closure: 
  assumes "t#x \<in> condition_to_set \<C>"
  shows "t \<in> carrier Q\<^sub>p"
  using assms condition_to_set.simps unfolding cell_def 
  by (metis (no_types, lifting) cell_hd_closed list_hd)

lemma (in cring) add_int_pow_int:
  shows "([(int (l::nat))]\<cdot>\<^bsub>R\<^esub>a) = ([l]\<cdot>a)"
  unfolding add_pow_def unfolding int_pow_int
  by blast 

lemma SA_int_add_pow:
  assumes "f \<in> carrier (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "([(k::int)]\<cdot>\<^bsub>SA m\<^esub>f) x = [k]\<cdot>(f x)"
proof(induction k)
  case (nonneg n)
  have 0: "[int n] \<cdot>\<^bsub>SA m\<^esub> f = [n] \<cdot>\<^bsub>SA m\<^esub> f"
    by(rule R.add_int_pow_int)
  have 1: "[int n] \<cdot> f x = [n] \<cdot> f x"
    by(rule Qp.add_int_pow_int)
  show ?case
    unfolding 0 1 
    using SA_add_pow_apply assms(1) assms(2) by blast
next
  case (neg n)
  have 0: "[(- int (Suc n))] \<cdot>\<^bsub>SA m\<^esub> f = \<ominus>\<^bsub>SA m\<^esub> ([(Suc n)] \<cdot>\<^bsub>SA m\<^esub> f)"
    using assms R.add.int_pow_neg_int by blast
  have 1: "[(- int (Suc n))] \<cdot> f x = \<ominus> ([(Suc n)] \<cdot> f x)"
    using assms SA_car_closed Qp.add.int_pow_neg_int by blast
  show ?case 
    unfolding 0 1 
    using assms SA_car_closed 
    using SA_add_pow_apply SA_add_pow_closed SA_u_minus_eval by presburger
qed

lemma SA_int_inc_eval: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "([(k::int)]\<cdot>\<^bsub>SA m\<^esub>\<one>\<^bsub>SA m\<^esub>) x = [k]\<cdot>\<one>"
  using SA_int_add_pow assms  R.cring_simprules(6) SA_oneE by presburger

lemma SA_nat_inc_eval:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "([(k::nat)]\<cdot>\<^bsub>SA m\<^esub>\<one>\<^bsub>SA m\<^esub>) x = [k]\<cdot>\<one>"
  using SA_add_pow_apply assms R.cring_simprules(6) SA_oneE by presburger

lemma Qp_res_res:
  assumes "t \<in> \<O>\<^sub>p"
  shows "Qp_res t k = Qp_res ([Qp_res t k] \<cdot> \<one>) k"
  unfolding Qp_res_int_inc using Qp_res_closed Qp_res_mod_triv[of t k] assms by presburger

lemma constant_res_arity:
"arity (constant_res m b l k) = m"
  unfolding constant_res_def arity.simps by blast 

lemma constant_res_cell_cond: 
  assumes "is_semialgebraic m b"
  shows "is_cell_condition (constant_res m b l k)"
  unfolding constant_res_def 
  apply(rule is_cell_conditionI', rule assms, blast, blast, blast)
  unfolding is_convex_condition_def by blast

lemma disjoint_decomp: 
  assumes "is_semialgebraic (Suc m) A"
  assumes "is_semialgebraic (Suc m) B"
  assumes "A \<inter> B = {}"
  assumes "is_cell_decomp m S A"
  assumes "is_cell_decomp m S' B"
  assumes "\<And>\<C>. \<C> \<in> S \<Longrightarrow> P \<C>"
  assumes "\<And>\<C>. \<C> \<in> S' \<Longrightarrow> P \<C>"
  assumes "C = A \<union> B"
  shows "is_cell_decomp m (S \<union> S') C"
        "\<And>\<C>. \<C> \<in> S \<union> S' \<Longrightarrow> P \<C>"
   apply(rule cell_decomp_union[of A])
  using assms apply blast 
  using assms is_semialgebraic_closed apply blast
  using assms apply blast
proof- 
  have 0: "B = C - A"
    unfolding assms using assms(3) by blast 
  show "is_cell_decomp m S' (C - A)"
    using assms unfolding 0 by blast 
  show "\<And>\<C>. \<C> \<in> S \<union> S' \<Longrightarrow> P \<C>"
    using assms by blast 
qed

text\<open>This lemma is needed to formalize the portion of Denef's proof where he claims that "$A \setminus A_0$ can be be partitioned into a finite number of cells of the form \[ 
  B = \{ (x,t) \mid x \in C, \text{ ord}(t - c(x)) = \text{ ord}\theta(x)\}\]
where $C$ is a semi-algebraic subset of $K^m$ and $\theta(x)$ is a semialgebraic function". In our version, Denef's set $A$ is our set $\texttt{condition\_to\_set} \mathcal{C}$ and the set $A_0$ is our set $A$. \<close>

lemma val_infty_iff:
  "val x = \<infinity> \<longleftrightarrow> x = \<zero>"
  unfolding val_def 
  by (metis eint.distinct(2))

lemma cell_at_infinity:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "val (x \<ominus> y) = \<infinity>"
  shows "x = y"
  using assms unfolding val_infty_iff 
  using Qp.r_right_minus_eq by blast

text\<open>This lemma will be needed later to decompose normalized cells. It shows that the 
        \texttt{constant\_res} cells can be used to decompose a normalized cell.\<close>

lemma constant_residue_normalized_cell_decomp:
  assumes "\<B> = (normal_cell m b)"
  assumes "is_semialgebraic m b"
  assumes "U = {x \<in> carrier (Zp_res_ring l). val ([x]\<cdot>\<one>) = 0}"
  assumes "l > 0"
  assumes "S = constant_res m b l ` U" 
  shows "is_cell_decomp m S (condition_to_set \<B>)"
        "\<And>xs k. k \<in> U \<Longrightarrow> xs \<in> condition_to_set (constant_res m b l k) \<Longrightarrow> 
                 hd xs \<in> \<O>\<^sub>p \<and> Qp_res (hd xs) l = k"
proof- 
  show C0: "\<And>xs k. k \<in> U \<Longrightarrow> xs \<in> condition_to_set (constant_res m b l k) \<Longrightarrow> 
              hd xs \<in> \<O>\<^sub>p \<and> Qp_res (hd xs) l = k"
  proof - 
    fix xs k assume A: "k \<in> U" " xs \<in> condition_to_set (constant_res m b l k)"
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A unfolding constant_res_def condition_to_set.simps cell_def by blast 
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Suc_pow_mem_decomp by blast
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using A unfolding tx_def 
      using cell_cond_head_closure by blast
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
    have 0: "([(k::int)]\<cdot>\<^bsub>SA m\<^esub>\<one>\<^bsub>SA m\<^esub>) x = [k]\<cdot>\<one>"
      by(rule SA_int_inc_eval, rule x_closed)
    have 1: "([(p^l)]\<cdot>\<^bsub>SA m\<^esub>\<one>\<^bsub>SA m\<^esub>) x = [(p^l)]\<cdot>\<one>"
      by(rule SA_int_inc_eval, rule x_closed)
    have 2: "val (t \<ominus> [k]\<cdot>\<one>) \<in> closed_interval (val ([(p^l)]\<cdot>\<one>)) (val (\<zero>\<^bsub>SA m\<^esub> x))"
      using A 
      unfolding constant_res_def condition_to_set.simps cell_def tx_def mem_Collect_eq  list_tl list_hd 
                1  0 
      by blast 
    hence 3: "val (t \<ominus> [k]\<cdot>\<one>) \<ge> val ([(p ^ l)] \<cdot> \<one>)"
      by(rule  closed_interval_memE)  
    have 4: "val ([(p ^ l)] \<cdot> \<one>) = l"
      by (metis Qp.int_nat_pow_rep int_pow_int val_p_int_pow)
    have 5: "val (t \<ominus> [k]\<cdot>\<one>) \<ge> l"
      using 3 unfolding 4 by blast 
    have 6: "val t \<ge> 0"
    proof- 
      have 60: "val ([k]\<cdot>\<one>) \<ge> 0"
        using val_of_int_inc by blast
      have 61: "val (t \<ominus> [k]\<cdot>\<one>) \<ge> 0"
        using 5 
        by (metis (no_types, opaque_lifting) "4" eint_ord_trans val_of_int_inc)
      show ?thesis using 60 61 t_closed val_ultrametric'[of t "[k]\<cdot>\<one>"] 
        by (metis (no_types, lifting) Qp.cring_simprules(6) Qp.int_inc_closed Qp_isosceles min.orderE padic_fields.notin_closed padic_fields_axioms val_one val_ultrametric' val_ultrametric_noteq'')
    qed
    have 7: "Qp_res t l = Qp_res ([k]\<cdot>\<one>) l"
      apply(rule Qp_res_eqI', rule val_ring_memI, rule t_closed, rule 6)
      using val_ring_int_inc_closed apply blast
      by(rule 5)
    have 8: "hd xs \<in> \<O>\<^sub>p "
      unfolding tx_def list_hd 
      by(rule val_ring_memI, rule t_closed, rule 6)
    have 9: "Qp_res (lead_coeff xs) l = k"
      unfolding tx_def list_hd 7 Qp_res_int_inc 
      using A unfolding assms mem_Collect_eq 
      by (meson mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
    show "hd xs \<in> \<O>\<^sub>p \<and> Qp_res (lead_coeff xs) l = k"
      using 8 9 by blast 
  qed
  have 1: "l > 0 \<Longrightarrow> is_cell_decomp m S (condition_to_set \<B>)"
  proof- assume A: "l > 0"
    obtain F where F_def: "F = constant_res m b l"
      by blast 
    have F_cell_cond: "\<And>k. is_cell_condition (F k)"
      unfolding F_def constant_res_def  apply(rule is_cell_conditionI', rule assms, blast, blast, blast)
      unfolding is_convex_condition_def by blast 
    have 0: "(condition_to_set ` F ` U) partitions (condition_to_set \<B>)"
    proof(rule is_partitionI, rule disjointI)
      fix A B assume 
      A0: "A \<in> condition_to_set ` F ` U" "B \<in> condition_to_set ` F ` U" "A \<noteq> B"
      obtain j where j_def: "j \<in> U \<and> A = condition_to_set (F j)"
        using A0 by blast 
      obtain k where k_def: "k \<in> U \<and> B = condition_to_set (F k)"
        using A0 by blast 
      have l_neq_k: "j \<noteq> k"
        using j_def k_def A0 by blast 
      show "A \<inter> B = {}"
      proof(rule equalityI')
        fix x assume A: "x \<in> A \<inter> B"
        have 01: "x \<in> condition_to_set (F j) \<inter> condition_to_set (F k)"
          using A j_def k_def by blast 
        have 02: " val([j]\<cdot>\<one>) = 0"
          using j_def unfolding assms by blast 
        have 03: " val([k]\<cdot>\<one>) = 0"
          using k_def unfolding assms by blast 
        have 04: "Qp_res ([j]\<cdot>\<one>) l = j"
          using j_def unfolding assms
          by (metis (no_types, lifting) Qp_res_int_inc mem_Collect_eq mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
        have 05: "Qp_res ([k]\<cdot>\<one>) l = k"
          using k_def unfolding assms
          by (metis (no_types, lifting) Qp_res_int_inc mem_Collect_eq mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
        show "x \<in> {}"
          using 01 C0[of j x] C0[of k x] l_neq_k j_def k_def 
          unfolding F_def by blast 
      next
        show "\<And>x. x \<in> {} \<Longrightarrow> x \<in> A \<inter> B"
          by blast 
      qed
    next 
      show " \<Union> (condition_to_set ` F ` U) = condition_to_set \<B>"
      proof(rule equalityI')
        show "\<And>xs. xs \<in> \<Union> (condition_to_set ` F ` U) \<Longrightarrow> xs \<in> condition_to_set \<B>"
        proof- fix xs assume A0: "xs \<in> \<Union> (condition_to_set ` F ` U)"
          then obtain j where j_def: "j \<in> U \<and> xs \<in>  condition_to_set (F j)"
            by blast 
          obtain t x where tx_def: "xs = t#x"
            using A  cell_conditon_mem_decomp j_def by blast
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
            using j_def assms
            unfolding tx_def F_def constant_res_def condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd
            by (metis (no_types, lifting) Qp_pow_ConsE(1) list_tl)
          have 0: "val (([(p ^ l)] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>) x) = l"
            using x_closed SA_int_inc_eval[of x m "p^l"] Qp.int_nat_pow_rep int_pow_int val_p_int_pow
            by metis 
          have 1: "([j] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>) x = [j]\<cdot>\<one>"
            by(rule SA_int_inc_eval, rule x_closed )
          have 2: "val (t \<ominus> [j]\<cdot>\<one>) \<ge> l"
            using j_def unfolding tx_def F_def constant_res_def 0 1
              condition_to_set.simps cell_def mem_Collect_eq  list_tl list_hd closed_interval_def 
            by blast 
          have 3: "val ([j]\<cdot>\<one>) = 0"
            using j_def unfolding assms by blast 
          have 4: "val (t \<ominus> [j]\<cdot>\<one>) > 0"
            using 2 A 
            by (meson eint_ord_simps(6) eint_ord_trans eint_pow_int_is_pos notin_closed of_nat_0_less_iff)
          have t_closed: "t \<in> carrier Q\<^sub>p"
            using j_def unfolding condition_to_set.simps F_def constant_res_def cell_def mem_Collect_eq list_hd tx_def 
            using cell_cond_head_closure j_def tx_def by blast
          have 5: "val t = 0"
            using t_closed 4 3 
            by (metis Qp.int_inc_closed ultrametric_equal_eq)
          show "xs \<in> condition_to_set \<B>"
            unfolding tx_def assms 
            apply(rule normal_cell_memI, rule assms)
            using j_def unfolding F_def constant_res_def condition_to_set.simps cell_def tx_def mem_Collect_eq list_tl 
              apply blast
             by(rule t_closed, rule 5)
        qed
        show "\<And>x. x \<in> condition_to_set \<B> \<Longrightarrow> x \<in> \<Union> (condition_to_set ` F ` U)"
        proof- 
          fix xs assume A0: "xs \<in> condition_to_set \<B>"
          obtain t x where tx_def: "xs = t#x"
            using A0 unfolding assms normal_cell_def condition_to_set.simps cell_def 
            using A0 cell_conditon_mem_decomp by blast
          obtain j where j_def: "j = Qp_res t l"
            by blast 
          have 0: "val t = 0"
            using A0 normal_cell_memE assms unfolding assms tx_def 
            by blast 
          have 1: "t \<in> carrier Q\<^sub>p"
            using A0 normal_cell_memE assms unfolding assms tx_def 
            by blast 
          have 2: "val (t \<ominus> [j]\<cdot>\<one>) \<ge> l"
            apply(rule Qp_res_eqE, rule val_ring_memI, rule 1)
            apply (simp add: "0") 
            using val_ring_int_inc_closed apply blast
            unfolding j_def apply(rule Qp_res_res, rule val_ring_memI, rule 1)
            using 0 by (simp add: "0")
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
            using A0 unfolding assms condition_to_set.simps normal_cell_def cell_def 
            by (metis (no_types, lifting) Qp_pow_ConsE(1) list_tl mem_Collect_eq tx_def)
          have 3: "val (([(p ^ l)] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>) (tl xs)) = l"
            unfolding tx_def list_tl 
            using x_closed SA_int_inc_eval[of x m "p^l"] Qp.int_nat_pow_rep int_pow_int val_p_int_pow
            by metis 
          have 4: "val (\<zero>\<^bsub>SA m\<^esub> (tl xs)) = \<infinity>"
            using  x_closed unfolding tx_def list_tl val_zero 
            using SA_zeroE local.val_zero by presburger
          have 5: "([j] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>) x = [j]\<cdot>\<one>"
            unfolding tx_def list_tl 
            using x_closed SA_int_inc_eval[of x m "j"] 
            by metis 
          have 6: "xs \<in> condition_to_set (F j)"
            unfolding F_def assms constant_res_def condition_to_set.simps
            apply(rule cell_memI) 
            using A0 unfolding assms condition_to_set.simps normal_cell_def cell_def apply blast
            using A0 unfolding assms condition_to_set.simps normal_cell_def cell_def apply blast
            unfolding 3 4 unfolding  tx_def list_tl list_hd 5 
            apply(rule closed_interval_memI, rule 2)
            using eint_ord_code(3) by blast
          have 7: "val t = val ([j]\<cdot>\<one>)"
            by (smt (verit) 0 1 2 A Qp.int_inc_closed Qp.minus_closed eint_defs(1) eint_ord_code(4)
                eint_ord_simps(1) eint_pow_int_is_pos local.val_zero of_nat_0_less_iff 
                ultrametric_equal_eq' val_ord') 
          have 8: "j \<in> U"
            using 0
            unfolding assms mem_Collect_eq 7 j_def 
            by (metis "0" "1" Qp_res_closed val_of_int_inc val_ringI)
          show "xs \<in> \<Union> (condition_to_set ` F ` U)"
            using 6 8 by blast 
        qed
      qed
    qed
    have 1: "finite U"
    proof- 
      have 0: "finite (carrier (Zp_res_ring l))"
        using residue_ring_card by blast 
      have "U \<subseteq> carrier (Zp_res_ring l)"
        unfolding assms by blast 
      thus ?thesis 
        using 0 finite_subset by blast 
    qed
    have 2: " \<And>s s'.
       s \<in> constant_res m b l ` {x \<in> carrier (residue_ring (p ^ l)). val ([x] \<cdot> \<one>) = 0} \<Longrightarrow>
       s' \<in> constant_res m b l ` {x \<in> carrier (residue_ring (p ^ l)). val ([x] \<cdot> \<one>) = 0} \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
    proof- fix s s'
      assume A: "s \<in> constant_res m b l ` {x \<in> carrier (residue_ring (p ^ l)). val ([x] \<cdot> \<one>) = 0}"
       "s' \<in> constant_res m b l ` {x \<in> carrier (residue_ring (p ^ l)). val ([x] \<cdot> \<one>) = 0}" "s \<noteq> s'"
      obtain j where j_def: "j \<in> {x \<in> carrier (residue_ring (p ^ l)). val ([x] \<cdot> \<one>) = 0} \<and> s = constant_res m b l j"
        using A by blast 
      have s_eq: "s = constant_res m b l j"
        using j_def by blast
      obtain k where k_def: "k \<in> {x \<in> carrier (residue_ring (p ^ l)). val ([x] \<cdot> \<one>) = 0} \<and> s' = constant_res m b l k"
        using A by blast 
      have s'_eq: "s' = constant_res m b l k"
        using k_def by blast
      have l_neq_k: "j \<noteq> k"
        using j_def k_def A by blast 
      obtain A where A_def: "A = condition_to_set s"
        by blast 
      obtain B where B_def: "B = condition_to_set s'"
        by blast 
      have 0: "A \<inter> B = {}"
      proof(rule equalityI')
        fix x assume A0: "x \<in> A \<inter> B"
        have 01: "x \<in> condition_to_set (F j) \<inter> condition_to_set (F k)"
          using A0 unfolding F_def A_def B_def s'_eq s_eq by blast 
        have 02: " val([j]\<cdot>\<one>) = 0"
          using j_def unfolding assms by blast 
        have 03: " val([k]\<cdot>\<one>) = 0"
          using k_def unfolding assms by blast 
        have 04: "Qp_res ([j]\<cdot>\<one>) l = j"
          using j_def unfolding assms
          by (metis (no_types, lifting) Qp_res_int_inc mem_Collect_eq mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
        have 05: "Qp_res ([k]\<cdot>\<one>) l = k"
          using k_def unfolding assms
          by (metis (no_types, lifting) Qp_res_int_inc mem_Collect_eq mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
        show "x \<in> {}"
          using C0[of j x] C0[of k x] 01 l_neq_k j_def k_def 
          unfolding F_def assms  by blast 
      next
        show "\<And>x. x \<in> {} \<Longrightarrow> x \<in> A \<inter> B"
          by blast 
      qed
      show "condition_to_set s \<inter> condition_to_set s' = {}"
        using 0 unfolding A_def B_def by blast 
    qed
    show "is_cell_decomp m S (condition_to_set \<B>)"
      apply(rule is_cell_decompI)
      using assms 1 apply blast 
      using 0 unfolding assms F_def  apply blast
      using assms constant_res_arity constant_res_cell_cond apply blast
      unfolding normal_cell_def condition_to_set.simps cell_def apply blast
      by(rule 2)
  qed
  show "is_cell_decomp m S (condition_to_set \<B>)" using assms 1 assms by blast 
qed

lemma remove_empty_cells:
  assumes "is_cell_decomp m S Y"
  shows "is_cell_decomp m {\<C> \<in> S. condition_to_set \<C> \<noteq> {}} Y"
proof-
  have 0: "finite S"
          "condition_to_set ` S partitions Y"
          "\<And> s. s \<in> S \<Longrightarrow> is_cell_condition s"
          "\<And> s. s \<in> S \<Longrightarrow> arity s = m"
          "\<And> s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
          " Y \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using assms is_cell_decompE[of m S Y] by auto 
  have 1: "\<And>A B. A \<in> condition_to_set ` {\<C> \<in> S. condition_to_set \<C> \<noteq> {}} \<Longrightarrow>
           B \<in> condition_to_set ` {\<C> \<in> S. condition_to_set \<C> \<noteq> {}} \<Longrightarrow> A \<noteq> B \<Longrightarrow> A \<inter> B = {}"
    using 0(5) by auto 
  have 2: "\<Union> (condition_to_set ` {\<C> \<in> S. condition_to_set \<C> \<noteq> {}}) = Y"
    using 0(2) is_partitionE(2)[of "condition_to_set ` S " Y] by auto 
  have 3: "\<And>s. s \<in> {\<C> \<in> S. condition_to_set \<C> \<noteq> {}} \<Longrightarrow> is_cell_condition s \<and> arity s = m"
    using 0 by auto 
  have 4: "Y \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using 0 by auto 
  have 5: "finite {\<C> \<in> S. condition_to_set \<C> \<noteq> {}}"
    using 0 by auto 
  have 6: "\<And>s s'.
       s \<in> {\<C> \<in> S. condition_to_set \<C> \<noteq> {}} \<Longrightarrow>
       s' \<in> {\<C> \<in> S. condition_to_set \<C> \<noteq> {}} \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<noteq> condition_to_set s'"
    using 0(5) by auto 
  show ?thesis 
    by(intro is_cell_decompI is_partitionI disjointI 1 2 3 4 5 6, auto )
qed

lemma retain_property:
  assumes "\<forall> \<C> \<in> S. P \<C>"
  shows "\<forall> \<C> \<in> {\<C> \<in> S. condition_to_set \<C> \<noteq> {}}. P \<C>"
  using assms by auto 

lemma constant_poly_residue_normalized_cell_decomp:
  assumes "is_semialgebraic m b"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "\<And> i x. x \<in> b \<Longrightarrow> g i x \<in> \<O>\<^sub>p"
  assumes "deg (SA m) g \<le> d"
  assumes "l > 0"
  shows "\<exists>S. is_cell_decomp m S (condition_to_set (normal_cell m b)) \<and>
             (\<forall> \<C> \<in> S. condition_to_set \<C> \<noteq> {} 
                  \<and> (\<exists>k \<in> carrier (Zp_res_ring l). \<exists>b'.\<exists> cl \<in> poly_res_classes N d.
                   is_semialgebraic m b' \<and> b' \<subseteq> b \<and> val([k]\<cdot>\<one>) = 0  \<and>
                     \<C> = constant_res m b' l k
                    \<and> (\<forall>x \<in> b'.   poly_res_class N d (SA_poly_to_Qp_poly m x g) = cl)))"
proof- 
  have b_sub: "b \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms is_semialgebraic_closed by presburger
  obtain S where S_def: "S = constant_res m b l ` {x \<in> carrier (Zp_res_ring l). val ([x]\<cdot>\<one>) = 0}"
    by blast 
  obtain U where U_def: "U = {x \<in> carrier (Zp_res_ring l). val ([x]\<cdot>\<one>) = 0}"
    by blast 
  have 0: "is_cell_decomp m S (condition_to_set (normal_cell m b))"
    by(intro constant_residue_normalized_cell_decomp[of _ _ b U l], 
                auto simp: assms U_def S_def)
  have 1: "\<And>xs k. k \<in> U
             \<Longrightarrow> xs \<in> condition_to_set (constant_res m b l k) \<Longrightarrow> 
                           hd xs \<in> \<O>\<^sub>p \<and> Qp_res (hd xs) l = k"
    by(intro constant_residue_normalized_cell_decomp[of _ _ b U l], 
                auto simp: assms U_def S_def)
  show ?thesis 
  proof(rule refine_each_cell[of _ S], rule 0)
    fix C assume A: "C \<in> S"
    have cell: "is_cell_condition C"
      using A 0 is_cell_decompE(3) by force
    then obtain k where k_def: "k \<in> U" "C = constant_res m b l k"
      using A unfolding S_def U_def by auto
    have k_props: "k \<in> carrier (residue_ring (p ^ l))" "val ([k] \<cdot> \<one>) = 0"
      using k_def unfolding U_def mem_Collect_eq by auto 
    obtain F where F_def: "F = (\<lambda>cl. {x \<in> b. SA_poly_to_Qp_poly m x g \<in> cl})"
      by blast 
    obtain bs where bs_def: "bs = F ` (poly_res_classes N d)"
      by blast 
    have bs_finite: "finite bs"
      unfolding bs_def using poly_res_classes_finite by auto 
    have bs_covers: "b = \<Union> bs"
    proof(rule equalityI', unfold bs_def F_def, auto) 
      fix x assume a: "x \<in> b"
      have 0: "SA_poly_to_Qp_poly m x g \<in> poly_res_class N d (SA_poly_to_Qp_poly m x g) 
              \<and> SA_poly_to_Qp_poly m x g \<in> val_ring_polys_grad d"
        apply(intro conjI poly_res_class_refl val_ring_polys_grad_memI SA_poly_to_Qp_poly_closed
                    assms)
        using a b_sub  assms SA_poly_to_Qp_poly_coeff[of x m g]  
              SA_poly_to_Qp_poly_deg_bound[of g m x] assms by auto 
      show "\<exists>cl\<in>poly_res_classes N d. SA_poly_to_Qp_poly m x g \<in> cl"
        using 0 unfolding poly_res_classes_def by auto 
    qed
    have bs_disjoint: "disjoint bs"
    proof(rule disjointI)
      fix A B assume A: "A \<in> bs" "B \<in> bs" "A \<noteq> B"
      obtain cl1 where cl1_def: 
          "cl1 \<in> poly_res_classes N d" "A = {x \<in> b. SA_poly_to_Qp_poly m x g \<in> cl1}"
        using A unfolding bs_def F_def by auto 
      obtain cl2 where cl2_def: 
          "cl2 \<in> poly_res_classes N d" "B = {x \<in> b. SA_poly_to_Qp_poly m x g \<in> cl2}"
        using A unfolding bs_def F_def by auto 
      have neq: "cl1 \<noteq> cl2" 
        using A cl1_def cl2_def by auto 
      hence "cl1 \<inter> cl2 = {}"
        using poly_res_classes_disjoint cl1_def cl2_def by blast
      thus "A \<inter> B = {}" using cl1_def cl2_def by auto 
    qed
    have bs_semialg: "\<And> b'. b' \<in> bs \<Longrightarrow> is_semialgebraic m b'"
    proof- 
      fix b' assume A: "b' \<in> bs"
      obtain cl where cl_def: 
          "cl \<in> poly_res_classes N d" "b' = {x \<in> b. SA_poly_to_Qp_poly m x g \<in> cl}"
        using A unfolding bs_def F_def by auto 
      show "is_semialgebraic m b'"
        unfolding cl_def 
        apply(intro  SA_poly_constant_res_class_semialg'[of _ _ _ d _ N] assms cl_def) 
        using assms(1) is_semialgebraic_closed by auto 
    qed
    obtain S where S_def: "S = refine_fibres C ` bs"
      by blast 
    obtain S' where S'_def: "S' = {\<D> \<in> S. condition_to_set \<D> \<noteq> {}}"
      by blast 
    have S_decomp: "is_cell_decomp m S (condition_to_set C)"
      apply(unfold S_def k_def constant_res_def, 
            rule partition_to_cell_decomp[of _ m b "[k] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>"
                "[(p ^ l)] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>" "\<zero>\<^bsub>SA m\<^esub>" closed_interval])
      using cell k_def constant_res_def apply auto[2] 
      using is_partitionI bs_covers bs_disjoint 
            bs_semialg are_semialgebraic_def bs_finite by auto
    have  "\<forall>\<C>\<in>S. (\<exists>k \<in> carrier (Zp_res_ring l). \<exists>b'.\<exists> cl \<in> poly_res_classes N d.
                   is_semialgebraic m b' \<and> b' \<subseteq> b \<and> val([k]\<cdot>\<one>) = 0  \<and>
                     \<C> = constant_res m b' l k
                    \<and> (\<forall>x \<in> b'.   poly_res_class N d (SA_poly_to_Qp_poly m x g) = cl))"
    proof
      fix \<C> assume A: "\<C> \<in> S" 
      obtain b' cl where defs: "b' \<in> bs" "\<C> = refine_fibres C b'" "b' = F cl" 
                               "cl \<in> poly_res_classes N d"
        using A S_def bs_def by auto 
      have b'_sub: "b' \<subseteq> b"
        using defs unfolding bs_def F_def by auto 
      have 0: "\<C> = constant_res m b' l k"
        unfolding defs k_def refine_fibres_def constant_res_def by auto 
      have 1: "is_semialgebraic m b' \<and> val([k]\<cdot>\<one>) = 0 \<and> b' \<subseteq> b"
        using defs k_props bs_semialg bs_def F_def by auto 
      have 2: " \<forall>x \<in> b'. (SA_poly_to_Qp_poly m x g) \<in>  cl"
        unfolding 0 constant_res_def condition_to_set.simps cell_def mem_Collect_eq 
                  defs F_def 
        by auto 
      have 3: "\<And> xs. xs \<in> condition_to_set \<C> \<Longrightarrow> tl xs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
              "\<And> xs. xs \<in> condition_to_set \<C> \<Longrightarrow> tl xs \<in> b"
              "\<And> x. x \<in> b' \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        unfolding defs refine_fibres_def k_def constant_res_def condition_to_set.simps
                  cell_def F_def mem_Collect_eq
        using cartesian_power_tail b_sub by auto  
      have 4: " \<forall>x \<in> b'. (SA_poly_to_Qp_poly m x g) \<in> val_ring_polys_grad d"
        apply(auto, intro val_ring_polys_grad_memI SA_poly_to_Qp_poly_closed 3 assms, auto)
        using 3 assms b'_sub SA_poly_to_Qp_poly_coeff apply auto[1]
        apply(rule le_trans[of _ "deg (SA m) g" d], rule SA_poly_to_Qp_poly_deg_bound[of g m])
        using assms 3 by auto 
      have 5: " \<forall>x \<in> b'. (SA_poly_to_Qp_poly m x g) \<in> 
         poly_res_class N d (SA_poly_to_Qp_poly m x g)"
        apply(auto, intro poly_res_class_refl)
        using 4 by auto 
      have 50: " \<forall> x \<in> b'.  poly_res_class N d (SA_poly_to_Qp_poly m x g)
              \<in> poly_res_classes N d"
        using 4 poly_res_classes_def by auto 
      have 6: "\<forall> x \<in> b'. poly_res_class N d (SA_poly_to_Qp_poly m x g) = cl"
        using poly_res_classes_disjoint[of cl N d ] defs(4) 2 3 4 5 50 
        by (smt Diff_Diff_Int Diff_empty disjoint_iff equals0I inf_commute
                inf_idem poly_res_classes_disjoint)
      have 7: " cl\<in>poly_res_classes N d \<and>
             (\<forall>x\<in>b'. poly_res_class N d (SA_poly_to_Qp_poly m x g) = cl)"
        using defs  6 by auto 
      have 8: "k\<in>carrier (residue_ring (p ^ l)) \<and>
             (\<exists>b'. is_semialgebraic m b' \<and> b' \<subseteq> b \<and> val ([k] \<cdot> \<one>) = 0 \<and> \<C> = constant_res m b' l k)"
        using k_def 0 1 unfolding U_def mem_Collect_eq by auto 
      thus "\<exists>k\<in>carrier (residue_ring (p ^ l)). \<exists>b'. \<exists>cl\<in>poly_res_classes N d.
              is_semialgebraic m b' \<and>   b' \<subseteq> b \<and>  val ([k] \<cdot> \<one>) = 0 \<and>
              \<C> = constant_res m b' l k \<and> 
              (\<forall>x\<in>b'. poly_res_class N d (SA_poly_to_Qp_poly m x g) = cl)"
        using k_def 0 unfolding U_def mem_Collect_eq 
        using 7 1 by blast        
    qed
    hence p: "\<forall>\<C>\<in>S'. condition_to_set \<C> \<noteq> {} \<and>
                     (\<exists>k\<in>carrier (residue_ring (p ^ l)). \<exists>b'. \<exists>cl\<in>poly_res_classes N d.
              is_semialgebraic m b' \<and>   b' \<subseteq> b \<and>  val ([k] \<cdot> \<one>) = 0 \<and>
              \<C> = constant_res m b' l k \<and> 
              (\<forall>x\<in>b'. poly_res_class N d (SA_poly_to_Qp_poly m x g) = cl))"
      unfolding S'_def by auto 
    have q: "is_cell_decomp m S' (condition_to_set C)"
      unfolding S'_def using remove_empty_cells S_decomp by auto 
    have "is_cell_decomp m S' (condition_to_set C) \<and>
             (\<forall>\<C>\<in>S'. condition_to_set \<C> \<noteq> {} \<and>
                     (\<exists>k\<in>carrier (residue_ring (p ^ l)). \<exists>b'. \<exists>cl\<in>poly_res_classes N d.
              is_semialgebraic m b' \<and>   b' \<subseteq> b \<and>  val ([k] \<cdot> \<one>) = 0 \<and>
              \<C> = constant_res m b' l k \<and> 
              (\<forall>x\<in>b'. poly_res_class N d (SA_poly_to_Qp_poly m x g) = cl)))"
      using p q by auto 
    thus " \<exists>S. is_cell_decomp m S (condition_to_set C) \<and>
             (\<forall>\<C>\<in>S. condition_to_set \<C> \<noteq> {} \<and>
         (\<exists>k\<in>carrier (residue_ring (p ^ l)).
             \<exists>b'. \<exists>cl\<in>poly_res_classes N d.
                     is_semialgebraic m b' \<and>
                     b' \<subseteq> b \<and>
                     val ([k] \<cdot> \<one>) = 0 \<and>
                     \<C> = constant_res m b' l k \<and>
                     (\<forall>x\<in>b'. poly_res_class N d (SA_poly_to_Qp_poly m x g) = cl)))"
      by auto 
  qed
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>The Case $r=1$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>The first case that needs to be dealt with is showing Denef's Theorem $II_d$ for the case 
     that we are only producing a cell decomposition on which we can factor a single semialgebraic 
     polynomial.  \<close>

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Refining a Cell According to the Coefficients of a Polynomial\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>We use this locale to show that a cell can be refined so that the coefficients of a 
     semialgebraic polynomial \<close>

locale denef_II_base = common_refinement_locale + 
  fixes n 
  assumes n_pos: "(n::nat) > 0"
  assumes inds_nonempty: "inds \<noteq> {}"
  assumes ubounded: "\<exists>N. SA_poly_ubounded p m f c (condition_to_set \<C>) N"
  assumes min_taylor_term: "has_minimal_i \<C>"
  assumes nontrivial: "condition_to_set \<C> \<noteq> {}"  

context denef_II_base
begin

lemmas assms = \<C>_def \<C>_cond f_deg ubounded

lemma obtain_coords:
  assumes "xs \<in> condition_to_set \<C>"
  shows "xs = (hd xs)#(tl xs)"
  using assms cell_conditon_mem_decomp by auto 

lemma some_closures:
  assumes "t#x \<in> condition_to_set \<C>"
  shows "t \<in> carrier Q\<^sub>p"
        "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        "t \<ominus> c x \<in> carrier Q\<^sub>p"
        "a i x \<in> carrier Q\<^sub>p"
proof- 
  show 0: "t \<in> carrier Q\<^sub>p"
    using assms cell_cond_head_closure by blast 
  show 1: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms  unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd
    by (metis cartesian_power_tail list.sel(3))
  show "t \<ominus> c x \<in> carrier Q\<^sub>p"
    by(intro Qp.ring_simprules 0 SA_car_closed[of _ m] c_closed 1)
  show "a i x \<in> carrier Q\<^sub>p"
    by (simp add: "1" a_eval)
qed

lemma \<C>_arity: "arity \<C> = m"
  using \<C>_def  arity.simps by blast 

lemma I_convex: "is_convex_condition I"
  using \<C>_def \<C>_cond is_cell_conditionE(5) by blast 

lemma f_taylor_term: "\<And> x t i. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
                        (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) = a i x \<otimes> (t \<ominus> c x)[^]i"
proof- fix x t i assume A0: "t#x \<in> condition_to_set \<C>"
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using A0 unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
    by (metis Qp_pow_ConsE(2) list_hd)
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using A0 unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
    by (metis Qp_pow_ConsE(1) list_tl)
  have B0: "SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f) = taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f)"
    by(rule SA_poly_to_Qp_poly_taylor_poly[of f m c x],rule  f_closed, rule c_closed,rule x_closed)
  have B1: "(UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) =  UPQ.taylor (c x) (SA_poly_to_Qp_poly m x f) i \<otimes> (t \<ominus> c x) [^] i"
    apply(rule UPQ.to_fun_taylor_term[of "SA_poly_to_Qp_poly m x f" t "c x" i])
    by(rule SA_poly_to_Qp_poly_closed, rule x_closed, rule f_closed, rule t_closed, rule SA_car_closed[of _ m], rule c_closed, rule x_closed)
  have B2: "SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f) i = taylor_expansion (SA m) c f i x"
    apply(rule SA_poly_to_Qp_poly_coeff, rule x_closed) 
    using taylor_closed c_closed f_closed  unfolding UPSA.taylor_def by blast 
  show B3: "UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t = a i x \<otimes> (t \<ominus> c x)[^]i"
    unfolding a_def B1 UPQ.taylor_def UPSA.taylor_def using B0 unfolding B2 
    using B2 by presburger
qed

definition N0 where N0: "(N0::nat) = (SOME N. \<forall>x t i.
           t # x \<in> condition_to_set \<C> \<longrightarrow>
           val (SA_poly_to_Qp_poly m x f \<bullet> t)
           \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint (int N))"

lemma N0_def: "\<And> x t i. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
                                val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint N0"
  using N0 assms SA_poly_uboundedE'''[of m f c "condition_to_set \<C>"] 
  by (smt (z3) someI_ex)

definition N1 where N1: "N1 = (SOME (N::nat). N > 1 \<and>
                                 (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n))"

lemma N1_def: "N1 > 1"
 "\<forall>u\<in>carrier Q\<^sub>p. ac N1 u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
proof- 
  have  " N1 > (1::nat) \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N1 u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  proof-
    have "\<exists>m>(1::nat). \<forall>u\<in>carrier Q\<^sub>p. ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
    apply(rule nth_power_fact''[of n])  
      using n_pos by auto 
    then obtain m where m_def: "m>(1::nat) \<and>( \<forall>u\<in>carrier Q\<^sub>p. ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
      by blast 
    show ?thesis 
      by(rule SomeE[of N1 _ m], rule N1, rule m_def)
  qed
  thus "N1 > 1"
      "\<forall>u\<in>carrier Q\<^sub>p. ac N1 u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
    by auto 
qed

definition N where N: "N = N0 + N1 + 1"

lemma N_ineq: "N > N0" "N \<ge> N0" "N > N1" "N \<ge> N1"
  unfolding N by auto 

lemma equal_pow_res_n_criterion:
  assumes "\<gamma> \<in> Units Q\<^sub>p"
  assumes "\<delta> \<in> carrier Q\<^sub>p"
  assumes "val \<gamma> = val \<delta>"
  assumes "val \<delta> \<le> N0"
  assumes "val (\<gamma> \<ominus> \<delta>) \<ge> N"
  shows "pow_res n \<delta> = pow_res n \<gamma>" 
        "pow_res n \<gamma> = pow_res n \<delta>" 
proof-
  have units:  "\<gamma> \<in> Units Q\<^sub>p" "\<delta> \<in> Units Q\<^sub>p"
  proof- 
    show "\<gamma> \<in> Units Q\<^sub>p"
      using assms val_zero  Units_eq_nonzero val_nonzero by auto
    thus "\<delta> \<in> Units Q\<^sub>p"
      using assms 
      by (metis Units_eq_nonzero equal_val_imp_equal_ord(2))
  qed
  have b: "val \<delta> + N1 < val (\<delta> \<ominus> \<gamma>)"
    apply(rule le_less_trans[of _ "eint (N0 + N1)"])
    apply (metis assms Num.of_nat_simps(4) add_right_mono plus_eint_simps(1))
    using assms N_ineq
    by (metis (no_types, lifting) Extended_Int.Suc_ile_eq N Num.of_nat_simps(2) Num.of_nat_simps(4) Qp.Units_closed val_dist_sym)
  have ac: "ac N1 \<delta> = ac N1 \<gamma>"
    apply(intro ac_val )
    using units Units_eq_nonzero assms b by auto  
  have c: "\<delta> = \<gamma> \<otimes> (\<delta> \<div> \<gamma>)"
    using Units_eq_nonzero assms local.fract_cancel_right units(2) by presburger
  obtain c where c_def: "c = (\<delta> \<div> \<gamma>) \<ominus> \<one>"
    by blast 
  have c_val: "val c \<ge> N1"
  proof- 
    have c_eq1: "c = (\<delta> \<ominus> \<gamma>) \<otimes> inv \<gamma>"
      unfolding c_def using units 
      by (metis (no_types, lifting) Qp.Units_closed Qp.Units_inv_closed Qp.Units_l_inv
          Qp.m_comm Qp.minus_closed Qp.r_minus_distr)
    have c_val: "val c = val (\<delta> \<ominus> \<gamma>) - val \<gamma>"
      unfolding c_eq1 using units 
      by (simp add: Qp.Units_closed Units_eq_nonzero val_fract)
    obtain i::int where i_def: "val \<gamma> = i"
      using assms by (metis eint_ile)
    hence i': "val \<delta> = i"
      using assms by auto 
    have 0: "val (\<delta> \<ominus> \<gamma>) \<ge> N"
      using assms by (simp add: Qp.Units_closed val_dist_sym)
    have 1: "i \<le> N0"
      using assms unfolding i' i_def 
      using eint_ord_code(1) by blast
    have 2: "eint (int N1) + eint i < N" 
      using 1 N_ineq unfolding c_val i_def i' 
      by (simp add: N)
    show "eint (int N1) \<le> val c"
      using 0 2 unfolding c_val i_def 
      by (smt (verit, best) Groups.add_ac(2) N1_def(1) Num.of_nat_simps(2) Qp.Units_closed 
          Qp.Units_inv_closed Qp.cring_simprules(5) Qp.minus_closed Qp.prod_unit_l 
          Qp.prod_unit_r Units_eq_nonzero ac ac_ord_prop add_cancel_eint_geq assms(1) assms(3) 
          c c_eq1 c_val eint.inject i_def less_imp_of_nat_less not_less of_nat_0_less_iff
          units(2) val_nonzero val_nonzero_frac val_ord)        
  qed
  have c_closed: "c \<in> carrier Q\<^sub>p"
    by (simp add: assms(1) assms(2) c_def)
  have \<gamma>_closed: "\<gamma> \<in> carrier Q\<^sub>p"
    using assms by auto 
  have d: "\<delta> = \<gamma> \<otimes> (\<one> \<oplus> c)"
  proof- 
    have 0: "\<one> \<oplus> c = (\<delta> \<div> \<gamma>)"
      using assms units unfolding c_def a_minus_def 
      by (metis Qp.Units_closed Qp.Units_inv_closed Qp.Units_minus_one_closed Qp.a_ac(2) 
                Qp.cring_simprules(19) Qp.cring_simprules(21) Qp.m_closed Qp.one_closed)
    show ?thesis unfolding 0 
      using c by auto
  qed
  have e: "N1 > 0"
    using N1_def by auto 
  show "pow_res n \<delta> = pow_res n \<gamma>" 
    by(intro equal_pow_res_criterion[of N1 _ _ _ c] n_pos assms N1_def(2) e
                \<gamma>_closed c_val c_closed d )
  thus "pow_res n \<gamma> = pow_res n \<delta>" 
    by auto 
qed

lemma N_def: "\<And> x t i. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
                              val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> 
                              val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint N"
proof- 
  have "\<And> x t i. val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint N0 \<le> 
                  val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint N"
  unfolding N using N0_def  by auto
  thus "\<And>x t i.
       t # x \<in> condition_to_set \<C> \<Longrightarrow>
       val (SA_poly_to_Qp_poly m x f \<bullet> t)
       \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint (int N) "
    using N0_def 
    by (meson eint_ord_trans)
qed

lemma N_pos: "N > 0"
  unfolding N using N1_def by linarith 

lemma N_fact0: "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
proof- 
  have "(\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  proof(rule, rule)
    fix u assume A: "u \<in> carrier Q\<^sub>p" " ac N u = 1 \<and> val u = 0 "
    have "ac N1 u = 1"
    proof(cases "N1 = N")
      case True
      then show ?thesis using A by auto 
    next
      case False
      then have F0: "N > N1"
        using N by auto 
      have F1: "ac N1 u = ac N u mod p^N1"
        apply(rule ac_mod, rule A, rule F0)
        using N1_def by auto 
      show ?thesis unfolding F1 using A 
        by (metis N1_def le_eq_less_or_eq mod_pos_pos_trivial order_trans_rules(22) p_residues rel_simps(44) residues.m_gt_one)
    qed
    thus "u \<in> P_set n"
      using N1_def A by auto 
  qed
  thus ?thesis using N N1_def by auto 
qed

lemma N_fact: "\<And>u. u \<in> carrier Q\<^sub>p \<Longrightarrow> ac N u = 1 \<Longrightarrow> val u = 0 \<Longrightarrow> u \<in> P_set n" 
  using N_fact0 by auto 

lemma \<C>_semialg: 
"is_semialgebraic (Suc m) (condition_to_set \<C>)"
  unfolding \<C>_def using arity.simps assms(1) assms(2) condition_to_set_is_semialg by blast

lemma taylor_term_nonzero:
  assumes "t#x \<in> condition_to_set \<C>"
  assumes "i \<in> inds"
  assumes nonzero: "t \<ominus> c x \<noteq> \<zero>"
  shows "a i x \<noteq> \<zero>"
        "(a i x)\<otimes>(t \<ominus> c x)[^]i \<noteq> \<zero>"
        "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) < \<infinity>"
        "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) = ord ((a i x)\<otimes>(t \<ominus> c x)[^]i)"
        "ord ((a i x)\<otimes>(t \<ominus> c x)[^]i) = ord (a i x) + i*ord(t \<ominus> c x)"
proof- 
  show "a i x \<noteq> \<zero>"
    using assms inds_memE some_closures by (meson SA_Units_memE')
  show 0: "(a i x)\<otimes>(t \<ominus> c x)[^]i \<noteq> \<zero>"
    using assms some_closures inds_memE 
    by (meson Qp.integral Qp.nat_pow_closed Qp.nonzero_pow_nonzero SA_Units_memE' nonzero)
  show "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) < \<infinity>"
    using 0 val_def by auto 
  show "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) = ord ((a i x)\<otimes>(t \<ominus> c x)[^]i)"
    using 0 val_def by auto 
  show "ord ((a i x)\<otimes>(t \<ominus> c x)[^]i) = ord (a i x) + i*ord(t \<ominus> c x)"
    using nonzero assms some_closures 0 Qp.integral_iff monom_term_ord by auto
qed

lemma taylor_term_zero:
  assumes "t#x \<in> condition_to_set \<C>"
  assumes "i \<notin> inds"
  shows "a i x = \<zero>"
        "(a i x)\<otimes>(t \<ominus> c x)[^]i = \<zero>"
        "val ((a i x)\<otimes>(t \<ominus> c x)[^]i) = \<infinity>"
  using assms
  by (auto simp: val_def inds_non_memE some_closures(2) some_closures(3))
 
definition i\<^sub>0 where i\<^sub>0_def: "i\<^sub>0 = (SOME i\<^sub>0. (\<forall>j. \<forall>t. \<forall>x. t#x \<in> condition_to_set \<C>
          \<longrightarrow> val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)))"

lemma i\<^sub>0_fact:   
  "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow>
                      val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
proof- 
  have 0: " \<forall>j t x.  t # x \<in> condition_to_set \<C> \<longrightarrow>
           val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) \<le> val (a j x \<otimes> (t \<ominus> c x) [^] j)"
    using i\<^sub>0_def min_taylor_term SomeE unfolding has_minimal_i_def by smt 
  show "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
                      val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
    using 0 by auto 
  obtain xs where xs_def: "xs \<in> condition_to_set \<C>"
    using nontrivial by blast
  obtain t x where tx_def: "xs = t#x"
    using xs_def obtain_coords by auto 
  obtain j where j_def: "j \<in> inds"
    using inds_nonempty by auto 
  have " val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
    using 0 xs_def unfolding tx_def by auto 
qed

lemma i\<^sub>0E':
  assumes "t#x \<in> condition_to_set \<C>"
  shows "val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i\<^sub>0 \<bullet> t)
                \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) j \<bullet> t)"
  using assms i\<^sub>0_fact(1)[of t x j] f_taylor_term[of t x] by presburger

lemma i\<^sub>0E:
  assumes "xs \<in> condition_to_set \<C>"
  shows "val (UPQ.taylor_term (c (tl xs)) (SA_poly_to_Qp_poly m (tl xs) f) i\<^sub>0 \<bullet> hd xs)
                \<le> val (UPQ.taylor_term (c (tl xs)) (SA_poly_to_Qp_poly m (tl xs) f) j \<bullet> hd xs)"
  using assms i\<^sub>0E'[of "hd xs" "tl xs" j] obtain_coords by presburger

definition A\<^sub>1 where A\<^sub>1_def: 
      "A\<^sub>1 = {xs \<in> condition_to_set \<C>. 
            (\<forall>j \<in> inds. j \<noteq> i\<^sub>0 \<longrightarrow> val (a i\<^sub>0 (tl xs) \<otimes> ((hd xs) \<ominus> c (tl xs))[^]i\<^sub>0) + N \<le>
                                   val (a j (tl xs) \<otimes> ((hd xs) \<ominus> c (tl xs))[^]j))}"
 
lemma A\<^sub>1_memE: "t#x \<in> A\<^sub>1 \<Longrightarrow>  j \<noteq> i\<^sub>0
             \<Longrightarrow> val ((a i\<^sub>0 x) \<otimes> (t \<ominus> c x)[^]i\<^sub>0) + N \<le> val (a j x \<otimes> (t \<ominus> c x)[^]j)"
  apply(cases "j \<in> inds")
  unfolding A\<^sub>1_def mem_Collect_eq list_hd list_tl apply blast 
  using inds_non_memE eint_ord_simps(3) local.val_zero taylor_term_zero(2) by presburger
 
lemma A\<^sub>1_closed: "A\<^sub>1 \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  unfolding A\<^sub>1_def condition_to_set.simps unfolding condition_to_set.simps \<C>_def cell_def by blast 

lemma A\<^sub>1_t_closed: "\<And> x t. t#x \<in> A\<^sub>1 \<Longrightarrow> t \<in> carrier Q\<^sub>p"
  using A\<^sub>1_closed Qp_pow_ConsE(2) list_hd   by (metis (no_types, opaque_lifting) UnCI Un_absorb2)

lemma A\<^sub>1_x_closed: "\<And> x t. t#x \<in> A\<^sub>1 \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  using A\<^sub>1_closed Qp_pow_ConsE  by (metis (no_types, lifting) list_tl subsetD)

lemma A\<^sub>1_x_closed': "\<And> x t. t#x \<in> A\<^sub>1 \<Longrightarrow> x \<in> A"
  unfolding A\<^sub>1_def unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl by blast 

lemma A\<^sub>1_semialg: "is_semialgebraic (Suc m) A\<^sub>1"
proof(cases "inds = {i\<^sub>0}")
  case True
  then have T0: "A\<^sub>1 = condition_to_set \<C>"
    unfolding A\<^sub>1_def by auto 
  then show ?thesis 
    by (simp add: \<C>_arity \<C>_cond condition_to_set_is_semialg)
next
  case False
  have 0: "\<And> xs j. xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow>
            monom_center_term m (a j) c j xs =  a j (tl xs) \<otimes> ((hd xs) \<ominus> c (tl xs))[^]j"
    by(intro monom_center_term_eval, auto simp: a_cfs_closed c_closed)
  have A\<^sub>1_alt: "A\<^sub>1 = {xs \<in> condition_to_set \<C>. 
            (\<forall>j \<in> inds. j \<noteq> i\<^sub>0 \<longrightarrow> val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + N \<le>
                                   val (monom_center_term m (a j) c j xs))}"
    unfolding A\<^sub>1_def apply(rule equalityI')
    unfolding mem_Collect_eq condition_to_set.simps \<C>_def cell_def 
    using 0  apply presburger using 0 by auto
  have A\<^sub>1_as_inter: "A\<^sub>1 = condition_to_set \<C> \<inter> 
          (\<Inter>j \<in> inds - {i\<^sub>0}. {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). 
                 
                       val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + N \<le> 
                                     val( monom_center_term m (a j) c j xs)})"
    apply(rule equalityI')
    using 0 i\<^sub>0_fact unfolding A\<^sub>1_alt unfolding \<C>_def condition_to_set.simps cell_def 
    by auto
  have 1: "\<And> i. is_semialgebraic (Suc m) {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
                   val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + int N
                   \<le> val (monom_center_term m (a i) c i xs)}"
  proof- 
    fix i 
    have 0: "{xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
                   val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + int N
                   \<le> val (monom_center_term m (a i) c i xs)} = 
            (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) - {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
                   val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + int N
                   \<ge> val (monom_center_term m (a i) c i xs)}) \<union> 
                {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
                    val (monom_center_term m (a i) c i xs)
                   = val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + int N}"
      by auto 
    show "is_semialgebraic (Suc m)
          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
           val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + eint (int N)
           \<le> val (monom_center_term m (a i) c i xs)}"
      unfolding 0 
      by(intro union_is_semialgebraic diff_is_semialgebraic carrier_is_semialgebraic
                  semialg_val_ineq_set_plus[of _ _ _ N] semialg_val_eq_set_plus[of _ _ _ N]
                  monom_center_term_closed c_closed a_closed cfs_closed, auto)
  qed
  show ?thesis 
  proof(cases "inds = {}")
    case True
    then show ?thesis using \<C>_semialg unfolding A\<^sub>1_def True  by auto 
  next
    case F: False
    show ?thesis 
      unfolding A\<^sub>1_as_inter 
      apply(intro intersection_is_semialg finite_intersection_is_semialg \<C>_semialg)
      using is_semialgebraic_def 1 inds_finite F False by auto 
  qed 
qed

lemma A\<^sub>1_subset: "A\<^sub>1 \<subseteq> condition_to_set \<C>"
  unfolding A\<^sub>1_def by blast 

lemma cx_closed: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "c x \<in> carrier Q\<^sub>p"
  by(rule SA_car_closed[of _ m], rule c_closed, rule assms)

definition near_equal_set where 
"near_equal_set (j::nat) (k::nat) = 
      {xs \<in> condition_to_set \<C>.
          val ((a i\<^sub>0 (tl xs))\<otimes>((hd xs \<ominus> c (tl xs)))[^]i\<^sub>0) + k = 
              val ((a j (tl xs)) \<otimes> ((hd xs \<ominus> c (tl xs))[^]j)) }"

lemma near_equal_set_semialg:
"is_semialgebraic (Suc m) (near_equal_set i k)"
proof-
  have 0: "\<And> xs j. xs \<in> condition_to_set \<C> \<Longrightarrow>
            monom_center_term m (a j) c j xs =  a j (tl xs) \<otimes> ((hd xs) \<ominus> c (tl xs))[^]j"
    unfolding \<C>_def condition_to_set.simps cell_def
    by(intro monom_center_term_eval, auto simp: a_cfs_closed c_closed)
  have 1: "\<And> i. is_semialgebraic (Suc m) {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
                   val (monom_center_term m (a i) c i xs) = 
                  val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + int k}"
    by(intro semialg_val_eq_set_plus monom_center_term_closed a_closed 
                cfs_closed[of a m] c_closed, auto)
  have 2: "near_equal_set i k = condition_to_set \<C> \<inter> {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
                   val (monom_center_term m (a i) c i xs) = 
                  val (monom_center_term m (a i\<^sub>0) c i\<^sub>0 xs) + int k}"
    apply(rule equalityI')
    using 0[of _ i\<^sub>0] 0[of _ i] 
     near_equal_set_def mem_Collect_eq \<C>_def condition_to_set.simps cell_def
    by auto 
  show ?thesis 
    unfolding 2
    by(intro intersection_is_semialg \<C>_semialg 1)
qed

lemma i\<^sub>0_inds_dichotomy:
  assumes "i\<^sub>0 \<notin> inds"
  shows "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
         (a j x)\<otimes>((t \<ominus> c x))[^]j = \<zero>"
proof- 
  have 0: "a i\<^sub>0 =  \<zero>\<^bsub>SA m\<^esub>"
    using assms a_def f_taylor_cfs inds_def by auto
  have "\<And> t x. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
         (a i\<^sub>0 x)\<otimes>((t \<ominus> c x))[^]i\<^sub>0 = \<zero>"
    unfolding 0
    unfolding  \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
    by (metis Qp.integral_iff Qp.minus_closed Qp.nat_pow_closed Qp.zero_closed SA_zeroE 
        cartesian_power_head cartesian_power_tail cx_closed list.sel(1) list.sel(3))
  thus "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
         (a j x)\<otimes>((t \<ominus> c x))[^]j = \<zero>"
    using i\<^sub>0_fact val_def 
    by (metis (no_types, lifting) UPQ.monom_term_car a_eval 
              some_closures(2) some_closures(3) val_ineq)
qed

lemma A\<^sub>1_comp_nonzero: 
  assumes "t#x \<in> condition_to_set \<C>"
  assumes "0 \<noteq> i\<^sub>0"
  assumes "t \<ominus> c x = \<zero>"
  shows "t#x \<in> A\<^sub>1"
proof- 
  have 0: "val (a i\<^sub>0 x \<otimes> \<zero> [^] i\<^sub>0) \<le> val (a 0 x \<otimes> \<zero> [^] (0::nat))"
    using assms i\<^sub>0_fact[of t x 0] unfolding assms by auto 
  have 1: "(0::nat) \<notin> inds"
  proof(rule ccontr)
    assume not: "\<not> 0 \<notin> inds"
    have 10: "a 0 x \<otimes> \<zero> [^] (0::nat) = a 0 x"
      using assms some_closures(4)[of t x 0]  by auto      
    have 11: "a i\<^sub>0 x \<otimes> \<zero> [^] i\<^sub>0 = \<zero>"
      using not assms 
      by (simp add: Qp.nat_pow_zero some_closures(4))
    show False 
      using 0 11 10 inds_memE 
      by (metis SA_Units_memE' assms(1) not some_closures(2) some_closures(4) val_ineq)
  qed   
  have closed: "a i\<^sub>0 x \<in> carrier Q\<^sub>p"
               "\<And>j. a j x \<in> carrier Q\<^sub>p"
    using some_closures assms by auto
  have 2: "\<And> j. j \<in> inds \<Longrightarrow> val ((a i\<^sub>0 x) \<otimes> (t \<ominus> c x)[^]i\<^sub>0) + N \<le> val (a j x \<otimes> (t \<ominus> c x)[^]j)"
  proof-
    fix j::nat assume a: "j \<in> inds"
    have j_pos: "j \<noteq> (0::nat)"
      using 1 a by smt 
    have 20: "val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) \<le> val (a j x \<otimes> (t \<ominus> c x) [^] j)"
      using assms i\<^sub>0_fact[of t x j]  by auto 
    have 21: "a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0 = \<zero>"
      unfolding assms using closed assms(2) 
      by (simp add: Qp.nat_pow_zero)
    have 22: "a j x \<otimes> (t \<ominus> c x) [^] j = \<zero>"
      unfolding assms using closed(2) j_pos 
      by (simp add: Qp.nat_pow_zero)
    thus "val ((a i\<^sub>0 x) \<otimes> (t \<ominus> c x)[^]i\<^sub>0) + N \<le> val (a j x \<otimes> (t \<ominus> c x)[^]j)"
      unfolding 21 22 val_zero by auto 
  qed
  show 3: "t#x \<in> A\<^sub>1"
    using assms 2 unfolding A\<^sub>1_def by auto 
qed

lemma near_equal_set_Unit_eq: 
  assumes "i\<^sub>0 \<in> inds"
  assumes "i \<in> inds"
  assumes "i\<^sub>0 \<noteq> i"
  shows "\<And> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<Longrightarrow> t \<ominus> c x \<in> nonzero Q\<^sub>p"
        "\<exists> \<phi> \<in> Units (SA m). \<forall> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<phi> x)"
proof-
  obtain \<eta> where \<eta>_def: "\<eta> = \<pp>[^](-k) \<odot>\<^bsub>SA m\<^esub> (a i \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a i\<^sub>0)"
    by blast 
  have units: "a i \<in> Units (SA m)" "a i\<^sub>0 \<in> Units (SA m)"
    using assms inds_memE by auto 
  have \<eta>_closed: "\<eta> \<in> carrier (SA m)"
    unfolding \<eta>_def apply(rule SA_smult_closed, rule R.m_closed)
    using units p_intpow_closed(1) by auto
  have \<eta>_Unit: "\<eta> \<in> Units (SA m)"
    unfolding \<eta>_def 
    apply(intro SA_Units_smult)
    using units Units_eq_nonzero p_intpow_closed(2) 
    by auto
  have val_fact: "\<And> t x. t#x \<in> near_equal_set i k \<Longrightarrow> 
            val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) + eint (int k) = val (a i x \<otimes> (t \<ominus> c x) [^] i)"
    unfolding near_equal_set_def by auto 
  obtain \<alpha> where \<alpha>_def: "\<alpha> = \<pp>[^](int k) \<odot>\<^bsub>SA m\<^esub> (a i\<^sub>0 \<otimes>\<^bsub>SA m\<^esub> inv \<^bsub>SA m\<^esub> a i)"
     by blast 
  have \<alpha>_Units: "\<alpha> \<in> Units (SA m)"
     unfolding \<alpha>_def
     using SA_Units_smult Qp.Units_int_pow_closed Units_eq_nonzero 
           a_quotient_unit assms(1) assms(2) p_nonzero by auto
  have facts: "\<And> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<Longrightarrow> ord (\<alpha> x) = (int i - int i\<^sub>0)*ord(t \<ominus> c x)"
       "\<And> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<Longrightarrow> t \<ominus> c x \<in> nonzero Q\<^sub>p"
  proof- fix x t assume A: "t#x \<in> near_equal_set i k - A\<^sub>1"
    have  tx_def: "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"                               
      using A near_equal_set_def some_closures Qp_pow_Suc_decomp
            Set.basic_monos(7) is_semialgebraic_closed near_equal_set_semialg by auto 
    have val: "val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) + eint (int k) = val (a i x \<otimes> (t \<ominus> c x) [^] i)"
      using val_fact A tx_def by auto 
    have closed: "a i x \<in> Units Q\<^sub>p" "a i\<^sub>0 x \<in> Units Q\<^sub>p" "t \<ominus> c x \<in> carrier Q\<^sub>p"
      unfolding Units_eq_nonzero 
      using tx_def c_closed SA_car_closed nonzero_memI a_eval assms tx_def SA_car_closed  
            SA_Units_nonzero units 
      by auto 
    have \<alpha>_eval: "\<alpha> x = \<pp>[^](int k) \<otimes> a i\<^sub>0 x \<otimes> inv a i x"
      unfolding \<alpha>_def using inds_memE assms closed 
      by (simp add: Qp.Units_closed Qp.m_assoc SA_div_eval SA_smult_formula
          a_cfs_closed p_intpow_closed(1) tx_def)
    have "ord (\<alpha> x) = (int i - int i\<^sub>0)*ord(t \<ominus> c x) \<and> t \<ominus> c x \<in> nonzero Q\<^sub>p"
    proof(cases "i\<^sub>0 = 0")
      case True
      have a1: "(a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) = a 0 x"
        using  tx_def unfolding True 
        by (simp add: a_eval)
      have a2: "t \<ominus> c x \<in> carrier Q\<^sub>p"
        using tx_def c_closed SA_car_closed by auto 
      have nonzero: "t \<ominus> c x \<noteq> \<zero>"
        using closed(3) a2 assms unfolding True a1 
        by (metis Qp.Units_closed Qp.integral_iff Qp.nat_pow_zero Qp.nonzero_memE(2) True
            Units_eq_nonzero a1 closed(1) closed(2) plus_eint_simps(1) val val_nonzero' val_ord)
      have nz: "t \<ominus> c x \<in> nonzero Q\<^sub>p"
        using a2 nonzero unfolding nonzero_def by auto 
      have \<alpha>_ord: "ord (\<alpha> x) = int k  + ord (a i\<^sub>0 x) - ord (a i x)"
        unfolding \<alpha>_eval 
        using closed Qp.Units_m_closed Units_eq_nonzero ord_fract ord_mult 
              ord_p_int_pow p_intpow_closed(2) by auto
      have a3: "ord (a i\<^sub>0 x) + k = ord (a i x \<otimes> (t \<ominus> c x) [^] i)"
        using val closed(3) val_ord a2 nonzero closed unfolding a1 True  
        by (metis Qp.Units_m_closed Qp.Units_pow_closed Qp.not_nonzero_memE True 
            Units_eq_nonzero a1 eint.simps(1) plus_eint_simps(1))
      have a4: "ord (a i\<^sub>0 x) + k = ord (a i x) + i*ord (t \<ominus> c x)"
        unfolding a3 using closed nonzero a2 
        by (meson Qp.not_nonzero_memE Units_nonzero_Qp monom_term_ord')
      show " ord (\<alpha> x) = (int i - int i\<^sub>0)* ord (t \<ominus> c x) \<and> t \<ominus> c x \<in> nonzero Q\<^sub>p"
        using a4 nz unfolding True \<alpha>_ord by auto 
    next
      case False
      have F0: "t \<ominus> c x \<noteq> \<zero>"
        using A False A\<^sub>1_comp_nonzero near_equal_set_def by auto         
      have x: "t \<ominus> c x \<in> nonzero Q\<^sub>p"
        using F0 closed unfolding nonzero_def by auto 
      have \<alpha>_ord: "ord (\<alpha> x) = int k  + ord (a i\<^sub>0 x) - ord (a i x)"
        unfolding \<alpha>_eval 
        using closed Qp.Units_m_closed Units_eq_nonzero ord_fract ord_mult 
              ord_p_int_pow p_intpow_closed(2) by auto
      have a3: "ord (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) + k = ord (a i x \<otimes> (t \<ominus> c x) [^] i)"
        using val_ord closed x val Qp.Units_m_closed Qp.Units_pow_closed Qp.not_nonzero_memE  
              Units_eq_nonzero  eint.simps(1) plus_eint_simps(1)
        by auto
      have a4: "ord (a i\<^sub>0 x) + i\<^sub>0*ord(t \<ominus> c x) +  k = ord (a i x) + i*ord (t \<ominus> c x)"
        unfolding a3 
        using closed Units_eq_nonzero x a3 monom_term_ord' by auto
      show "ord (\<alpha> x) = (int i - int i\<^sub>0) * ord (t \<ominus> c x) \<and> t \<ominus> c x \<in> nonzero Q\<^sub>p"
        using a4 unfolding \<alpha>_ord by (simp add: left_diff_distrib' x)
    qed                    
    thus "ord (\<alpha> x) = (int i - int i\<^sub>0) * ord (t \<ominus> c x)"
         "t \<ominus> c x \<in> nonzero Q\<^sub>p"
      by auto 
  qed
  thus "\<And> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<Longrightarrow> t \<ominus> c x \<in> nonzero Q\<^sub>p"
    by auto 
  have bounds: "i \<le> Suc d" "i\<^sub>0 \<le> Suc d"
    using assms inds_bounded' by auto 
  show "\<exists>\<phi>\<in>Units (SA m). \<forall>t x. t # x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<phi> x)"
  proof(cases "i\<^sub>0 < i")
    case True
    obtain \<eta> where \<eta>_def: "\<eta> \<in> Units (SA m)" 
                          "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). int (i - i\<^sub>0) * ord (\<eta> x) + ord (\<alpha> x) mod int (i - i\<^sub>0) = ord (\<alpha> x)"
      using denef_lemma_2_4_floor[of d "i - i\<^sub>0" \<alpha> m] \<alpha>_Units assms True bounds 
      by (smt (verit, del_insts) One_nat_def Suc_leI denef_II_axioms diff_le_self le_trans zero_less_diff)
    have 0: "\<forall>t x. t # x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<eta> x)"
    proof(intro allI impI)
      fix t x assume a: "t#x \<in> near_equal_set i k - A\<^sub>1"
      have tx_closed: "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using a near_equal_set_def some_closures by auto 
      have 0: "t \<ominus> c x \<in> nonzero Q\<^sub>p" "ord (\<alpha> x) = (int i - int i\<^sub>0)*ord(t \<ominus> c x)"
        using a facts by auto 
      have 1: " int (i - i\<^sub>0) * ord (\<eta> x) + ord (\<alpha> x) mod int (i - i\<^sub>0) = ord (\<alpha> x)"
        using a \<eta>_def tx_closed by auto 
      have 2: " int (i - i\<^sub>0) * ord (\<eta> x) =  int (i - i\<^sub>0) * ord (t \<ominus> c x)"
        using 0 1 True 
        by (simp add: of_nat_diff)
      hence 3:  " ord (\<eta> x) =  ord (t \<ominus> c x)"
        using assms True  by simp
      thus "val (t \<ominus> c x) = val (\<eta> x)"
        using 0 val_ord tx_closed \<eta>_def 
        by (simp add: SA_Units_memE' val_def)
    qed
    then show ?thesis using \<eta>_def by auto 
  next
    case False
    obtain \<alpha>' where \<alpha>'_def: "\<alpha>' = inv \<^bsub>SA m\<^esub> \<alpha> "
      by blast 
    have \<alpha>'_Units: "\<alpha>' \<in> Units (SA m)"
      using \<alpha>_Units \<alpha>'_def by auto 
    have bigger: "i\<^sub>0 > i"
      using False assms by auto 
    obtain \<eta> where \<eta>_def: "\<eta> \<in> Units (SA m)" 
                          "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). int (i\<^sub>0 - i) * ord (\<eta> x) + ord (\<alpha>' x) mod int (i\<^sub>0 - i) = ord (\<alpha>' x)"
      using denef_lemma_2_4_floor[of d "i\<^sub>0 - i" \<alpha>' m] \<alpha>'_Units assms False bounds bigger
      by (smt (verit, del_insts) One_nat_def Suc_leI denef_II_axioms diff_le_self le_trans zero_less_diff)
    have 0: "\<forall>t x. t # x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<eta> x)"
    proof(intro allI impI)
      fix t x assume a: "t#x \<in> near_equal_set i k - A\<^sub>1"
      have tx_closed: "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using a near_equal_set_def some_closures by auto
      have 0: "t \<ominus> c x \<in> nonzero Q\<^sub>p" "ord (\<alpha> x) = (int i - int i\<^sub>0)*ord(t \<ominus> c x)"
        using a facts by auto 
      have 1: "ord (\<alpha>' x) = - ord (\<alpha> x)"
        using ord_of_inv tx_closed unfolding \<alpha>'_def 
        using SA_Units_closed_fun SA_Units_memE' SA_inv_eval \<alpha>_Units by auto
      have 2: " int (i\<^sub>0 - i) * ord (\<eta> x) + ord (\<alpha>' x) mod int (i\<^sub>0 - i) = ord (\<alpha>' x)"
        using a \<eta>_def tx_closed by auto 
      have 3:  "ord (\<alpha>' x) = (int i\<^sub>0 - int i)*ord(t \<ominus> c x)"
        unfolding 1 0 using bigger 
        by (simp add: minus_mult_left)
      have mod: " ord (\<alpha>' x) mod int (i\<^sub>0 - i) = 0"
        unfolding 3 using bigger by (simp add: of_nat_diff)
      have 4: " int (i\<^sub>0 - i) * ord (\<eta> x) =  int (i\<^sub>0 - i) * ord (t \<ominus> c x)"
        using 2 bigger unfolding mod unfolding 3 by auto 
      hence 4:  "ord (\<eta> x) =  ord (t \<ominus> c x)"
        using assms bigger by simp 
      thus "val (t \<ominus> c x) = val (\<eta> x)"
        using 0 val_ord tx_closed \<eta>_def        
        by (simp add: SA_Units_memE' val_def)
    qed
    then show ?thesis using \<eta>_def by auto 
  qed
qed

lemma near_equal_set_Unit_eq_edge_case: 
  assumes "i\<^sub>0 \<notin> inds \<or> inds = {i\<^sub>0}"
  shows "\<exists> u h k. SA_poly_factors p m n f (center \<C>) (condition_to_set \<C>) u h k"
proof(cases "i\<^sub>0 \<notin> inds")
  case True
  then have a: "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
         (a j x)\<otimes>((t \<ominus> c x))[^]j = \<zero>"
    by (simp add: i\<^sub>0_inds_dichotomy)
  have b: "\<And> t x. t#x \<in> condition_to_set \<C> \<Longrightarrow> t \<in> carrier Q\<^sub>p"
       "\<And> t x. t#x \<in> condition_to_set \<C> \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using some_closures(1) some_closures(2) by auto
  have 0: "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_Qp_poly m x f \<bullet> t = \<zero>"
  proof-
    have 1: "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_SA_fun m f (t # x) = (\<Oplus>i\<in>inds. a i x \<otimes> (t \<ominus> c x) [^] i)"
      using a b f_eval_formula by auto 
    have 2: "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_SA_fun m f (t # x) = (\<Oplus> i \<in> inds. \<zero>)"
      by(unfold 1, rule Qp.add.finprod_cong', auto simp: a)
    have 3: "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_Qp_poly m x f \<bullet> t = (\<Oplus> i \<in> inds. \<zero>)"
      using 2 SA_poly_to_SA_fun_formula f_closed b by auto 
    show "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_Qp_poly m x f \<bullet> t = \<zero>" 
      unfolding 3 by(intro  Qp.finsum_zero)
  qed
  have 1: "SA_poly_factors p m n f (center \<C>) (condition_to_set \<C>) \<one>\<^bsub>SA (Suc m)\<^esub> \<zero>\<^bsub>SA m\<^esub> 0"
    apply(rule SA_poly_factorsI)
        apply (simp add: \<C>_semialg is_semialgebraic_closed)
    using SA_car semialg_functions_memE(3) apply blast
    using \<C>_def center.simps c_closed apply auto[1]
     apply auto[1]
    unfolding 0 
    using Qp.cring_simprules(26) Qp.cring_simprules(27) Qp.nat_pow_0 Qp.nat_pow_closed 
      Qp.one_closed Qp_pow_ConsI SA_oneE SA_zero local.function_zero_eval val_one by presburger
  thus "\<exists>u h k. SA_poly_factors p m n f (center \<C>) (condition_to_set \<C>) u h k"
    by auto 
next
  case False 
  have inds: "inds = {i\<^sub>0}"
    using assms False by auto 
  have b: "\<And> t x. t#x \<in> condition_to_set \<C> \<Longrightarrow> t \<in> carrier Q\<^sub>p"
       "\<And> t x. t#x \<in> condition_to_set \<C> \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using some_closures(1) some_closures(2) by auto
  then have a: "\<And> t x j. j \<noteq> i\<^sub>0 \<Longrightarrow> t#x \<in> condition_to_set \<C> \<Longrightarrow> 
         (a j x)\<otimes>((t \<ominus> c x))[^]j = \<zero>"
    using False assms taylor_term_zero  by auto
  have 0: "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_Qp_poly m x f \<bullet> t = a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0"
  proof-
    have 1: "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_SA_fun m f (t # x) = (\<Oplus>i\<in>inds. a i x \<otimes> (t \<ominus> c x) [^] i)"
      using a b f_eval_formula by auto 
    have 2: "\<And> t x j. t#x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_Qp_poly m x f \<bullet> t = (\<Oplus>i\<in>inds. a i x \<otimes> (t \<ominus> c x) [^] i)"
      using 1 SA_poly_to_SA_fun_formula f_closed b by auto 
    show "\<And>t x j. t # x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_Qp_poly m x f \<bullet> t = a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0" 
      unfolding 2 inds apply(rule Qp.finsum_singleton, simp)
      by (simp add: a_eval b(2) cx_closed some_closures(1))
  qed
  have 1: "SA_poly_factors p m n f (center \<C>) (condition_to_set \<C>) \<one>\<^bsub>SA (Suc m)\<^esub> (a i\<^sub>0) i\<^sub>0"
   apply(rule SA_poly_factorsI, unfold 0)
        apply (simp add: \<C>_semialg is_semialgebraic_closed)
    using SA_car semialg_functions_memE(3) apply blast
    using \<C>_def center.simps c_closed apply auto[1]
     apply (metis a_cfs_closed)
    unfolding \<C>_def center.simps 
    using Qp.l_one Qp.nat_pow_one Qp_pow_ConsI SA_oneE a_eval val_one by presburger 
  thus ?thesis by auto
qed

definition Ls where Ls_def: "Ls = (inds - {i\<^sub>0}) \<times> {..< N}"

lemma Ls_finite: "finite Ls" 
  using Ls_def inds_finite by auto 

lemma fibre_sets_for_cover_are_semialg1:
  assumes "\<phi> \<in> Units (SA m)"
  assumes "C1 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<phi> x) \<in> I (val (a1 x)) (val (a2 x))}"
  shows "is_semialgebraic m C1"
    unfolding assms 
    using cell_cond_semialg assms I_convex SA_Units_closed a1_closed a2_closed by presburger

lemma fibre_sets_for_cover_are_semialg2:
  assumes "\<phi> \<in> Units (SA m)"
  assumes "\<psi> \<in> Units (SA m)"
  assumes "\<rho> \<in> Units (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). int i * ord (\<phi> x) - int j* ord (\<phi> x) = 
                                      ord(\<psi> x) - ord (\<rho> x)  - int (k::nat) }"
proof- 
  obtain C0 where C0_def: "C0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). int i * ord (\<phi> x) - int j* ord (\<phi> x) = 
                                      ord(\<psi> x) - ord (\<rho> x)  - int (k::nat) }"
    by auto 
  obtain \<gamma> where \<gamma>_def: "\<gamma> = \<phi>[^]\<^bsub>SA m\<^esub>(int i - int j) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> \<psi> \<otimes>\<^bsub>SA m\<^esub> \<rho>"
    by blast
  have \<gamma>_Units: "\<gamma> \<in> Units (SA m)"
    unfolding \<gamma>_def 
    using assms R.Units_inverse R.Units_m_closed R.int_pow_unit_closed by presburger
  have \<gamma>_eval: "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<gamma> x = \<phi> x[^](int i - int j) \<otimes> inv \<psi> x \<otimes> \<rho> x"
    using assms unfolding \<gamma>_def 
    using SA_inv_eval SA_mult SA_unit_int_pow by presburger
  have \<gamma>_ord: "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (\<gamma> x) = int i * ord (\<phi> x) - int j* ord (\<phi> x) - ord (\<psi> x) + ord (\<rho> x)"
    unfolding \<gamma>_eval using assms 
    by (smt (verit, ccfv_SIG) Qp.Units_m_closed Qp_int_pow_nonzero SA_Units_nonzero Units_eq_nonzero 
            int_pow_ord left_diff_distrib' nonzero_inverse_Qp ord_fract ord_mult)
  have 0: "C0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<gamma> x) = -int k}"
  proof- 
    have a: "\<And> x. x \<in> C0 \<Longrightarrow> ord (\<gamma> x) = int i * ord (\<phi> x) - int j* ord (\<phi> x) - ord (\<psi> x) + ord (\<rho> x)"
            "\<And> x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> ord (\<gamma> x) = - int k \<Longrightarrow> 
              ord (\<gamma> x) = int i * ord (\<phi> x) - int j* ord (\<phi> x) - ord (\<psi> x)+ ord (\<rho> x)"
      using \<gamma>_ord assms C0_def by auto 
    have b: "\<And>x. x \<in> C0 \<Longrightarrow> x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<gamma> x) = - int k}"
      unfolding mem_Collect_eq a  unfolding C0_def assms by auto 
    have c: "\<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<gamma> x) = - int k} \<Longrightarrow>  x \<in> C0 "
      unfolding assms mem_Collect_eq using a C0_def by force
    show ?thesis by(intro equalityI' b, simp, intro c, simp)
  qed
  have 1: "C0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<gamma> x) = -int k}"
    unfolding 0 
    using \<gamma>_Units SA_Units_closed_fun SA_Units_memE' val_ord' by fastforce
  show ?thesis
    using 1 C0_def semialg_val_eq_set_is_semialg'
    using \<gamma>_Units by auto 
qed

lemma near_equal_cover:
  assumes "t#x \<in> condition_to_set \<C> - A\<^sub>1"
  shows "\<exists> i \<in> inds - {i\<^sub>0}. \<exists> k \<in> {..< N}. t#x \<in> near_equal_set i k"
proof- 
  have 0: "\<exists> i \<in> inds - {i\<^sub>0}. 
        val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) + N > val (a i x \<otimes> (t \<ominus> c x) [^] i)"
    using assms unfolding A\<^sub>1_def Diff_iff mem_Collect_eq list_tl  list_hd 
    by (metis Diff_iff eint_ord_simps(3) notin_closed singleton_mem)
  then obtain i where i_def: "i \<in> inds - {i\<^sub>0}" 
                             "val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) + N > val (a i x \<otimes> (t \<ominus> c x) [^] i)"
    by auto 
  have 1: "val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) \<le> val (a i x \<otimes> (t \<ominus> c x) [^] i)"
    using i\<^sub>0_fact assms by auto
  have closures: "a i\<^sub>0 x \<in> carrier Q\<^sub>p" "\<And> j::nat. (t \<ominus> c x)[^]j \<in> carrier Q\<^sub>p" "a i x \<in> nonzero Q\<^sub>p"
                 "a i x \<otimes> (t \<ominus> c x) [^] i \<in> carrier Q\<^sub>p" "a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0 \<in> carrier Q\<^sub>p"
    using  val_zero assms inds_memE some_closures DiffE i_def unfolding nonzero_def by auto 
  have 2: " \<exists> k \<in> {..< N}. t#x \<in> near_equal_set i k"
  proof(cases "t \<ominus> c x = \<zero>")
    case True
    have 0: "i \<noteq> 0"
    proof(rule ccontr)
      assume "\<not> i \<noteq> 0" then have not: "i = 0" by auto
      then have a: "a i x \<otimes> (t \<ominus> c x) [^] i \<noteq> \<zero>"
        using i_def closures unfolding not 
        by (simp add: Qp.Units_closed Qp.nonzero_memE(2) Units_eq_nonzero)
      have b: "a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0 = \<zero>"
        using i_def closures unfolding True  
        using Qp.nat_pow_zero \<open>\<not> i \<noteq> 0\<close> by auto
      thus False using 1 a unfolding b val_zero 
        by (simp add: closures(4) val_ineq)
    qed
    have 1: "a i x \<otimes> (t \<ominus> c x) [^] i = \<zero>"
      unfolding True  
      using closures 0 Qp.cring_simprules(27) Qp.nat_pow_zero Qp.nonzero_memE(1) by presburger
    have 2: "val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) = \<infinity>"
      using i_def unfolding 1 val_zero 
      using eint_ord_simps(6) by blast
    have 3: "val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) = val (a i x \<otimes> (t \<ominus> c x) [^] i)"
      unfolding 1 2 val_zero by auto 
    have "t#x \<in> near_equal_set i 0"
      unfolding near_equal_set_def mem_Collect_eq list_tl list_hd 3 
      using "1" i_def(2) local.val_zero by auto
    then show ?thesis using i_def 
      by (simp add: "1" local.val_zero)
  next
    case False
    have F0: "a i x \<otimes> (t \<ominus> c x) [^] i \<in> nonzero Q\<^sub>p"
      using closures False by (meson i_def(2) val_nonzero)
    have F1:  "a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0 \<in> nonzero Q\<^sub>p"
      using F0 1 val_ord 
      by (metis closures(4) closures(5) not_nonzero_Qp val_ineq)
    have 0: "ord (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) \<le> ord (a i x \<otimes> (t \<ominus> c x) [^] i)"
            "ord (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) + N > ord (a i x \<otimes> (t \<ominus> c x) [^] i)"
      using val_ord F0 F1 1 i_def  by auto
    obtain k0 where k0_def: "k0 = ord (a i x \<otimes> (t \<ominus> c x) [^] i) -  ord (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0)"
      by auto 
    have k0_bounds: "0 \<le> k0" "k0 < N"
      unfolding k0_def using 0 by auto
    obtain k where k_def: "k = nat k0"
      by blast 
    have "t#x \<in> near_equal_set i k"
      unfolding near_equal_set_def 
      using F0 F1 assms k0_bounds k0_def k_def by force
    thus ?thesis using k0_bounds k_def i_def by auto 
  qed
  thus ?thesis using i_def by auto 
qed

lemma A\<^sub>1_comp_decomp:
  assumes "i\<^sub>0 \<in> inds"
  assumes "inds \<noteq> {i\<^sub>0}"
  shows "\<exists>S. is_cell_decomp m S (condition_to_set \<C> - A\<^sub>1)\<and>
                                     (\<forall>\<C> \<in> S. center \<C> = c \<and> boundary_condition \<C> = closed_interval \<and>
                                         (\<exists>\<phi> \<in> Units (SA m). u_bound \<C> = \<phi> \<and> l_bound \<C> = \<phi>))"
proof- 
  have Ls_nonempty: "Ls \<noteq> {}"
      unfolding Ls_def using assms N_pos by auto  
  have 0: "\<And> t x i k. \<lbrakk>i \<in> inds - {i\<^sub>0}; t#x \<in> near_equal_set i k - A\<^sub>1\<rbrakk> \<Longrightarrow> t \<ominus> c x \<in> nonzero Q\<^sub>p"
       "\<And> t x i k. \<lbrakk>i \<in> inds - {i\<^sub>0}; t#x \<in> near_equal_set i k - A\<^sub>1\<rbrakk> \<Longrightarrow> 
            \<exists> \<phi> \<in> Units (SA m). \<forall> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<phi> x)"
    using assms near_equal_set_Unit_eq by auto 
  obtain \<phi> where \<phi>_def: "\<phi> = (\<lambda> (i,k). 
       (SOME \<phi> . \<phi> \<in> Units (SA m) \<and>
                 (\<forall> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<phi> x))))"
    by blast 
  have hE: "\<And> i k. i \<in> inds - {i\<^sub>0} \<Longrightarrow> 
                \<phi> (i,k) \<in> Units (SA m) \<and>
                 (\<forall> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<phi> (i,k) x))"    
  proof- 
    have 0: "\<And> i k. i \<in> inds - {i\<^sub>0} \<Longrightarrow> 
                (\<exists> \<phi> \<in> Units (SA m).
                 \<forall> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<phi> x))" 
      using \<phi>_def near_equal_set_Unit_eq assms(1) by blast
    have 1: "\<And> i k P. (\<exists>y. P y) \<Longrightarrow> (\<phi> (i,k) = (SOME x. P x)) \<Longrightarrow> P (\<phi> (i,k))"
      by (simp add: someI_ex)
    show "\<And> i k. i \<in> inds - {i\<^sub>0} \<Longrightarrow>
                \<phi> (i,k) \<in> Units (SA m) \<and>
                 (\<forall> t x. t#x \<in> near_equal_set i k - A\<^sub>1 \<longrightarrow> val (t \<ominus> c x) = val (\<phi> (i,k) x))"   
      apply(rule 1)
      unfolding \<phi>_def  apply auto 
      by (metis Diff_iff assms(1) near_equal_set_Unit_eq(2))
  qed
  obtain As0 where As0_def: "As0 = (\<lambda>q. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<phi> q x) \<in> I (val (a1 x)) (val (a2 x))})"
    by blast 
  obtain As1 where As1_def: "As1 = (\<lambda> q. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). int i\<^sub>0 * ord (\<phi> q x) - fst q* ord (\<phi> q x) = ord(a (fst q) x) - ord (a i\<^sub>0 x)  - int (snd q) })"
    by blast 
  have 1: "\<And> q. q \<in> Ls \<Longrightarrow> \<phi> q \<in> Units (SA m)"
    using hE unfolding Ls_def by auto 
  have As01_semialg: "\<And> q. q \<in> Ls \<Longrightarrow> is_semialgebraic m (As0 q)"
                    "\<And> q. q \<in> Ls \<Longrightarrow> is_semialgebraic m (As1 q)"
  proof- 
    fix q assume a: "q \<in> Ls"
    then obtain j k where defs: "q = (j,k)"
      using Ls_def by auto 
    show "is_semialgebraic m (As0 q)"
      unfolding As0_def 
      apply(intro fibre_sets_for_cover_are_semialg1[of "\<phi> q"])
      using a 1 by auto 
    show "is_semialgebraic m (As1 q)"
      unfolding As1_def defs apply simp     
      apply(intro fibre_sets_for_cover_are_semialg2[of ])
      using a 1 defs inds_memE assms unfolding Ls_def 
      by auto
  qed
  obtain As where As_def: "As = (\<lambda>q. A \<inter> As0 q \<inter> As1 q)"
    by blast 
  have As_semialg: "\<And> q. q \<in> Ls \<Longrightarrow> is_semialgebraic m (As q)"
    unfolding As_def apply(intro intersection_is_semialg As01_semialg A_semialg)
    by auto 
  have 2: "\<And> xs. xs \<in> condition_to_set \<C> - A\<^sub>1
             \<Longrightarrow> \<exists> q \<in> Ls. xs \<in> condition_to_set (Cond m (As q) c (\<phi> q) (\<phi> q) closed_interval)"
  proof- fix xs assume "xs \<in> condition_to_set \<C> - A\<^sub>1"
    then obtain t x where A: "xs = t#x" "t#x \<in> condition_to_set \<C> - A\<^sub>1" "t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      by (metis Diff_iff Qp_pow_ConsI cell_cond_head_closure cell_conditon_mem_decomp some_closures(2))
    obtain i k where defs: "i \<in> inds - {i\<^sub>0}" "k \<in> {..<N}" "t#x \<in> near_equal_set i k"
      using A near_equal_cover by smt 
    hence 0: "(i,k) \<in> Ls"
      unfolding Ls_def by simp 
    have 1: "val (t \<ominus> c x) = val (\<phi> (i,k) x)"
      using hE 0 defs A by auto 
    have 2: "val (a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0) + eint (int k) = val (a i x \<otimes> (t \<ominus> c x) [^] i)"
      using defs unfolding near_equal_set_def mem_Collect_eq list_tl list_hd by auto 
    have 3: "t \<ominus> c x \<in> nonzero Q\<^sub>p"
      using assms A defs near_equal_set_Unit_eq by auto 
    have closures: "a i x \<in> Units Q\<^sub>p" "a i\<^sub>0 x \<in> Units Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using defs(1) assms SA_Units_nonzero[of "a i" m] SA_Units_nonzero[of "a i\<^sub>0" m]
            some_closures A inds_memE 
      unfolding  Units_eq_nonzero  mem_Collect_eq
      by auto 
    have 4: "ord (a i\<^sub>0 x) + i\<^sub>0 * ord (t \<ominus> c x) + eint (int k) = ord (a i x) + i * ord (t \<ominus> c x) "
      using 2 closures 
      by (metis "3" A Diff_iff Qp.nonzero_memE(2) Units_eq_nonzero 
          inds_non_memE monom_term_ord' taylor_term_nonzero(4))
    have 5: "ord (t \<ominus> c x) = ord (\<phi>(i,k) x)"
      by (metis (no_types, lifting) 1 3 eint.simps(1) val_def val_infty_iff)
    hence 6: "x \<in> As (i,k)"
      using A 4 closures
      unfolding Diff_iff As_def As0_def As1_def Int_iff mem_Collect_eq 1 fst_conv snd_conv
                \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 5
      by auto 
    hence "x \<in> As  (i,k) \<and> val (t \<ominus> c x) = val (\<phi>  (i,k) x)"
      using 0 1 6 by auto 
    hence "xs \<in> condition_to_set (Cond m (As (i,k)) c (\<phi> (i,k)) (\<phi> (i,k)) closed_interval)"
      using A 
      unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd A closed_interval_def 
      by auto 
    thus " \<exists>q\<in>Ls. xs \<in> condition_to_set (Cond m (As q) c (\<phi> q) (\<phi> q) closed_interval)"
      using 0 by auto
  qed
  have 3: "\<And> xs q. q \<in> Ls \<Longrightarrow> xs \<in> condition_to_set (Cond m (As q) c (\<phi> q) (\<phi> q) closed_interval)
              \<Longrightarrow> xs \<in> condition_to_set \<C> - A\<^sub>1"
  proof- 
    fix q xs assume A: 
      "q \<in> Ls" "xs \<in> condition_to_set (Cond m (As q) c (\<phi> q) (\<phi> q) closed_interval)"
    obtain i k where defs: "q = (i,k)"
      using A Ls_def by auto 
    obtain t x 
      where tx: "xs = t#x" "t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A by (metis cartesian_power_tail cell_cond_mem_decomp 
          cell_hd_closed cell_memE(1) condition_to_set.simps)
    have unit: "\<phi> (i,k) \<in> Units (SA m)"
      using A unfolding defs Ls_def using "1" Ls_def by presburger
    have 0: "val (t \<ominus> c x) = val (\<phi> (i,k) x)"
      using A unfolding tx condition_to_set.simps cell_def
                mem_Collect_eq list_tl list_hd closed_interval_def defs
      by auto 
    have 1: "xs \<in> condition_to_set \<C>"
      using A tx unfolding tx condition_to_set.simps cell_def \<C>_def
                mem_Collect_eq list_tl list_hd closed_interval_def defs 0 As_def As0_def
      by auto 
    have 2: "t \<ominus> c x \<in> nonzero Q\<^sub>p" "a i\<^sub>0 x \<in> nonzero Q\<^sub>p" "a i x \<in> nonzero Q\<^sub>p"
      using assms inds_memE unit tx 0 A defs nonzero_def 
      apply (metis (mono_tags, opaque_lifting) Qp.not_eq_diff_nonzero Qp.r_right_minus_eq SA_Units_nonzero cx_closed val_infty_iff)
      using assms A defs SA_Units_nonzero inds_memE tx(4) unfolding defs Ls_def tx by auto 
    have 3: "int i\<^sub>0 * ord (\<phi> (i, k) x) - int i * ord (\<phi> (i, k) x) = 
             ord (a i x) - ord (a i\<^sub>0 x) - int k"
      using A 1
      unfolding tx near_equal_set_def unfolding  condition_to_set.simps cell_def \<C>_def
                mem_Collect_eq list_tl list_hd closed_interval_def defs 0 As_def As1_def Int_iff
      by auto 
    have 4: "int i\<^sub>0 * ord (t \<ominus> c x) - int i * ord (t \<ominus> c x) = 
             ord (a i x) - ord (a i\<^sub>0 x) - int k"
      by (metis (no_types, lifting) 0 2 3 eint.inject val_def val_infty_iff)
    have 5: "ord ((a i\<^sub>0 x) \<otimes> (t \<ominus> c x)[^] i\<^sub>0) + k = ord ((a i x) \<otimes> (t \<ominus> c x)[^] i)"
      using 4 2 monom_term_ord' by auto
    have 5: "ord ((a i\<^sub>0 x) \<otimes> (t \<ominus> c x)[^] i\<^sub>0) + N > ord ((a i x) \<otimes> (t \<ominus> c x)[^] i)"
      using 5 A unfolding defs Ls_def by auto  
    have 6: "val ((a i\<^sub>0 x) \<otimes> (t \<ominus> c x)[^] i\<^sub>0) + N > val ((a i x) \<otimes> (t \<ominus> c x)[^] i)"
      using 2 5 val_ord Qp.Units_m_closed Qp.nat_pow_nonzero Units_eq_nonzero by force
    have 7: "xs \<notin> A\<^sub>1"
      using 6 A unfolding defs Ls_def A\<^sub>1_def mem_Collect_eq tx list_tl list_hd 6 A defs 
      by auto 
    show " xs \<in> condition_to_set \<C> - A\<^sub>1"
      using 7 1 by auto 
  qed
  have 4: "condition_to_set \<C> - A\<^sub>1 = 
                (\<Union> q \<in> Ls. condition_to_set (Cond m (As q) c (\<phi> q) (\<phi> q) closed_interval))"
    using 2 3 by auto
  have 5: "(\<forall>l. l \<in> Ls \<longrightarrow> \<phi> l \<in> carrier (SA m))"
    using hE Ls_def  by auto 
  interpret one_val_point_decomp _ _ _ _ _ _ _ _ _ _ _ _ _ "condition_to_set \<C> - A\<^sub>1" Ls As \<phi>
    using common_refinement_locale_axioms Ls_finite Ls_nonempty 5 As_semialg 4
    unfolding one_val_point_decomp_def one_val_point_decomp_axioms_def Q\<^sub>p_def Z\<^sub>p_def \<iota>_def
    by auto 
  have 6: "\<phi> ` Ls \<subseteq> Units (SA m)"
    using 5 hE Ls_def by auto 
  show ?thesis using 6 decomp 
    by fastforce
qed

lemma A\<^sub>1_factor_by_unit: 
  assumes "i\<^sub>0 \<in> inds"
  assumes "t#x \<in> A\<^sub>1"
  shows "\<exists> u \<in> carrier Q\<^sub>p. 
            val u = 0 \<and> ac N1 u = 1 \<and> 
            SA_poly_to_Qp_poly m x f \<bullet> t = u \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0"
proof-
  have B: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p"  "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" 
          "t#x \<in> condition_to_set \<C>" "t#x \<in> A\<^sub>1"
    using assms  Qp_pow_ConsI  f_closed Qp_pow_ConsE[of "t#x" m]
                SA_poly_to_Qp_poly_closed UPQ.to_fun_closed 
    unfolding A\<^sub>1_def unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq
                              list_tl list_hd 
    by auto 
  have a0: "monom_center_term m (a i\<^sub>0) c i\<^sub>0 (t#x) = a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0"
    using B monom_center_term_eval[of "a i\<^sub>0" m c "t#x" i\<^sub>0] a_cfs_closed c_closed B
    unfolding list_tl list_hd by auto 
  have a1: "SA_poly_to_Qp_poly m x f \<bullet> t = (\<Oplus>i\<in>inds. a i x \<otimes> (t \<ominus> c x) [^] i)"
      using f_eval_formula[of x t] 
      by (simp add: B(1) B(2) SA_poly_to_SA_fun_formula f_closed) 
  obtain u where u_def: 
    "u = (if (monom_center_term m (a i\<^sub>0) c i\<^sub>0 (t#x) = \<zero>) then \<one>
              else SA_poly_to_SA_fun m f (t#x) \<otimes> 
                      inv  monom_center_term m (a i\<^sub>0) c i\<^sub>0 (t#x))"
    by blast 
  have a2: "monom_center_term m (a i\<^sub>0) c i\<^sub>0 (t#x) \<in> carrier Q\<^sub>p"
    by(intro SA_car_closed[of _ "Suc m"] monom_center_term_closed
                  a_cfs_closed c_closed B)
  have a3: "SA_poly_to_SA_fun m f (t#x) \<in> carrier Q\<^sub>p"
    by(intro SA_car_closed[of _ "Suc m"] SA_poly_to_SA_fun_is_SA f_closed B)
  have u_prop: "u \<in> carrier Q\<^sub>p"
  proof(cases "monom_center_term m (a i\<^sub>0) c i\<^sub>0 (t#x) = \<zero>")
    case True
    then show ?thesis unfolding u_def by auto 
  next
    case False
    have F0: "monom_center_term m (a i\<^sub>0) c i\<^sub>0 (t#x) \<in> Units Q\<^sub>p"
      using a2 False Qp.nonzero_memI Units_eq_nonzero by presburger
    show ?thesis 
      using False a3 B F0 unfolding u_def by auto 
  qed
  have a3: "SA_poly_to_Qp_poly m x f \<bullet> t \<in> carrier Q\<^sub>p"
    by (simp add: B(1) B(2) SA_poly_to_Qp_poly_closed UPQ.to_fun_closed f_closed)
  have a4: "SA_poly_to_Qp_poly m x f \<bullet> t = u \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0
          \<and> val u = 0
          \<and> ac N1 u = 1"
  proof(cases "monom_center_term m (a i\<^sub>0) c i\<^sub>0 (t#x) = \<zero>")
    case True 
    then have T0: "u = \<one>"
      using u_def B by auto 
    have T1: "a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0 = \<zero>"
      using True unfolding a0 by auto 
    have T2: "\<And> j. a j x \<otimes> (t \<ominus> c x) [^]j = \<zero>"
      using i\<^sub>0_fact[of t x] B unfolding T1 val_def 
      by (smt (verit, best) antisym_conv eint.simps(2) eint_ord_simps(3))
    have T3: "SA_poly_to_Qp_poly m x f \<bullet> t = \<zero>"
      unfolding T2 Qp.finsum_zero a1 by auto          
    show ?thesis 
      using T1 T3 u_prop ac_one[of N1] N1_def by (simp add: B(1) T0 a_eval)
  next
    case False
    have F0: "monom_center_term m (a i\<^sub>0) c i\<^sub>0 (t # x) \<in> Units Q\<^sub>p"
      using False Qp.not_nonzero_memE Units_eq_nonzero a2 by blast
    have F1: "\<And> j. j \<noteq> i\<^sub>0 \<Longrightarrow> 
        val (a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0) + N \<le> val (a j x \<otimes> (t \<ominus> c x)[^]j)"
      using A\<^sub>1_memE B by auto 
    have F2: "val (a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0) = ord (a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0)"
      using F0 unfolding a0 by (simp add: Units_nonzero_Qp)
    have F3: "\<And>j. j \<noteq> i\<^sub>0 \<Longrightarrow> val (a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0) < val (a j x \<otimes> (t \<ominus> c x)[^]j)"
      using F2 N_pos unfolding F2 
      by (smt (z3) Extended_Int.Suc_ile_eq F1 F2 bot_nat_0.not_eq_extremum eint_ord_simps(1) 
          eint_ord_simps(3) of_nat_le_0_iff plus_eint_simps(1) val_def)
    have F4: "\<And> i. a i x \<otimes> (t \<ominus> c x) [^] i \<in> carrier Q\<^sub>p"
      using B UPQ.monom_term_car a_eval some_closures(3) by presburger
    have F5: "(\<Oplus>j\<in>inds. a j x \<otimes> (t \<ominus> c x) [^] j) = 
              a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0 \<oplus> (\<Oplus>j\<in>inds - {i\<^sub>0}. a j x \<otimes> (t \<ominus> c x) [^] j)"
    proof- 
      have 20: "inds = insert i\<^sub>0 (inds - {i\<^sub>0})"
        using assms by auto 
      have 21: "(\<Oplus>j\<in>insert i\<^sub>0 (inds - {i\<^sub>0}). a j x \<otimes> (t \<ominus> c x) [^] j) = 
              a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0 \<oplus> (\<Oplus>j\<in>inds - {i\<^sub>0}. a j x \<otimes> (t \<ominus> c x) [^] j)"
        apply(rule Qp.finsum_insert)
          using inds_finite apply blast
            apply auto[1]
          using F4  by auto 
      show ?thesis using 20 21 by auto 
    qed
    have F6: "val ((\<Oplus>j\<in>inds - {i\<^sub>0}. a j x \<otimes> (t \<ominus> c x) [^] j)) > val (a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0)"
      apply(rule finsum_val_ultrametric'')
      using F4 inds_finite F3 unfolding F2 by auto 
    have F7: "(\<Oplus>j\<in>inds - {i\<^sub>0}. a j x \<otimes> (t \<ominus> c x) [^] j) \<in> carrier Q\<^sub>p"
      by(intro Qp.finsum_closed, auto simp: F4)
    have F8: "val (SA_poly_to_Qp_poly m x f \<bullet> t) = val (a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0)"
      unfolding a1 F3 F5 using F6 F7 F4[of i\<^sub>0] 
      by (metis (no_types, lifting) Qp.a_ac(2) val_ultrametric_noteq)
    have u_eq: "u = (SA_poly_to_Qp_poly m x f \<bullet> t)\<otimes> inv (a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0)"
      unfolding u_def a0 
      using B False f_closed SA_poly_to_SA_fun_formula[of f m x t] a0
      by auto 
    have F9: "a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0 \<in> Units Q\<^sub>p"
      using False a2 unfolding a0 using F0 a0 by auto
    have F10: "SA_poly_to_Qp_poly m x f \<bullet> t = u \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0"
      unfolding u_eq using F9 a3 
      by (simp add: B(1) B(4) Qp.cring_simprules(11) a_eval some_closures(3))
    have F11: "val u = 0"
      unfolding u_eq using F8 F9 a3 
      by (metis Qp.one_closed Qp.r_one Units_eq_nonzero a0 a2 local.fract_cancel_right prod_equal_val_imp_equal_val u_eq u_prop val_one)
    have F12: "ac N1 u = 1"
    proof- 
      obtain \<gamma> where \<gamma>_def: "\<gamma> = (\<Oplus>j\<in>inds - {i\<^sub>0}. a j x \<otimes> (t \<ominus> c x) [^] j)"
        by auto 
      obtain \<alpha> where \<alpha>_def: "\<alpha> = SA_poly_to_Qp_poly m x f \<bullet> t"
        by blast 
      obtain \<beta> where \<beta>_def: "\<beta> = a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0"
        by blast 
      have 0: "val \<gamma> \<ge> val \<beta> + N"
        unfolding \<gamma>_def \<beta>_def 
        apply(rule finsum_val_ultrametric')
        using F4 inds_finite F3 F1 unfolding F2 \<beta>_def \<gamma>_def by auto 
      have 1: "val \<beta> = ord \<beta>"
        unfolding \<beta>_def using F2 by fastforce
      have 2: "val \<gamma> \<ge> val \<beta> + N1"
        using N  0 unfolding 1 
        by (smt (verit, best) Num.of_nat_simps(4) eint_ord_code(2) eint_ord_simps(3)
            not_less of_nat_0_le_iff plus_eint_simps(1) val_def)
      have 3: "\<beta> \<in> Units Q\<^sub>p"
        using \<beta>_def F0 a0 by auto
      have 4: "u = (\<beta> \<oplus> \<gamma>)\<otimes> inv \<beta>"
        unfolding u_eq a1 F5 \<gamma>_def \<beta>_def by auto 
      have 5: "\<gamma> \<in> carrier Q\<^sub>p"
        using \<gamma>_def F7 by force
      have 6: "u = \<one> \<oplus> (\<gamma> \<otimes> inv \<beta>)"
        unfolding 4 using 3 5 Qp.Units_closed Qp.cring_simprules(13) by auto
      have 7: "u  \<ominus> \<one> = \<gamma> \<otimes> inv \<beta>"
        using 5 3 unfolding 6 
        using Qp.Units_inv_closed Qp.a_ac(2) Qp.add.inv_solve_right' Qp.add.m_closed 
          Qp.cring_simprules(6) Qp.m_closed Qp.minus_eq by presburger
      have 8: "val (\<gamma> \<otimes> inv \<beta>) \<ge> N1"
        using 2 
        by (metis "1" "3" "5" Qp.not_nonzero_memE Units_eq_nonzero add_cancel_eint_geq
            eint_ord_simps(3) local.val_zero val_nonzero_frac zero_fract)
      have 9: "u \<in> carrier Q\<^sub>p \<and> u \<noteq> \<zero>"
        using F11 B u_prop val_zero by auto 
      have 7: "ac N1 u = ac N1 \<one>"
        apply(intro ac_val, unfold nonzero_def mem_Collect_eq val_one F11 7)
        using 8 9 by auto 
      thus ?thesis using ac_one N1_def by auto 
    qed
    thus ?thesis using F9 F10 F11 by auto 
  qed
  thus ?thesis using u_prop by auto 
qed

lemma A\<^sub>1_factor_by_nth_power: 
  assumes "i\<^sub>0 \<in> inds"
  assumes "t#x \<in> A\<^sub>1"
  shows "\<exists> u \<in> carrier Q\<^sub>p. 
            val u = 0 \<and> 
            SA_poly_to_Qp_poly m x f \<bullet> t = u[^]n \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0"
proof- 
  obtain w where w_def: "w \<in> carrier Q\<^sub>p \<and>
            val w = 0 \<and> ac N1 w = 1 \<and> 
            SA_poly_to_Qp_poly m x f \<bullet> t = w \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0"
    using assms A\<^sub>1_factor_by_unit[of t x] by auto 
  have w_Pset: "w \<in> P_set n"
    using w_def N1_def(2) by blast
  then obtain u where u_def: "u \<in> carrier Q\<^sub>p" "w = u[^]n"
    unfolding P_set_def by auto 
  have u_val: "val u = 0"
  proof- 
    have a: "w \<in> nonzero Q\<^sub>p"
      using w_def nonzero_def val_zero P_set_nonzero'(1) w_Pset by auto
    have b: "u \<in> nonzero Q\<^sub>p"
      using a unfolding u_def 
      using Qp_nonzero_nat_pow n_pos u_def(1) by blast
    have c: "ord w = 0"
      using w_def a val_ord[of w] 
      by (metis eint_0_iff(1))
    have "ord u = 0"
      using c a w_def n_pos unfolding u_def  
      by (simp add: b nonzero_nat_pow_ord)
    thus ?thesis using a n_pos w_def b 
      unfolding u_def val_ord eint_0_iff 
      using val_ord zero_eint_def by presburger      
  qed
  have u_factor: "SA_poly_to_Qp_poly m x f \<bullet> t = u[^]n \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0"
    using w_def unfolding u_def by auto 
  show "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> SA_poly_to_Qp_poly m x f \<bullet> t = u [^] n \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0"
    using u_def u_val u_factor by auto 
qed

lemma A\<^sub>1_factored_decomp: 
  assumes "i\<^sub>0 \<in> inds"
  assumes "inds \<noteq> {i\<^sub>0}"
  shows "\<exists>S. is_cell_decomp m S A\<^sub>1 \<and>
             (\<forall> \<D> \<in> S. \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
proof- 
  have 0: "A\<^sub>1 = condition_to_set \<C> - (condition_to_set \<C> - A\<^sub>1)"
    unfolding A\<^sub>1_def by auto 
  have 1: " (\<exists>S. is_cell_decomp m S (condition_to_set \<C> - (condition_to_set \<C> - A\<^sub>1)) \<and> 
                      (\<forall>A \<in> S. center A = c))"
    apply(rule cell_decomp_same_center[of \<C> _ A c a1 a2 I ])
    using \<C>_cond \<C>_def  A\<^sub>1_comp_decomp assms by auto 
  have 2: "(\<exists>S. is_cell_decomp m S A\<^sub>1 \<and> 
                      (\<forall>A \<in> S. center A = c))"
    using 0 1 by auto 
  then obtain S where S_def: "is_cell_decomp m S A\<^sub>1 \<and> (\<forall>A \<in> S. center A = c)"
    by blast  
  have "\<forall>\<D>\<in>S. \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k"
  proof 
    fix \<D> assume A: "\<D> \<in> S"
    have 0: "center \<D> = c"
      using A S_def by auto 
    show "\<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k"
    proof- 
      obtain u where u_def: 
        "u = (\<lambda> xs. if xs \<in> A\<^sub>1 then 
                    (SOME u. u \<in> carrier Q\<^sub>p \<and>   val u = 0 \<and> 
                             SA_poly_to_Qp_poly m (tl xs) f \<bullet> (hd xs) 
                               = u[^]n \<otimes> a i\<^sub>0 (tl xs) \<otimes> ((hd xs) \<ominus> c (tl xs))[^]i\<^sub>0)
                    else \<one>)"
        by auto 
      have u_if_in: "\<And> xs. xs \<in> A\<^sub>1 \<Longrightarrow> u xs \<in> carrier Q\<^sub>p \<and>   val (u xs) = 0 \<and> 
                             SA_poly_to_Qp_poly m (tl xs) f \<bullet> (hd xs) 
                               = (u xs)[^]n \<otimes> a i\<^sub>0 (tl xs) \<otimes> ((hd xs) \<ominus> c (tl xs))[^]i\<^sub>0"
      proof-
        fix xs assume a: "xs \<in> A\<^sub>1"
        then obtain t x where tx_def: "xs = t#x"
          by (meson A\<^sub>1_subset Set.basic_monos(7) obtain_coords)
        have 0: "\<exists> u \<in> carrier Q\<^sub>p. 
            val u = 0 \<and> 
            SA_poly_to_Qp_poly m x f \<bullet> t = u[^]n \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x)[^]i\<^sub>0"
          apply(rule A\<^sub>1_factor_by_nth_power)
          using a assms unfolding tx_def by auto 
        thus "u xs \<in> carrier Q\<^sub>p \<and>   val (u xs) = 0 \<and> 
                             SA_poly_to_Qp_poly m (tl xs) f \<bullet> (hd xs) 
                               = (u xs)[^]n \<otimes> a i\<^sub>0 (tl xs) \<otimes> ((hd xs) \<ominus> c (tl xs))[^]i\<^sub>0"
          using u_def a tx_def  
          by (smt (z3) list.sel(1) list.sel(3) someI_ex)
      qed
      have u_if_not_in: "\<And> xs. xs \<notin> A\<^sub>1 \<Longrightarrow> u xs = \<one>"
        using u_def by auto 
      have u_prop: "u \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
        apply auto 
        using u_if_in u_if_not_in Qp.one_closed by smt 
      have "SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u (a i\<^sub>0) i\<^sub>0"
        apply(intro SA_poly_factorsI' u_prop a_cfs_closed, unfold 0)
        using A S_def is_cell_decompE 
        apply (meson is_cell_decomp_subset subset_trans)
        using c_closed apply blast 
      proof- fix x t 
        assume B: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p" "t # x \<in> condition_to_set \<D>"
        have tx: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "t#x \<in> condition_to_set \<C>" "t#x \<in> A\<^sub>1"
                 "SA_poly_to_Qp_poly m x f \<bullet> t \<in> carrier Q\<^sub>p"
          using S_def A B Qp_pow_ConsI is_cell_decomp_subset[of m S A\<^sub>1 \<D>] f_closed 
                SA_poly_to_Qp_poly_closed UPQ.to_fun_closed 
                  unfolding A\<^sub>1_def by auto 
        show "SA_poly_to_Qp_poly m x f \<bullet> t = u (t # x) [^] n \<otimes> a i\<^sub>0 x \<otimes> (t \<ominus> c x) [^] i\<^sub>0"
                    "val (u (t # x)) = 0"
          using tx u_if_in[of "t#x"] unfolding list_tl list_hd 
          by auto 
      qed
      thus ?thesis by auto 
    qed
  qed
  thus ?thesis using S_def by auto 
qed
end

locale normal_cell_transformation = 
  denef_II_base + 
  fixes \<B> b \<phi> H
  assumes subset: "condition_to_set \<B> \<subseteq> condition_to_set \<C> - A\<^sub>1"
  assumes \<phi>_Unit: "\<phi> \<in> Units (SA m)"
  assumes B_cell: "is_cell_condition \<B>"
  assumes B_eq: "\<B> = Cond m b c \<phi> \<phi> closed_interval"
  assumes b_nonempty: "b \<noteq> {}"

context normal_cell_transformation
begin

lemma i\<^sub>0_min: "\<And>j t x. t # x \<in> condition_to_set \<B> \<Longrightarrow> 
                        val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"
  apply(rule i\<^sub>0_fact)
  using subset by auto 

lemma cell_normalization_axioms_hold:
"cell_normalization p \<B> a b c \<phi> m f inds i\<^sub>0"
"(Q\<^sub>p \<equiv> Frac Z\<^sub>p)""\<iota> \<equiv> Frac_inc Z\<^sub>p" "Z\<^sub>p \<equiv> padic_int p"
proof-
  have 1: "\<And>j. j \<in> inds \<Longrightarrow> a j \<in> Units (SA m)"
          "\<And>j. j \<notin> inds \<Longrightarrow> a j = \<zero>\<^bsub>SA m\<^esub>"
     apply (simp add: inds_memE)
    using a_def f_taylor_cfs inds_def by auto
  show "cell_normalization p \<B> a b c \<phi> m f inds i\<^sub>0" 
        "(Q\<^sub>p \<equiv> Frac Z\<^sub>p)""\<iota> \<equiv> Frac_inc Z\<^sub>p" "Z\<^sub>p \<equiv> padic_int p"
   apply(intro cell_normalization.intro refined_one_val_point_cell.intro one_val_point_cell.intro
             refined_one_val_point_cell_axioms.intro one_val_point_cell_axioms.intro
              cell_normalization_axioms.intro f_closed \<phi>_Unit B_cell B_eq a_def b_nonempty 
              padic_fields_axioms inds_nonempty 1)
    using i\<^sub>0_min unfolding Q\<^sub>p_def Z\<^sub>p_def \<iota>_def by auto        
qed

interpretation cell_normalization _ _ _ _ \<B> a b c \<phi> _ _ inds i\<^sub>0
  using cell_normalization_axioms_hold by auto  

lemma normal_ubounded: "SA_poly_ubounded p m g (\<zero>\<^bsub>SA m\<^esub>) (condition_to_set (normal_cell m b)) N0"
proof- 
  have 0: "normal_cell m b = normalize_cell \<B>"
    by (simp add: normalize_\<C>)
  have 1: "\<zero>\<^bsub>SA m\<^esub> = center (normalize_cell \<B>)"
    unfolding normalize_\<C>  normal_cell_def center.simps by auto 
  have 2: "SA_poly_ubounded p m f (center \<B>) (condition_to_set \<B>) N0"
    apply(intro SA_poly_uboundedI f_closed)
      apply (simp add: \<C>_eq c_closed)
    using  cell_subset A\<^sub>1_closed N0_def subset A\<^sub>1_def B_eq center.simps 
    by auto
  show ?thesis 
    unfolding 0 1
    by(intro exI[of _ N] transfer_SA_poly_ubounded2 B_cell 2, unfold B_eq arity.simps, auto)
qed

lemma g_deg_bound: 
"deg (SA m) g \<le> Suc d"
  unfolding g_deg 
  by (simp add: assms(3))

lemma b_decomp_by_res_classes: "b = (\<Union> C \<in> poly_res_classes N (Suc d). {x \<in> b. SA_poly_to_Qp_poly m x g \<in> C})"
  by(intro SA_poly_constant_res_class_decomp  g_closed g_cfs_integral g_deg_bound b_closures, auto)
end

locale normal_cell_transformation_constant_res_class = normal_cell_transformation + 
  fixes cl l \<D>
  defines "\<D> \<equiv> constant_res m b N l"
  assumes nonempty: "condition_to_set \<D> \<noteq> {}"
  assumes cl_class: "cl \<in> poly_res_classes N (Suc d)"
  assumes constant_res_class: "\<And> x. x \<in> b \<Longrightarrow> 
                              SA_poly_to_Qp_poly m x (cell_normalization.g p a \<phi> m i\<^sub>0) \<in> cl"
  assumes l_in: "l \<in> carrier (Zp_res_ring N)"
  assumes l_val: "val ([l]\<cdot>\<one>) = 0"
 
context normal_cell_transformation_constant_res_class
begin

interpretation cell_normalization _ _ _ _ \<B> a b c \<phi> _ _ inds i\<^sub>0
  using cell_normalization_axioms_hold by auto  

lemma l_res: "Qp_res ([l] \<cdot> \<one>) N = l"
  using l_in by(simp add:  Qp_res_int_inc p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))

lemma \<D>_memE: 
  assumes "s#y \<in> condition_to_set \<D>"
  shows "s \<in> carrier Q\<^sub>p" "y \<in> b" "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "val s = 0" "Qp_res s N = l"
proof- 
  show sy_closed: "s \<in> carrier Q\<^sub>p" "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "y \<in> b"
    using assms unfolding \<D>_def constant_res_def 
    using cell_cond_head_closure apply blast
        using assms unfolding \<D>_def constant_res_def condition_to_set.simps cell_def
     mem_Collect_eq list_tl list_hd 
        using b_closures(3) by auto
  have 0: "val ([(p ^ N)] \<cdot> \<one>) \<le> val (s \<ominus> [l] \<cdot> \<one>)"
          "val (s \<ominus> [l] \<cdot> \<one>) \<le> \<infinity>"
    using assms sy_closed
    unfolding \<D>_def condition_to_set.simps cell_def constant_res_def mem_Collect_eq list_tl list_hd 
              closed_interval_def 
    using SA_int_inc_eval by auto
  have 1: "val ([(p ^ N)] \<cdot> \<one>) = N"
    using Qp.int_nat_pow_rep val_p_nat_pow by presburger
  have 2: "val (s \<ominus> [l] \<cdot> \<one>) > val ([l]\<cdot>\<one>)"
    using 0 unfolding l_val 1 
    by (smt (verit, ccfv_SIG) N_pos eint_ord_simps(1) eint_ord_trans not_less of_nat_0_less_iff zero_eint_def)
  hence 3: "val s = val ([l]\<cdot>\<one>)"
    by (metis Qp.int_inc_closed sy_closed(1) ultrametric_equal_eq)
  show 4: "val s = 0" 
    using "3" l_val by presburger
  have 5: "Qp_res s N = Qp_res ([l] \<cdot> \<one>) N"
    apply(intro Qp_res_eqI'[of s "[l]\<cdot>\<one>" N] val_ring_memI sy_closed, unfold 4 l_val, auto)
    using 0 1 by auto 
  thus "Qp_res s N = l"    
    using l_res by auto 
qed

lemma b_semialg: "is_semialgebraic m b"
  using \<D>_def  b_closures(2) by fastforce

lemma \<D>_sub: "condition_to_set \<D> \<subseteq> condition_to_set (normal_cell m b)"
              "condition_to_set \<D> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  apply(rule subsetI)
proof- 
  fix xs assume a: "xs \<in> condition_to_set \<D>"
  then have A:  "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> tl xs \<in> b \<and>
                val (([(p ^ N)] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>) (tl xs))
                     \<le> val (hd xs \<ominus> ([l] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>) (tl xs)) \<and>
            val (hd xs \<ominus> ([l] \<cdot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>) (tl xs)) \<le> val (\<zero>\<^bsub>SA m\<^esub> (tl xs)) "
  using normal_cell_memI
  unfolding \<D>_def condition_to_set.simps cell_def constant_res_def 
            closed_interval_def mem_Collect_eq by auto 
  obtain t x where tx_def: "xs = t#x" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using A by (meson Qp_pow_Suc_decomp)
  show "xs \<in> condition_to_set (normal_cell m b)"
    apply(unfold tx_def, intro normal_cell_memI b_semialg)
    using A a tx_def \<D>_memE(4)[of t x]  unfolding tx_def list_tl by auto  
next 
  show "condition_to_set \<D> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    by (metis Qp_pow_ConsI \<D>_memE(3) cell_conditon_mem_decomp cell_hd_closed subsetI)
qed

definition xs where xs_def: "xs = (SOME xs. xs \<in> condition_to_set \<D>)"

definition t where t_def: "t = hd xs"

definition x where x_def: "x = tl xs"

definition \<gamma> where \<gamma>_def: "\<gamma> = (SA_poly_to_Qp_poly m x g) \<bullet> t"

lemma \<D>_closures: 
"ys \<in> condition_to_set \<D> \<Longrightarrow> hd ys \<in> \<O>\<^sub>p"
"ys \<in> condition_to_set \<D> \<Longrightarrow> SA_poly_to_Qp_poly m (tl ys) g \<in> carrier (UP Q\<^sub>p)"
"ys \<in> condition_to_set \<D> \<Longrightarrow> hd ys \<in> carrier Q\<^sub>p"
"ys \<in> condition_to_set \<D> \<Longrightarrow> tl ys \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
"ys \<in> condition_to_set \<D> \<Longrightarrow> tl ys \<in> b"
"ys \<in> condition_to_set \<D> \<Longrightarrow> SA_poly_to_Qp_poly m (tl ys) g j \<in> \<O>\<^sub>p"
"ys \<in> condition_to_set \<D> \<Longrightarrow> SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys) \<in> \<O>\<^sub>p"
"ys \<in> condition_to_set \<D> \<Longrightarrow> deg Q\<^sub>p (SA_poly_to_Qp_poly m (tl ys) g) \<le> Suc d"
"ys \<in> condition_to_set \<D> \<Longrightarrow> SA_poly_to_Qp_poly m (tl ys) g \<in> val_ring_polys_grad (Suc d)"
"ys \<in> condition_to_set \<D> \<Longrightarrow> poly_res_class N (Suc d) (SA_poly_to_Qp_poly m (tl ys) g)  = cl"
proof- 
  fix ys assume A: "ys \<in> condition_to_set \<D>"
  show 0: " hd ys \<in> \<O>\<^sub>p" "SA_poly_to_Qp_poly m (tl ys) g \<in> carrier (UP Q\<^sub>p)"
  "hd ys \<in> carrier Q\<^sub>p" "tl ys \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "tl ys \<in> b"
    unfolding \<D>_def using \<D>_sub A  unfolding B_eq condition_to_set.simps cell_def 
        apply (metis (no_types, lifting) Qp_pow_ConsE(2) Qp_val_ringI basic_trans_rules(31) 
                  cell_conditon_mem_decomp cell_normalization_axioms_hold(2) 
                  cell_normalization_axioms_hold(4) \<D>_memE(4) l_val
                  normal_cell_transformation_constant_res_class_axioms val_ring_int_inc_closed val_ring_memE(1))    
       apply (metis A \<D>_memE(2) cell_conditon_mem_decomp g_closures(1))
    using A cell_hd_closed apply force
  apply (meson A Qp_pow_ConsE(1) \<D>_sub(2) subset_eq)
    by (metis A \<D>_memE(2) cell_conditon_mem_decomp)
  obtain g0 where g0_def: "g0 = SA_poly_to_Qp_poly m (tl ys) g"
    by blast 
  have 1: "\<And>j. SA_poly_to_Qp_poly m (tl ys) g j = g j (tl ys)"
    by (meson 0 A cell_normalization.to_Qp_g_cfs cell_normalization_axioms)
  show 2: "\<And>j. SA_poly_to_Qp_poly m (tl ys) g j \<in> \<O>\<^sub>p"
    unfolding 1 using 0 A g_cfs_integral(1) by blast
  show 3: "deg Q\<^sub>p (SA_poly_to_Qp_poly m (tl ys) g) \<le> Suc d"
    using "0"(4) SA_poly_to_Qp_poly_deg_bound f_deg g_closed g_deg by force
  show 4: " SA_poly_to_Qp_poly m (tl ys) g \<in> val_ring_polys_grad (Suc d)"
    by(intro val_ring_polys_grad_memI 0 A 2 3)
  show 5: "poly_res_class N (Suc d) (SA_poly_to_Qp_poly m (tl ys) g) = cl"
  proof-
    have 50: "g0 \<in> cl"
      using g0_def 0 4 constant_res_class by blast
    have 52: "g0 \<in> poly_res_class N (Suc d) g0"
      apply(rule poly_res_class_refl)
      using 4 g0_def by auto 
    have 51: "poly_res_class N (Suc d) g0 \<in> poly_res_classes N (Suc d)"
      unfolding poly_res_classes_def using 4 g0_def by auto 
    show ?thesis
      using poly_res_classes_disjoint[of cl N "Suc d" "poly_res_class N (Suc d) g0"]
      using 50 52 51 unfolding g0_def 
      by (smt (z3) "50" "51" "52" Diff_Diff_Int Diff_empty Int_commute Int_iff cl_class empty_iff
          equals0I g0_def poly_res_classes_disjoint)
  qed
  show "SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys) \<in> \<O>\<^sub>p"
    using 0 1 2 3 4 5 by (meson val_ring_poly_eval)
qed

lemma tx_closures: "t#x \<in> condition_to_set \<D>"
                   "t#x \<in> condition_to_set (normal_cell m b)"
                   "t \<in> carrier Q\<^sub>p"
                   "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                   "x \<in> b"
                   "SA_poly_to_Qp_poly m x g \<in> carrier (UP Q\<^sub>p)"
                   "t \<in> \<O>\<^sub>p"
                   "SA_poly_to_Qp_poly m x g w \<in> \<O>\<^sub>p"
                   "SA_poly_to_Qp_poly m x g \<in> val_ring_polys_grad (Suc d)"
                   "poly_res_class N (Suc d) (SA_poly_to_Qp_poly m x g) = cl"
                    "SA_poly_to_Qp_poly m x g \<bullet> t \<in> \<O>\<^sub>p"
proof-
  have xs_in: "xs \<in> condition_to_set \<D>"
    using xs_def nonempty SomeE by (metis all_not_in_conv)
  have xs_eq: "xs = t#x"
    using xs_in unfolding t_def x_def 
    using cell_conditon_mem_decomp by blast
  show 0: "t#x \<in> condition_to_set \<D>"
                   "t#x \<in> condition_to_set (normal_cell m b)"
                   "t \<in> carrier Q\<^sub>p"
                   "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                   "x \<in> b"
    using xs_in cell_cond_head_closure \<D>_sub  Qp_pow_ConsE(1)[of xs] Set.basic_monos(7) x_def xs_in
    unfolding xs_eq \<D>_def constant_res_def condition_to_set.simps cell_def  by auto 
  show  1: "SA_poly_to_Qp_poly m x g w \<in> \<O>\<^sub>p"
        "SA_poly_to_Qp_poly m x g \<in> carrier (UP Q\<^sub>p)"
        "t \<in> \<O>\<^sub>p"
    using 0 \<D>_closures[of "t#x"]  unfolding list_tl list_hd by auto 
  show "poly_res_class N (Suc d) (SA_poly_to_Qp_poly m x g) = cl"
      "SA_poly_to_Qp_poly m x g \<in> val_ring_polys_grad (Suc d)"
      "SA_poly_to_Qp_poly m x g \<bullet> t \<in> \<O>\<^sub>p"
    using 0(1) \<D>_closures[of "t#x"] unfolding list_tl by auto 
qed

lemma \<gamma>_closed: "\<gamma> \<in> carrier Q\<^sub>p"
  unfolding \<gamma>_def 
  by(intro UPQ.to_fun_closed SA_poly_to_Qp_poly_closed tx_closures g_closed)

lemma in_cl: "SA_poly_to_Qp_poly m x g \<in> cl"
  by(intro constant_res_class tx_closures)

lemma poly_eval_res:
assumes "ys \<in> condition_to_set \<D>"
shows "Qp_res ((SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys)) N = 
                              Qp_res ((SA_poly_to_Qp_poly m x g) \<bullet> t) N"
  apply(intro Qp_poly_res_eval_2 tx_closures \<D>_closures assms \<D>_closures assms, 
      rule poly_res_class_memE[of _ _ "Suc d"])
    using \<D>_closures(10) assms in_cl apply presburger
  by (metis \<D>_memE(5) assms cell_conditon_mem_decomp tx_closures(1))

lemma g_eval_val_bound: 
  assumes "ys \<in> condition_to_set \<D>"
  shows "val (SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys)) < N"
        "val (SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys)) \<le> N0"
proof- 
  obtain s y where s_def: "ys = s#y" "s \<in> carrier Q\<^sub>p" "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using  \<D>_sub assms
    by (meson Qp_pow_Suc_decomp subset_iff)
  have syin: "s#y \<in> condition_to_set (normal_cell m b)"
    using assms unfolding s_def 
    using \<D>_sub(1) by blast
  have 0: " val (SA_poly_to_Qp_poly m y g \<bullet> s)
        \<le> val (UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> y) (SA_poly_to_Qp_poly m y g) i\<^sub>0 \<bullet> s) + eint (int N0)"
    using syin normal_ubounded SA_poly_uboundedE' by blast
  have 1: "\<zero>\<^bsub>SA m\<^esub> y = \<zero>"
    using s_def SA_zeroE by auto 
  have pclosed: "SA_poly_to_Qp_poly m y g \<in> carrier (UP Q\<^sub>p)"
    by(intro SA_poly_to_Qp_poly_closed g_closed s_def )
  have 2: "UPQ.taylor \<zero> (SA_poly_to_Qp_poly m y g) i\<^sub>0 = g i\<^sub>0 y"
  proof- 
    have 20: "UPQ.taylor \<zero> (SA_poly_to_Qp_poly m y g) = (SA_poly_to_Qp_poly m y g)"
      unfolding UPQ.taylor_def 
      using UPQ.taylor_expansion_at_zero pclosed by blast
    show ?thesis  unfolding 20 
      using \<D>_memE(2) assms s_def(1) to_Qp_g_cfs by blast
  qed
  have gi: "g i\<^sub>0 = \<one>\<^bsub>SA m\<^esub>"
    unfolding g_cfs(2)[of i\<^sub>0] 
    by (simp add: i\<^sub>0_inds inds_memE)
  have 3: "(UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> y) (SA_poly_to_Qp_poly m y g) i\<^sub>0 \<bullet> s) =  
          s [^] i\<^sub>0"
    using UPQ.to_fun_taylor_term[of "SA_poly_to_Qp_poly m y g" s "\<zero>\<^bsub>SA m\<^esub> y" i\<^sub>0]
          s_def pclosed 1 2 Qp.minus_zero unfolding 1 2 gi 
    using Qp.cring_simprules(12) Qp.cring_simprules(2) Qp.nat_pow_closed SA_oneE by presburger
  have 4: "val (s[^]i\<^sub>0) = 0" 
    using \<D>_memE[of s y] assms s_def(1) val_zero_imp_val_pow_zero by force
  have 6: " val (SA_poly_to_Qp_poly m y g \<bullet> s) \<le> N0"
    using 0 unfolding 3 4 by auto 
  show "val (SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys)) \<le> N0"
        "val (SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys)) < N"
    using 6 s_def apply auto[1]    
    by(rule le_less_trans[of _ "eint N0" N], unfold s_def list_tl list_hd,   
          intro 6, unfold N, auto)
qed
   
lemma constant_pow_res_and_val: 
  assumes "ys \<in> condition_to_set \<D>"
  shows "val ((SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys)) = val \<gamma>"
        "pow_res n ((SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys)) =  pow_res n \<gamma>"
        "\<exists> w \<in> Units Q\<^sub>p. (SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys) = \<gamma> \<otimes> w[^]n"
proof- 
  obtain s y where s_def: "ys = s#y" "s \<in> carrier Q\<^sub>p" "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms  \<D>_sub
    by (meson Qp_pow_Suc_decomp subset_iff)
  have 0: "SA_poly_to_Qp_poly m (tl ys) g \<in> cl"
    apply(rule constant_res_class)
    using assms unfolding s_def \<D>_def condition_to_set.simps constant_res_def cell_def by auto 
  have 1: "Qp_res ((SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys)) N = 
                              Qp_res ((SA_poly_to_Qp_poly m x g) \<bullet> t) N"
    using assms poly_eval_res by auto 
  obtain \<delta> where \<delta>_def: "\<delta> = (SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys)"
    by auto 
  have \<delta>_closed: "\<delta> \<in> carrier Q\<^sub>p"
    unfolding \<delta>_def 
    by (simp add: UPQ.to_fun_closed \<D>_closures(2) \<D>_closures(3) assms)
  have 2: "val \<gamma> < N"
    using  g_eval_val_bound[of "t#x"] tx_closures
    unfolding \<gamma>_def list_tl list_hd by auto 
  have 3: "val \<delta> < N"
    by(unfold \<delta>_def, rule g_eval_val_bound, rule assms)
  have 4: "val (\<delta> \<ominus> \<gamma>) \<ge> N"
    by(unfold \<delta>_def  \<gamma>_def, intro Qp_res_eqE \<D>_closures poly_eval_res[of ys] tx_closures assms)
  have 5: "val \<delta> = val \<gamma> "
    using 2 3 4 \<gamma>_closed \<delta>_closed 
    by (meson basic_trans_rules(23) not_less ultrametric_equal_eq')
  have 6: "pow_res n \<delta> = pow_res n \<gamma>"
    apply(rule equal_pow_res_n_criterion)
        apply (metis "3" "5" Units_eq_nonzero \<gamma>_closed val_nonzero)
  apply (simp add: \<delta>_closed)
  using "5" apply presburger
  using \<delta>_def assms g_eval_val_bound(2) 4 \<delta>_closed \<gamma>_closed val_dist_sym by auto
  have "\<exists> w \<in> Units Q\<^sub>p. \<delta> = \<gamma> \<otimes> w[^]n"
    using 6 equal_pow_resE[of \<delta> \<gamma> n] n_pos \<gamma>_closed \<delta>_closed 
    unfolding P_set_def Units_eq_nonzero 
    using Qp_nonzero_nat_pow by blast
  thus "val ((SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys)) = val \<gamma>"
        "pow_res n ((SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys)) =  pow_res n \<gamma>"
         "\<exists>w\<in> Units Q\<^sub>p. SA_poly_to_Qp_poly m (tl ys) g \<bullet> lead_coeff ys = \<gamma> \<otimes> w [^] n"
    using 5 6 \<delta>_def by auto 
qed

definition w where w_def: "w =  
        (\<lambda>ys. if ys \<in> condition_to_set \<D> then 
        (SOME y. y \<in> Units Q\<^sub>p \<and> ((SA_poly_to_Qp_poly m (tl ys) g) \<bullet> (hd ys)) = \<gamma> \<otimes> y[^]n)
          else \<one>)"

lemma \<D>_w_eval:
  assumes "ys \<in> condition_to_set \<D>"
  shows "w ys \<in> Units Q\<^sub>p"
        "SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys) = \<gamma> \<otimes> (w ys)[^]n"
        "val (w ys) = 0"
proof- 
  show 0: "w ys \<in> Units Q\<^sub>p"
        "SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys) = \<gamma> \<otimes> (w ys)[^]n"
    using constant_pow_res_and_val(3)[of ys] assms someI_ex unfolding w_def 
     apply (metis (mono_tags, lifting) )
    using constant_pow_res_and_val(3)[of ys] assms someI_ex unfolding w_def 
    by (smt (verit, del_insts))
  obtain \<delta> where \<delta>_def: "\<delta> = SA_poly_to_Qp_poly m (tl ys) g \<bullet> (hd ys)"
    by auto 
  have \<delta>_closed: "\<delta> \<in> carrier Q\<^sub>p"
    by (simp add: UPQ.to_fun_closed \<D>_closures(2) \<D>_closures(3) \<delta>_def assms)
  have \<delta>_val: "val \<delta> = val \<gamma>"
    using \<delta>_def assms constant_pow_res_and_val(1) by blast
  have "val \<delta> = val \<gamma> + val ((w ys)[^]n)"
    using 0 \<delta>_closed unfolding \<delta>_def 
    using Qp.Units_closed Qp.nat_pow_closed \<gamma>_closed val_mult by presburger
  hence 1: "val ((w ys)[^]n) = 0"
    unfolding \<delta>_val 
    by (metis (no_types, lifting) "0"(1) "0"(2) Qp.Units_closed Qp.nat_pow_closed \<D>_memE(4) \<gamma>_closed 
        arith_simps(50) assms g_eval_val_bound(1) prod_equal_val_imp_equal_val tx_closures(1) 
        tx_closures(3) val_mult val_nonzero)
  hence 2: "w ys \<noteq> \<zero>"
    using val_zero n_pos Qp.pow_zero by force
  have 3: "ord ((w ys)[^]n) = 0"
    using 0(1) 1 2 unfolding val_def 
    by (meson Extended_Int.infinity_ne_i0 eint_0_iff(1))
  hence "n* ord (w ys) = 0"
    using 2 0  
    by (metis Units_eq_nonzero nonzero_nat_pow_ord)
  hence 4: "ord (w ys) = 0"
    using n_pos by auto 
  show "val (w ys) = 0"
    using 2 unfolding val_def 4 
    using eint_0 by presburger
qed

lemma w_closed:
  shows "\<And>ys. w ys \<in> Units Q\<^sub>p"
        "w \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
        
proof- 
  show "\<And> ys. w ys \<in> Units Q\<^sub>p"
  proof- fix ys show "w ys \<in> Units Q\<^sub>p"
    apply(cases "ys \<in> condition_to_set \<D>")
    using \<D>_w_eval apply auto[1]
    using w_def Qp.Units_one_closed by presburger
  qed
  thus "w \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    by auto 
qed

lemma poly_factors: "SA_poly_factors p m n g (center \<D>) (condition_to_set \<D>) w (\<cc>\<^bsub>m\<^esub>\<gamma>) (0::nat)"
proof(intro SA_poly_factorsI w_closed \<D>_sub(2))
  show "center \<D> \<in> carrier (SA m)"
    unfolding \<D>_def constant_res_def center.simps by auto 
  show "(\<cc>\<^bsub>m\<^esub>\<gamma>) \<in> carrier (SA m)"
    using \<gamma>_closed constant_fun_closed by presburger
  show "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>
           t \<in> carrier Q\<^sub>p \<Longrightarrow>
           t # x \<in> condition_to_set \<D> \<Longrightarrow>
           val (w (t # x)) = 0 \<and>
           SA_poly_to_Qp_poly m x g \<bullet> t =
           w (t # x) [^] n \<otimes> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<gamma> x \<otimes> (t \<ominus> center \<D> x) [^] (0::nat)"
  proof- 
    fix s y assume A: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
           "s \<in> carrier Q\<^sub>p"
           "s # y \<in> condition_to_set \<D>"
    have 0: "w (s # y) \<in> Units Q\<^sub>p"
            "SA_poly_to_Qp_poly m y g \<bullet> s = \<gamma> \<otimes> (w (s # y))[^]n"
      using A(3) \<D>_w_eval[of "s#y"] unfolding list_tl list_hd by auto
    have 1: "constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<gamma> y = \<gamma>"
      by (simp add: A(1) Qp_constE \<gamma>_closed)
    have 2: "(s \<ominus> center \<D> y) [^] (0::nat) = \<one>"
      by simp 
    have 3: "SA_poly_to_Qp_poly m y g \<bullet> s = 
          w (s#y) [^] n \<otimes> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<gamma> y \<otimes> (s \<ominus> center \<D> y) [^] (0::nat)"
      unfolding 0 1 2 
      by (simp add: "0"(1) Qp.Units_closed Qp.m_comm \<gamma>_closed)
    have 4: "val (w (s#y)) = 0"
      using \<D>_w_eval A by auto 
    thus "val (w (s#y)) = 0 \<and>
        SA_poly_to_Qp_poly m y g \<bullet> s = 
          w (s#y) [^] n \<otimes> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<gamma> y \<otimes> (s \<ominus> center \<D> y) [^] (0::nat)"
      using 3 by auto 
  qed
qed

lemma poly_factors_ex: "\<exists> u h k. SA_poly_factors p m n g (center \<D>) (condition_to_set \<D>) u h k"
  using poly_factors by auto 
end

context normal_cell_transformation
begin

interpretation cell_normalization _ _ _ _ \<B> a b c \<phi> _ _ inds i\<^sub>0
  using cell_normalization_axioms_hold by auto  

lemma normal_cell_decomp: 
"\<exists>S. is_cell_decomp m S (condition_to_set (normal_cell m b)) \<and> 
      (\<forall> \<D> \<in> S. \<exists> u h k. SA_poly_factors p m n g (center \<D>) (condition_to_set \<D>) u h k)"
proof- 
  obtain S where S_def: " is_cell_decomp m S (condition_to_set (normal_cell m b)) \<and>
        (\<forall>\<C>\<in>S. condition_to_set \<C> \<noteq> {} \<and>
                (\<exists>k\<in>carrier (residue_ring (p ^ N)).
                    \<exists>b'. \<exists>cl\<in>poly_res_classes N (Suc d).
                            is_semialgebraic m b' \<and>
                            b' \<subseteq> b \<and>
                            val ([k] \<cdot> \<one>) = 0 \<and>
                            \<C> = constant_res m b' N k \<and>
                            (\<forall>x\<in>b'. poly_res_class N (Suc d) (SA_poly_to_Qp_poly m x g) = cl)))"
    using constant_poly_residue_normalized_cell_decomp[of m b g "Suc d" N N] b_closures(2) g_closed 
          f_deg N_pos  unfolding g_deg 
    using g_cfs_integral(1) by presburger
  have 0: "is_cell_decomp m S (condition_to_set (normal_cell m b))"
    using S_def by auto 
  have 1: "condition_to_set (Cond m b c \<phi> \<phi> closed_interval) \<subseteq> condition_to_set \<C> - A\<^sub>1"
    using B_eq subset by auto 
  have 2: "\<forall>\<D>\<in>S. \<exists>u h k. SA_poly_factors p m n g (center \<D>) (condition_to_set \<D>) u h k"
  proof
    fix \<D> assume A: "\<D> \<in> S"
    obtain l b' cl where defs0:"cl\<in>poly_res_classes N (Suc d)" "l \<in> carrier (residue_ring (p ^ N))"
                        "is_semialgebraic m b' \<and>
                        b' \<subseteq> b \<and>
                        val ([l] \<cdot> \<one>) = 0 \<and>
                        \<D> = constant_res m b' N l \<and>
                        (\<forall>x\<in>b'. poly_res_class N (Suc d) (SA_poly_to_Qp_poly m x g) = cl)"
      using S_def A by blast 
    have defs: 
              "b' \<subseteq> b" "l \<in> carrier (residue_ring (p ^ N))"
              "is_semialgebraic m b'" "val ([l] \<cdot> \<one>) = 0" "\<D> = constant_res m b' N l"
              "cl\<in>poly_res_classes N (Suc d)"
              "\<And>x. x \<in> b' \<Longrightarrow> SA_poly_to_Qp_poly m x g \<in> cl"
    proof- 
      show p0: "b' \<subseteq> b" "l \<in> carrier (residue_ring (p ^ N))"
              "is_semialgebraic m b'" "val ([l] \<cdot> \<one>) = 0" "\<D> = constant_res m b' N l"
              "cl\<in>poly_res_classes N (Suc d)"
        using defs0 by auto 
      show "\<And>x. x \<in> b' \<Longrightarrow> SA_poly_to_Qp_poly m x g \<in> cl"
      proof- fix x assume A: "x \<in> b'"
        have 0: "cl = poly_res_class N (Suc d) (SA_poly_to_Qp_poly m x g)"
          using defs0 A by auto 
        show "SA_poly_to_Qp_poly m x g \<in> cl"
          unfolding 0 
          apply(intro poly_res_class_refl val_ring_polys_grad_memI SA_poly_to_Qp_poly_closed)
          using A p0 b_closures(3) apply auto[1]
          using g_closed apply auto[1]
          apply(rule g_cfs_integral)
          using p0 A apply auto[1]
        apply(rule le_trans[of _ "deg (SA m) g" "Suc d"],rule SA_poly_to_Qp_poly_deg_bound[of g m] )
          unfolding g_deg using g_closed
          using f_deg A p0 b_closures(3) by auto 
      qed
    qed
    have \<D>_nonempty: "condition_to_set \<D> \<noteq> {}"
      using A S_def by auto 
    have p0: "condition_to_set (Cond m b' c \<phi> \<phi> closed_interval) \<subseteq> 
                  condition_to_set (Cond m b c \<phi> \<phi> closed_interval)"
      using 1 defs unfolding condition_to_set.simps cell_def  by auto 
    have p1: "condition_to_set (Cond m b' c \<phi> \<phi> closed_interval) \<subseteq> condition_to_set \<C> - A\<^sub>1"
      using 1 p0 by auto 
    have p2: "\<And>j t x.
       t # x \<in> condition_to_set (Cond m b' c \<phi> \<phi> closed_interval) \<Longrightarrow>
       val (a i\<^sub>0 x \<otimes>\<^bsub>Frac (padic_int p)\<^esub> (t \<ominus>\<^bsub>Frac (padic_int p)\<^esub> c x) [^]\<^bsub>Frac (padic_int p)\<^esub> i\<^sub>0)
       \<le> val (a j x \<otimes>\<^bsub>Frac (padic_int p)\<^esub> (t \<ominus>\<^bsub>Frac (padic_int p)\<^esub> c x) [^]\<^bsub>Frac (padic_int p)\<^esub> j)"
      using i\<^sub>0_min p0 unfolding Q\<^sub>p_def Z\<^sub>p_def B_eq by auto 
    have p3: "b' \<noteq> {}"
      using \<D>_nonempty  unfolding constant_res_def defs condition_to_set.simps cell_def by auto
    have p4: "\<And>x. x \<in> b' \<Longrightarrow> SA_poly_to_Qp_poly m x g \<in> cl"
      using defs by auto 
    have p5: "is_cell_condition \<D>"
      using A S_def is_cell_decompE by auto 
    have p6: "is_cell_condition (Cond m b' c \<phi> \<phi> closed_interval)"
      apply(rule is_cell_conditionI')
      using defs c_closed \<phi>_closures is_convex_condition_def by auto 
    interpret normal_cell_transformation_constant_res_class _ _ _ _ _ _ _ _ _ _ 
                                                          _ _ _ _ "Cond m b' c \<phi> \<phi> closed_interval"
                                                          b' _  _ cl l \<D>     
          apply(intro  normal_cell_transformation_constant_res_class.intro
                        normal_cell_transformation_constant_res_class_axioms.intro
                       normal_cell_transformation.intro
                       normal_cell_transformation_axioms.intro)
      using denef_II_base_axioms p1 \<phi>_Unit p6 p2  p3 \<D>_nonempty defs 
      unfolding \<iota>_def  Z\<^sub>p_def Q\<^sub>p_def defs by auto 
    show "\<exists>u h k. SA_poly_factors p m n g (center \<D>) (condition_to_set \<D>) u h k"
      using poly_factors_ex by auto 
  qed
  thus ?thesis using S_def by auto 
qed

lemma cell_decomp: 
"\<exists>S. is_cell_decomp m S (condition_to_set \<B>) \<and> 
      (\<forall> \<D> \<in> S. \<exists> u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
  apply(intro transfer_decomp_poly_factors[of \<B>])
  using B_cell normal_cell_decomp unfolding B_eq arity.simps by auto   
end 

context denef_II_base
begin

lemma A\<^sub>1_comp_factored_decomp:
  assumes "i\<^sub>0 \<in> inds"
  assumes "inds \<noteq> {i\<^sub>0}"
  shows "\<exists>S. is_cell_decomp m S (condition_to_set \<C> - A\<^sub>1)  \<and> 
      (\<forall> \<D> \<in> S. \<exists> u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
proof- 
  obtain S0 where S0_def: "is_cell_decomp m S0 (condition_to_set \<C> - A\<^sub>1)\<and>
                       (\<forall>\<C> \<in> S0. center \<C> = c \<and> boundary_condition \<C> = closed_interval \<and>
                                (\<exists>\<phi> \<in> Units (SA m). u_bound \<C> = \<phi> \<and> l_bound \<C> = \<phi>))"
    using A\<^sub>1_comp_decomp assms by auto 
  obtain S where S_def: "S = {\<C> \<in> S0. condition_to_set \<C> \<noteq> {}}"
    by auto
  have S_decomp: "is_cell_decomp m S (condition_to_set \<C> - A\<^sub>1)"
    using S0_def unfolding S_def
    using remove_empty_cells by presburger
  have S_bounds: "\<forall>\<C> \<in> S. center \<C> = c \<and> boundary_condition \<C> = closed_interval \<and>
                                (\<exists>\<phi> \<in> Units (SA m). u_bound \<C> = \<phi> \<and> l_bound \<C> = \<phi>)"
    using S0_def S_def by auto 
  show ?thesis
     apply(rule refine_each_cell[of _ S])
    using S_decomp apply auto[1]
  proof- 
    fix \<B> assume A: "\<B> \<in> S"
    obtain b \<phi> where defs: "\<phi> \<in> Units (SA m)" "\<B> = Cond m b c \<phi> \<phi> closed_interval"
      using S_bounds A S_decomp by (metis condition_decomp' is_cell_decompE(4))
    interpret normal_cell_transformation _ _ _ _ _ _ _ _ _ _ _ _ _ _ \<B> b \<phi> i\<^sub>0
    proof(intro normal_cell_transformation.intro denef_II_base_axioms 
                normal_cell_transformation_axioms.intro defs)
      show 0: "condition_to_set \<B> \<subseteq> condition_to_set \<C> - A\<^sub>1"
        using A S_decomp is_cell_decomp_subset[of m S] by auto 
      show 1: "is_cell_condition \<B>"
        using A S_decomp is_cell_decompE by auto 
      show "b \<noteq> {}"
        using A unfolding S_def defs mem_Collect_eq condition_to_set.simps cell_def by auto 
      show  "Z\<^sub>p \<equiv> padic_int p"
            "Q\<^sub>p \<equiv> Frac Z\<^sub>p"
            "\<iota> \<equiv> Frac_inc Z\<^sub>p"
        unfolding Z\<^sub>p_def Q\<^sub>p_def \<iota>_def 
        by auto 
    qed
    show "\<exists>S. is_cell_decomp m S (condition_to_set \<B>) \<and>
             (\<forall>\<D>\<in>S. \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
      using cell_decomp by auto 
  qed
qed

lemma f_eval_formula': "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> t \<in> carrier Q\<^sub>p \<Longrightarrow> 
                      SA_poly_to_Qp_poly m x f \<bullet> t = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
proof-
  fix x t assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) "" t \<in> carrier Q\<^sub>p"
  have 0: "SA_poly_to_Qp_poly m x f \<bullet> t = SA_poly_to_SA_fun m f (t#x)"
    using A SA_poly_to_SA_fun_formula f_closed by auto  
  show "SA_poly_to_Qp_poly m x f \<bullet> t = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
    unfolding 0
    using f_eval_formula A by auto 
qed

lemma f_eval_formula'': "\<And>x t. t#x \<in> condition_to_set \<C> \<Longrightarrow> 
                      SA_poly_to_Qp_poly m x f \<bullet> t = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
  apply(rule f_eval_formula')
   apply (simp add: some_closures(2)) 
  by (simp add: some_closures(1))

lemma binary_decomp:
  assumes "is_cell_decomp m S0 A0"
  assumes "is_cell_decomp m S1 (A1 - A0)"
  assumes "A0 \<subseteq> A1"
  assumes "\<And> C. C \<in> S0 \<Longrightarrow> P C"
  assumes "\<And> C. C \<in> S1 \<Longrightarrow> P C"
  shows "is_cell_decomp m (S0 \<union> S1) A1 \<and> (\<forall>C \<in> (S0 \<union> S1). P C)"
  apply(intro conjI is_cell_decompI is_partitionI disjointI)
  using assms is_cell_decompE apply auto[1]
  using assms is_cell_decompE is_partitionE disjointE assms 
        apply (smt (verit) Diff_disjoint Int_absorb2 Un_iff image_iff inf_bot_right 
                          inf_commute inf_left_commute is_cell_decomp_subset)
  using assms(1,2,3) is_cell_decompE(2)[of m S0 A0] is_partitionE(2)[of "condition_to_set ` S0" A0]
       is_cell_decompE(2)[of m S1 "A1 - A0"] is_partitionE(2)[of "condition_to_set ` S1 " "A1 - A0"] 
  apply auto[1]
  using assms is_cell_decompE assms apply auto[1]
    using assms is_cell_decompE assms apply auto[1]
    using assms is_cell_decompE assms  Diff_partition Un_least apply metis 
    using assms is_cell_decompE assms  Diff_partition Un_least  apply (metis cell_decomp_union)
    using assms by auto 

lemma denef_II_base_cell_decomp: 
"\<exists>S. is_cell_decomp m S (condition_to_set \<C>) \<and>
     (\<forall> \<D> \<in> S. \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
proof(cases "i\<^sub>0 \<notin> inds \<or> inds = {i\<^sub>0}")
  case True
  have T0: "\<exists>u h k. SA_poly_factors p m n f (center \<C>) (condition_to_set \<C>) u h k"
    using near_equal_set_Unit_eq_edge_case True by auto 
  have T1: "is_cell_decomp m {\<C>} (condition_to_set \<C>)"
    by (simp add: \<C>_arity assms(2) singleton_cell_decomp)
  have T2: "(\<forall>\<D>\<in> {\<C>} . \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
    using T0 by auto 
  show ?thesis 
    using T1 T2 by auto 
next
  case False
  obtain S0 where S0_def: "is_cell_decomp m S0 (condition_to_set \<C> - A\<^sub>1)  \<and> 
      (\<forall> \<D> \<in> S0. \<exists> u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
    using A\<^sub>1_comp_factored_decomp False by auto 
  obtain S1 where S1_def: "is_cell_decomp m S1 A\<^sub>1  \<and> 
      (\<forall> \<D> \<in> S1. \<exists> u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
    using A\<^sub>1_factored_decomp False by auto 
  obtain S where S_def: "S = S1 \<union> S0"
    by auto 
  have " is_cell_decomp m S (condition_to_set \<C>) \<and> 
          (\<forall>\<D>\<in>S. \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
    unfolding S_def 
    apply(rule binary_decomp[of _ A\<^sub>1])
    using S1_def S0_def A\<^sub>1_def by auto 
  thus ?thesis by auto 
qed

end
end

