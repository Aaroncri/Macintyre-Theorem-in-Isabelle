theory Constructing_Semialgebraic_Functions
  imports Locales_For_Macintyre
begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Constructing Semialgebraic Functions with Hensel's Lemma\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Denef's cell decomposition theorems both rely on two lemmas about constructing new 
semialgebraic functions. These are lemmas 2.3 and 2.4 from the paper. The proofs of both of these 
lemmas fit into the inductive scheme for proving cell decomposition theorems $I$ and $II$, and thus 
they both can assume decomposition theorem $II_d$ for some $d$. To avoid redundancy in their proofs,
analyzing their structure shows that they both can be derived from the following criterion for 
semialgebraicity, which is formalized here as the lemma in the locale $denef\_II$ with the name 
'SA\_fun\_test':

Suppose Denef's cell decomposition theorem $II_d$ holds. Let $g(t,x)$ be a polynomial in 
$UP (SA (m))$. That is, a univariate polynomial in $t$ with coefficients which are semialgebraic 
functions $g_i(x):\mathbb{Q}_p^{m} \to \mathbb{Q}_p$. Suppose also that $0 < \text{deg }(g) \leq d+1$
 and the leading term of $g$ is a unit in the ring $SA (m)$. Let $\xi: \mathbb{Q}_p^m \to \mathbb{Q}_p$
 be an extensional function satisfying:
\[
g(\xi(x), x) = 0
\]
for all $x \in \mathbb{Q}_p^m$. Suppose that we have verified that all sets of the forms
\begin{enumerate}
    \item $\{(x,y) \in \mathbb{Q}_p^m \times \mathbb{Q}_p^k \mid \exists \alpha \in \mathbb{Q}_p. (\xi(x) - c(x,y) = \rho \cdot \alpha^n) \}$
    \item $\{(x,y) \in \mathbb{Q}_p^m \times \mathbb{Q}_p^k \mid \text{ val }(\xi(x) - c(x,y)) \leq \text{ val } (a(x,y))\}$
\end{enumerate}
are semialgebraic, where $k \in \mathbb{N}$, $a,c \in SA(m+k)$, and $\rho \in \mathcal{O}_p$. Then 
$\xi$ is a semialgebraic function. 

The following section builds up to and includes the proof of this criterion.\<close>

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Cell Preparation Lemmas\<close>
(**************************************************************************************************)
(**************************************************************************************************)
text\<open>This section establishes some lemmas about cell decompositions which will be needed for the 
proof of the main result.\<close>

context padic_fields
begin

lemma SA_car_eqI:
  assumes "f \<in> carrier (SA m)"
  assumes "g \<in> carrier (SA m)"
  assumes "\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> f a = g a"
  shows "f = g"
  apply(rule function_ring_car_eqI[of _ m])
using assms apply (simp add: SA_car_memE(2)) 
 using assms apply (simp add: SA_car_memE(2)) 
  by(rule assms)

lemma SA_smult_distrib:
assumes "a \<in> carrier Q\<^sub>p"
assumes "b \<in> carrier Q\<^sub>p"
assumes "x \<in> carrier (SA m)"
shows" (a \<oplus> b) \<odot>\<^bsub>SA m\<^esub> x = a \<odot>\<^bsub>SA m\<^esub> x \<oplus>\<^bsub>SA m\<^esub> b \<odot>\<^bsub>SA m\<^esub> x"
  apply(rule SA_car_eqI[of _ m])
  using function_ring_car_eqI assms
  apply (simp add: SA_smult_closed) 
    using function_ring_car_eqI assms
     apply (simp add: SA_smult_closed) 
  by (simp add: SA_car_memE(2) SA_plus SA_smult assms(1) assms(2) assms(3) local.function_smult_l_distr) 

lemma SA_smult_distrib':
assumes "a \<in> carrier Q\<^sub>p"
assumes "x \<in> carrier (SA m)"
assumes "y \<in> carrier (SA m)"
shows "a \<odot>\<^bsub>SA m\<^esub> (x \<oplus>\<^bsub>SA m\<^esub> y) = a \<odot>\<^bsub>SA m\<^esub> x \<oplus>\<^bsub>SA m\<^esub> a \<odot>\<^bsub>SA m\<^esub> y"
  apply(rule SA_car_eqI[of _ m])
  using function_ring_car_eqI assms
  apply (simp add: SA_smult_closed) 
    using function_ring_car_eqI assms
     apply (simp add: SA_smult_closed) 
  by (simp add: SA_car_memE(2) SA_plus SA_smult assms(1) assms(2) assms(3) local.function_smult_r_distr) 

lemma SA_smult_assoc:
assumes "a \<in> carrier Q\<^sub>p"
assumes "b \<in> carrier Q\<^sub>p"
assumes "x \<in> carrier (SA m)"
shows "a \<otimes> b \<odot>\<^bsub>SA m\<^esub> x = a \<odot>\<^bsub>SA m\<^esub> (b \<odot>\<^bsub>SA m\<^esub> x)"
  apply(rule SA_car_eqI[of _ m])
  using function_ring_car_eqI assms
  apply (simp add: SA_smult_closed) 
    using function_ring_car_eqI assms
     apply (simp add: SA_smult_closed) 
  by (simp add: SA_car_memE(2) SA_smult assms(1) assms(2) assms(3) local.function_smult_assoc1) 

lemma SA_is_module:
  "module Q\<^sub>p (SA m)"
  apply(rule moduleI)
  apply (simp add: local.F.R_cring) 
  apply (simp add: R.abelian_group_axioms) 
      apply (simp add: SA_smult_closed) 
  apply (simp add: SA_smult_distrib) 
  apply (meson SA_smult_distrib') 
    apply (meson SA_smult_assoc) 
apply(rule SA_car_eqI[of _ m])    
  apply (simp add: SA_smult_closed) 
  apply simp 
  by (simp add: SA_car_memE(2) SA_smult) 
  
lemma poly_cell_decomp:
assumes "r \<in> carrier (SA n)"
assumes "is_cell_condition \<C>"
assumes "arity \<C> = n"
assumes "m > 0"
shows "\<exists> Cs. is_cell_decomp n Cs (condition_to_set \<C>)  \<and> 
          (\<forall>cell \<in> Cs. (\<forall> x \<in> fibre_set cell. r x = \<zero> ) \<or> (\<exists> \<rho> \<in> nth_pow_wits m. \<forall> x \<in> fibre_set cell. pow_res m (r x) = pow_res m \<rho>))
          \<and> Cs =refine_fibres \<C> ` ({(fibre_set \<C>) \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>}} \<union> ((\<lambda> \<rho>. (r  \<inverse>\<^bsub>n\<^esub> (pow_res m \<rho>)) \<inter> (fibre_set \<C>)) ` (nth_pow_wits m)))"
proof-
  obtain C where C_def: "C = fibre_set \<C>"
    by blast
  have C_semialg: "is_semialgebraic n C"
    using assms C_def is_cell_conditionE'(1) by blast
  obtain f where f_def: "f = (\<lambda> \<rho>. (r  \<inverse>\<^bsub>n\<^esub> (pow_res m \<rho>)) \<inter> C)"
    by blast 
  have 0: "\<And>\<rho>. \<rho> \<in> (nth_pow_wits m) \<Longrightarrow> is_semialgebraic n (f \<rho>)"
    using f_def C_semialg nth_pow_wits_SA_fun_prep[of m r] assms intersection_is_semialg 
    by blast
  have 1: "C = (C \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>}) \<union> \<Union> (f ` (nth_pow_wits m))"
  proof 
    show " C \<subseteq> (C \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>}) \<union> \<Union> (f ` nth_pow_wits m)"
    proof fix x assume A: "x \<in> C"
      then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        using C_semialg by (meson in_mono is_semialgebraic_closed)
      show "x \<in> C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>} \<union> \<Union> (f ` nth_pow_wits m)"
      proof(cases "r x = \<zero>")
        case True
        then show ?thesis 
          using x_closed A by blast                        
      next
        case False
        then have rx_nonzero: "r x \<in> nonzero Q\<^sub>p"
          using assms(1) x_closed unfolding nonzero_def  
          using Qp.function_ring_car_memE SA_car_memE(2) by blast
        then obtain \<rho> where rho_def: "\<rho> \<in> nth_pow_wits m \<and> pow_res m (r x) = pow_res m \<rho>"
          using nth_pow_wits_covers[of m "r x"] Qp.nonzero_closed assms equal_pow_resI
          by blast
        then have "r x \<in> pow_res m \<rho>"
          using pow_res_refl[of "r x " m] assms rx_nonzero unfolding nonzero_def by blast
        then show ?thesis 
          using f_def A x_closed  rho_def by blast
      qed
    qed
    show "C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>} \<union> \<Union> (f ` nth_pow_wits m) \<subseteq> C"
    proof fix x assume A: "x \<in> C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>} \<union> \<Union> (f ` nth_pow_wits m)"
      show "x \<in> C"
        apply(cases "x \<in> C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>} ")
          apply blast 
             using A unfolding f_def by blast 
    qed
  qed
  obtain Cs where Cs_def: "Cs = {C \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>}} \<union> (f ` (nth_pow_wits m))"
    by blast 
  have Cs_partition: "Cs partitions C"
  proof(rule is_partitionI)
    show "disjoint Cs"
    proof(rule disjointI)
      fix A B assume  A: "A \<in> Cs" "B \<in> Cs" "A \<noteq> B"
      show "A \<inter> B = {}"
      proof(cases "A = C \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>}")
        case True
        then have "B \<in> f ` nth_pow_wits m"
          using A unfolding Cs_def by fastforce           
        then obtain \<rho> where rho_def: "\<rho> \<in> nth_pow_wits m \<and> B = f \<rho>"
          by blast
        have "\<And>x. x \<in> A \<Longrightarrow> x \<notin> B"
        proof- fix x assume x_in: "x \<in> A"
          then have "r x = \<zero>"
            using True by blast 
          then have "r x \<notin> pow_res m \<rho>"
            using nonzero_pow_res[of \<rho> m] Qp.not_nonzero_memI assms nth_pow_wits_closed(3) rho_def by blast
          then show "x \<notin> B"
            using rho_def  unfolding f_def 
            by blast
        qed
        thus ?thesis 
          by blast
      next
        case False
        show ?thesis proof(cases "B = C \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>}")
          case True
          then have "A \<in> f ` nth_pow_wits m"
            using A unfolding Cs_def by fastforce           
          then obtain \<rho> where rho_def: "\<rho> \<in> nth_pow_wits m \<and> A = f \<rho>"
            by blast
          have "\<And>x. x \<in> B \<Longrightarrow> x \<notin> A"
          proof- fix x assume x_in: "x \<in> B"
            then have "r x = \<zero>"
              using True by blast 
            then have "r x \<notin> pow_res m \<rho>"
              using nonzero_pow_res[of \<rho> m] Qp.not_nonzero_memI assms nth_pow_wits_closed(3) rho_def by blast
            then show "x \<notin> A"
              using rho_def  unfolding f_def 
              by blast
          qed
          thus ?thesis 
            by blast
         next
           case F: False
           have F0: "A \<in> f ` nth_pow_wits m"
           proof-
             have "A \<notin> {C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>}} " using False by blast 
             thus ?thesis using A(1) unfolding  Cs_def
             proof -
               assume "A \<in> {C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>}} \<union> f ` nth_pow_wits m"
               then show ?thesis
                 using \<open>A \<notin> {C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>}}\<close> by blast
             qed 
           qed
           have F1: "B \<in> f ` nth_pow_wits m" using F A unfolding Cs_def
           proof -
             assume "B \<in> {C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>}} \<union> f ` nth_pow_wits m"
             then show ?thesis
               using F by fastforce
           qed  
           obtain \<rho> where rho_def: "\<rho> \<in> nth_pow_wits m \<and> A = f \<rho>"
             using F0 by blast
           obtain \<gamma> where gamma_def: "\<gamma> \<in> nth_pow_wits m \<and> B = f \<gamma>"
             using F1 by blast
           have rho_not_gamma: "\<rho> \<noteq> \<gamma>"
             using A rho_def gamma_def by blast
           have "pow_res m \<rho> \<inter> pow_res m \<gamma> = {}"
             using rho_not_gamma nth_pow_wits_neq_pow_res assms gamma_def nth_pow_wits_disjoint_pow_res rho_def
             by blast 
           then show "A \<inter> B = {}"
             using rho_def gamma_def unfolding f_def 
             by blast    
         qed
       qed
    qed
    show "\<Union> Cs = C"
    proof-
      have "\<Union> Cs = (C \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>}) \<union> \<Union> (f ` (nth_pow_wits m))"
      proof
        show "\<Union> Cs \<subseteq> C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>} \<union> \<Union> (f ` nth_pow_wits m)"
          unfolding Cs_def 
          by blast
        show "C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>} \<union> \<Union> (f ` nth_pow_wits m) \<subseteq> \<Union> Cs"
          unfolding Cs_def 
          by (metis (no_types, lifting) Sup_insert Un_iff Union_Un_distrib subsetI)
      qed        
      thus ?thesis using 1 
        by presburger
    qed
  qed
  have 2: "is_semialgebraic n (C \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>})"
  proof-
    have "is_univ_semialgebraic {\<zero>}"
    apply(rule finite_is_univ_semialgebraic) 
      apply blast 
      by blast
    then show "is_semialgebraic n (C \<inter> r \<inverse>\<^bsub>n\<^esub> {\<zero>})"
      using C_semialg assms evimage_is_semialg intersection_is_semialg 
      by blast
  qed
  hence 3: "\<And>c. c \<in> Cs \<Longrightarrow> is_semialgebraic n c"
    unfolding Cs_def using C_semialg 0 
    by blast
  have "finite Cs"
    using Cs_def nth_pow_wits_finite assms 
    by (metis finite.simps finite_Un finite_imageI finite_insert le_eq_less_or_eq less_one linorder_neqE_nat not_numeral_le_zero)
  hence 4:  "is_cell_decomp n (refine_fibres \<C> ` Cs) (condition_to_set \<C>) "
    using 3 Cs_partition partition_to_cell_decomp[of \<C> n C "center \<C>" "l_bound \<C>" "u_bound \<C>" "boundary_condition \<C>" Cs ] 
          assms condition_decomp'[of \<C>] C_def are_semialgebraicI by blast
  obtain CD where CD_def: "CD = refine_fibres \<C> ` Cs"
    by blast 
  have "\<And>cell. cell \<in> CD \<Longrightarrow>  (\<forall> x \<in> fibre_set cell. r x = \<zero> ) \<or> (\<exists> \<rho> \<in> nth_pow_wits m. \<forall> x \<in> fibre_set cell. pow_res m (r x) = pow_res m \<rho>)"
  proof- fix cell assume A0: "cell \<in> CD" 
    then have "fibre_set cell \<in> Cs"
      by (metis CD_def image_eqI refine_fibres_fibre_sets)
    show "(\<forall>x\<in>fibre_set cell. r x = \<zero>) \<or> (\<exists>\<rho>\<in>nth_pow_wits m. \<forall>x\<in>fibre_set cell. pow_res m (r x) = pow_res m \<rho>)"
    proof(cases "(\<forall>x\<in>fibre_set cell. r x = \<zero>)")
      case True
      then show ?thesis by blast 
    next
      case False 
      show ?thesis proof(cases "fibre_set cell = {}")
        case True
        then show ?thesis by blast 
      next
        case F: False
        have "(\<exists>\<rho>\<in>nth_pow_wits m. \<forall>x\<in>fibre_set cell. pow_res m (r x) = pow_res m \<rho>)"    
        proof-
          have "fibre_set cell  \<in>  f ` (nth_pow_wits m)"
          using Cs_def False \<open>fibre_set cell \<in> Cs\<close> by blast        
          then obtain \<rho> where rho_def: "\<rho> \<in> nth_pow_wits m \<and> fibre_set cell = r  \<inverse>\<^bsub>n\<^esub> (pow_res m \<rho>) \<inter> C"
          using f_def by blast
         have "\<forall>x\<in>fibre_set cell. pow_res m (r x) = pow_res m \<rho>" proof fix x assume A1: "x \<in> fibre_set cell"
          then have 5: "r x \<in> pow_res m \<rho>"
            using A1 rho_def by blast     
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
            using A1 rho_def by (metis IntD1 evimage_eq)
          have rho_nonzero: "\<rho> \<in> nonzero Q\<^sub>p"
            using rho_def nth_pow_wits_closed assms by blast 
          hence 6: "r x \<in> nonzero Q\<^sub>p"
            using 5 unfolding pow_res_def 
            by (smt Qp.integral Qp.nonzero_closed Qp_nat_pow_nonzero mem_Collect_eq not_nonzero_Qp)          
          have 7: "r x \<in> pow_res m \<rho>"
            using rho_def 5 by blast
          show  "pow_res m (r x) = pow_res m \<rho>"
          proof-
            have 80: "r x \<in> carrier Q\<^sub>p"
            using "6" Qp.nonzero_closed by blast
            have 81: "\<rho> \<in> nonzero Q\<^sub>p"
            using rho_def nth_pow_wits_closed(3)[of m \<rho>] assms 
            by blast
            thus ?thesis using equal_pow_resI[of \<rho> "r x" m] assms
                  7  80 81 unfolding   nonzero_def
            by blast 
          qed         
          qed
          then show ?thesis using rho_def by blast         
        qed
        thus ?thesis by blast 
      qed
    qed
  qed
  hence " (\<forall>cell \<in> CD. (\<forall> x \<in> fibre_set cell. r x = \<zero> ) \<or> (\<exists> \<rho> \<in> nth_pow_wits m. \<forall> x \<in> fibre_set cell. pow_res m (r x) = pow_res m \<rho>))"
    by blast
  thus ?thesis
    using CD_def unfolding Cs_def f_def C_def 
    using "4" CD_def by metis
qed

definition prepare_cell_pow_res where
"prepare_cell_pow_res n m \<C> r = refine_fibres \<C> ` ({(fibre_set \<C>) \<inter> r\<inverse>\<^bsub>n\<^esub>{\<zero>}} \<union> ((\<lambda> \<rho>. (r  \<inverse>\<^bsub>n\<^esub> (pow_res m \<rho>)) \<inter> (fibre_set \<C>)) ` (nth_pow_wits m))) "

lemma prepare_cell_pow_res_decomp:
assumes "r \<in> carrier (SA n)"
assumes "is_cell_condition \<C>"
assumes "arity \<C> = n"
assumes "n > 0"
assumes "m > 0"
shows "is_cell_decomp n (prepare_cell_pow_res n m \<C> r) (condition_to_set \<C>)"
  using poly_cell_decomp assms unfolding prepare_cell_pow_res_def by blast 

lemma prepare_cell_pow_res_decomp_fibre_set:
assumes "r \<in> carrier (SA n)"
assumes "is_cell_condition \<C>"
assumes "arity \<C> = n"
assumes "n > 0"
assumes "m > 0"
assumes "\<C>' \<in> (prepare_cell_pow_res n m \<C> r)"
shows "fibre_set \<C>' \<subseteq> r\<inverse>\<^bsub>n\<^esub>{\<zero>} \<or> (\<exists> \<rho> \<in> nth_pow_wits m. fibre_set \<C>' \<subseteq> r\<inverse>\<^bsub>n\<^esub>(pow_res m \<rho>))"
proof-
  have "(\<forall>cell \<in> (prepare_cell_pow_res n m \<C> r). (\<forall> x \<in> fibre_set cell. r x = \<zero> ) \<or> (\<exists> \<rho> \<in> nth_pow_wits m. \<forall> x \<in> fibre_set cell. pow_res m (r x) = pow_res m \<rho>))"
    using poly_cell_decomp assms unfolding prepare_cell_pow_res_def by blast 
  then have 0: "(\<forall> x \<in> fibre_set \<C>'. r x = \<zero> ) \<or> (\<exists> \<rho> \<in> nth_pow_wits m. \<forall> x \<in> fibre_set \<C>'. pow_res m (r x) = pow_res m \<rho>)"
    using assms by blast  
  have fibre_set_closed: "fibre_set \<C>' \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms 
    by (metis SA_car affine_alg_set_empty affine_alg_set_empty_set is_cell_conditionE'(1) 
        is_cell_decompE(3) is_cell_decompE(4) is_semialgebraic_closed prepare_cell_pow_res_decomp)
  show ?thesis proof(cases "\<forall> x \<in> fibre_set \<C>'. r x = \<zero> ")
    case True
    hence "fibre_set \<C>' \<subseteq> r\<inverse>\<^bsub>n\<^esub>{\<zero>}" 
      unfolding evimage_def using fibre_set_closed by blast
    then show ?thesis by blast 
  next
    case False
    then obtain \<rho> where rho_def: "\<rho> \<in> nth_pow_wits m \<and> (\<forall> x \<in> fibre_set \<C>'. pow_res m (r x) = pow_res m \<rho>)"
      using 0 by blast 
    have "\<forall> x \<in> fibre_set \<C>'. r x \<in>  pow_res m \<rho>" proof fix x assume A: "x \<in> fibre_set \<C>'" 
      then have 2: "pow_res m (r x) = pow_res m \<rho>"
        using rho_def by blast 
      have "\<rho> \<in> pow_res m (r x )"
        using pow_res_refl[of \<rho> m] assms(5) nth_pow_wits_closed(3) rho_def unfolding nonzero_def 2 
        by blast
      then obtain y where y_def: "y \<in> nonzero Q\<^sub>p \<and>   \<rho> = r x \<otimes> y [^] m" 
        unfolding pow_res_def by blast 
      have rho_nonzero: "\<rho> \<in> nonzero Q\<^sub>p"
        using rho_def nth_pow_wits_closed assms by blast 
      have 0: "is_cell_condition \<C>'"
        using assms is_cell_decompE(3) prepare_cell_pow_res_decomp by blast
      have 1: "arity \<C>' = n"
        using assms prepare_cell_pow_res_decomp is_cell_decompE(4) by blast
      have rx_closed: "r x \<in> carrier Q\<^sub>p"
        using 0 1 A assms fibre_set_closed SA_car_memE by blast 
      then have "r x \<in> nonzero Q\<^sub>p"
        using rho_nonzero assms A fibre_set_closed y_def unfolding nonzero_def 
        by (metis (mono_tags, lifting) Qp.integral_iff Qp.nat_pow_closed mem_Collect_eq)       
      thus " r x \<in> pow_res m \<rho>"
        using 2 rho_def fibre_set_closed assms(1) pow_res_refl[of "r x " m] assms(5) unfolding nonzero_def  by blast
    qed
    then have "(\<exists>\<rho>\<in>nth_pow_wits m. fibre_set \<C>' \<subseteq> r \<inverse>\<^bsub>n\<^esub> pow_res m \<rho>)"
      unfolding evimage_def using rho_def 
      by (smt Int_iff fibre_set_closed subset_iff vimage_eq)
    then show ?thesis using rho_def by blast  
  qed
qed

lemma pow_res_eq_statement:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "a \<in> pow_res n b \<equiv> pow_res n a = pow_res n b"
proof- 
  have 0: "a \<in> pow_res n b \<Longrightarrow> pow_res n b = pow_res n a"
    by(intro equal_pow_resI assms, auto)
  have 1: "pow_res n a = pow_res n b \<Longrightarrow> a \<in> pow_res n b"
    using pow_res_refl assms by auto 
  show "a \<in> pow_res n b \<equiv> pow_res n a = pow_res n b" 
    using 0 1  by (smt (verit, del_insts)) 
qed

lemma equivalent_pow_res_sets:
  assumes "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>M\<^esup>) \<Longrightarrow> f x \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows " {x \<in> carrier (Q\<^sub>p\<^bsup>M\<^esup>). pow_res n (f x) = pow_res n b} = 
          {x \<in> carrier (Q\<^sub>p\<^bsup>M\<^esup>). f x \<in> pow_res n b}"
  apply(rule equalityI'')
  unfolding mem_Collect_eq using assms pow_res_eq_statement by auto 

lemma(in denef_II) cell_decomp_nth_pow_refinement:
  assumes "n > 0"
  assumes "m > 0"  
  assumes "r \<in> carrier (UP (SA n))"
  assumes "deg (SA n) r \<le> d"
  shows "\<exists> S. (is_cell_decomp n S (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) \<and> 
              (\<forall>A \<in> S. \<exists>u h k. SA_poly_factors p n m r (center A) (condition_to_set A) u h k \<and>
                  (fibre_set A \<subseteq> (h\<inverse>\<^bsub>n\<^esub>{\<zero>}) \<or> 
                  (\<exists> \<alpha> \<in> nth_pow_wits m. (fibre_set A) \<subseteq> h\<inverse>\<^bsub>n\<^esub>(pow_res m \<alpha>)
                  ))
              ))"
proof-
  have "finite {r} \<and> (\<forall>P\<in>{r}. P \<in> carrier (UP (SA n)) \<and> deg (SA n) P \<le> d)"
    using assms by blast
  then obtain S where S_def: "is_cell_decomp n S (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) \<and> 
                           (\<forall>A \<in> S.  \<exists>u h k. SA_poly_factors p n m r (center A) (condition_to_set A) u h k)"
    using assms cell_decomp[of "{r}" n m] by (meson singletonI)
  show ?thesis 
    apply(rule refine_each_cell[of n S])
    using S_def apply blast 
  proof- 
    fix A assume A: "A \<in> S"
    obtain h where h_def: "\<exists>u k. SA_poly_factors p n m r (center A) (condition_to_set A) u h k"
      using A S_def by blast 
    have h_semialg: "h \<in> carrier (SA n)"
      using h_def  SA_poly_factors_closure(4) by blast   
    obtain S' where  S'_def: "S' = prepare_cell_pow_res n m A h"
      by blast 
    have 1: "is_cell_decomp n S' (condition_to_set A)"
      using prepare_cell_pow_res_decomp assms h_semialg unfolding S'_def  
      using A S_def is_cell_decompE(3) is_cell_decompE(4) by auto    
    have 2: "\<And>\<C>. \<C> \<in> S' \<Longrightarrow> 
          fibre_set \<C> \<subseteq> h\<inverse>\<^bsub>n\<^esub>{\<zero>} \<or> (\<exists> \<rho> \<in> nth_pow_wits m. fibre_set \<C> \<subseteq> h \<inverse>\<^bsub>n\<^esub>(pow_res m \<rho>))"
      using 1 assms prepare_cell_pow_res_decomp_fibre_set[of _ n _ m] S'_def h_semialg 
      by (metis A S_def is_cell_decompE(3) is_cell_decompE(4)) 
    have 3: " (\<forall>A\<in> S'. \<exists>u h k.
                   SA_poly_factors p n m r (center A) (condition_to_set A) u h k \<and>
                   (fibre_set A \<subseteq> h \<inverse>\<^bsub>n\<^esub> {\<zero>} \<or>
                    (\<exists>\<alpha>\<in>nth_pow_wits m. fibre_set A \<subseteq> h \<inverse>\<^bsub>n\<^esub> pow_res m \<alpha>)))"
    proof fix \<A> assume A': "\<A> \<in> S'"
    have 40: " fibre_set \<A> \<subseteq> h\<inverse>\<^bsub>n\<^esub>{\<zero>} \<or> (\<exists> \<rho> \<in> nth_pow_wits m. fibre_set \<A> \<subseteq> h \<inverse>\<^bsub>n\<^esub>(pow_res m \<rho>))"
      using 2[of \<A>] A' by blast
    have 41: "\<exists>u k. SA_poly_factors p n m r (center \<A>) (condition_to_set \<A>) u h k"
    proof-
      obtain u k where uk_def: "SA_poly_factors p n m r (center A) (condition_to_set A) u h k"
        using h_def by blast 
      have "SA_poly_factors p n m r (center \<A>) (condition_to_set \<A>) u h k"
      proof(rule SA_poly_factorsI')
        show "condition_to_set \<A> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
          using  A' 1 is_cell_decomp_subset 
          by (metis cell_condition_to_set_subset is_cell_decompE(4)) 
        show " u \<in> (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
          using uk_def SA_poly_factorsE by (metis SA_poly_factors_closure(2)) 
        show "center \<A> \<in> carrier (SA n)"
          using uk_def SA_poly_factorsE 
          by (metis "1" A' SA_poly_factors_def is_cell_decompE(4) padic_fields.condition_decomp' padic_fields.is_cell_conditionE(2) padic_fields.is_cell_decompE(3)) 
        show "h \<in> carrier (SA n)"
          using h_semialg by blast
        show "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow>
           t \<in> carrier Q\<^sub>p \<Longrightarrow> t # x \<in> condition_to_set \<A> \<Longrightarrow> val (u (t # x)) = 0"
          by (meson A  uk_def  "1" A' SA_poly_factorsE(1) is_cell_decomp_subset subsetD)           
        have 00: "center \<A> = center A"
          using A A' assms  unfolding S'_def prepare_cell_pow_res_def refine_fibres_def   
          using center.simps imageE by blast           
        have 11:"condition_to_set \<A> \<subseteq> condition_to_set A"
          using A assms  unfolding S'_def prepare_cell_pow_res_def refine_fibres_def   
          using "1"  is_cell_decomp_subset A' by blast           
        show "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> t \<in> carrier Q\<^sub>p \<Longrightarrow> t # x \<in> condition_to_set \<A> \<Longrightarrow>
             SA_poly_to_Qp_poly n x r \<bullet> t = u (t # x) [^] m \<otimes> h x \<otimes> (t \<ominus> center \<A> x) [^] k"
          using 00 11 A SA_poly_factorsE(2)[of n m r "center A" "condition_to_set A" u h] uk_def
          by (smt subsetD)
      qed          
      then show ?thesis by blast 
    qed
    show "\<exists>u h k.
            SA_poly_factors p n m r (center \<A>) (condition_to_set \<A>) u h k \<and>
            (fibre_set \<A> \<subseteq> h \<inverse>\<^bsub>n\<^esub> {\<zero>} \<or> (\<exists>\<alpha>\<in>nth_pow_wits m. fibre_set \<A> \<subseteq> h \<inverse>\<^bsub>n\<^esub> pow_res m \<alpha>))"
      using 40 41 by blast 
    qed
    show "\<exists>S. is_cell_decomp n S (condition_to_set A) \<and>
             (\<forall>A\<in>S. \<exists>u h k.
                        SA_poly_factors p n m r (center A) (condition_to_set A) u h k \<and>
                        (fibre_set A \<subseteq> h \<inverse>\<^bsub>n\<^esub> {\<zero>} \<or>
                         (\<exists>\<alpha>\<in>nth_pow_wits m. fibre_set A \<subseteq> h \<inverse>\<^bsub>n\<^esub> pow_res m \<alpha>)))"
      using 1 2 3 by blast
  qed
qed
end
(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>A Key Lemma on Multivariable Polynomial Division\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>The key ingredient of the proof of our criterion is established in this subsection. Given a 
semialgebraic polynomial $f(t,y)$ of abitrary degree, with $y$ a variable over $\mathbb{Q}_p^k$ , 
and a semialgebraic polynomial $g(t,x)$ (with $x \in \mathbb{Q}_p^m$) in one variable $t$ where 
$\text{ deg }(g) \leq d+1$, we can construe both of these as polynomials in the variable $t$ with 
coefficients in $SA(m+k)$. We can then perform euclidean division in this ring to obtain a 
polynomial $r(t,x,y)$ of degree $\leq d$ and $q(t,x,y)$ where:
\[
f(t,y) = q(t,x,y)g(t,x) + r(t,x,y).
\]
If, as in the context of our main result of this section, we know that $g(\xi(x),x) = 0$ for all 
$x \in \mathbb{Q}_p^m$, then we know that for all $x,y$:
\[
f(\xi(x),y) = r(\xi(x), x, y). 
\]
In this way, by adding some extra variables, we can replace the description of a basic semialgebraic 
set in terms of a polynomial $f(t,x)$ with a description in terms of a polynomial $r(t,x,y)$ of 
bounded degree. This is the content of the result in this section called 
\texttt{partial\_pullback\_division\_lemma}.\<close>

context padic_fields
begin

definition var_shift where
"var_shift (n::nat) k g =  Qp.relabel_vars {..<n} {..<n + k} (\<lambda> i. i + k) g"

lemma var_shift_closed:
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "var_shift n k g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n+ k\<^esub>])"
  unfolding var_shift_def coord_ring_def 
  apply(rule Qp.relabel_vars_closed)  
  apply (meson Pi_I add_less_cancel_right lessThan_iff)
  using assms unfolding coord_ring_def by blast 

lemma var_shift_relabel_function:
"(\<lambda> i. i + k) \<in> {..<(n::nat)}  \<rightarrow> {..< n + k}" 
  by (meson Pi_I add_less_cancel_right lessThan_iff)

lemma var_shift_is_hom:
"var_shift n k \<in> ring_hom (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (Q\<^sub>p[\<X>\<^bsub>n+k\<^esub>])"
  using var_shift_relabel_function Qp.relabel_vars_is_morphism(1) ring_hom_ring.homh
  unfolding var_shift_def  coord_ring_def  
  by metis

lemma var_shift_add: 
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "var_shift n k (f \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub>g) = var_shift n k g  \<oplus> \<^bsub> Q\<^sub>p[\<X>\<^bsub>n+ k\<^esub>]\<^esub> var_shift n k f"
  using assms var_shift_is_hom ring_hom_add 
  by (metis (no_types, lifting) MP.add.m_comm)

lemma var_shift_mult: 
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "var_shift n k (f \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub>g) = var_shift n k g  \<otimes> \<^bsub> Q\<^sub>p[\<X>\<^bsub>n+ k\<^esub>]\<^esub> var_shift n k f"
  using assms var_shift_is_hom 
  by (metis (no_types, lifting) MP.m_comm ring_hom_mult)

lemma var_shift_smult: 
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "var_shift n k (a \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub>f) = a \<odot>\<^bsub> Q\<^sub>p[\<X>\<^bsub>n+ k\<^esub>]\<^esub> var_shift n k f"
  using Qp.relabel_vars_smult assms var_shift_relabel_function
  unfolding coord_ring_def var_shift_def 
  by metis

lemma var_shift_indexed_constant: 
  assumes "a \<in> carrier Q\<^sub>p"
  shows "var_shift n k (Qp.indexed_const a) = Qp.indexed_const a"
  using assms var_shift_relabel_function[of k n] Qp.relabel_vars_is_morphism(3)[of "\<lambda>i. i + k" "{..<n}" "{..<n+k}"  a]
  unfolding coord_ring_def var_shift_def by blast 

lemma var_shift_pvar: 
  assumes "i < n"
  shows "var_shift n k (pvar Q\<^sub>p i) = pvar Q\<^sub>p (i + k)"
  using assms var_shift_relabel_function[of k n] Qp.relabel_vars_is_morphism(2)[of "\<lambda>i. i + k" "{..<n}" "{..<n+k}"  ]
  unfolding coord_ring_def var_shift_def by blast 

lemma var_shift_eval:
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes  "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "b \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  shows "eval_at_point Q\<^sub>p (b@a) (var_shift n k g) = eval_at_point Q\<^sub>p a g"
proof(rule coord_ring_car_induct[of g n])
  have ba_closed: "b @ a \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
    using assms cartesian_power_concat(2) by blast
  show "g \<in> carrier (Q\<^sub>p [\<X>\<^bsub>n\<^esub>])"
    using assms by blast 
  show "\<And>c. c \<in> carrier Q\<^sub>p \<Longrightarrow> eval_at_point Q\<^sub>p (b @ a) (var_shift n k (Qp.indexed_const c)) = eval_at_point Q\<^sub>p a (Qp.indexed_const c)"
    using assms var_shift_indexed_constant ba_closed   by (metis eval_at_point_const)
  show "\<And>p q. p \<in> carrier (Q\<^sub>p [\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
           q \<in> carrier (Q\<^sub>p [\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
           eval_at_point Q\<^sub>p (b @ a) (var_shift n k p) = eval_at_point Q\<^sub>p a p \<Longrightarrow>
           eval_at_point Q\<^sub>p (b @ a) (var_shift n k q) = eval_at_point Q\<^sub>p a q \<Longrightarrow>
           eval_at_point Q\<^sub>p (b @ a) (var_shift n k (p \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> q)) = eval_at_point Q\<^sub>p a (p \<oplus>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> q)"
    using assms ba_closed var_shift_add eval_at_point_add  MP.add.m_comm var_shift_closed by presburger
  show "\<And>p i. p \<in> carrier (Q\<^sub>p [\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
           i < n \<Longrightarrow>
           eval_at_point Q\<^sub>p (b @ a) (var_shift n k p) = eval_at_point Q\<^sub>p a p \<Longrightarrow>
           eval_at_point Q\<^sub>p (b @ a) (var_shift n k (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p i)) = eval_at_point Q\<^sub>p a (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p i)"
  proof- fix i p assume A: "p \<in> carrier (Q\<^sub>p [\<X>\<^bsub>n\<^esub>])" "i < n"
           "eval_at_point Q\<^sub>p (b @ a) (var_shift n k p) = eval_at_point Q\<^sub>p a p"
    have 0: "(var_shift n k (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p i)) = (var_shift n k p) \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n+k\<^esub>]\<^esub> pvar Q\<^sub>p (i + k)"
      using var_shift_mult var_shift_pvar A assms 
      by (metis MP.m_comm local.pvar_closed)
    hence 1: "eval_at_point Q\<^sub>p (b @ a) (var_shift n k (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p i)) = eval_at_point Q\<^sub>p a p \<otimes> (b@a)!(i+k)"
      using A var_shift_closed eval_pvar eval_at_point_mult[of "b@a" "n + k" "var_shift n k p" "pvar Q\<^sub>p (i + k)"] 
      by (metis add.commute ba_closed eval_at_point_indexed_pmult nat_add_left_cancel_less pvar_indexed_pmult)
    hence 2: "eval_at_point Q\<^sub>p (b @ a) (var_shift n k (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p i)) = eval_at_point Q\<^sub>p a p \<otimes> a!i"
      using assms cartesian_power_car_memE by (metis add.commute nth_append_length_plus)
    show "eval_at_point Q\<^sub>p (b @ a) (var_shift n k (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p i)) = eval_at_point Q\<^sub>p a (p \<otimes>\<^bsub>Q\<^sub>p [\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p i)"
      using 2 assms ba_closed var_shift_pvar[of i n] eval_pvar var_shift_mult pvar_closed A eval_at_point_mult 
      by metis 
  qed
qed

lemma(in UP_ring) lcoeff_Lcf:
  assumes "f \<in> carrier P"
  shows "lcoeff f = lcf f"
  unfolding P_def
  using assms  coeff_simp[of f] by metis

lemma multivar_poly_factor:
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
  assumes  "g \<noteq> \<zero>\<^bsub>UP (SA n)\<^esub>"
  obtains  q r k where "q \<in> carrier (UP (SA n)) \<and> r \<in> carrier (UP (SA n)) \<and>
        (UP_ring.lcf(SA n)  g)[^]\<^bsub>SA n\<^esub>(k::nat)\<odot>\<^bsub>UP (SA n)\<^esub>f = g \<otimes>\<^bsub>UP (SA n)\<^esub> q \<oplus>\<^bsub>UP (SA n)\<^esub> r \<and>  
        (r  = \<zero>\<^bsub>UP (SA n)\<^esub> \<or> deg (SA n) r < deg (SA n) g)"
  using assms UP_cring.long_div_theorem[of "SA n" g f]
  using SA_is_cring UP_ring.lcoeff_Lcf[of "SA n" g] 
    unfolding UP_cring_def UP_ring_def
  by (metis  cring.axioms(1) that)
  
lemma SA_is_algebra:
  shows "algebra (SA n) (UP (SA n))"
  by (simp add: SA_is_cring UP_cring.UP_algebra UP_cring.intro )

lemma UP_SA_smult_closed:
  assumes "a \<in> carrier (SA n)"
  assumes "g \<in> carrier (UP (SA n))"
  shows "a \<odot>\<^bsub>UP (SA n)\<^esub> g \<in> carrier (UP (SA n))"
  using SA_is_algebra assms  unfolding algebra_def 
  by (meson module.smult_closed)

lemma multivar_poly_factor'':
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA n))"
  assumes "g \<noteq> \<zero>\<^bsub>UP (SA n)\<^esub>"
  assumes "UP_ring.lcf (SA n) g \<in> Units (SA n)"
  shows  "\<exists>q r. q \<in> carrier (UP (SA n)) \<and> r \<in> carrier (UP (SA n)) \<and>
        f = q \<otimes>\<^bsub>UP (SA n)\<^esub> g \<oplus>\<^bsub>UP (SA n)\<^esub> r \<and>  (r  = \<zero>\<^bsub>UP (SA n)\<^esub> \<or> deg (SA n) r < deg (SA n) g)"
proof-
  obtain q r k where A: "q \<in> carrier (UP (SA n)) \<and> r \<in> carrier (UP (SA n)) \<and>
        ((UP_ring.lcf (SA n)) g)[^]\<^bsub>SA n\<^esub>(k::nat)\<odot>\<^bsub>UP (SA n)\<^esub>f = g \<otimes>\<^bsub>UP (SA n)\<^esub> q \<oplus>\<^bsub>UP (SA n)\<^esub> r \<and>  (r  = \<zero>\<^bsub>UP (SA n)\<^esub> \<or> deg (SA n) r < deg (SA n) g)"
    using assms multivar_poly_factor  by blast 
  obtain a where a_def: "a = UP_ring.lcf (SA n)  g"
    by blast 
  have "a \<in> Units (SA n)"
    using a_def assms by blast 
  hence  0: "a[^]\<^bsub>SA n\<^esub> k \<in> Units (SA n)"
    using SA_is_monoid[of n] assms monoid.Units_pow_closed[of "SA n" a k]
    by blast 
  have 1: "(a[^]\<^bsub>SA n\<^esub> k)\<odot>\<^bsub>UP (SA n)\<^esub>f = g \<otimes>\<^bsub>UP (SA n)\<^esub> q \<oplus>\<^bsub>UP (SA n)\<^esub> r \<and>  (r  = \<zero>\<^bsub>UP (SA n)\<^esub> \<or> deg (SA n) r < deg (SA n) g)"
    using A a_def  by blast   
  have 2: "(inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub>((a[^]\<^bsub>SA n\<^esub> k)\<odot>\<^bsub>UP (SA n)\<^esub>f) = f"
  proof-
    have 20: "(inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub>((a[^]\<^bsub>SA n\<^esub> k)\<odot>\<^bsub>UP (SA n)\<^esub>f) = ((inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<otimes>\<^bsub>SA n\<^esub>(a[^]\<^bsub>SA n\<^esub> k))\<odot>\<^bsub>UP (SA n)\<^esub>f "
      using UP_ring.UP_smult_assoc1[of "SA n" "inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)" "a[^]\<^bsub>SA n\<^esub> k" f] 
      unfolding UP_ring_def using SA_is_ring monoid.Units_closed[of "SA n"] SA_is_monoid
      using "0" SA_Units_inv_closed assms(1) assms(2) by presburger
    have 21: "((inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<otimes>\<^bsub>SA n\<^esub>(a[^]\<^bsub>SA n\<^esub> k)) = \<one>\<^bsub>SA n\<^esub>"
      using 0 SA_is_monoid[of n] assms SA_Units_memE(2) by blast
    thus ?thesis using assms UP_ring.UP_smult_one[of "SA n" f] SA_is_ring 
      unfolding UP_ring_def 
      by (simp add: \<open>f \<in> carrier (UP (SA n))\<close> \<open>g (deg (SA n) g) \<in> Units (SA n)\<close> \<open>g \<in> carrier (UP (SA n))\<close> "20")      
  qed
  have 3: "inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k) \<in> carrier (SA n)"
    using 0 SA_Units_inv_closed assms(1) by blast
  have 4: "(inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> (g \<otimes>\<^bsub>UP (SA n)\<^esub> q \<oplus>\<^bsub>UP (SA n)\<^esub> r) = 
            ((inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> g) \<otimes>\<^bsub>UP (SA n)\<^esub> q \<oplus>\<^bsub>UP (SA n)\<^esub> (inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> r"
    using 3 A UP_ring.UP_smult_r_distr[of "SA n"] UP_ring.UP_smult_assoc2[of "SA n"] SA_is_ring
    unfolding UP_ring_def 
    by (metis UP_SA_n_is_ring assms  ring.ring_simprules(5))
  have 5: "((inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> g) \<otimes>\<^bsub>UP (SA n)\<^esub> q = ((inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> q) \<otimes>\<^bsub>UP (SA n)\<^esub> g"  
    using A 3 SA_is_cring 
    by (metis (no_types, lifting) UP_SA_n_is_cring UP_cring.UP_algebra UP_cring.intro algebra.smult_assoc2 assms  cring.cring_simprules(14))
  hence 6: "(inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> (g \<otimes>\<^bsub>UP (SA n)\<^esub> q \<oplus>\<^bsub>UP (SA n)\<^esub> r) = 
            ((inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> q) \<otimes>\<^bsub>UP (SA n)\<^esub> g \<oplus>\<^bsub>UP (SA n)\<^esub> (inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> r"
    by (simp add: "4")
  obtain q' where q'_def: "q' = (inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> q"
    by blast 
  obtain r' where r'_def: "r' = (inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> r"
    by blast 
  have q'_closed: "q' \<in> carrier (UP (SA n))"
    using q'_def A 3 UP_SA_smult_closed assms(1) by blast
  have r'_closed: "r' \<in> carrier (UP (SA n))"
    using r'_def A 3 UP_SA_smult_closed assms(1) by blast
  have r'_deg: "r' = \<zero>\<^bsub>UP (SA n)\<^esub> \<or>  deg (SA n) r' \<le> deg (SA n) r"
    using A r'_def 3 r'_closed UP_ring.deg_smult_ring[of "SA n"] 
    by (meson SA_is_ring UP_ring.deg_smult_decr UP_ring_def assms(1))
  have 7: " f = (inv\<^bsub>SA n\<^esub> (a[^]\<^bsub>SA n\<^esub> k)) \<odot>\<^bsub>UP (SA n)\<^esub> (g \<otimes>\<^bsub>UP (SA n)\<^esub> q \<oplus>\<^bsub>UP (SA n)\<^esub> r) "
    using "1" "2" by auto
  hence "f = q' \<otimes>\<^bsub>UP (SA n)\<^esub> g \<oplus>\<^bsub>UP (SA n)\<^esub> r'"
    using "6" q'_def r'_def by blast
  hence "q' \<in> carrier (UP (SA n)) \<and> r' \<in> carrier (UP (SA n)) \<and>
        f = q' \<otimes>\<^bsub>UP (SA n)\<^esub> g \<oplus>\<^bsub>UP (SA n)\<^esub> r' \<and>  (r'  = \<zero>\<^bsub>UP (SA n)\<^esub> \<or> deg (SA n) r' < deg (SA n) g)"
    using A r'_closed q'_closed  r'_deg  
    by (smt "3" SA_is_algebra Suc_lessD UP_SA_n_is_ring algebra.smult_assoc2 assms(1) le_neq_implies_less less_trans_Suc r'_def ring.ring_simprules(25))
  thus ?thesis by blast 
qed

lemma multivar_poly_factor''':
  assumes "f \<in> carrier (UP (SA n))"
  assumes "g \<in> carrier (UP (SA k))"
  assumes "g \<noteq> \<zero>\<^bsub>UP (SA k)\<^esub>"
  assumes "deg (SA k) g > 0"
  assumes "UP_ring.lcf (SA k) g \<in> Units (SA k)"
  assumes "\<xi> \<in> carrier (Fun\<^bsub>k\<^esub> Q\<^sub>p)"
  assumes "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). (SA_poly_to_SA_fun k g) ((\<xi> x)#x) = \<zero>"
  shows  "\<exists>r.  r \<in> carrier (UP (SA (n+k))) \<and> 
                  (deg (SA (n+k)) r < deg (SA k) g) \<and> 
                        (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). \<forall>y \<in> carrier  (Q\<^sub>p\<^bsup>n\<^esup>). 
                              (SA_poly_to_SA_fun n f) (\<xi> x # y) = (SA_poly_to_SA_fun (n+k) r) (\<xi> x # (x@y)))"
proof-
  obtain f0 where f0_def: "f0 = poly_lift_hom (SA n) (SA (n + k)) (drop_apply (n + k) k) f"
    by blast 
  have f0_closed: "f0 \<in> carrier (UP (SA (n +k)))"
    using UP_cring.poly_lift_hom_closed[of "SA n" "SA (n+k)" "drop_apply (n+k) k"  f]
    by (metis SA_is_cring UP_cring.intro add_gr_0 assms(1) assms(2) assms(3) drop_apply_is_hom f0_def)
  obtain g0 where g0_def: "g0 = poly_lift_hom (SA k) (SA (n + k)) (take_apply (n + k) k) g"
    by blast 
  have g0_closed: "g0 \<in> carrier (UP (SA (n + k)))"
    using UP_cring.poly_lift_hom_closed[of "SA k" "SA (n+k)" "take_apply (n+k) k"  g]
       take_apply_is_hom[of n k] SA_is_cring unfolding UP_cring_def 
    by (metis add_pos_pos assms g0_def)
  obtain a where a_def: "a = UP_ring.lcf (SA k) g" 
    by blast 
  have 0: "take_apply (n+k) k a \<in> Units (SA (n+k))"
    using assms a_def take_apply_units[of  a] by blast   
  hence 1: "take_apply (n+k) k a \<noteq> \<zero>\<^bsub>SA (n+k)\<^esub>"
    by (simp add: "0" SA_units_not_zero assms(2))
  hence 2: "take_apply (n + k) k a  = UP_ring.lcf (SA (n+k)) g0"
    using assms UP_cring.poly_lift_hom_lcoeff[of "SA k" "SA (n+k)" "take_apply (n+k) k" g ] 
    unfolding UP_cring_def a_def g0_def
    using padic_fields.SA_is_cring padic_fields.take_apply_is_hom padic_fields_axioms trans_less_add1 
    by presburger
  have 3: "g0 \<noteq> \<zero>\<^bsub>UP (SA (n+k))\<^esub>"
  proof-
    have "g0 (deg (SA (n+k)) g0)  \<noteq> \<zero>\<^bsub>UP (SA (n+k))\<^esub> (deg (SA (n+k)) g0)"
      using 2 1 UP_ring.cfs_zero[of "SA (n+k)" "deg (SA (n+k)) g0"] unfolding UP_ring_def 
      by (simp add: assms(2) padic_fields.SA_is_ring padic_fields_axioms)
    thus ?thesis by blast 
  qed
  have 4: "deg (SA (n+k)) g0 = deg (SA k) g"
    using assms UP_cring.poly_lift_hom_degree_eq[of "SA k" "SA (n+k)" "take_apply (n+k) k" g]
    unfolding g0_def UP_cring_def by (metis "1" SA_is_cring a_def add_pos_pos take_apply_is_hom)
  obtain r q where qr_def: 
    "q \<in> carrier (UP (SA (n+k))) \<and> r \<in> carrier (UP (SA (n+k))) \<and>
        f0 = q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0 \<oplus>\<^bsub>UP (SA (n+k))\<^esub> r \<and>  (r  = \<zero>\<^bsub>UP (SA (n+k))\<^esub> \<or> deg (SA (n+k)) r < deg (SA (n+k)) g0)"
    using multivar_poly_factor''[of f0 n g0 ] 
    by (metis (no_types, lifting) "0" "2" "3" add_pos_pos assms(1) assms(2) f0_closed g0_closed multivar_poly_factor'')
  have r_closed: "r \<in> carrier (UP (SA (n+k)))"
    using qr_def by blast 
  have q_closed: "q \<in> carrier (UP (SA (n+k)))"
    using qr_def by blast 
  have f0_decomp: "f0 = q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0 \<oplus>\<^bsub>UP (SA (n+k))\<^esub> r"
    using  qr_def by blast 
  have 5: " (r  = \<zero>\<^bsub>UP (SA (n+k))\<^esub> \<or> deg (SA (n+k)) r < deg (SA k) g)"
    using 4 qr_def g0_def by linarith
  have r_deg: "deg (SA (n+k)) r < deg (SA k) g"
    apply(cases "r = \<zero>\<^bsub>UP (SA (n+k))\<^esub>")
    using UP_ring.deg_zero[of "SA (n+k)"] unfolding UP_ring_def 
    apply (simp add: SA_is_ring assms)
      using 5 by blast      
  have 6: "\<And>x y. x \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>) \<Longrightarrow> y \<in> carrier Q\<^sub>p \<Longrightarrow> 
          SA_poly_to_SA_fun (n+k) f0 (y#x) =   SA_poly_to_SA_fun (n+k) (q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0 \<oplus>\<^bsub>UP (SA (n+k))\<^esub> r) (y#x)"
    using f0_decomp  by blast 
  have 7: " SA_poly_to_SA_fun (n+k) (q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0 \<oplus>\<^bsub>UP (SA (n+k))\<^esub> r) = 
            SA_poly_to_SA_fun (n+k) (q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0) \<oplus>\<^bsub>SA (n+k+1)\<^esub> SA_poly_to_SA_fun (n+k) r"
 
  proof-
    have "q \<otimes>\<^bsub>UP (SA (n + k))\<^esub> g0 \<in> carrier (UP (SA (n + k)))"
      by (meson UP_SA_n_is_ring add_pos_pos assms(1) assms(2) g0_closed qr_def ring.ring_simprules(5))
    thus ?thesis 
      using q_closed r_closed g0_closed SA_poly_to_SA_fun_add[of  "q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0""n+k" r]
      by (metis add.commute add_gr_0 assms(1) plus_1_eq_Suc)
  qed
  hence 8: " SA_poly_to_SA_fun (n+k) (q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0 \<oplus>\<^bsub>UP (SA (n+k))\<^esub> r) = 
            (SA_poly_to_SA_fun (n+k) q \<otimes>\<^bsub>SA (n+k+1)\<^esub>SA_poly_to_SA_fun (n+k)  g0) \<oplus>\<^bsub>SA (n+k+1)\<^esub> SA_poly_to_SA_fun (n+k) r"
    using SA_poly_to_SA_fun_mult[of q "n+k"  g0] g0_closed q_closed 
    by (metis add.commute add_gr_0 assms(1) plus_1_eq_Suc)
  have 9: " (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). \<forall>y \<in> carrier  (Q\<^sub>p\<^bsup>n\<^esup>). 
        (SA_poly_to_SA_fun n f) (\<xi> x # y) = (SA_poly_to_SA_fun (n+k) r) (\<xi> x # (x@y)))"
  proof fix x assume x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
    show "\<forall>y\<in>carrier (Q\<^sub>p\<^bsup>n\<^esup>). SA_poly_to_SA_fun n f (\<xi> x # y) = SA_poly_to_SA_fun (n + k) r (\<xi> x # x @ y)"
    proof fix y assume y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      show "SA_poly_to_SA_fun n f (\<xi> x # y) = SA_poly_to_SA_fun (n + k) r (\<xi> x # x @ y)"
      proof-
        have 0: "\<xi> x#y \<in> carrier (Q\<^sub>p\<^bsup>n+1\<^esup>)"
          using y_closed x_closed assms cartesian_power_cons 
          by (metis Qp.function_ring_car_memE)
        have 1: "(\<xi> x # x @ y) \<in> carrier (Q\<^sub>p\<^bsup>n+k+1\<^esup>)"
          using y_closed x_closed assms cartesian_power_cons 
          by (metis Qp.function_ring_car_memE cartesian_power_concat(2))
        have 2: "SA_poly_to_SA_fun n f (\<xi> x # y) = (SA_poly_to_Qp_poly n y f)\<bullet>(\<xi> x)"
          using SA_poly_to_SA_fun_formula[of f n "y" "\<xi> x"]
              Qp.function_ring_car_memE assms x_closed y_closed by blast
        have 3: "x @ y \<in> carrier (Q\<^sub>p\<^bsup>n + k\<^esup>)" 
          using cartesian_power_concat(2) x_closed y_closed by blast
        have 4: "\<xi> x \<in> carrier Q\<^sub>p"
          using assms Qp.function_ring_car_memE[of \<xi> k] x_closed by blast 
        hence 5: "SA_poly_to_SA_fun (n+k) f0 (\<xi> x # x@ y) = (SA_poly_to_Qp_poly (n+k) (x@y) f0)\<bullet>(\<xi> x)"
          using 3 SA_poly_to_SA_fun_formula[of  f0 "n+k" "x@y" "\<xi> x"] f0_closed 
          using assms(1) by linarith
        have 6: "(SA_poly_to_Qp_poly n y f) = (SA_poly_to_Qp_poly (n+k) (x@y) f0)"
        proof fix j
          show "(SA_poly_to_Qp_poly n y f) j = (SA_poly_to_Qp_poly (n+k) (x@y) f0) j"
          proof-
            have 0: "(SA_poly_to_Qp_poly n y f) j = (f j) y"
              using SA_poly_to_Qp_poly_coeff assms y_closed by blast
            have 1: "(SA_poly_to_Qp_poly (n+k) (x@y) f0) j = (f0 j) (x@y)"
              by (meson "3" SA_poly_to_Qp_poly_coeff assms(1) f0_closed trans_less_add1)
            have 2: "(f0 j) (x@y) = (drop_apply (n + k) k) (f j) (x @ y)"
              using UP_cring.poly_lift_hom_cf[of "SA n" "SA (n+k)" "drop_apply (n + k) k" f j] 
                   drop_apply_is_hom[of n k] assms                              
              unfolding f0_def 
              by (metis SA_is_UP_cring SA_is_cring add_pos_pos)
            have 3: "drop_apply (k + n) k (f j) (x @ y) = f j y"
              using drop_apply_apply[of "f j" n x k y] x_closed y_closed 
                    SA_is_ring[of n] assms(1) assms(2) assms(3)
                    UP_ring.cfs_closed[of "SA n" f j]
              unfolding UP_ring_def  by blast
            show ?thesis
              using 0 1 2  assms              
              by (metis "3" add.commute)
          qed
        qed
        have 7: "(SA_poly_to_Qp_poly n y f) = (SA_poly_to_Qp_poly (n+k) (x@y) ( q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0 \<oplus>\<^bsub>UP (SA (n+k))\<^esub> r))"
          using 6 f0_decomp by blast
        have 8: "(SA_poly_to_Qp_poly n y f) = (SA_poly_to_Qp_poly (n+k) (x@y) ( q \<otimes>\<^bsub>UP (SA (n+k))\<^esub> g0))
                                     \<oplus>\<^bsub>UP Q\<^sub>p\<^esub>((SA_poly_to_Qp_poly (n+k) (x@y) r))"
        proof-
          have "q \<otimes>\<^bsub>UP (SA (n + k))\<^esub> g0 \<in> carrier (UP (SA (n + k)))"
            by (meson UP_SA_n_is_ring add_pos_pos assms(1) assms(2) g0_closed q_closed ring.ring_simprules(5))
          thus ?thesis 
            using 7 SA_poly_to_Qp_poly_add[of  "x @ y""n+k" "q \<otimes>\<^bsub>UP (SA (n + k))\<^esub> g0" r]
            using "3" add_gr_0 assms(1) r_closed by presburger
        qed
        hence 9: "(SA_poly_to_Qp_poly n y f) = SA_poly_to_Qp_poly (n+k) (x@y) q \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> (SA_poly_to_Qp_poly (n+k) (x@y)  g0)
                                     \<oplus>\<^bsub>UP Q\<^sub>p\<^esub>(SA_poly_to_Qp_poly (n+k) (x@y) r)"
          using SA_poly_to_Qp_poly_mult[of  "x@y""n+k" q g0]  q_closed g0_closed  "3" add_gr_0 assms(1)
          by presburger
        have 10: "(SA_poly_to_Qp_poly n y f)\<bullet>(\<xi> x) = (SA_poly_to_Qp_poly (n+k) (x@y) q \<bullet> (\<xi> x)) \<otimes> ((SA_poly_to_Qp_poly (n+k) (x@y)  g0)\<bullet> (\<xi> x) )
                                     \<oplus> (SA_poly_to_Qp_poly (n+k) (x@y) r) \<bullet> (\<xi> x) "
        proof-
          have 100: "SA_poly_to_Qp_poly (n+k) (x@y) q \<in> carrier (UP Q\<^sub>p)"
            using SA_poly_to_Qp_poly_closed 3 q_closed by (meson add_pos_pos assms(1) assms(2))
          have 101: "SA_poly_to_Qp_poly (n+k) (x@y) g0 \<in> carrier (UP Q\<^sub>p)"
            using SA_poly_to_Qp_poly_closed 3 g0_closed by (meson add_pos_pos assms(1) assms(2))
          have 102: "SA_poly_to_Qp_poly (n+k) (x@y) r \<in> carrier (UP Q\<^sub>p)"
            using SA_poly_to_Qp_poly_closed 3 r_closed by (meson add_pos_pos assms(1) assms(2))
          thus ?thesis using 0 
            using "100" "101" "4" "9" UPQ.UP_mult_closed UPQ.to_fun_mult UPQ.to_fun_plus by presburger
        qed
        have 11: "(SA_poly_to_Qp_poly k x g) = (SA_poly_to_Qp_poly (n+k) (x@y) g0)"
        proof fix j
          show "(SA_poly_to_Qp_poly k x g) j = (SA_poly_to_Qp_poly (n+k) (x@y) g0) j"
          proof-
            have 0: "(SA_poly_to_Qp_poly k x g) j = (g j) x"
              using SA_poly_to_Qp_poly_coeff assms x_closed by blast              
            have 1: "(SA_poly_to_Qp_poly (n+k) (x@y) g0) j = (g0 j) (x@y)"
              by (meson "3" SA_poly_to_Qp_poly_coeff add_pos_pos assms(1) assms(2) g0_closed)
            have 2: "(g0 j) (x@y) = (take_apply (n + k) k) (g j) (x @ y)"
              using UP_cring.poly_lift_hom_cf[of "SA k" "SA (n+k)" "take_apply (n + k) k" g j] 
                   take_apply_is_hom[of n k] assms                              
              unfolding g0_def 
              by (metis SA_is_UP_cring SA_is_cring add_pos_pos)
            have 3: "take_apply (n + k) k (g j) (x @ y) = g j x"
              using take_apply_apply[of "g j" k x  y] x_closed y_closed 
                    SA_is_ring[of k] assms(1) assms(2) assms(3)
                    UP_ring.cfs_closed[of "SA k" g j]
              unfolding UP_ring_def by (metis add.commute assms(4))              
            show ?thesis
              using 0 1 2 3 assms              
              by (metis)
          qed
        qed
        have 12: "(SA_poly_to_Qp_poly k x g)\<bullet>(\<xi> x) = (SA_poly_to_Qp_poly (n+k) (x@y) g0)\<bullet>(\<xi> x)"
          using 11  by presburger
        hence 13: "SA_poly_to_SA_fun k g (\<xi> x#x) = SA_poly_to_SA_fun (n+k) g0 (\<xi> x#(x@y))"
          using 12 SA_poly_to_SA_fun_formula 
          by (metis "3" "4" add_pos_pos assms g0_closed x_closed)
        hence 14: "SA_poly_to_SA_fun (n+k) g0 (\<xi> x#(x@y)) = \<zero>"
          using assms x_closed  by blast 
        have 15: "(SA_poly_to_Qp_poly n y f)\<bullet>(\<xi> x) = (SA_poly_to_Qp_poly (n+k) (x@y) r) \<bullet> (\<xi> x) "
        proof-
          have 140: "SA_poly_to_Qp_poly (n+k) (x@y) q \<bullet> (\<xi> x) \<in> carrier Q\<^sub>p"
            using SA_poly_to_Qp_poly_closed 3 q_closed 4 
            by (meson UPQ.to_fun_closed add_pos_pos assms(1) assms(2))
          have 141: "(SA_poly_to_Qp_poly (n+k) (x@y) r) \<bullet> (\<xi> x) \<in> carrier Q\<^sub>p"
            using SA_poly_to_Qp_poly_closed 3 r_closed 4 
            by (meson UPQ.to_fun_closed add_pos_pos assms(1) assms(2))
          have 142: "SA_poly_to_Qp_poly (n + k) (x @ y) q \<bullet> \<xi> x \<otimes> (SA_poly_to_Qp_poly (n + k) (x @ y) g0 \<bullet> \<xi> x) = \<zero>"
            using 140 14 
            by (metis "12" "4" Qp.integral_iff Qp.zero_closed SA_poly_to_SA_fun_formula assms x_closed)
          thus ?thesis using 10 12 141 Qp.l_zero by presburger
        qed
        thus ?thesis using  SA_poly_to_SA_fun_formula "2" "3" "4" assms(2) r_closed trans_less_add2 
          by presburger
      qed
    qed
  qed
  thus ?thesis  using 9 r_deg r_closed 
    by blast
qed

theorem partial_pullback_division_lemma:
  assumes "0 < deg (SA m) F"
  assumes "P \<in> carrier (Q\<^sub>p [\<X>\<^bsub>1 + j\<^esub>])"
  assumes "F \<in> carrier (UP (SA m))"
  assumes "F \<noteq> \<zero>\<^bsub>UP (SA m)\<^esub>"
  assumes "deg (SA m) F > 0"
  assumes "UP_ring.lcf (SA m) F \<in> Units (SA m)"
  assumes "\<xi> \<in> carrier (Fun\<^bsub>m\<^esub> Q\<^sub>p)"
  assumes "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (SA_poly_to_SA_fun m F) ((\<xi> x)#x) = \<zero>"
  shows  "\<exists>r. r \<in> carrier (UP (SA (j+m))) \<and> 
                  (deg (SA (j+m)) r < deg (SA m) F) \<and> 
                       (\<forall>n. ( (partial_pullback m \<xi> j (basic_semialg_set (1 + j) n P)) = 
                        {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (j + m) r (\<xi> (take m a) # take m a @ drop m a) = y [^] n}))"
proof- 
  have 10: "coord_ring_to_UP_SA j P \<in> carrier (UP (SA j))"
      apply(intro coord_ring_to_UP_SA_closed) 
      using assms by (metis plus_1_eq_Suc)
  have 1: "  \<exists>r. r \<in> carrier (UP (SA (j + m))) \<and>  deg (SA (j + m)) r < deg (SA m) F \<and>
      (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<forall>y\<in>carrier (Q\<^sub>p\<^bsup>j\<^esup>). SA_poly_to_SA_fun j (coord_ring_to_UP_SA j P) (\<xi> x # y) = SA_poly_to_SA_fun (j + m) r (\<xi> x # x @ y))"
  proof-
    show ?thesis 
      by(intro multivar_poly_factor'''[of "coord_ring_to_UP_SA j P" j F m \<xi>] assms 10 )
  qed
  then obtain r where r_def: "r \<in> carrier (UP (SA (j + m))) \<and>  deg (SA (j + m)) r < deg (SA m) F \<and>
      (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<forall>y\<in>carrier (Q\<^sub>p\<^bsup>j\<^esup>). SA_poly_to_SA_fun j (coord_ring_to_UP_SA j P) (\<xi> x # y) = SA_poly_to_SA_fun (j + m) r (\<xi> x # x @ y))"
        by blast 
  have r_closed: "r \<in> carrier (UP (SA (j + m)))"
        using r_def by blast 
  have r_deg: "deg (SA (j + m)) r < deg (SA m) F"
    using r_def by blast 
                 
  have r_eval: "\<And>x y. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> y\<in>carrier (Q\<^sub>p\<^bsup>j\<^esup>) \<Longrightarrow> 
                         SA_poly_to_SA_fun j (coord_ring_to_UP_SA j P) (\<xi> x # y) = SA_poly_to_SA_fun (j + m) r (\<xi> x # x @ y)"
    using r_def by blast             
  have r_eval': "\<And>x y. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> y\<in>carrier (Q\<^sub>p\<^bsup>j\<^esup>) \<Longrightarrow> 
                           eval_at_point Q\<^sub>p ((\<xi> x)#y) P = SA_poly_to_SA_fun (j + m) r (\<xi> x # x @ y)"
  proof- fix x y assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "y \<in> carrier (Q\<^sub>p\<^bsup>j\<^esup>)"
        have 0: "SA_poly_to_SA_fun j (coord_ring_to_UP_SA j P) (\<xi> x # y) = SA_poly_to_Qp_poly j y (coord_ring_to_UP_SA j P) \<bullet> \<xi> x"
          by(intro SA_poly_to_SA_fun_formula[of "coord_ring_to_UP_SA j P" j y "\<xi> x"] 10  A
                  Qp.function_ring_car_mem_closed[of \<xi> "carrier (Q\<^sub>p\<^bsup>m\<^esup>)"] assms(7) A  )              
        have 1: " SA_poly_to_SA_fun j (coord_ring_to_UP_SA j P) (\<xi> x # y) =  SA_poly_to_Qp_poly j y (coord_ring_to_UP_SA j P) \<bullet> \<xi> x"
          using SA_poly_to_SA_fun_formula  "0" by blast
        hence 2: "eval_at_point Q\<^sub>p ((\<xi>  x)#y) P = SA_poly_to_SA_fun j (coord_ring_to_UP_SA j P) (\<xi> x # y)"
          using r_eval[of x y]  A assms coord_ring_to_UP_SA_eval plus_1_eq_Suc
          by (metis Qp.function_ring_car_memE) 
        thus " eval_at_point Q\<^sub>p ((\<xi> x)#y) P = SA_poly_to_SA_fun (j + m) r (\<xi> x # x @ y)"using A r_eval by blast
  qed
  have " (\<forall>n. ( (partial_pullback m \<xi> j (basic_semialg_set (1 + j) n P)) = 
                        {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (j + m) r (\<xi> (take m a) # take m a @ drop m a) = y [^] n}))"
  proof fix n 
    have 2: "(partial_pullback m \<xi> j (basic_semialg_set (1 + j) n P)) = {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p (\<xi> (take m a) # drop m a) P = y [^] n}"
        unfolding basic_semialg_set_def partial_pullback_def partial_image_def 
    proof
        show "(\<lambda>xs. \<xi> (take m xs) # drop m xs) \<inverse>\<^bsub>m + j\<^esub> {q \<in> carrier (Q\<^sub>p\<^bsup>1 + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p q P = y [^] n}
    \<subseteq> {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p (\<xi> (take m a) # drop m a) P = y [^] n}"
          apply(rule subsetI) unfolding mem_Collect_eq
          using Groups.add_ac(2) IntE Q\<^sub>p_def Zp_def cartesian_power_cons cartesian_power_drop assms take_closed' evimage_Collect subsetI
          unfolding image_iff evimage_def 
          by blast
        show "{a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p (\<xi> (take m a) # drop m a) P = y [^] n}
    \<subseteq> (\<lambda>xs. \<xi> (take m xs) # drop m xs) \<inverse>\<^bsub>m + j\<^esub> {q \<in> carrier (Q\<^sub>p\<^bsup>1 + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p q P = y [^] n} "
          apply(rule subsetI)
          unfolding mem_Collect_eq evimage_def vimage_def Int_iff
          using   add.commute cartesian_power_cons cartesian_power_drop take_closed 
          by (metis Qp.function_ring_car_mem_closed assms(7) le_add1 plus_1_eq_Suc) 
    qed
    show 3: "(partial_pullback m \<xi> j (basic_semialg_set (1 + j) n P)) = {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (j + m) r (\<xi> (take m a) # take m a @ drop m a) = y [^] n}"
      using 2  r_eval' Collect_cong add.commute cartesian_power_drop le_add2 local.take_closed    
      by (smt (z3) le_add1) 
  qed
  thus ?thesis using r_closed r_deg
    by blast 
qed
end 

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Proving the Main Result\<close>
(**************************************************************************************************)
(**************************************************************************************************)

locale SA_fun_proof = denef_II + 
 fixes g \<xi> m
  assumes g_deg_bound:"deg (SA m) g \<le> Suc d"
  assumes g_deg_pos:"deg (SA m) g > 0"
  assumes g_closed:"g \<in> carrier (UP (SA m))"
  assumes \<xi>_fun:"\<xi> \<in> carrier (Fun\<^bsub>m\<^esub> Q\<^sub>p)"
  assumes g_ltrm_Unit:"UP_ring.lcf (SA m) g \<in> Units (SA m)"
  assumes \<xi>_root:"\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
  assumes val_leq_inv_im: "\<And> k c a. \<lbrakk>c \<in> carrier (SA (m+k)); a \<in> carrier (SA (m+k)) \<rbrakk> \<Longrightarrow> 
                          is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). 
                                     val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)}"
  assumes pow_res_inv_im: "\<And> k c \<alpha> n. \<lbrakk>c \<in> carrier (SA (m+k)); \<alpha> \<in> carrier Q\<^sub>p ; n > 0 \<rbrakk>
                            \<Longrightarrow> is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  (\<xi> (take m x) \<ominus> c x) \<in>  pow_res n \<alpha>}"

context SA_fun_proof
begin

lemma val_eq_inv_im:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "b \<in> carrier (SA (m+k))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = val (b x)}"
proof- 
  obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = val (b x)}"
    by blast 
  obtain S0 where S0_def: "S0 = S \<inter> SA_zero_set (m+k) b"
    by blast 
  obtain S1 where S1_def: "S1 = S \<inter> SA_nonzero_set (m+k) b"
    by blast 
  have S1_semialg: "is_semialgebraic (m+k) S1"
  proof-
    obtain a where a_def: "a = \<pp>[^](-1::int)\<odot>\<^bsub>SA (m+k)\<^esub>b" 
      by blast 
    have a_closed: "a \<in> carrier (SA (m+k))"
      unfolding a_def apply(intro SA_smult_closed assms)  
      by (simp add: p_intpow_closed(1))
    have b_eq: "b = \<pp> \<odot>\<^bsub>SA (m+k)\<^esub> a"
    proof- 
    have 0: "(\<pp> \<otimes> \<pp>[^](-1::int))\<odot>\<^bsub>SA (m+k)\<^esub>b = \<pp> \<odot>\<^bsub>SA (m+k)\<^esub> a "
      unfolding a_def apply(rule SA_smult_assoc)
        apply simp 
      apply (simp add: p_intpow_closed(1)) 
      by (simp add: assms(2)) 
    have 1: "\<pp> \<otimes> \<pp>[^](-1::int) = \<one>"
      by (metis Qp.int_inc_closed Qp.nat_pow_eone int_pow_int ord_p ord_p_nat_pow p_intpow_inv) 
    have 2: "(\<pp> \<otimes> \<pp>[^](-1::int))\<odot>\<^bsub>SA (m+k)\<^esub>b = b"
      unfolding 1 using assms 
      by (meson SA_is_module module.smult_one) 
    show ?thesis using 0 unfolding 2 by auto 
    qed
    have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> val (b x) = val (a x) + 1"
      unfolding b_eq
      using a_closed p_mult_function_val 
      by blast      
    have 1: "\<And> x n. x \<in> SA_nonzero_set (m+k) b \<Longrightarrow> n < val (b x) \<longleftrightarrow> n \<le> val (a x)"
    proof- 
    fix x n assume A: "x \<in> SA_nonzero_set (m+k) b"
    have 10: "b x \<in> nonzero Q\<^sub>p"
      using A unfolding S1_def using assms 
      by (metis Qp.not_nonzero_memE SA_car_closed SA_nonzero_set_memE UnCI zero_set_nonzero_set_covers) 
    have 11: "a x \<in> nonzero Q\<^sub>p"
      unfolding a_def using A assms 10 unfolding S1_def SA_nonzero_set_def Int_iff mem_Collect_eq 
      by (metis "0" Qp.nat_pow_eone Qp.nonzero_closed SA_car_closed a_def eint_diff_imp_eint local.a_closed p_nonzero val_p val_p_nat_pow)     
    have 12: " val (b x) = val (a x) + 1"
      apply(rule 0)
      using A 
      by (metis IntE S1_def UnCI zero_set_nonzero_set_covers) 
    show "(n < val (b x)) = (n \<le> val (a x))"
      unfolding 12 
      using 11 10 
      by (smt (z3) Extended_Int.iless_Suc_eq Extended_Int.less_infinityE Qp.nonzero_closed eint_ord_simps(4) notin_closed one_eint_def p_nonzero plus_eint_simps(2) prod_equal_val_imp_equal_val val_mult0 val_p) 
    qed
    obtain A where A_def: "A = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)}"
      by blast 
    obtain B where B_def: "B = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (b x)}"
      by blast 
    have A_semialg: "is_semialgebraic (m+k) A"
      unfolding A_def by(intro val_leq_inv_im a_closed assms) 
    have B_semialg: "is_semialgebraic (m+k) B"
      unfolding B_def by(intro val_leq_inv_im  assms)   
    have 2: "\<And>x. x \<in> S1 \<Longrightarrow> val (\<xi> (take m x) \<ominus> c x) \<le> val (b x)"
      using 1 unfolding S1_def S_def by simp 
    obtain C where C_def: "C = (B - A) \<inter> SA_nonzero_set (m+k) b"
      by blast 
    have C_eq: "C = S1"
      unfolding C_def S1_def A_def B_def 
      apply(intro equalityI' IntI)
      unfolding Int_iff Diff_iff mem_Collect_eq S_def 
         apply (meson "1" order_le_less, blast) 
      using "1" apply auto[1] 
      by blast 
    have C_semialg: "is_semialgebraic (m+k) C"
      unfolding C_def 
      by(intro intersection_is_semialg diff_is_semialgebraic A_semialg B_semialg SA_nonzero_set_is_semialgebraic assms)
    show ?thesis using C_semialg unfolding C_eq by auto 
  qed
  have S0_semialg: "is_semialgebraic (m+k) S0"
  proof- 
    have 0: "S0 =SA_zero_set (m+k) b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). \<xi> (take m x) \<ominus> c x = \<zero>}"
      apply(rule equalityI')
      unfolding S0_def SA_zero_set_def Int_iff mem_Collect_eq S_def val_def  
       apply (metis eint.distinct(2)) 
       by(intro conjI, auto )
     have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). \<xi> (take m x) \<ominus> c x = \<zero>} = 
              {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  (\<xi> (take m x) \<ominus> c x)  \<in> pow_res (Suc 0) \<zero>}"
       using pow_res_zero[of 1]
       by auto 
     show ?thesis 
       unfolding 0 1 
       by(intro intersection_is_semialg SA_zero_set_is_semialgebraic assms pow_res_inv_im, auto)
  qed
  have S_inter: "S = S0 \<union> S1"
    apply(intro equalityI'  )
    unfolding S0_def S1_def S_def SA_zero_set_def SA_nonzero_set_def  mem_Collect_eq Int_iff
    by auto  
  have S_semialg: "is_semialgebraic (m+k) S"
    unfolding S_inter 
    by(intro union_is_semialgebraic S0_semialg S1_semialg)
  thus ?thesis unfolding S_def by auto 
qed

lemma val_gt_inv_im:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "a \<in> carrier (SA (m+k))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) > val (a x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) > val (a x)} = carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) -  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) > val (a x)} \<subseteq> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)}"
      unfolding assms by (metis (mono_tags, lifting) DiffI linorder_not_less mem_Collect_eq subsetI)
    show "carrier (Q\<^sub>p\<^bsup>m + k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) > val (a x)}"
      unfolding assms using mem_Collect_eq linorder_not_less 
      by (smt DiffE le_less_linear subsetI)
  qed
  show ?thesis unfolding 0 
    apply(rule diff_is_semialgebraic)
     apply (simp add: carrier_is_semialgebraic) 
    by(intro val_leq_inv_im assms a_closed) 
qed

lemma val_le_inv_im:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "a \<in> carrier (SA (m+k))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < val (a x)}"
proof -
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < val (a x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)} - {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = val (a x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < val (a x)} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)} - {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = val (a x)}"
      unfolding assms using DiffI linorder_not_less mem_Collect_eq subsetI 
      by (smt order_le_less)
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)} - {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = val (a x)} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < val (a x)}"
      unfolding assms using mem_Collect_eq linorder_not_less DiffE le_less_linear subsetI
      by (smt le_less)
  qed
  show ?thesis unfolding 0 
    apply(rule diff_is_semialgebraic)
     by(intro val_leq_inv_im assms a_closed, intro val_eq_inv_im assms)
qed

lemma val_geq_inv_im:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "a \<in> carrier (SA (m+k))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<ge> val (a x)}"
proof -
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<ge> val (a x)} = carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < val (a x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<ge> val (a x)} \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < val (a x)}"
      unfolding assms using DiffI linorder_not_less mem_Collect_eq subsetI 
      by (metis (mono_tags, lifting))     
    show "carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < val (a x)} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<ge> val (a x)}"
      unfolding assms using mem_Collect_eq linorder_not_less DiffE le_less_linear subsetI
      by (smt le_less)
  qed
  show ?thesis unfolding 0 
    apply(rule diff_is_semialgebraic)
         apply (simp add: carrier_is_semialgebraic) 
    by(intro val_le_inv_im assms a_closed) 
qed

lemma cell_inv_im:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "a1 \<in> carrier (SA (m+k))"
  assumes "a2 \<in> carrier (SA (m+k))"
  assumes "is_convex_condition I"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
proof(cases "I = closed_interval")
  case True
  have T0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  val (\<xi> (take m x) \<ominus> c x) \<le> val (a2 x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  val (\<xi> (take m x) \<ominus> c x) \<ge> val (a1 x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a2 x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (a1 x) \<le> val (\<xi> (take m x) \<ominus> c x)}"
      unfolding assms True using mem_Collect_eq by (smt Int_Collect closed_interval_def subsetI)
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a2 x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (a1 x) \<le> val (\<xi> (take m x) \<ominus> c x)} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
      unfolding assms True closed_interval_def  using mem_Collect_eq by blast
  qed
  show ?thesis 
    unfolding T0  
    by(intro intersection_is_semialg val_geq_inv_im val_leq_inv_im assms)
next
  case False
  show ?thesis 
  proof(cases "I = left_closed_interval")
    case True
    have T0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  val (\<xi> (take m x) \<ominus> c x) < val (a2 x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  val (\<xi> (take m x) \<ominus> c x) \<ge> val (a1 x)}"
      unfolding assms True left_closed_interval_def mem_Collect_eq  by blast
    show ?thesis 
      unfolding T0  
      by(intro intersection_is_semialg val_gt_inv_im val_le_inv_im val_geq_inv_im val_leq_inv_im assms)
  next
    case F: False
    show ?thesis 
    proof(cases "I = closed_ray")
      case True
      have T0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  val (\<xi> (take m x) \<ominus> c x) \<le> val (a2 x)}"
        unfolding assms closed_ray_def True by blast  
      show ?thesis 
        unfolding T0  
        by(intro intersection_is_semialg val_gt_inv_im val_le_inv_im val_geq_inv_im val_leq_inv_im assms)
    next
      case F': False
      then have 0: "I = open_ray" using False F F' assms unfolding is_convex_condition_def 
        by blast 
      have T0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  val (\<xi> (take m x) \<ominus> c x) < val (a2 x)}"
        unfolding assms open_ray_def 0 by blast  
      show ?thesis 
        unfolding T0  
        by(intro intersection_is_semialg val_gt_inv_im val_le_inv_im val_geq_inv_im val_leq_inv_im assms)
    qed
  qed
qed

lemma g_not_zero: "g \<noteq> \<zero>\<^bsub>UP (SA m)\<^esub>"
  using g_deg_pos by force 

definition rem where
  "rem j P = (SOME r.  r \<in> carrier (UP (SA (j+m))) \<and> 
                  (deg (SA (j+m)) r < deg (SA m) g) \<and> 
                       (\<forall>n. (partial_pullback m \<xi> j (basic_semialg_set (1 + j) n P)) = 
                        {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (j + m) r (\<xi> (take m a) # take m a @ drop m a) = y [^] n}))"

lemma remE: 
  assumes "P \<in> carrier (Q\<^sub>p [\<X>\<^bsub>1 + j\<^esub>])"
  assumes "r = rem j P"
  shows " r \<in> carrier (UP (SA (j+m))) \<and> 
                  (deg (SA (j+m)) r < deg (SA m) g) \<and> 
                       (\<forall>n. (partial_pullback m \<xi> j (basic_semialg_set (1 + j) n P)) = 
                        {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (j + m) r (\<xi> (take m a) # take m a @ drop m a) = y [^] n})"
proof- 
  have "\<exists>r. r \<in> carrier (UP (SA (j+m))) \<and> 
                  (deg (SA (j+m)) r < deg (SA m) g) \<and> 
                       (\<forall>n. ( (partial_pullback m \<xi> j (basic_semialg_set (1 + j) n P)) = 
          {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (j + m) r (\<xi> (take m a) # take m a @ drop m a) = y [^] n}))"
    by(intro  partial_pullback_division_lemma g_deg_pos assms g_closed g_not_zero g_ltrm_Unit \<xi>_fun \<xi>_root)
  then obtain c where c_def: "c \<in> carrier (UP (SA (j + m))) \<and>
    deg (SA (j + m)) c < deg (SA m) g \<and>
    (\<forall>n. partial_pullback m \<xi> j (basic_semialg_set (1 + j) n P) =
         {a \<in> carrier (Q\<^sub>p\<^bsup>m + j\<^esup>).
          \<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (j + m) c (\<xi> (take m a) # take m a @ drop m a) = y [^] n})"
    by blast 
  show ?thesis
    apply(rule SomeE[of r _ c]) 
    using assms rem_def apply blast 
    using c_def by auto 
qed

theorem \<xi>_semialg:
"\<xi> \<in> carrier (SA m)"
proof(rule SA_car_memI)
  show c0: " \<xi> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)"
    using \<xi>_fun by blast 
  show "is_semialg_function m \<xi>"
  proof(rule is_semialg_functionI')
    show   "\<xi> \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
      using Qp_funs_car_memE \<open>\<xi> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)\<close> by blast
    show "\<And>k S. S \<in> basic_semialgs (1 + k) \<Longrightarrow> is_semialgebraic (m + k) (partial_pullback m \<xi> k S)"
    proof-
      have 0: "\<And>k S. k > 0 \<Longrightarrow> S \<in> {S. is_basic_semialg (1 + k) S} \<Longrightarrow> is_semialgebraic (m + k) (partial_pullback m \<xi> k S)"
      proof- fix k S assume AA: "(k::nat) > 0" assume A0: "S \<in> basic_semialgs (1 + k)"
        then obtain f n where f_n_def: "(n::nat) \<noteq> 0 \<and> f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1 + k\<^esub>]) \<and> S = basic_semialg_set (1+k) n f"
          unfolding is_basic_semialg_def unfolding basic_semialg_set_def by blast 
        have n_bound: "n > 0"
          using f_n_def by auto 
        show "is_semialgebraic (m + k) (partial_pullback m \<xi> k S)" 
        proof(cases "n = 1")
          case T: True
          have "(partial_pullback m \<xi> k S) = carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          proof 
            show "partial_pullback m \<xi> k S \<subseteq> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
              unfolding partial_pullback_def evimage_def by blast 
            show "carrier (Q\<^sub>p\<^bsup>m + k\<^esup>) \<subseteq> partial_pullback m \<xi> k S"
            proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
              have 0: "eval_at_point Q\<^sub>p (\<xi> (take m x) # drop m x) f \<in> carrier  Q\<^sub>p "
                apply(rule eval_at_point_closed[of _ "1+k"])
                apply (metis A Qp.function_ring_car_mem_closed Qp_pow_ConsI \<xi>_fun cartesian_power_drop le_add1 local.take_closed plus_1_eq_Suc) 
                using f_n_def by blast 
              show "x \<in> partial_pullback m \<xi> k S"
                apply(intro partial_pullback_memI A)
                using f_n_def 0 unfolding basic_semialg_set_def T 
                by (metis (no_types, lifting) A Qp.nat_pow_eone T add.commute basic_semialg_set_memI c0 cartesian_power_cons cartesian_power_drop f_n_def le_add1 local.function_ring_car_closed local.take_closed) 
            qed
          qed
          then show ?thesis 
            by (simp add: carrier_is_semialgebraic)
        next
          case F: False
          obtain r where r_def: "r = rem k f"
            by blast 
          have r_closed: "r \<in> carrier (UP (SA (k+m)))"
            unfolding r_def 
            using f_n_def remE by presburger 
          have r_deg: "deg (SA (k+m)) r \<le> d"
            using remE[of f k r] g_deg_bound f_n_def unfolding r_def 
            by fastforce  
          obtain \<S> where \<S>_def: "is_cell_decomp (k + m) \<S> (carrier (Q\<^sub>p\<^bsup>Suc (k + m)\<^esup>)) \<and> (\<forall>A\<in>\<S>. \<exists>u h ka.
                   SA_poly_factors p (k + m) n r (center A) (condition_to_set A) u h ka \<and>
                   (fibre_set A \<subseteq> h \<inverse>\<^bsub>k + m\<^esub> {\<zero>} \<or> (\<exists>\<alpha>\<in>nth_pow_wits n. fibre_set A \<subseteq> h \<inverse>\<^bsub>k + m\<^esub> pow_res n \<alpha>)))"
            using cell_decomp_nth_pow_refinement[of "k+m" n r] r_deg r_closed n_bound add_gr_0 AA 
            by presburger                                                 
          obtain part where part_def: "part = (\<lambda> \<C> \<in> \<S>. {a \<in> partial_pullback m \<xi> k S. 
                        \<xi> (take m a) # take m a @ drop m a \<in> condition_to_set \<C>})"
            by blast 
          have part_closed: "\<And> \<C>. \<C> \<in> \<S> \<Longrightarrow> part \<C> \<subseteq> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
            by (smt local.part_def mem_Collect_eq partial_pullback_closed restrict_apply' subset_iff)
          have part_subset: "\<And> \<C>. \<C> \<in> \<S> \<Longrightarrow> part \<C> \<subseteq> partial_pullback m \<xi> k S"
            by (metis (no_types, lifting) local.part_def mem_Collect_eq restrict_apply' subsetI)
          have part_partitions: "partial_pullback m \<xi> k S = \<Union> (part ` \<S>)"
          proof
            show "partial_pullback m \<xi> k S \<subseteq> \<Union> (part ` \<S>)"
            proof fix x assume A: "x \<in> partial_pullback m \<xi> k S"
              then have "(\<xi> (take m x) # take m x @ drop m x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (m + k)\<^esup>)"
                by (metis Qp.function_ring_car_mem_closed Qp_pow_ConsI \<xi>_fun append_take_drop_id le_add1 local.take_closed partial_pullback_memE(1))                
              then obtain \<C> where C_def: "\<C>\<in>\<S> \<and> (\<xi> (take m x) # take m x @ drop m x) \<in> condition_to_set \<C>"                 by (metis (no_types, lifting) UN_E \<S>_def add.commute is_cell_decomp_def is_partitionE(2))
              have "\<C>\<in>\<S>  \<and> x \<in> partial_pullback m \<xi> k S \<and> \<xi> (take m x) # take m x @ drop m x \<in> condition_to_set \<C>"
                using A C_def by blast
              then have "x \<in> part \<C>"
                unfolding part_def 
                by (metis (no_types, lifting) mem_Collect_eq restrict_apply')
              then show "x \<in> \<Union> (part ` \<S>)" 
                using C_def by blast
            qed
            show "\<Union> (part ` \<S>) \<subseteq> partial_pullback m \<xi> k S"
              using part_subset by blast 
          qed
          have 3: "\<And> \<C>. \<C> \<in> \<S> \<Longrightarrow> is_semialgebraic (m + k) (part \<C>)"
          proof- fix \<C> assume A: "\<C> \<in> \<S>"
            obtain u h l where ukd_def: "SA_poly_factors p (k + m) n r (center \<C>) (condition_to_set \<C>) u h l \<and>
                   (fibre_set \<C> \<subseteq> h \<inverse>\<^bsub>k + m\<^esub> {\<zero>} \<or> (\<exists>\<alpha>\<in>nth_pow_wits n. fibre_set \<C> \<subseteq> h \<inverse>\<^bsub>k + m\<^esub> pow_res n \<alpha>))"
              using \<S>_def A by blast 
            have u_closed: "u \<in> (carrier (Q\<^sub>p\<^bsup>Suc (k+m)\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
              using SA_poly_factors_closure(2) ukd_def by blast
            have x_closed: "h \<in> carrier (SA (k+m))"
              using SA_poly_factors_closure(4) ukd_def by blast
            have center_closed: "center \<C> \<in> carrier (SA (k+m))"
              using SA_poly_factors_closure(3) ukd_def by blast
            show "is_semialgebraic (m + k) (part \<C>)"
            proof(cases "fibre_set \<C> \<subseteq> h \<inverse>\<^bsub>k + m\<^esub> {\<zero>} ")
              case True
              have 1: "part \<C> = {a \<in> partial_pullback m \<xi> k S. \<xi> (take m a) # take m a @ drop m a \<in> condition_to_set \<C>}"
                by (metis (no_types, lifting) A local.part_def restrict_apply')
              hence 2: "part \<C> = {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m a) # take m a @ drop m a) \<in> condition_to_set \<C> \<and> (\<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m a) # take m a @ drop m a) = y [^] n)}"
                using f_n_def r_def remE by auto                 
              have 3: "part \<C> = {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m a) # take m a @ drop m a) \<in> condition_to_set \<C> }"
              proof
                show "part \<C> \<subseteq> {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # take m a @ drop m a \<in> condition_to_set \<C>}"
                  using 2 by blast 
                show " {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # take m a @ drop m a \<in> condition_to_set \<C>} \<subseteq> part \<C>"
                proof fix x assume AX: " x \<in> {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # take m a @ drop m a \<in> condition_to_set \<C>}"
                  then have 30: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>) \<and> \<xi> (take m x) # take m x @ drop m x\<in> condition_to_set \<C>"
                    by blast 
                  then have 31: "x \<in> fibre_set \<C>"
                    by (metis A \<S>_def append_take_drop_id condition_decomp' list.sel(3) padic_fields.condition_to_set_memE(1) padic_fields.is_cell_decompE(3) padic_fields_axioms)
                  then have 32: "h x = \<zero>"
                    using True by blast
                  have 33: " \<xi> (take m x ) # x \<in> condition_to_set \<C>" 
                  proof-
                    have "x = take m x @ drop m x"
                      using 30  by (metis append_take_drop_id)
                    then show ?thesis using 
                      30 by presburger
                  qed
                  then have 31: "SA_poly_to_Qp_poly (k + m) x r \<bullet> \<xi> (take m x )= u ( \<xi> (take m x ) # x) [^] (n::nat) \<otimes> h x \<otimes> (\<xi> (take m x) \<ominus> center \<C> x) [^] l" 
                    using ukd_def SA_poly_factorsE[of "k+m" n r "center \<C>" "condition_to_set \<C>" u h l " \<xi> (take m x )" x] 
                    by blast 
                  have 310: "\<xi> (take m x ) # x \<in> carrier (Q\<^sub>p\<^bsup>Suc (k + m)\<^esup>)"
                    using "33" A \<S>_def is_cell_decomp_subset by blast
                  have take_m: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                    by (meson "30" Ring_Powers.take_closed le_add1) 
                  have 311: "(\<xi> (take m x) \<ominus> center \<C> x) \<in> carrier Q\<^sub>p"
                    apply(intro Qp.ring_simprules  Qp.function_ring_car_mem_closed[of \<xi> "carrier (Q\<^sub>p\<^bsup>m\<^esup>)"] c0 take_m)
                    by (metis "30" SA_car_closed add.commute center_closed) 
                  have 312: "u ( \<xi> (take m x ) # x) [^] n \<in> carrier Q\<^sub>p"
                    using u_closed 310 nat_pow_closed by blast  
                  have "SA_poly_to_Qp_poly (k + m) x r \<bullet> \<xi> (take m x )= \<zero>"
                    using u_closed center_closed 31 310 311 312 
                    by (metis "32" Qp.integral_iff Qp.nat_pow_closed Qp.zero_closed)  
                  hence 313: "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x) = \<zero>"
                    unfolding SA_poly_to_SA_fun_def using 310 by simp 
                  have " \<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x) = y [^] n"
                    unfolding 313 using Qp.pow_zero n_bound by blast 
                  then show "x \<in> part \<C>" using 2 AX
                    by blast
                qed
              qed
              obtain I where I_def: "I = boundary_condition \<C>"
                by blast 
              have cell_cond: "is_cell_condition \<C>"
                using A \<S>_def is_cell_decompE(3) by blast
              hence convex: "is_convex_condition I"
                using I_def by (simp add: is_cell_conditionE'(5))
              obtain a1 where a1_def: "a1 = l_bound \<C>"
                by blast 
              obtain a2 where a2_def: "a2 = u_bound \<C>"
                by blast 
              have a1_closed: "a1 \<in> carrier (SA (m+k))"
                using a1_def cell_cond is_cell_conditionE 
                by (metis (no_types, lifting) A \<S>_def add.commute condition_decomp' is_cell_decomp_def)
              have a2_closed: "a2 \<in> carrier (SA (m+k))"
                using a2_def cell_cond is_cell_conditionE 
                by (metis (no_types, lifting) A \<S>_def add.commute condition_decomp' is_cell_decomp_def)
              obtain c where c_def: "c = center \<C>"
                by blast 
              have c_closed: "c \<in> carrier (SA (m+k))"
                using cell_cond is_cell_conditionE by (metis add.commute c_def center_closed)
              have "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
                by(intro cell_inv_im  carrier_is_semialgebraic c_closed a1_closed a2_closed convex)
              have 4: "part \<C> = {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # a \<in> condition_to_set \<C> }"
              proof 
                show "part \<C> \<subseteq> {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # a \<in> condition_to_set \<C>}"
                  unfolding 3 by (smt Collect_mono_iff append_take_drop_id)
                show "{a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # a \<in> condition_to_set \<C>} \<subseteq> part \<C>"
                  unfolding 3 by (smt Collect_mono_iff append_take_drop_id)
              qed
              have 5: "part \<C> =  {x \<in> fibre_set \<C>. val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
              proof
                show "part \<C> \<subseteq> {x \<in> fibre_set \<C>. val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
                proof fix x assume A: "x \<in> part \<C>"
                  then have 40: "x \<in> fibre_set \<C> \<and> \<xi> (take m x) # x \<in> condition_to_set \<C>"
                    unfolding 4 using cell_cond 
                    by (metis (no_types, lifting) condition_decomp' mem_Collect_eq padic_fields.condition_to_set_memE'(1) padic_fields_axioms)
                  hence " val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))"
                    unfolding c_def a1_def a2_def using cell_condition_set_memE[of \<C>]
                    by (metis I_def a1_def a2_def c_def cell_cond condition_decomp' list.sel(1) list.sel(3))
                  then show "x \<in> {x \<in> fibre_set \<C>. val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
                    using 40 by blast 
                qed
                show "{x \<in> fibre_set \<C>. val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))} \<subseteq> part \<C>"
                proof fix x assume A: "x \<in> {x \<in> fibre_set \<C>. val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
                  then have 40: "x \<in> fibre_set \<C> \<and> val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))"
                    by blast
                  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                    using 40 cell_cond 
                    by (metis (no_types, opaque_lifting) True add.commute evimage_eq subset_eq)
                  hence 41: " \<xi> (take m x) # x \<in> carrier (Q\<^sub>p\<^bsup>Suc (m + k)\<^esup>)"
                    using 40 Qp.function_ring_car_memE Qp_pow_ConsI \<xi>_fun le_add1 local.take_closed
                    by metis 
                  hence "\<xi> (take m x) # x \<in> condition_to_set \<C>"
                    using cell_cond 40 cell_condition_set_memI[of "\<xi> (take m x) # x" "m+k" \<C> "fibre_set \<C>" c a1 a2 I]  
                    unfolding 4 a1_def a2_def c_def  I_def
                    by (metis cartesian_power_head cell_condition_set_memI' condition_decomp' is_cell_conditionE'(1) is_semialgebraic_closed list.sel(1))
                  then show "x \<in> part \<C>" unfolding 4 
                    using x_closed by blast
                qed
              qed
              have fibre_set_closed: "fibre_set \<C> \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                by (metis (no_types, opaque_lifting) True add.commute dual_order.trans extensional_vimage_closed)
              have 6: "part \<C> = fibre_set \<C> \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
                  unfolding 5 using fibre_set_closed  by blast 
              show "is_semialgebraic (m + k) (part \<C>)"
                unfolding 6 using cell_cond 
                by (metis (no_types, lifting) A \<S>_def \<open>is_semialgebraic (m + k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}\<close> add.commute intersection_is_semialg is_cell_conditionE'(1) is_cell_decomp_def)          
            next
              case False
              obtain \<alpha> where alpha_def: "\<alpha> \<in> nth_pow_wits n \<and> fibre_set \<C> \<subseteq> h \<inverse>\<^bsub>k + m\<^esub> pow_res n \<alpha>"
                using False ukd_def by blast
              obtain part' where part'_def: "part' = (\<lambda> \<alpha>. {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m a) # a) \<in> condition_to_set \<C> \<and> \<xi> (take m a) \<ominus> (center \<C> a) \<in> pow_res n \<alpha> })"
                by blast 
              have 1: "part \<C> = {a \<in> partial_pullback m \<xi> k S. \<xi> (take m a) # take m a @ drop m a \<in> condition_to_set \<C>}"
                by (metis (no_types, lifting) A local.part_def restrict_apply')
              hence 2: "part \<C> = {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m a) # take m a @ drop m a) \<in> condition_to_set \<C> \<and> (\<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m a) # take m a @ drop m a) = y [^] n)}"
                using f_n_def r_def remE by auto                 
              have 3: "is_semialgebraic (m+k) {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m a) # a) \<in> condition_to_set \<C>}"
              proof-
                obtain a1 where a1_def: "a1 = l_bound \<C>"
                  by blast 
                obtain a2 where a2_def: "a2 = u_bound \<C>"
                  by blast 
                obtain I where I_def: "I = boundary_condition \<C>"
                  by blast 
                obtain c where c_def: "c = center \<C>"
                  by blast 
                obtain C where C_def: "C = fibre_set \<C>"
                  by blast 
                have 30: "\<C> = Cond (m+k) C c a1 a2 I"
                  by (metis A C_def I_def \<S>_def a1_def a2_def add.commute c_def condition_decomp' padic_fields.is_cell_decompE(4) padic_fields_axioms)
                have a1_closed: "a1 \<in> carrier (SA (m+k))"
                  using a1_def 
                  by (metis "30" A \<S>_def is_cell_conditionE(3) padic_fields.is_cell_decompE(3) padic_fields_axioms)
                have a2_closed: "a2 \<in> carrier (SA (m+k))"
                  using a2_def 
                  by (metis "30" A \<S>_def is_cell_conditionE(4) padic_fields.is_cell_decompE(3) padic_fields_axioms)
                have c_closed: "c \<in> carrier (SA (m+k))"
                  using c_def 
                  by (simp add: add.commute center_closed)
                have convex: "is_convex_condition I"
                  by (metis "30" A \<S>_def is_cell_conditionE(5) is_cell_decomp_def)
                have 31:"is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
                  by(intro cell_inv_im is_cell_conditionI' carrier_is_semialgebraic c_closed a1_closed a2_closed convex)
                have 32: "C \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))} = 
                          {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m a) # a) \<in> condition_to_set \<C>}"
                proof
                  show "C \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))} \<subseteq> {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # a \<in> condition_to_set \<C>}"
                  proof fix x assume A: "x \<in> C \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
                    then have A0: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)" by blast
                    have A1: " val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))"
                      using A by blast 
                    have A2: "\<xi> (take m x)#x \<in> carrier (Q\<^sub>p\<^bsup>Suc (m+k)\<^esup>)"
                      using A0 
                      by (meson Qp.function_ring_car_mem_closed Qp_pow_ConsI \<xi>_fun le_add1 local.take_closed)                    
                    have A3: " tl (\<xi> (take m x) # x) \<in> C"
                    proof -
                      have "x \<in> C"
                        using A by fastforce
                      then show ?thesis
                        by (metis (no_types) list.sel(3))
                    qed
                    show "x \<in> {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # a \<in> condition_to_set \<C>}"
                      unfolding 30 condition_to_set.simps cell_def mem_Collect_eq using A A0 A1 A2
                      by (metis A3 list.sel(1) list.sel(3))
                  qed
                  show " {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m a) # a \<in> condition_to_set \<C>} \<subseteq> C \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))}"
                    unfolding 30 condition_to_set.simps cell_def mem_Collect_eq 
                    by (smt Int_Collect list.sel(1) list.sel(3) mem_Collect_eq subset_iff)                    
                qed
                then show ?thesis 
                by (metis (no_types, lifting) "30" "31" A C_def \<S>_def arity.simps intersection_is_semialg is_cell_conditionE'(1) padic_fields.is_cell_decompE(3) padic_fields_axioms)
              qed     
              have e: "\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> (\<xi> (take m a) # a) = (\<xi> (take m a) # take m a @ drop m a)"
                by (metis append_take_drop_id)
              have f: "\<And>a. a \<in> part \<C> \<Longrightarrow> (\<xi> (take m a) # a) = (\<xi> (take m a) # take m a @ drop m a)"
                by (metis append_take_drop_id)
              have 4: "part \<C> = {a \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m a) # a) \<in> condition_to_set \<C> \<and> (\<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m a) # a) = y [^] n)}"
                unfolding 2 using e f 
                by (metis (mono_tags, lifting) )
              have fibre_set_closed: "fibre_set \<C> \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
               by (metis (no_types, opaque_lifting) add.commute alpha_def extensional_vimage_closed subsetI subset_iff)               
              have part'_partitions: "part \<C> = part \<C> \<inter> \<Union> (part' ` (nth_pow_wits n \<union> {\<zero>}))"
              proof show "part \<C> \<subseteq> part \<C> \<inter> \<Union> (part' ` (nth_pow_wits n \<union> {\<zero>}))"
                proof fix x assume A: "x \<in> part \<C>"
                  then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)" using "2" by blast
                  have 00: "(\<xi> (take m x) \<ominus> (center \<C> x)) \<in>  carrier Q\<^sub>p"
                    using x_closed 
                    by (metis Qp.function_ring_car_memE Qp.minus_closed SA_car_memE(2) \<open>\<xi> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)\<close> add.commute center_closed le_add1 local.take_closed)
                  show "x \<in> part \<C> \<inter> \<Union> (part' ` (nth_pow_wits n \<union> {\<zero>}))"
                  proof(cases "\<xi> (take m x) \<ominus> (center \<C> x) = \<zero>")
                    case True
                    then have T0: "\<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n \<zero>"
                      using Qp.zero_closed f_n_def gr0I pow_res_refl by presburger
                    then have "x \<in> part' \<zero>"
                      using A  part'_def unfolding 4 by blast              
                    then show ?thesis 
                      using A by blast                    
                  next
                    case False
                    then have F0: "\<xi> (take m x) \<ominus> (center \<C> x) \<in> nonzero Q\<^sub>p"
                      using 00 by (meson not_nonzero_Qp)
                    then obtain \<beta> where beta_def: "\<beta> \<in> nth_pow_wits n \<and> pow_res n (\<xi> (take m x) \<ominus> (center \<C> x)) = pow_res n \<beta>"
                      using nth_pow_wits_covers[of n "\<xi> (take m x) \<ominus> (center \<C> x)"] f_n_def  linorder_not_less less_one
                      pow_res_refl[of _ n] unfolding nonzero_def 
                      by (metis (no_types, lifting) equal_pow_resI gr0I val_ring_memE(2))      
                    then have "(\<xi> (take m x) \<ominus> (center \<C> x)) \<in>  pow_res n \<beta>"
                      using F0 n_bound pow_res_refl unfolding nonzero_def by blast
                    then have "x \<in> part' \<beta>"
                      using A part'_def  "4" by blast                      
                    then show ?thesis 
                      using beta_def  A by blast                     
                  qed
                qed
                show "part \<C> \<inter> \<Union> (part' ` (nth_pow_wits n \<union> {\<zero>})) \<subseteq> part \<C>"
                  by blast 
              qed
              have part'_semialg: "\<And>x. x \<in> nth_pow_wits n \<Longrightarrow> is_semialgebraic (m+k) (part \<C> \<inter> part' x)"
              proof- fix a assume A: "a \<in> nth_pow_wits n"
                then have a_nonzero: "a \<in> nonzero Q\<^sub>p"
                  using n_bound nth_pow_wits_closed(3) f_n_def by blast  
                have "\<And>x y. x \<in> part' a \<Longrightarrow> y \<in> part' a \<Longrightarrow> 
                          pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x))
                        = pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m y) # take m y @ drop m y))"
                proof- fix x y assume A0: "x \<in> part' a" "y \<in> part' a"
                  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                    using A0  part'_def by blast
                  have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                    using A0  part'_def by blast
                  have 00: "\<xi> (take m x)#x \<in> condition_to_set \<C>"
                    using A0  part'_def by blast
                  have 01: "\<xi> (take m y)#y \<in> condition_to_set \<C>"
                    using A0  part'_def by blast
                  have 02: "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = u (\<xi> (take m x) # x) [^] n \<otimes> h x \<otimes> (\<xi> (take m x) \<ominus> center \<C> x) [^] l"
                    using SA_poly_factorsE[of "k+m" n r "center \<C>" "condition_to_set \<C>" u h l ]  ukd_def 
                    by (metis (no_types, lifting) "00" SA_poly_to_SA_fun_formula add.commute c0 f_n_def le_add2 local.function_ring_car_closed local.take_closed r_def remE x_closed) 
                  have 03: "SA_poly_to_SA_fun (k + m) r (\<xi> (take m y) # y) = u (\<xi> (take m y) # y) [^] n \<otimes> h y \<otimes> (\<xi> (take m y) \<ominus> center \<C> y) [^] l"
                    using SA_poly_factorsE[of "k+m" n r "center \<C>" "condition_to_set \<C>" u h l ]  ukd_def 
                    by (metis (no_types, lifting) "01" Qp.function_ring_car_mem_closed SA_poly_to_SA_fun_formula add.commute c0 le_add1 local.take_closed r_closed y_closed) 
                  have 04: "x \<in> fibre_set \<C>"
                    using 00  by (metis cell_formula(2) condition_decomp' condition_to_set.simps)
                  have 05: "y \<in> fibre_set \<C>"
                    using 01 
                    by (metis cell_formula(2) condition_decomp' condition_to_set.simps)
                  have 06: "pow_res n (h x) = pow_res n (h y)"
                    using 04 05 alpha_def equal_pow_resI[of \<alpha> "h x" n] equal_pow_resI[of \<alpha> "h y" n] 
                    nth_pow_wits_closed 
                    by (metis (no_types, lifting) evimageE f_n_def gr0I subset_iff)                    
                  have 07: "val (u (\<xi> (take m x) # x)) = 0"
                    using ukd_def  SA_poly_factors_def 00 by (meson SA_poly_factorsE(1))
                  have 08: "val (u (\<xi> (take m y) # y)) = 0 "
                    using ukd_def  SA_poly_factors_def 01 SA_poly_factorsE(1) by meson
                  have 080: "(\<xi> (take m x) # x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (k + m)\<^esup>)"
                    using x_closed Suc_eq_plus1 cartesian_power_cons val_ring_memE(2)
                    by (metis Groups.add_ac(2) Qp.function_ring_car_mem_closed c0 le_add2 local.take_closed) 
                  have 09: "u (\<xi> (take m x) # x) \<in> nonzero Q\<^sub>p"
                    apply(rule nonzero_memI)
                    using 07 ukd_def u_closed 080 apply blast 
                    using 08 unfolding val_def 
                    by (metis "07" infinity_ne_i0 local.val_zero)
                  have 081: "(\<xi> (take m y) # y) \<in> carrier (Q\<^sub>p\<^bsup>Suc (k + m)\<^esup>)"
                    using y_closed Suc_eq_plus1 cartesian_power_cons val_ring_memE(2) 
                    by (metis Groups.add_ac(2) Qp.function_ring_car_mem_closed c0 le_add2 local.take_closed)                 
                  have 10: "u (\<xi> (take m y) # y) \<in> nonzero Q\<^sub>p"
                  apply(rule nonzero_memI)
                    using 07 ukd_def u_closed 081 apply blast 
                    using 08 unfolding val_def by (metis  infinity_ne_i0 )
                  hence 11: "pow_res n (u (\<xi> (take m x) # x) [^] n) = pow_res n (u (\<xi> (take m y) # y)[^] n)"
                    using 10 09 pow_res_nth_pow[of "u (\<xi> (take m x) # x)" n] pow_res_nth_pow[of "u (\<xi> (take m y) # y)" n] f_n_def 
                    by blast
                  have 12: "(\<xi> (take m x) \<ominus> center \<C> x) \<in> carrier Q\<^sub>p"
                    by (metis Qp.function_ring_car_memE Qp.minus_closed SA_car_memE(2) \<open>\<xi> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)\<close> add.commute center_closed le_add1 local.take_closed x_closed)
                  have 13: "(\<xi> (take m y) \<ominus> center \<C> y) \<in> carrier Q\<^sub>p"
                    by (metis Qp.function_ring_car_memE Qp.minus_closed SA_car_memE(2) \<open>\<xi> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)\<close> add.commute center_closed le_add1 local.take_closed y_closed)
                  have 14: "a \<in>  nonzero Q\<^sub>p"
                    by (simp add: a_nonzero)
                  have 15: "pow_res n (\<xi> (take m x) \<ominus> center \<C> x) = pow_res n a"
                    using A0 equal_pow_resI[of _ ] unfolding part'_def 
                    using "12" a_nonzero f_n_def unfolding nonzero_def mem_Collect_eq  by blast
                  have 14: "pow_res n (\<xi> (take m y) \<ominus> center \<C> y) = pow_res n a"
                    using A0 equal_pow_resI[of a] unfolding part'_def 
                    using "13" a_nonzero f_n_def unfolding nonzero_def mem_Collect_eq  by blast
                  have 15: "pow_res n ((\<xi> (take m x) \<ominus> center \<C> x) [^] l) = pow_res n ((\<xi> (take m y) \<ominus> center \<C> y) [^] l)"
                    using f_n_def pow_res_nat_pow[of n "\<xi> (take m x) \<ominus> center \<C> x" "\<xi> (take m y) \<ominus> center \<C> y" l] 14 15 12 13 
                    by blast
                  show "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m y) # take m y @ drop m y))"
                  proof-
                    have 160:" u (\<xi> (take m x) # x) [^] n \<in> carrier Q\<^sub>p"
                      using "09" Qp.nonzero_closed by blast
                    have 161:"  h x \<in> carrier Q\<^sub>p"
                      by (metis Qp.function_ring_car_memE SA_car_memE(2) SA_poly_factors_closure(4) add.commute ukd_def x_closed)
                    have 162:" (\<xi> (take m x) \<ominus> center \<C> x) [^] l \<in> carrier Q\<^sub>p"
                      using "12" by blast
                    have 163:"u (\<xi> (take m y) # y) [^] n \<in> carrier Q\<^sub>p"
                      using 10 Qp.nonzero_closed by blast
                    have 164:"  h y \<in> carrier Q\<^sub>p"
                      by (metis Qp.function_ring_car_memE SA_car_memE(2) SA_poly_factors_closure(4) add.commute ukd_def y_closed)
                    have " (\<xi> (take m y) \<ominus> center \<C> y) [^] l \<in> carrier Q\<^sub>p"
                      using "13" by blast
                    thus ?thesis
                      using 15 11 06 02 03 160 161 162 163 164 
                            pow_res_mult'[of n "(u (\<xi> (take m x) # x) [^] n)" "(h x)" "(\<xi> (take m x) \<ominus> center \<C> x) [^] l"
                                               "(u (\<xi> (take m y) # y) [^] n)" "(h y)" "(\<xi> (take m y) \<ominus> center \<C> y) [^] l"] 
                      by (metis append_take_drop_id f_n_def neq0_conv)
                  qed
                qed
                then obtain \<beta> where beta_def: "\<And>x. x \<in> part' a \<Longrightarrow> 
                          pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = \<beta>"
                  by meson
                obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m x) # x) \<in> condition_to_set \<C>}"
                  by blast 
                show "is_semialgebraic (m + k) (part \<C> \<inter> part' a)"
                proof(cases "\<beta> = pow_res n \<one>")
                  case True
                  have T0: "part \<C> \<inter> part' a = S  \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n a}"
                  proof
                    show "part \<C> \<inter> part' a \<subseteq> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n a}"
                      apply(rule subsetI)
                      unfolding part'_def S_def 4 mem_Collect_eq by blast
                    show "S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n a} \<subseteq> part \<C> \<inter> part' a"
                    proof fix x assume A: "x \<in> S\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n a}"
                      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
                        using A by blast 
                      have x_cond: "(\<xi> (take m x) # x) \<in> condition_to_set \<C>"
                        using A unfolding S_def by blast 
                      have x_pow_res: " \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n a"
                        using A by blast 
                      have "x \<in> part \<C>"
                      proof-
                        have AA: "x \<in> part' a"
                          using A unfolding S_def part'_def by blast 
                        hence 00: "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n \<one>"
                          using True beta_def by blast
                        have 01: "(\<xi> (take m x) # take m x @ drop m x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (m+k)\<^esup>)"
                          using x_closed 
                          by (metis Qp.function_ring_car_mem_closed Qp_pow_ConsI append_take_drop_id c0 le_add1 local.take_closed) 

                        have "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> carrier Q\<^sub>p"
                          using 01  SA_poly_to_SA_fun_is_SA 
                          by (metis Qp.function_ring_car_memE SA_car_memE(2) add.commute  r_closed)
                        hence "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in>  pow_res n \<one>"
                          using pow_res_refl[of "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)" n]
                                "00" f_n_def pow_res_refl by blast
                        hence "\<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = y [^] n"
                          by (metis Qp.nonzero_closed append_take_drop_id f_n_def neq0_conv pow_res_one_imp_nth_pow)
                        thus ?thesis 
                          by (metis (mono_tags, lifting) "2" append_take_drop_id mem_Collect_eq x_closed x_cond)
                      qed
                      then show "x \<in> part \<C> \<inter> part' a"                 
                        using A unfolding S_def part'_def by blast 
                    qed
                  qed
                  have T1: "is_semialgebraic (m+k) S"
                    unfolding S_def using 3 by blast
                  have "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n a}"
                    apply(rule pow_res_inv_im)
                      apply (simp add: Groups.add_ac(2) center_closed) 
                    using Qp.nonzero_closed a_nonzero apply auto[1] 
                    using n_bound by auto 
                  then show ?thesis using T0 T1 
                    using intersection_is_semialg by presburger
                next
                  case False
                  then show ?thesis 
                  proof(cases "\<beta> = pow_res n \<zero>")
                    case True
                    have T0: "part \<C> \<inter> part' a = S  \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n a}"
                    proof
                     show "part \<C> \<inter> part' a \<subseteq> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n a}"
                      apply(rule subsetI)
                      unfolding part'_def S_def 4 mem_Collect_eq by blast
                     show "S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n a} \<subseteq> part \<C> \<inter> part' a"
                     proof fix x assume A: "x \<in> S\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n a}"
                       have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
                        using A by blast 
                       have x_cond: "(\<xi> (take m x) # x) \<in> condition_to_set \<C>"
                        using A unfolding S_def by blast 
                       have x_pow_res: " \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n a"
                        using A by blast 
                        have "x \<in> part \<C>"
                        proof-
                        have AA: "x \<in> part' a"
                          using A unfolding S_def part'_def by blast 
                        hence 00: "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n \<zero>"
                          using True beta_def[of x]  by blast   
                        have 01: "(\<xi> (take m x) # take m x @ drop m x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (m+k)\<^esup>)"
                          using x_closed 
                          by (metis Qp.function_ring_car_mem_closed Qp_pow_ConsI append_take_drop_id c0 le_add1 local.take_closed) 
                        have "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> carrier Q\<^sub>p"
                          using 01  SA_poly_to_SA_fun_is_SA 
                          by (metis SA_car_closed add.commute r_closed) 
                        hence 02: "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in>  pow_res n \<zero>"
                          using pow_res_refl[of "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)" n]
                                "00" f_n_def pow_res_refl by blast
                        have "\<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = y [^] n"
                        proof-
                          have "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = \<zero>"
                            using 02 pow_res_zero[of n] f_n_def  
                            by (metis append_take_drop_id neq0_conv singletonD)
                          thus ?thesis 
                            using Qp.pow_zero f_n_def by blast
                        qed
                        then show ?thesis using 00 01 AA  
                          using "4" x_closed x_cond by blast
                        qed
                        then show "x \<in> part \<C> \<inter> part' a"                 
                        using A unfolding S_def part'_def by blast 
                    qed
                    qed
                    have T1: "is_semialgebraic (m+k) S"
                    unfolding S_def using 3 by blast
                    have "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n a}"
                    apply(rule pow_res_inv_im)
                     apply (simp add: Groups.add_ac(2) center_closed) 
                       apply (simp add: Qp.nonzero_closed a_nonzero) 
                         using n_bound by blast 
                    then show ?thesis using T0 T1 
                    using intersection_is_semialg by presburger
                  next 
                  case F: False
                  have "part \<C> \<inter> part' a = {}"
                  proof(rule ccontr)
                    assume CA: "part \<C> \<inter> part' a \<noteq> {} "
                    then obtain x where x_def: "x \<in> part \<C> \<inter> part' a"
                      by blast 
                    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
                      using "2" by blast
                    have F0: "(\<xi> (take m x) # take m x @ drop m x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (m + k)\<^esup>)"
                      using x_closed 
                      by (metis Qp.function_ring_car_mem_closed Qp_pow_ConsI append_take_drop_id c0 le_add1 local.take_closed) 
                    have F1: "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> carrier Q\<^sub>p"
                      using F0 
                      by (metis SA_car_closed SA_poly_to_SA_fun_is_SA add.commute r_closed)                       
                    have F2: "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = \<beta>"
                      using beta_def CA x_def by blast
                    have F3: "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> nonzero Q\<^sub>p" 
                      using F F2 F1 pow_res_zero by (metis not_nonzero_Qp)
                    have beta_closed: "\<beta> \<in> pow_res_classes n"
                      using CA F0 F3 beta_def[of x] 
                      by (metis (mono_tags, lifting) F2 mem_Collect_eq pow_res_classes_def)
                    obtain b0 where  "b0 \<in> nonzero Q\<^sub>p \<and> b0 \<noteq> \<one>  \<and> \<beta> = pow_res n b0"
                      using F False beta_closed unfolding pow_res_classes_def by blast
                    then obtain b where b_def: "b \<in> nth_pow_wits n \<and> b \<in> nonzero Q\<^sub>p \<and> b \<in> \<O>\<^sub>p \<and>
                                                              \<beta> = pow_res n b"
                      using nth_pow_wits_covers[of n b0] 
                      by (metis equal_pow_resI f_n_def gr0I val_ring_memE(2))   
                    have  C0:"\<not> (\<exists>y \<in> nonzero Q\<^sub>p. (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = y[^]n)"
                      using pow_res_disjoint'[of n "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x))"] F3
                        F False by (metis F2 Qp.nat_pow_0 gr0I)
                    have C1: "\<exists>y \<in> nonzero Q\<^sub>p. (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = y[^]n"
                    proof-
                      obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and>  (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = y[^]n"
                        using x_def unfolding 2  using mem_Collect_eq by blast 
                      have " (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<noteq> \<zero>"
                        using F beta_def  by (metis F2)
                      then have "y \<in> nonzero Q\<^sub>p "
                        using y_def by (metis F3 Qp_nonzero_nat_pow f_n_def gr0I)       
                      thus ?thesis using y_def by blast 
                    qed
                    then show False using C0 by blast 
                  qed
                  thus ?thesis 
                    by (simp add: empty_is_semialgebraic)
                  qed
                qed
              qed
              have 5: "is_semialgebraic (m+k) (part \<C> \<inter> part' \<zero>)"
              proof(cases "l = 0")
                case True
                have T0: "\<And>t x.  t # x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_Qp_poly (k + m) x r \<bullet> t = u (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> center \<C> x) [^] l"
                  using SA_poly_factorsE[of "k+m" n r "center \<C>" "condition_to_set \<C>" u h l] using ukd_def by blast 
                hence T1: "\<And>t x.  t # x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_SA_fun (k + m) r (t#x) = u (t # x) [^] n \<otimes> h x"
                proof-
                  fix t x assume T10: "t # x \<in> condition_to_set \<C>"
                  hence T11: " SA_poly_to_Qp_poly (k + m) x r \<bullet> t = u (t # x) [^] n \<otimes> h x \<otimes> \<one>"
                    using True T0 Qp.nat_pow_0 by presburger
                  have 0: "arity \<C> = k + m"
                    using A \<S>_def is_cell_decompE by blast 
                  have 1: "(t#x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (k+m)\<^esup>)"
                    using T10 cell_condition_to_set_subset[of \<C>] unfolding 0 by auto 
                  have 2: "x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>)"
                      using 1 cartesian_power_tail list.sel(3) by metis  
                  have T12: "u (t # x) [^] n \<otimes> h x \<in> carrier Q\<^sub>p"
                  proof-
                    have T120: "u (t # x) \<in> carrier Q\<^sub>p"
                      using  u_closed 1 by blast  
                    have T121: "h x \<in> carrier Q\<^sub>p"
                      using 2 function_ring_car_closed SA_car_memE(2) x_closed by blast
                    show ?thesis using T120 T121
                      by blast
                  qed 
                  then show "SA_poly_to_SA_fun (k + m) r (t#x) = u (t # x) [^] n \<otimes> h x"
                    using T11 r_closed 1 by (simp add: SA_poly_to_SA_fun_def)                    
                qed 
                have T2: "\<And>x.  (\<xi> (take m x) # take m x @ drop m x) \<in> condition_to_set \<C> \<Longrightarrow>  pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n \<alpha>"
                proof-
                  fix x assume T20: " \<xi> (take m x) # take m x @ drop m x \<in> condition_to_set \<C> "
                  have \<C>_arity: "arity \<C> = k + m"
                    using A \<S>_def is_cell_decompE(4) by blast 
                  have pt_closed: "\<xi> (take m x) # take m x @ drop m x \<in> carrier (Q\<^sub>p\<^bsup>Suc (k+m)\<^esup>)"
                    using T20 cell_condition_to_set_subset[of \<C>] unfolding \<C>_arity by auto 
                  then have "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x) = u (\<xi> (take m x) # take m x @ drop m x) [^] n \<otimes> h (take m x @ drop m x)"
                    using T1 T20 by blast
                  have 00: "take m x @ drop m x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>)"
                    using T20 pt_closed by (metis cartesian_power_tail list.sel(3))                   
                  have 01: "u (\<xi> (take m x) # take m x @ drop m x) [^] n \<in> carrier Q\<^sub>p"
                    using pt_closed Qp.nat_pow_closed[of "u (\<xi> (take m x) # take m x @ drop m x)" n]
                          u_closed SA_car_memE(2) SA_poly_factors_def T20 subsetD ukd_def by blast 
                  have 02: "u (\<xi> (take m x) # take m x @ drop m x) [^] n \<otimes> h (take m x @ drop m x) \<in> carrier Q\<^sub>p"
                    using 00 01 T20 ukd_def function_ring_car_closed Qp.m_closed  SA_car_memE(2)
                      SA_poly_factors_def cartesian_power_tail list.sel(3) subset_iff
                    using x_closed by presburger
                  have 03: "val (u (\<xi> (take m x) # take m x @ drop m x)) = 0"
                    using ukd_def SA_poly_factorsE 01 T20 by blast
                  have 04: "u (\<xi> (take m x) # take m x @ drop m x) \<in> carrier Q\<^sub>p"
                    using pt_closed u_closed SA_car_memE(2) SA_poly_factors_def T20 subsetD ukd_def by blast 
                  hence 05: "u (\<xi> (take m x) # take m x @ drop m x) \<in> nonzero Q\<^sub>p"
                    using 03 function_ring_car_closed SA_car_memE(2) SA_poly_factors_def T20 ukd_def
                    by (metis (no_types, lifting) val_nonzero' zero_eint_def)
                  have 06: "pow_res n (h (take m x @ drop m x)) = pow_res n \<alpha>"
                  proof-
                    have "take m x @ drop m x \<in> fibre_set \<C>"
                      using T20 by (metis cell_formula(2) condition_decomp' condition_to_set.simps)
                    hence "h (take m x @ drop m x) \<in> pow_res n \<alpha>"
                      using alpha_def by blast 
                    then show ?thesis 
                      using alpha_def pow_res_eq[of n \<alpha> "h (take m x @ drop m x)"] 
                      nth_pow_wits_closed' by (meson f_n_def gr0I val_ring_memE(2))
                  qed
                  have "pow_res n (u (\<xi> (take m x) # take m x @ drop m x) [^] n \<otimes> h (take m x @ drop m x))
                        = pow_res n (h (take m x @ drop m x))"
                    using 00 01 05 06 
                    by (metis (no_types, lifting) function_ring_car_closed Qp.m_comm Qp.nat_pow_0
                        Qp.nat_pow_closed Qp.r_one Qp_nat_pow_nonzero SA_car_memE(2) gr0I 
                        pow_res_disjoint equal_pow_resI pow_res_mult x_closed)
                   then show "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n \<alpha>"
                    by (metis  "06"  \<open>SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x) = u (\<xi> (take m x) # take m x @ drop m x) [^] n \<otimes> h (take m x @ drop m x)\<close>  append_take_drop_id)                    
                qed
                obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m x) # x) \<in> condition_to_set \<C>}"
                  by blast 
                show "is_semialgebraic (m + k) (part \<C> \<inter> part' \<zero>)"
                proof(cases "pow_res n \<alpha> = pow_res n \<one>")
                  case True
                  have T0: "part \<C> \<inter> part' \<zero> = S  \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n \<zero>}"
                  proof
                    show "part \<C> \<inter> part' \<zero> \<subseteq> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>}"
                      apply(rule subsetI)
                      unfolding part'_def S_def 4 mem_Collect_eq by blast 
                    show "S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>} \<subseteq> part \<C> \<inter> part' \<zero>"
                    proof fix x assume A: " x \<in> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>}"
                      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
                        using A by blast 
                      have x_cond: "(\<xi> (take m x) # x) \<in> condition_to_set \<C>"
                        using A unfolding S_def by blast 
                      have x_pow_res: " \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero> "
                        using A by blast 
                      have "x \<in> part \<C>"
                      proof-
                        have AA: "x \<in> part' \<zero>"
                          using A unfolding S_def part'_def by blast 
                        hence 00: "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n \<one>"
                          using True T2 A e x_closed x_cond by presburger
                        have 01: "(\<xi> (take m x) # take m x @ drop m x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (m+k)\<^esup>)"
                          using x_closed 
                          by (metis Qp.function_ring_car_mem_closed Qp_pow_ConsI append_take_drop_id c0 le_add1 local.take_closed) 
                        have "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> carrier Q\<^sub>p"
                          using 01  SA_poly_to_SA_fun_is_SA 
                          by (metis SA_car_closed add.commute r_closed) 
                        hence "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in>  pow_res n \<one>"
                          using pow_res_refl[of "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)" n]
                                "00" f_n_def pow_res_refl by blast
                        hence "\<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = y [^] n"
                          by (metis Qp.nonzero_closed append_take_drop_id f_n_def neq0_conv pow_res_one_imp_nth_pow)
                        thus ?thesis 
                          by (metis (mono_tags, lifting) "2" append_take_drop_id mem_Collect_eq x_closed x_cond)
                      qed
                      then show "x \<in> part \<C> \<inter> part' \<zero>"                 
                        using A unfolding S_def part'_def by blast 
                    qed
                  qed
                  have T1: "is_semialgebraic (m+k) S"
                    unfolding S_def using 3 by blast
                  have "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n \<zero>}"                   
                    apply(rule pow_res_inv_im)
                      apply (simp add: add.commute center_closed)
                      using Qp.nonzero_closed apply blast
                         using f_n_def by blast
                       then show ?thesis using T0 T1 
                         using intersection_is_semialg by presburger
                next
                  case False
                  then show ?thesis 
                  proof(cases "pow_res n \<alpha> = pow_res n \<zero>")
                    case True
                    have T0: "part \<C> \<inter> part' \<zero> = S  \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n \<zero>}"
                    proof
                      show "part \<C> \<inter> part' \<zero> \<subseteq> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>}"
                      apply(rule subsetI)
                      unfolding part'_def S_def 4 mem_Collect_eq by blast
                     show "S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>} \<subseteq> part \<C> \<inter> part' \<zero>"
                     proof fix x assume A: "x \<in> S\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>}"
                       have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
                        using A by blast 
                      have x_cond: "(\<xi> (take m x) # x) \<in> condition_to_set \<C>"
                        using A unfolding S_def by blast 
                      have x_pow_res: " \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>"
                        using A by blast 
                      have "x \<in> part \<C>"
                      proof-
                        have AA: "x \<in> part' \<zero>"
                          using A unfolding S_def part'_def by blast 
                        hence 00: "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n \<zero>"
                          using True by (metis T2 append_take_drop_id x_cond)                          
                        have 01: "(\<xi> (take m x) # take m x @ drop m x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (m+k)\<^esup>)"
                          using x_closed 
                          by (metis Qp.function_ring_car_mem_closed Qp_pow_ConsI append_take_drop_id c0 le_add1 local.take_closed) 
                        have "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> carrier Q\<^sub>p"
                          using 01  SA_poly_to_SA_fun_is_SA 
                          by (metis SA_car_closed add.commute r_closed) 
                        hence 02: "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in>  pow_res n \<zero>"
                          using pow_res_refl[of "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)" n]
                                "00" f_n_def pow_res_refl by blast
                        have "\<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = y [^] n"
                        proof-
                          have "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = \<zero>"
                            using 02 pow_res_zero[of n] f_n_def  
                            by (metis append_take_drop_id neq0_conv singletonD)
                          thus ?thesis 
                            using Qp.pow_zero f_n_def by blast
                        qed
                        then show ?thesis using 00 01 AA  
                          using "4" x_closed x_cond by blast
                      qed
                        then show "x \<in> part \<C> \<inter> part' \<zero>"                 
                        using A unfolding S_def part'_def by blast 
                     qed
                    qed
                    have T1: "is_semialgebraic (m+k) S"
                      unfolding S_def using 3 by blast
                    have "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n \<zero>}"
                      apply(rule pow_res_inv_im)
                       apply (simp add: add.commute center_closed)
                      using Qp.nonzero_closed apply blast
                         using f_n_def by blast
                       then show ?thesis using T0 T1 
                         using intersection_is_semialg by presburger
                  next 
                  case F: False
                  have "part \<C> \<inter> part' \<zero> = {}"
                  proof(rule ccontr)
                    assume CA: "part \<C> \<inter> part' \<zero> \<noteq> {} "
                    then obtain x where x_def: "x \<in> part \<C> \<inter> part' \<zero>"
                      by blast 
                    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
                      using "2" by blast
                    have F0: "(\<xi> (take m x) # take m x @ drop m x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (m + k)\<^esup>)"
                      using x_closed                           
                      by (metis Qp.function_ring_car_mem_closed Qp_pow_ConsI append_take_drop_id c0 le_add1 local.take_closed) 
                    have F1: "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> carrier Q\<^sub>p"
                      using F0 SA_poly_to_SA_fun_is_SA 
                      by (metis SA_car_closed add.commute r_closed)                   
                    have F2: "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n \<alpha>"
                      using CA x_def by (metis (no_types, lifting) "1" IntE T2 mem_Collect_eq)                     
                    have F3: "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> nonzero Q\<^sub>p" 
                      using F F2 F1 pow_res_zero by (metis not_nonzero_Qp)
                    have beta_closed: "pow_res n \<alpha> \<in> pow_res_classes n"
                      using CA F0 F3 
                      by (metis (mono_tags, lifting) alpha_def f_n_def gr0I mem_Collect_eq nth_pow_wits_closed' pow_res_classes_def)                      
                    obtain b0 where  "b0 \<in> nonzero Q\<^sub>p \<and> b0 \<noteq> \<one>  \<and> pow_res n \<alpha> = pow_res n b0"
                      using F False beta_closed unfolding pow_res_classes_def by blast
                    then obtain b where b_def: "b \<in> nth_pow_wits n \<and> b \<in> nonzero Q\<^sub>p \<and> b \<in> \<O>\<^sub>p \<and>
                                                              pow_res n \<alpha> = pow_res n b"
                      using nth_pow_wits_covers[of n b0] 
                      by (metis alpha_def f_n_def gr0I nth_pow_wits_closed(2) nth_pow_wits_closed(3))                      
                    have  C0:"\<not> (\<exists>y \<in> nonzero Q\<^sub>p. (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = y[^]n)"
                      using pow_res_disjoint'[of n "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x))"] F3
                        F False by (metis F2 Qp.nat_pow_0 gr0I)
                    have C1: "\<exists>y \<in> nonzero Q\<^sub>p. (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = y[^]n"
                    proof-
                      obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and>  (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = y[^]n"
                        using x_def unfolding 2  using mem_Collect_eq by blast 
                      have " (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<noteq> \<zero>"
                        using F by (metis F2)                       
                      then have "y \<in> nonzero Q\<^sub>p "
                        using y_def by (metis F3 Qp_nonzero_nat_pow f_n_def gr0I)       
                      thus ?thesis using y_def by blast 
                    qed
                    then show False using C0 by blast 
                  qed
                  thus ?thesis 
                    by (metis empty_is_semialgebraic)
                  qed
                qed
              next
                case False
                have F0: "\<And>t x.  t # x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_Qp_poly (k + m) x r \<bullet> t  = u (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> center \<C> x) [^] l"
                  using SA_poly_factorsE[of "k+m" n r "center \<C>" "condition_to_set \<C>" u h l] using ukd_def by blast
                have F1: "\<And>t x.  t # x \<in> condition_to_set \<C> \<Longrightarrow> u (t # x) [^] n \<in> carrier Q\<^sub>p"
                  using ukd_def SA_poly_factorsE by (meson function_ring_car_closed Qp.nat_pow_closed SA_car_memE(2) SA_poly_factors_def subsetD)
                have F2: "\<And>t x.  t # x \<in> condition_to_set \<C> \<Longrightarrow> h x \<in> carrier Q\<^sub>p"
                  using ukd_def 
                  by (metis (no_types, lifting) A function_ring_car_closed SA_car_memE(2) \<S>_def cartesian_power_tail is_cell_decomp_subset list.sel(3) subsetD x_closed)
                have F3: "\<And>x. x \<in> part' \<zero> \<Longrightarrow> SA_poly_to_Qp_poly (k + m) x r \<bullet> \<xi> (take m x) = \<zero>"
                proof- fix x assume A: "x \<in> part' \<zero>"
                  then have F30: "\<xi> (take m x)#x \<in> condition_to_set \<C>"
                    unfolding part'_def by blast                    
                  have F31: " (\<xi> (take m x) \<ominus> center \<C> x) [^] l = \<zero>"
                  proof-
                    have "\<xi> (take m x) \<ominus> center \<C> x = \<zero>"
                      using A unfolding part'_def 
                      by (metis (no_types, lifting) f_n_def mem_Collect_eq not_gr0 pow_res_zero singletonD)                     
                    then show ?thesis using False Qp.nat_pow_zero by presburger
                  qed
                  show F32: "SA_poly_to_Qp_poly (k + m) x r \<bullet> \<xi> (take m x) = \<zero>"
                    using F0 F1 F2 F30 F31 A Qp.m_closed Qp.r_null by presburger
                qed
                obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). (\<xi> (take m x) # x) \<in> condition_to_set \<C>}"
                  by blast 
                have "part \<C> \<inter> part' \<zero> = S  \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n \<zero>}"
                proof-
                  show T0: "part \<C> \<inter> part' \<zero> = S  \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n \<zero>}"
                  proof
                      show "part \<C> \<inter> part' \<zero> \<subseteq> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>}"
                      apply(rule subsetI)
                      unfolding part'_def S_def 4 mem_Collect_eq by blast
                     show "S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>} \<subseteq> part \<C> \<inter> part' \<zero>"
                     proof fix x assume A: "x \<in> S\<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>}"
                       have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
                        using A by blast 
                      have x_cond: "(\<xi> (take m x) # x) \<in> condition_to_set \<C>"
                        using A unfolding S_def by blast 
                      have x_pow_res: " \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>"
                        using A by blast 
                      have "x \<in> part \<C>"
                      proof-
                        have AA: "x \<in> part' \<zero>"
                          using A unfolding S_def part'_def by blast 
                        hence 00: "pow_res n (SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) = pow_res n \<zero>"
                          using AA F3 
                          by (metis (no_types, lifting) Groups.add_ac(2) Qp.function_ring_car_mem_closed SA_poly_to_SA_fun_formula append_take_drop_id c0 le_add1 local.take_closed r_closed x_closed) 
                        have 01: "(\<xi> (take m x) # take m x @ drop m x) \<in> carrier (Q\<^sub>p\<^bsup>Suc (m+k)\<^esup>)"
                          using x_closed 
                          by (metis Qp.function_ring_car_mem_closed Qp_pow_ConsI append_take_drop_id c0 le_add1 local.take_closed) 
                        have "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in> carrier Q\<^sub>p"
                          using 01  SA_poly_to_SA_fun_is_SA 
                          by (metis SA_car_closed add.commute r_closed)                          
                        hence 02: "(SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)) \<in>  pow_res n \<zero>"
                          using pow_res_refl[of "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # take m x @ drop m x)" n]
                                "00" f_n_def pow_res_refl by blast
                        have "\<exists>y\<in>carrier Q\<^sub>p. SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = y [^] n"
                        proof-
                          have "SA_poly_to_SA_fun (k + m) r (\<xi> (take m x) # x) = \<zero>"
                            using 02 pow_res_zero[of n] f_n_def  
                            by (metis append_take_drop_id neq0_conv singletonD)
                          thus ?thesis 
                            using Qp.pow_zero f_n_def by blast
                        qed
                        then show ?thesis using 00 01 AA  
                          using "4" x_closed x_cond by blast
                      qed
                        then show "x \<in> part \<C> \<inter> part' \<zero>"                 
                        using A unfolding S_def part'_def by blast 
                     qed
                   qed
                qed
                have F3: "is_semialgebraic (m+k) S"
                  unfolding S_def using 3 by blast
                have "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> (center \<C> x) \<in> pow_res n \<zero>}"
                    apply(rule pow_res_inv_im)
                       apply (simp add: add.commute center_closed)
                         using Qp.nonzero_closed apply blast
                         using f_n_def by blast 
               then show ?thesis using F3 intersection_is_semialg 
                 using \<open>part \<C> \<inter> part' \<zero> = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> center \<C> x \<in> pow_res n \<zero>}\<close> by presburger
              qed
              obtain F where F_def: "F = (\<lambda> \<alpha>. part \<C> \<inter> part' \<alpha>)"
                by blast 
              have F: "part \<C> = \<Union> (F `(nth_pow_wits n \<union> {\<zero>}))"
                using part'_partitions unfolding F_def by (metis Int_UN_distrib)
              have F_semialg: "\<And>s. s \<in> (nth_pow_wits n \<union> {\<zero>}) \<Longrightarrow> is_semialgebraic (m+k) (F s)"
                using  part'_semialg 5 unfolding F_def by blast
              have "finite (nth_pow_wits n)"
                using nth_pow_wits_finite[of n] f_n_def by linarith
              hence "finite (nth_pow_wits n \<union> {\<zero>})"
                by blast
              hence "finite (F `(nth_pow_wits n \<union> {\<zero>}))"
                by blast 
              thus ?thesis unfolding F using F_semialg finite_union_is_semialgebraic[of "F `(nth_pow_wits n \<union> {\<zero>})" "m+k"]
                by (meson image_subsetI is_semialgebraicE)
            qed
          qed
          have "finite (part ` \<S>)"
            using \<S>_def is_cell_decompE(1) by blast 
          thus ?thesis using 3 finite_union_is_semialgebraic[of  "part ` \<S>" "m+k"] unfolding part_partitions 
            by (meson image_subsetI is_semialgebraicE)
        qed
      qed
      fix k S assume A: "S \<in> basic_semialgs (1 + k)"
      show "is_semialgebraic (m + k) (partial_pullback m \<xi> k S)"
      proof(cases "k > 0")
        case True
        then show ?thesis using A 0  by blast        
      next
        case False
        then have F0: "k = 0"
          by linarith 
        then obtain f n where f_n_def: "(n::nat) \<noteq> 0 \<and> f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1\<^esub>]) \<and> S = basic_semialg_set 1 n f"
          unfolding is_basic_semialg_def by (metis A add.right_neutral is_basic_semialg_def mem_Collect_eq)
        have F1: "(partial_pullback m \<xi> k S) = {a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p ([\<xi> (take m a)]) f = y [^] n}"
          unfolding basic_semialg_set_def partial_pullback_def partial_image_def 
        proof
          show " (\<lambda>xs. \<xi> (take m xs) # drop m xs) \<inverse>\<^bsub>m + k\<^esub> S \<subseteq> {a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p [\<xi> (take m a)] f = y [^] n}"
            apply(rule subsetI)
            using F0 unfolding evimage_def 
            using  IntD1 IntD2 add.right_neutral basic_semialg_set_memE(1) basic_semialg_set_memE(2) f_n_def list.inject mem_Collect_eq Qp.to_R1_to_R vimageE
            by smt  
          show "{a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p [\<xi> (take m a)] f = y [^] n} \<subseteq> (\<lambda>xs. \<xi> (take m xs) # drop m xs) \<inverse>\<^bsub>m + k\<^esub> S"
          proof(rule subsetI) fix x assume A: "x \<in> {a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>y\<in>carrier Q\<^sub>p. eval_at_point Q\<^sub>p [\<xi> (take m a)] f = y [^] n}"
            show  " x \<in> (\<lambda>xs. \<xi> (take m xs) # drop m xs) \<inverse>\<^bsub>m + k\<^esub> S"
            proof-
              obtain y where y_def: "y\<in>carrier Q\<^sub>p \<and> eval_at_point Q\<^sub>p [\<xi> (take m x)] f = y [^] n"
                using A by blast 
              hence 00: "[\<xi> (take m x)] \<in> S"
                using A  f_n_def basic_semialg_set_memI[of "[\<xi> (take m x)]" 1 y f n ] 
                by (metis (no_types, lifting) Qp.function_ring_car_mem_closed add.commute arith_extra_simps(5) c0 le_add1 local.take_closed mem_Collect_eq Qp.to_R1_closed) 
              have " \<xi> (take m x) # drop m x = [ \<xi> (take m x)] "
                using A  
                by (metis (no_types, lifting) \<open>[\<xi> (take m x)] \<in> S\<close> add.commute add.right_neutral 
                    basic_semialg_set_memE(1) cartesian_power_car_memE' cartesian_power_cons 
                    cartesian_power_drop f_n_def less_one mem_Collect_eq nth_Cons_0 Qp.to_R1_to_R)     
              then show ?thesis using 00 
                by (metis (no_types, lifting) A F0 add.right_neutral evimageI2 mem_Collect_eq)
            qed
          qed
        qed   
        have F2: "cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) \<in> {S. is_basic_semialg (1 + 1) S}"
          using Qp_times_basic_semialg_right[of f 1 n 1] f_n_def zero_less_one 
          by (metis (no_types, lifting) is_basic_semialg_def mem_Collect_eq poly_ring_car_mono'(2) subsetD)
        have F3: "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1+1\<^esub>])"
          using f_n_def poly_ring_car_mono'(2) by blast
        have F4: "is_semialgebraic (1+1) (basic_semialg_set (1+ 1) n f)"
          using f_n_def F3 basic_semialg_is_semialgebraic' by blast
        have F5: "cartesian_product (partial_pullback m \<xi> 0 S) (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) = partial_pullback m \<xi> 1 (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)))"
          using partial_pullback_cartesian_product[of \<xi> m S] f_n_def 
                \<open>\<xi> \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p\<close> basic_semialg_set_memE(1) by blast
        have F6: "is_semialgebraic (m+1) (cartesian_product (partial_pullback m \<xi> 0 S) (carrier (Q\<^sub>p\<^bsup>1\<^esup>)))"
        proof-
          have "is_semialgebraic (m+1) (partial_pullback m \<xi> 1 (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))))"
               using F2 0[of 1 "cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"] zero_less_one by blast         
          then show ?thesis unfolding F5 by blast 
        qed
        then show "is_semialgebraic (m + k) (partial_pullback m \<xi> k S)"
          by (metis F0 Qp_n_nonempty add.right_neutral carrier_is_semialgebraic cartesian_product_factor_projection_is_semialg is_semialgebraic_closed partial_pullback_closed)
      qed
    qed
  qed
qed
end

text\<open>Here we can remove the result from the proof locale for ease of use in the proofs of later 
lemmas:\<close>

theorem(in denef_II) SA_fun_test:
  assumes g_deg_bound:"deg (SA m) g \<le> Suc d"
  assumes g_deg_pos:"deg (SA m) g > 0"
  assumes g_closed:"g \<in> carrier (UP (SA m))"
  assumes \<xi>_fun:"\<xi> \<in> carrier (Fun\<^bsub>m\<^esub> Q\<^sub>p)"
  assumes g_ltrm_Unit:"UP_ring.lcf (SA m) g \<in> Units (SA m)"
  assumes \<xi>_root:"\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
  assumes val_leq_inv_im: "\<And> k c a. \<lbrakk>c \<in> carrier (SA (m+k)); a \<in> carrier (SA (m+k)) \<rbrakk> \<Longrightarrow> 
                          is_semialgebraic (m+k) 
                              {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)}"
  assumes pow_res_inv_im: "\<And> k c \<alpha> n. \<lbrakk>c \<in> carrier (SA (m+k)); \<alpha> \<in> carrier Q\<^sub>p ; n > 0 \<rbrakk>
                            \<Longrightarrow> is_semialgebraic (m+k) 
                                    {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  (\<xi> (take m x) \<ominus> c x) \<in>  pow_res n \<alpha>}"
  shows "\<xi> \<in> carrier (SA m)"
  apply(intro SA_fun_proof.\<xi>_semialg[of _ d g] SA_fun_proof.intro denef_II_axioms SA_fun_proof_axioms.intro assms)
  using assms unfolding Q\<^sub>p_def Z\<^sub>p_def by auto 
  
end  


