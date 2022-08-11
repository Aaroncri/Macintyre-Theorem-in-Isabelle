theory Padic_Cells
imports Padic_Field.Padic_Semialgebraic_Function_Ring 
        
begin

context padic_fields
begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>$p$-adic Cells\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Cells are the fundamental type of semialgebraic set, in the sense that they are easy to analyze 
structurally, and, as will be shown, every semialgebraic set can be parititioned into them. As sets, 
they are defined by the formula:
\[
\mathcal{C} = \{(t,x) \in \mathbb{Q}_p \times \mathbb{Q}_p^m \mid x \in C \land \text{ val }(a_1(x)) \square_1 \text{ val }(t - c(x)) \square_2 \text{ val } (a_2(x)) \}
\]
where $C \subseteq \mathbb{Q}_p^m$ is a semialgebraic set, $\square_i$ is either $\leq, <$, or no 
condition, and $a_1$, $a_2$, and $c$ are semialgebraic functions. For the purposes of stating and 
proving Denef's cell decomposition theorems, it will be important to keep track not just of the 
underlying set of a cell, but also of the defining parameters $C, a_1, a_2, c, \square_1, \square_2$, 
which in general are not unique. For this reason, we will define an abstract data type for these 
parameters, and a function which maps an object of this type to its underlying set. 

Instead of speaking in terms of the conditions $\square_i$, we will assign to each cell a convex 
condition $I$, which is either \texttt{closed\_interval}, \texttt{left\_closed\_interval}, 
\texttt{closed\_ray}, or \texttt{open\_ray}. We will refer to the function $c(x)$ as the center of 
the cell, in keeping with standard terminology. \<close>

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Cells as Sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition cell where
  "cell m C c a1 a2 I  = {as \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
                          tl as \<in> C \<and>
                          val (hd as \<ominus> (c (tl as))) \<in> I (val (a1 (tl as))) (val (a2 (tl as))) }"

lemma cell_subset: 
"cell m C c a1 a2 I \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  unfolding cell_def by blast 

lemma cell_formula:
  assumes "as = t#x"
  assumes "as \<in> cell m C c a1 a2 I"
  shows  "as \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
         "x \<in> C"
         "val (t \<ominus> (c x)) \<in>  I (val (a1 x)) (val (a2 x))"
using assms cell_def apply blast 
proof-
  have 0: "length as = Suc m"
    using cell_subset assms cartesian_power_car_memE 
    by blast
  have 1: "x = tl as"
    by (simp add: assms(1))   
  have 2: "t = hd as"
    by (simp add: assms(1))
  show "x \<in> C" 
    using 1 assms 
    unfolding cell_def 
    by blast 
  have "val ((hd as)\<ominus> (c (tl as))) \<in> I (val (a1 (tl as))) (val (a2 (tl as)))"
    using 1 2 assms
    unfolding cell_def 
    by blast
  then have "val ((hd as)\<ominus> (c (tl as))) \<in> I (val (a1 (tl as))) (val (a2 (tl as)))"
    using 1 2 assms 
    by blast
  then show  "val (t \<ominus> (c x)) \<in>  I (val (a1 x)) (val (a2 x))"
    unfolding 1 2 by auto 
qed

lemma cell_memI:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  assumes "(tl as) \<in> C"
  assumes "val (hd as \<ominus> (c (tl as))) \<in> I (val (a1 (tl as))) (val (a2 (tl as)))"
  shows "as \<in> cell m C c a1 a2 I"
using assms unfolding cell_def by blast 

lemma cell_memI':
  assumes "C \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "x \<in> C"
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "val (t \<ominus> (c x)) \<in> I (val (a1 x)) (val (a2 x))"
  shows "t#x \<in> cell n C c a1 a2 I"
proof(rule cell_memI[of "t#x" n C c I a1 a2 ])
  have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms  
    by blast 
  have 1: "length (t#x) = Suc n "
    using assms 
    by (metis "0" cartesian_power_car_memE length_Cons)   
  have 2: " set (t#x) \<subseteq> carrier Q\<^sub>p"
    using assms cartesian_power_car_memE''[of x Q\<^sub>p n] 1
    by (metis (no_types, lifting) set_ConsD subset_iff)  
  have 3: "tl (t#x) = x"
    by simp 
  show "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    using assms cartesian_power_car_memI[of "t#x" "Suc n" Q\<^sub>p] "1" "2" 
    by blast
  show "tl (t#x) \<in> C"
    using "3" assms(2) 
    by (simp add: assms(2))
  show "val (hd (t # x) \<ominus> c (tl (t # x))) \<in> I (val (a1 (tl (t # x)))) (val (a2 (tl (t # x))))"
    by (metis "3" assms(4) list.sel(1))
qed  

lemma cell_memE:
  assumes "x \<in> cell n C c a1 a2 I"
  shows "x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
        "tl x \<in> C"
        "val (hd x \<ominus> (c (tl x))) \<in> I (val (a1 (tl x))) (val (a2 (tl x)))"
  using assms unfolding cell_def apply blast 
  using assms unfolding cell_def apply blast 
  using assms unfolding cell_def by blast 

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>A Datatype for Cell Conditions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

datatype cell_condition = Cond nat 
                               "padic_tuple set" 
                               "padic_nary_function" 
                               "padic_nary_function" 
                               "padic_nary_function"
                               "eint \<Rightarrow> eint \<Rightarrow> eint set"

fun arity :: "cell_condition \<Rightarrow> nat" where
"arity (Cond n C c a1 a2 I) = n"

fun fibre_set :: "cell_condition \<Rightarrow> padic_tuple set" where
"fibre_set (Cond n C c a1 a2 I) = C"

fun center :: "cell_condition \<Rightarrow> padic_nary_function" where
"center (Cond n C c a1 a2 I) = c"

fun l_bound :: "cell_condition \<Rightarrow> padic_nary_function" where
"l_bound (Cond n C c a1 a2 I) = a1"

fun u_bound :: "cell_condition \<Rightarrow> padic_nary_function" where
"u_bound (Cond n C c a1 a2 I) = a2"

fun boundary_condition :: "cell_condition \<Rightarrow> (eint \<Rightarrow> eint \<Rightarrow> eint set)" 
  where
"boundary_condition (Cond n C c a1 a2 I) = I"

lemma condition_decomp:
  assumes "condition = Cond m C c a1 a2 I"
  shows "arity condition = m"
        "fibre_set condition = C"
        "center condition = c"
        "l_bound condition = a1"
        "u_bound condition = a2"
"boundary_condition (Cond n C c a1 a2 I) = I"

apply (simp add: assms)
  apply (simp add: assms)
     apply (simp add: assms)
    apply (simp add: assms)
      apply (simp add: assms)
  by (simp add: assms)

lemma condition_decomp':
"condition = Cond (arity condition) 
                  (fibre_set condition)
                  (center condition)
                  (l_bound condition)
                  (u_bound condition)
                  (boundary_condition condition)"
  using cell_condition.exhaust condition_decomp by metis          

primrec is_cell_condition :: "cell_condition \<Rightarrow> bool" where
"is_cell_condition (Cond n C c a1 a2 I) = (is_semialgebraic n C \<and>
                                        c \<in> carrier (SA n) \<and>
                                        a1 \<in> carrier (SA n) \<and>
                                        a2 \<in> carrier (SA n) \<and>
                                        is_convex_condition I)"

abbreviation are_cell_condition_params :: "nat \<Rightarrow> padic_tuple set  \<Rightarrow>
                                       padic_nary_function \<Rightarrow> 
                                         padic_nary_function \<Rightarrow> 
                                           padic_nary_function \<Rightarrow> 
                      (eint \<Rightarrow> eint \<Rightarrow> eint set) \<Rightarrow> bool" 
where
"are_cell_condition_params n C c a1 a2 I \<equiv> is_cell_condition (Cond n C c a1 a2 I)"

lemma is_cell_conditionE:
  assumes "is_cell_condition (Cond n C c a1 a2 I)"
  shows "is_semialgebraic n C" 
        "c \<in> carrier (SA n)"
        "a1 \<in> carrier (SA n)"
        "a2 \<in> carrier (SA n)"
        "is_convex_condition I"
  using assms is_cell_condition.simps apply blast
  using assms is_cell_condition.simps apply blast
  using assms is_cell_condition.simps apply blast
  using assms is_cell_condition.simps apply blast
  using assms is_cell_condition.simps by blast

lemma is_cell_conditionE':
  assumes "is_cell_condition cond"
  shows "is_semialgebraic (arity cond) (fibre_set cond)"
        "is_semialg_function (arity cond) (center cond)"
        "is_semialg_function (arity cond) (l_bound cond)"
        "is_semialg_function (arity cond) (u_bound cond)"
        " is_convex_condition (boundary_condition cond)"
      apply (metis assms condition_decomp' is_cell_conditionE(1))
  using SA_car_memE(1)  apply (metis assms condition_decomp' is_cell_conditionE(2))
  using SA_car_memE(1)  apply (metis assms condition_decomp' is_cell_conditionE(3))
  using SA_car_memE(1)  apply (metis assms condition_decomp' is_cell_conditionE(4))
  by (metis assms condition_decomp' is_cell_conditionE(5))

lemma is_cell_conditionE'':
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  shows "is_semialgebraic n C"
        "is_semialg_function n c"
        "is_semialg_function n a1"
        "is_semialg_function n a2"
        "c \<in> carrier (SA n)"
        "a1 \<in> carrier (SA n)"
        "a2 \<in> carrier (SA n)"
        "is_convex_condition I"
  using is_cell_conditionE assms   apply blast
  using is_cell_conditionE assms   apply (meson SA_imp_semialg)  
  using is_cell_conditionE assms   apply (meson SA_imp_semialg)
  using is_cell_conditionE assms   apply (meson SA_imp_semialg)
  using is_cell_conditionE assms   apply blast
  using is_cell_conditionE assms   apply blast
  using is_cell_conditionE assms   apply meson  
  using is_cell_conditionE assms   by meson

lemma is_cell_condition_closure:
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "C \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
proof-
  have "is_semialgebraic n C"
    using assms(1) assms(2) is_cell_conditionE''(1) by blast
  then show "C \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using is_semialgebraic_closed[of n C] 
    by blast
qed    

lemma is_cell_condition_closure':
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "c x \<in> carrier Q\<^sub>p"
        "a1 x \<in> carrier Q\<^sub>p"
        "a2 x \<in> carrier Q\<^sub>p"
  using assms is_cell_conditionE''(2)[of \<C> n C c a1 a2 I]
        is_semialg_function_closed[of n c] apply blast 
  using assms is_cell_conditionE''(3)[of \<C> n C c a1 a2 I]
        is_semialg_function_closed[of n a1] apply blast 
  using assms is_cell_conditionE''(4)[of \<C> n C c a1 a2 I]
        is_semialg_function_closed[of n a2] 
  by blast         
  
lemma is_cell_conditionI:
  assumes "is_semialgebraic (arity cond) (fibre_set cond)"
  assumes "(center cond) \<in> carrier (SA (arity cond))"
  assumes "(l_bound cond)  \<in> carrier (SA (arity cond))"
  assumes "(u_bound cond)  \<in> carrier (SA (arity cond))"
  assumes " is_convex_condition (boundary_condition cond)"
  shows   "is_cell_condition cond"
  using assms 
  by (metis (no_types, lifting) condition_decomp' is_cell_condition.simps)
  
lemma is_cell_conditionI':
  assumes "is_semialgebraic n C"
  assumes "c \<in> carrier (SA n)"
  assumes "a1 \<in> carrier (SA n)"
  assumes "a2 \<in> carrier (SA n)"
  assumes "is_convex_condition I"
  shows   "is_cell_condition (Cond n C c a1 a2 I)"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5))

fun condition_to_set :: "cell_condition \<Rightarrow> padic_tuple set" where
"condition_to_set (Cond m C c a1 a2 I) =  cell m C c a1 a2 I"

lemma cell_condition_to_set_subset:
"condition_to_set cond \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc (arity cond)\<^esup>)"
  by (metis cell_subset condition_decomp' condition_to_set.simps)
  
definition is_cell :: "arity \<Rightarrow> padic_tuple set \<Rightarrow> bool" where
"is_cell m S = (\<exists>cond. is_cell_condition cond \<and> S = condition_to_set cond \<and> arity cond = m)"

lemma is_cell_subset:
  assumes "is_cell m S"
  shows "S \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
proof-
  obtain cond where cond_def: " is_cell_condition cond \<and> S = condition_to_set cond \<and> arity cond = m"
    using assms is_cell_def 
    by blast
  then show ?thesis 
    using assms cell_condition_to_set_subset[of cond]
    by blast 
qed

lemma is_cellI:
  assumes "is_cell_condition cond"
  shows "is_cell (arity cond) (condition_to_set cond)"
  using assms is_cell_def 
  by blast

lemma is_cellI':
  assumes "is_cell_condition (Cond n C c a1 a2 I)"
  shows "is_cell n (cell n C c a1 a2 I)"
  using assms 
  by (metis arity.simps condition_to_set.simps is_cell_def)

lemma is_cellI'':
  assumes "is_semialgebraic m C"
  assumes "c \<in> carrier (SA m)"
  assumes "a1 \<in> carrier (SA m)"
  assumes "a2 \<in> carrier (SA m)"
  assumes " is_convex_condition I"
  shows "is_cell m (cell m C c a1 a2 I)"
  using is_cell_conditionI'[of m C c a1 a2 I]
        assms is_cellI'[of m C c a1 a2 I] 
  by blast 

lemma cell_condition_set_memI:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  assumes "\<C> = (Cond m C c a1 a2 I)"
  assumes "(tl as) \<in> C"
  assumes "val (hd as \<ominus> (c (tl as))) \<in> I (val (a1 (tl as))) (val (a2 (tl as)))"
  shows "as \<in> condition_to_set \<C>"
proof-
  have "condition_to_set \<C> = cell m C c a1 a2 I"
    using assms(2) condition_to_set.simps by blast
  have "as \<in> cell m C c a1 a2 I"
    apply(rule cell_memI)
    using assms(1) apply blast
      using assms(3) apply blast
    using assms(4) by blast
  thus ?thesis 
    by (simp add: \<open>as \<in> cell m C c a1 a2 I\<close> \<open>condition_to_set \<C> = cell m C c a1 a2 I\<close>)
qed   

lemma cell_condition_set_memI':
  assumes "C \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "\<C> = (Cond n C c a1 a2 I)"
  assumes "x \<in> C"
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "val (t \<ominus> (c x)) \<in> I (val (a1 x)) (val (a2 x))"
  shows "t#x \<in> condition_to_set \<C>"
  apply(rule cell_condition_set_memI[of _ n \<C> C c a1 a2 I])
  using assms cartesian_power_cons[of x Q\<^sub>p n t] cell_memE(1) cell_memI'  apply blast
    using assms(2) apply blast 
      using assms(3) apply (simp add: assms(3))
        by (metis assms(5) list.sel(1) list.sel(3))
   
lemma cell_condition_set_memE:
  assumes "is_cell_condition \<C>"
  assumes "\<C> = (Cond n C c a1 a2 I)"
  assumes "x \<in> condition_to_set \<C>"
  shows "x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
        "tl x \<in> C"
        "val (hd x \<ominus> (c (tl x))) \<in> I (val (a1 (tl x))) (val (a2 (tl x)))"
  using cell_memE[of x n C c a1 a2 I] assms(2) assms(3) condition_to_set.simps apply blast
  using cell_memE[of x n C c a1 a2 I] assms(2) assms(3) condition_to_set.simps apply blast
  using cell_memE[of x n C c a1 a2 I] assms(2) assms(3) condition_to_set.simps by blast

lemma condition_to_set_memE:
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  assumes "as \<in> condition_to_set \<C>"
  shows "tl as \<in> C"
         "val ((hd as) \<ominus> (c (tl as)))
            \<in> I (val (a1 (tl as))) (val (a2 (tl as)))"
proof-
  show "tl as \<in> C"
    using assms  condition_to_set.simps[of n C c a1 a2 I]
    unfolding cell_def 
    by(metis (no_types, lifting) cell_def condition_to_set.simps mem_Collect_eq)
  show "val ((hd as) \<ominus> (c (tl as)))
            \<in> I (val (a1 (tl as))) (val (a2 (tl as)))"
    using assms  condition_to_set.simps[of n C c a1 a2 I]
    unfolding cell_def 
    by blast
qed    

lemma condition_to_set_memE':
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  assumes "t#x \<in> condition_to_set \<C>"
  shows "x \<in> C"
    "val (t \<ominus> (c x))
            \<in> I (val (a1 x)) (val (a2 x))"
  using assms condition_to_set_memE
   apply (metis cell_formula(2) condition_to_set.simps)
  using assms condition_to_set_memE
  by (metis cell_formula(3) condition_to_set.simps)

lemma carrier_is_cell:
"\<exists> \<C>. is_cell_condition \<C> \<and> arity \<C> = n \<and>  \<C> = Cond n (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<zero>\<^bsub>SA n\<^esub> \<zero>\<^bsub>SA n\<^esub> \<zero>\<^bsub>SA n\<^esub> closed_ray \<and>
           condition_to_set \<C> = carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
proof-
  obtain I:: "eint \<Rightarrow> eint \<Rightarrow> eint set" where I_def: "I = closed_ray"
    by blast 
  obtain a where a_def: "a = \<zero>\<^bsub>SA n\<^esub>"
    by blast 
  have a_closed: "a \<in> carrier (SA n)"
    using SA_is_ring  a_def ring.ring_simprules(2) by blast
  obtain \<C> where \<C>_def: "\<C> = Cond n (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) a a a I"
    by blast 
  have 0: "is_cell_condition \<C>"
    unfolding \<C>_def is_cell_condition.simps using a_closed unfolding is_convex_condition_def I_def 
    using carrier_is_semialgebraic by blast
  have 1: "condition_to_set \<C> = carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  proof
    show "condition_to_set \<C> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
      using 0 unfolding \<C>_def 
      by (metis arity.simps is_cell_subset padic_fields.is_cellI padic_fields_axioms)
    show "carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<subseteq> condition_to_set \<C>"
    proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
      have 0: "hd x \<in> carrier Q\<^sub>p"
        using A cartesian_power_head by blast 
      have 1: "tl x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        using A cartesian_power_tail by blast
      then obtain b t where at_def: "b \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<and> t \<in> carrier Q\<^sub>p \<and> x = t#b"
        using 0 by (metis (no_types, opaque_lifting) A One_nat_def 
            cartesian_power_car_memE list.discI list.expand list.sel(1) list.sel(2) list.sel(3) 
            list.size(3) Qp.to_R1_to_R)
      have 2: "(\<zero>\<^bsub>SA n\<^esub> (tl (t # b))) = \<zero>"
        using SA_zeroE at_def 1 by blast
      have "t#b \<in> condition_to_set \<C>"
        unfolding \<C>_def condition_to_set.simps apply(rule cell_memI)
        using A at_def apply blast
         apply (simp add: at_def)
        unfolding a_def 2 I_def val_zero closed_ray_def 
        using eint_ord_code(3) by blast
      thus " x \<in> condition_to_set \<C>"
        using at_def by blast 
    qed
  qed
  thus ?thesis 
    using "0" \<C>_def arity.simps unfolding a_def I_def by blast 
qed

lemma equal_CondI:
  assumes "arity \<C> = m"
  assumes "fibre_set \<C> = B"
  assumes "center \<C> = c"
  assumes "l_bound \<C> = a1"
  assumes "u_bound \<C> = a2"
  assumes "boundary_condition \<C> = I"
  shows "\<C> = Cond m B c a1 a2 I"
  using assms condition_decomp' by blast

lemma val_dist_sym:
 "\<lbrakk>a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p\<rbrakk>\<Longrightarrow> val (a \<ominus> b) = val (b \<ominus> a)"
proof- fix a b assume A: "a \<in> carrier Q\<^sub>p" " b \<in> carrier Q\<^sub>p"
  have 0: "b \<ominus> a = \<ominus>(a \<ominus> b)"
    using A 
    by (meson Qp.minus_a_inv)
  show "val (a \<ominus> b) = val (b \<ominus> a)"
    unfolding 0 using A 
    by (meson Qp.cring_simprules(4) val_minus)
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Cells are Semialgebraic\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context padic_fields
begin

lemma convex_condition_induct:
  assumes "is_convex_condition I"
  assumes "P closed_interval"
  assumes "P left_closed_interval"
  assumes "P closed_ray"
  assumes "P open_ray"
  shows "P I"
  using assms unfolding is_convex_condition_def 
  by blast
  
definition is_interval where
"is_interval I = (I = closed_interval \<or> I = left_closed_interval)"

definition is_ray where
"is_ray I = (I = closed_ray \<or> I = open_ray)"

lemma is_intervalE:
  assumes "is_interval I"
  shows "I = closed_interval \<or> I = left_closed_interval"
  using assms unfolding is_interval_def by blast 

lemma is_intervalI:
  assumes "I = closed_interval"
  shows "is_interval I"
  by (simp add: assms is_interval_def)

lemma is_intervalI':
  assumes "I = left_closed_interval"
  shows "is_interval I"
  by (simp add: assms is_interval_def)

lemma is_rayE:
  assumes "is_ray I"
  shows "I = closed_ray \<or> I = open_ray"
  using assms unfolding is_ray_def by blast 

lemma is_rayI:
  assumes "I = closed_ray"
  shows "is_ray I"
  by (simp add: assms is_ray_def)

lemma is_rayI':
  assumes "I = open_ray"
  shows "is_ray I"
  by (simp add: assms is_ray_def)

lemma mem_Collect_inter:
"{x \<in> S. P1 x \<and> P2 x} = {x \<in> S. P1 x} \<inter> {x \<in> S. P2 x}"
  by blast 

lemma semialg_convexity_condition_is_semialg:
  assumes "a1 \<in> carrier (SA m)"
  assumes "a2 \<in> carrier (SA m)"
  assumes "f \<in> carrier (SA m)"
  assumes "is_convex_condition I"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (f x) \<in> I (val (a1 x)) (val (a2 x))}"
proof(cases "I = closed_interval")
  case True
  then show ?thesis unfolding True closed_interval_def mem_Collect_eq 
    using assms semialg_val_ineq_set_is_semialg[of  f m a2]
    semialg_val_ineq_set_is_semialg[of  a1 m f]
    intersection_is_semialg[of m "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (a1 x) \<le> val (f x)}" 
              "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (f x) \<le> val (a2 x)}"]  
    unfolding mem_Collect_inter by blast
next 
  case F0: False
  show ?thesis  
  proof(cases "I = left_closed_interval")
    case True
      then show ?thesis unfolding True left_closed_interval_def mem_Collect_eq 
    using assms semialg_val_strict_ineq_set_is_semialg[of  f m a2]
    semialg_val_ineq_set_is_semialg[of  a1 m f]
    intersection_is_semialg[of m "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (a1 x) \<le> val (f x)}" 
              "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (f x) < val (a2 x)}"]  
    unfolding mem_Collect_inter by blast
  next
    case F1: False
    show ?thesis 
    proof(cases "I = closed_ray")
      case True
      show ?thesis unfolding True closed_ray_def mem_Collect_eq 
    using assms semialg_val_ineq_set_is_semialg[of  f m a2] assms  by blast 
    next
      case False
      then have 0: "I = open_ray"
        using assms F1 F0 unfolding is_convex_condition_def by blast 
      show ?thesis unfolding 0 open_ray_def mem_Collect_eq 
    using assms semialg_val_strict_ineq_set_is_semialg[of  f m a2] assms  by blast 
  qed
 qed
qed

lemma condition_to_set_is_semialg:
  assumes "is_cell_condition \<C>"
  assumes "arity \<C> = m"
  shows "is_semialgebraic (Suc m) (condition_to_set \<C>)"
proof- 
  obtain C c a1 a2 I where param_defs: "\<C> = Cond m C c a1 a2 I"
    using assms condition_decomp' by blast
  obtain f1 where f1_def: "f1 = drop_apply (Suc m) (Suc 0) a1"
    by blast 
  obtain f2 where f2_def: "f2 = drop_apply (Suc m) (Suc 0) a2"
    by blast 
  have a1_closed: "a1 \<in> carrier (SA m)"
    using param_defs assms is_cell_conditionE(3) by blast
  have a2_closed: "a2 \<in> carrier (SA m)"
    using param_defs assms is_cell_conditionE(4) by blast 
  have c_closed: "c \<in> carrier (SA m)"
    using param_defs assms is_cell_conditionE(2) by blast
  have f1_closed: "f1 \<in> carrier (SA (Suc m))"
    using drop_apply_closed a1_closed unfolding f1_def 
    by (metis One_nat_def diff_Suc_1 le_0_eq nat.simps(3) not_less_eq_eq padic_fields.drop_apply_SA_closed padic_fields_axioms)
  have f2_closed: "f2 \<in> carrier (SA (Suc m))"
    using  a2_closed unfolding f2_def 
    by (metis One_nat_def diff_Suc_1 le_0_eq nat.simps(3) not_less_eq_eq padic_fields.drop_apply_SA_closed padic_fields_axioms)
  obtain g where g_def: "g = Qp_ith (Suc m) 0 \<ominus>\<^bsub>SA (Suc m)\<^esub> drop_apply (Suc m) (Suc 0) c"
    by blast 
  have g_closed: "g \<in> carrier (SA (Suc m))"
    using Qp_ith_closed[of 0 "Suc m"] drop_apply_closed[of c "Suc 0" "Suc m"] c_closed  
    using SA_minus_closed g_def le_simps(1) lessI drop_apply_SA_closed zero_less_Suc 
    by (metis (no_types, lifting) One_nat_def Suc_lessI diff_Suc_1 diff_is_0_eq)
  have "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> g x = Qp_ith (Suc m) 0 x \<ominus> drop_apply (Suc m) (Suc 0) c x"
    unfolding g_def using drop_apply_SA_closed[of c "Suc m" 1] Qp_ith_closed 
    by (metis One_nat_def SA_minus_eval Suc_leI c_closed diff_Suc_1 zero_less_Suc)
  hence 00: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> g x = x!0 \<ominus> c (drop (Suc 0) x)"
    unfolding g_def Qp_ith_def drop_apply_def restrict_def comp_apply 
    by presburger
  hence g_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> g x = hd x \<ominus> c (tl x)"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    have xl: "length x = Suc m"
      using A cartesian_power_car_memE by blast
    have 0: "hd x = x!0"
      using xl 
      by (metis Zero_not_Suc hd_conv_nth list.size(3))
    have 1: "drop (Suc 0) x = tl x"  
      by (simp add: drop_Suc)
    show "g x = lead_coeff x \<ominus> c (tl x)"
      using 00[of x] A unfolding 0 1  by blast 
  qed
  have f1_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> f1 x = a1 (tl x)"
    unfolding f1_def drop_apply_def restrict_def comp_apply drop_Suc 
    by (metis drop0)
  have f2_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> f2 x = a2 (tl x)"
    unfolding f2_def drop_apply_def restrict_def comp_apply drop_Suc 
    by (metis drop0)
  have 0: "{ x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). val (hd x \<ominus> c (tl x)) \<in>  I (val (a1 (tl x))) (val (a2 (tl x)))} = 
           {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).  val (g x) \<in>  I (val (f1 x)) (val (f2 x))}"
    apply(rule equalityI')
    unfolding mem_Collect_eq using f1_eval f2_eval g_eval by auto 
  have 1: "is_semialgebraic (Suc m) {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). val (hd x \<ominus> c (tl x)) \<in>  I (val (a1 (tl x))) (val (a2 (tl x)))}"
    unfolding 0 apply(intro semialg_convexity_condition_is_semialg f1_closed f2_closed g_closed 
                            is_cell_conditionE[of m C c a1 a2 I])
    using assms unfolding param_defs by auto 
  have 2: "is_semialgebraic (Suc m) {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C}"
  proof-
    have d: "(Suc 0) + m = Suc m"
      by auto 
    have e: "C \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using param_defs assms is_cell_conditionE''(1) is_semialgebraic_closed[of m C] drop_Suc[of 0]
      by blast 
    have f: "{x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C} = cartesian_product (carrier (Q\<^sub>p\<^bsup>Suc 0\<^esup>)) C"
      apply(intro equalityI' cartesian_product_memI[of _ Q\<^sub>p "Suc 0"_ m] e 
                  take_closed[of "Suc 0" "Suc m"], 
            unfold drop0 drop_Suc[of 0] mem_Collect_eq)
      using e cartesian_product_memE(2)[of _ "carrier (Q\<^sub>p\<^bsup>Suc 0\<^esup>)" C Q\<^sub>p "Suc 0"] 
          cartesian_product_closed[of "carrier (Q\<^sub>p\<^bsup>Suc 0\<^esup>)" Q\<^sub>p "Suc 0" C m] 
      unfolding drop0 d drop_Suc[of 0] by auto
    have g: "is_semialgebraic m C"
      using param_defs assms is_cell_conditionE''(1) is_semialgebraic_closed[of m C] drop_Suc[of 0]
      by blast 
    show ?thesis unfolding f using cartesian_product_is_semialgebraic[of 1 "carrier (Q\<^sub>p\<^bsup>Suc 0\<^esup>)" m C] g 
      by (simp add: carrier_is_semialgebraic)
  qed
  have 3: "condition_to_set \<C> = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C} \<inter> 
                 {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). val (hd x \<ominus> c (tl x)) \<in>  I (val (a1 (tl x))) (val (a2 (tl x)))}"
    unfolding param_defs condition_to_set.simps cell_def by auto 
  show ?thesis 
    unfolding 3 by(intro intersection_is_semialg 1 2)
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Cell Decompositions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Denef's proof of Macintyre's Theorem proceeds by proving two cell decomposition theorems. These 
theorems, which Denef numbers $I$ and $II$, state that the set $\mathbb{Q}_p^{m+1}$ can be 
decomposed into $p$-adic cells such that one or more $p$-adic polynomials are well-behaved on each 
cell. Towards the proofs of these facts, we formalize the notion of a cell decomposition of a 
semialgebraic set, and prove several important lemmas about them. \<close>

context padic_fields
begin

text\<open>Since cells are identified by their defining parameters instead of by their underlying sets, 
there is a slight technical detail that complicates the following definition. Instead of simply 
defining a cell decomposition as a finite collection of cells whose underlying sets partition the 
larger set, we have to add the condition that distinct cells are disjoint. If we did not, we could 
have a set with two different cells which define the exact same set. Then the collection of 
underlying sets would still partition the larger set, but there would be an undesirable redundancy 
in our decomposition.\<close>

definition is_cell_decomp :: "arity \<Rightarrow> cell_condition set \<Rightarrow> padic_tuple set \<Rightarrow> bool" where
"is_cell_decomp n S A \<equiv> finite S \<and> (\<forall>s \<in> S. is_cell_condition s \<and> arity s = n) \<and>
                                      ((condition_to_set ` S) partitions A) \<and> 
                                          (A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) \<and> 
                                    (\<forall> s \<in> S. \<forall>s' \<in> S. s \<noteq> s' \<longrightarrow>condition_to_set s \<inter> condition_to_set s' = {})" 

lemma is_cell_decompI:
  assumes "finite S"
  assumes "((condition_to_set ` S) partitions A)"
  assumes "\<And>s. s \<in> S \<Longrightarrow> is_cell_condition s \<and> arity s = n"
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes "\<And>s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
  shows "is_cell_decomp n S A"
proof-
  have "\<forall> s \<in> S. \<forall>s' \<in> S. s \<noteq> s' \<longrightarrow>condition_to_set s \<inter> condition_to_set s' = {}"
    using assms by blast
  thus ?thesis 
  using assms unfolding is_cell_decomp_def by blast 
qed  

lemma is_cell_decompI':
  assumes "finite S"
  assumes "\<And>A B. A \<in> condition_to_set ` S \<Longrightarrow> B \<in> condition_to_set ` S \<Longrightarrow> A \<noteq> B \<Longrightarrow> A \<inter> B = {}"
  assumes " \<Union> (condition_to_set ` S) = B"
  assumes "\<And>s. s \<in> S \<Longrightarrow> is_cell_condition s \<and> arity s = m"
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  assumes "\<And>s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<noteq>  condition_to_set s'"
  shows "is_cell_decomp m S B"
  apply(rule is_cell_decompI) using assms apply blast 
  apply(rule is_partitionI) apply(rule disjointI)
  using assms apply blast using assms  apply blast using assms apply meson 
  using assms apply blast using assms(5) assms(2) 
  by (meson assms(6) image_eqI)  

lemma is_cell_decompE:
  assumes "is_cell_decomp n S A"
  shows  "finite S"
         "(condition_to_set ` S) partitions A"
         "\<And>s. s \<in> S \<Longrightarrow> is_cell_condition s"
         "\<And>s. s \<in> S \<Longrightarrow>arity s = n"
         "\<And>s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
         "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  using assms is_cell_decomp_def apply blast
  using assms is_cell_decomp_def apply blast
  using assms is_cell_decomp_def  apply meson
  using assms is_cell_decomp_def  apply meson
  using assms is_cell_decomp_def apply meson
  using assms is_cell_decomp_def by blast 

lemma is_cell_decomp_subset:
  assumes "is_cell_decomp n S A"
  assumes "s \<in> S"
  shows   "condition_to_set s \<subseteq> A"
proof-
  have "(condition_to_set ` S) partitions A"
    using assms is_cell_decompE(2) 
    by blast
  then show 0: "condition_to_set s \<subseteq> A"
    by (metis Sup_upper assms(2) image_eqI is_partitionE(2))
qed

lemma cell_decomp_imp_semialgebraic:
  assumes "is_cell_decomp m S B"
  shows "is_semialgebraic (Suc m)  B"
proof- 
  have 0: "B = (\<Union> s \<in> S. condition_to_set s)"
    using assms is_cell_decompE(2)[of m S B] is_partitionE[of "condition_to_set ` S"] by auto 
  show ?thesis unfolding 0 
    apply(rule finite_union_is_semialgebraic')
    using is_cell_decompE(1) assms apply blast
    apply(rule subsetI)
    using assms is_cell_decompE(3)[of m S B] condition_to_set_is_semialg unfolding is_semialgebraic_def
    by (metis image_iff is_cell_decompE(4))
qed

lemma is_cell_decomp_pairwise_disjoint:
  assumes "is_cell_decomp n S A"
  assumes "s \<in> S"
  assumes "s' \<in> S"
  assumes "s \<noteq> s'"
  shows   "condition_to_set s \<inter> condition_to_set s' = {}"
  using assms is_cell_decompE(5)[of n S A s s'] is_cell_decompE(2)[of n S A]
          is_partitionE[of "condition_to_set ` S" A] 
          disjointE[of "condition_to_set ` S" "condition_to_set s" "condition_to_set s'"] 
  by blast 
end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Refinements of Cell Decompositions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>The basic technique for building the desired cell decompositions in the conclusions of Denef's 
theorems will be to start from some basic cell decomposition of a set, and to successively decompose 
each cell in that decomposition into finer decompositions, until we have reached a collection of 
cells with the desired property. One basic way to do this is by noticing that any semialgebraic 
partition of the fibre set of a cell induces an obvious cell decomposition of the underlying set of 
the cell. Each cell in this decomposition will have all of the same defining parameters, except the 
fibre sets will come from the partition. This is what the function \texttt{refine\_fibres} will be 
used for. \<close>

context padic_fields 
begin

definition subcell :: "cell_condition \<Rightarrow> cell_condition \<Rightarrow> bool"where
"subcell C1 C2 = (arity C1 = arity C2 \<and> condition_to_set C1 \<subseteq> condition_to_set C2)"

lemma subcellI:
  assumes "arity C1 = arity C2"
  assumes "condition_to_set C1 \<subseteq> condition_to_set C2"
  shows "subcell C1 C2"
  using assms unfolding subcell_def by blast 

lemma subcellE:
  assumes "subcell C1 C2"
  shows "arity C1 = arity C2"
        "condition_to_set C1 \<subseteq> condition_to_set C2"
  using assms unfolding subcell_def apply blast 
  using assms unfolding subcell_def by blast 

definition is_refinement :: "arity \<Rightarrow> padic_tuple set \<Rightarrow> cell_condition set \<Rightarrow> cell_condition set \<Rightarrow>  bool" 
          where

"is_refinement n A S1 S2 \<equiv> (is_cell_decomp n S1 A) \<and> 
                            (is_cell_decomp n S2 A) \<and>
                              (\<forall>s1 \<in> S1. \<exists> s2 \<in> S2. subcell s1 s2)"

lemma projection_to_fibre_set:
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  shows "(tl) ` (condition_to_set \<C>) \<subseteq> C"
proof
  fix x assume A: "x \<in> tl ` condition_to_set \<C>"
  then obtain as where "as \<in> condition_to_set \<C> \<and> tl as = x"
    by blast
  then show "x \<in> C"
    using assms(2) condition_to_set.simps[of n C c a1 a2 I] 
    unfolding cell_def
    by blast
qed

text\<open>Subcells obtained by subsets of the fibre set\<close>

lemma fibre_set_subset:
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  assumes "C' \<subseteq> C"
  assumes "is_semialgebraic n C'"
  shows "is_cell_condition (Cond n C' c a1 a2 I)"
        "subcell (Cond n C' c a1 a2 I) \<C>"
proof-
  show 0: "is_cell_condition (Cond n C' c a1 a2 I)"
    apply(rule is_cell_conditionI)
    using assms arity.simps fibre_set.simps apply presburger
    using assms  apply (metis arity.simps center.simps is_cell_conditionE(2))
    apply (metis arity.simps assms(1) assms(2) is_cell_conditionE(3) l_bound.simps)
    apply (metis arity.simps assms(1) assms(2) is_cell_conditionE(4) u_bound.simps)
    by (metis assms(1) assms(2) boundary_condition.simps is_cell_conditionE(5))
  show "subcell (Cond n C' c a1 a2 I) \<C>"
    apply(rule subcellI)
    using assms  arity.simps apply presburger
  proof-
    show "condition_to_set (Cond n C' c a1 a2 I) \<subseteq> condition_to_set \<C>"
    proof fix x assume A: "x \<in> condition_to_set (Cond n C' c a1 a2 I)"
      show "x \<in> condition_to_set \<C>"
        apply(rule cell_condition_set_memI[of _ n \<C> C c a1 a2 I])
        using A 0 cell_condition_set_memE(1) apply presburger
        using A 0 cell_condition_set_memE assms(2) apply blast
        using A cell_condition_set_memE(2)[of _ n C' c a1 a2 I x] assms(2) 0 assms(3) apply blast
        using "0" A cell_condition_set_memE(3) by blast
    qed
  qed   
qed

text\<open>Replaces the fibre set of a cell with a new set\<close>

definition refine_fibres where
"refine_fibres \<C> C' = Cond (arity \<C>) C' (center \<C>) (l_bound \<C>) (u_bound \<C>) (boundary_condition \<C>)"

lemma refine_fibres_is_subcell:
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  assumes "C' \<subseteq> C"
  assumes "is_semialgebraic n C'"
  shows "subcell (refine_fibres \<C> C') \<C>"
  unfolding refine_fibres_def using fibre_set_subset assms arity.simps boundary_condition.simps
      center.simps l_bound.simps u_bound.simps by presburger

lemma refine_fibres_is_cell:
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  assumes "C' \<subseteq> C"
  assumes "is_semialgebraic n C'"
  shows "is_cell_condition (refine_fibres \<C> C')"
  apply(rule is_cell_conditionI)
  using assms  condition_decomp(1) fibre_set.simps refine_fibres_def apply presburger
  apply (metis arity.simps assms(1) assms(2) center.simps is_cell_conditionE(2) refine_fibres_def)
  apply (metis arity.simps assms(1) assms(2) is_cell_conditionE(3) l_bound.simps refine_fibres_def)
  apply (metis arity.simps assms(1) assms(2) is_cell_conditionE(4) refine_fibres_def u_bound.simps)
  by (simp add: assms(1) is_cell_conditionE'(5) refine_fibres_def)

lemma refine_fibres_fibre_set[simp]:
"fibre_set (refine_fibres \<C> C') = C'"
  unfolding refine_fibres_def  
  using fibre_set.simps by blast

lemma refine_fibres_fibre_sets[simp]:
"fibre_set ` (refine_fibres \<C> ` Cs) = Cs"
proof-
  have 0: "\<And>a. a \<in> Cs \<Longrightarrow> fibre_set (refine_fibres \<C> a) = a"
    using refine_fibres_fibre_set by blast
  have 1: "fibre_set ` refine_fibres \<C> ` Cs \<subseteq> Cs"
    by (metis (mono_tags, lifting) image_iff image_subsetI refine_fibres_fibre_set)
  have 2: "Cs \<subseteq> fibre_set ` refine_fibres \<C> ` Cs"
    using "0" by blast
  show ?thesis using 1 2 by blast 
qed

lemma disj_fibres_imp_disj_cells:
  assumes "C0 \<inter> C1 = {}"
  assumes "\<C>0 = Cond n C0 c a1 a2 I"
  assumes "\<C>1 = Cond n' C1 c' a1' a2' I'"
  shows "condition_to_set \<C>0 \<inter> condition_to_set \<C>1 = {}"
proof-
  have "\<And>x. x \<in> condition_to_set \<C>0 \<Longrightarrow> x \<notin> condition_to_set \<C>1"
  proof- fix x assume A: "x \<in> condition_to_set \<C>0"
    then have 0: "tl x \<in> C0"
      using A assms cell_memE(2) padic_fields.condition_to_set.simps padic_fields_axioms by blast
    then have "tl x \<notin> C1"
      using assms  by blast
    then show "x \<notin> condition_to_set \<C>1"
      using assms(3) cell_memE(2) condition_to_set.simps by blast
  qed
  then show ?thesis by blast 
qed

lemma fibre_subset_imp_cell_subset:
  assumes "C0 \<subseteq> C1"
  assumes "\<C>0 = Cond n C0 c a1 a2 I"
  assumes "\<C>1 = Cond n C1 c a1 a2 I"
  assumes "is_cell_condition \<C>1"
  shows "condition_to_set \<C>0 \<subseteq> condition_to_set \<C>1"
proof fix x assume A: "x \<in> condition_to_set \<C>0"
  show "x \<in> condition_to_set \<C>1"
    apply(rule cell_condition_set_memI[of _ n \<C>1 C1 c a1 a2 I])
    using assms cell_condition_to_set_subset[of "\<C>1"] apply (metis A cell_memE(1) condition_to_set.simps)
    using assms(3) apply blast
    using A assms(1) assms(2) cell_memE(2) condition_to_set.simps apply blast
    using A assms(2) cell_memE(3) condition_to_set.simps by blast
qed

lemma fibre_subset_imp_cell_subset':
  assumes "C0 \<subseteq> fibre_set \<C>"
  assumes "is_cell_condition \<C>"
  shows "condition_to_set (refine_fibres \<C> C0) \<subseteq> condition_to_set \<C>"
  unfolding refine_fibres_def 
  using fibre_subset_imp_cell_subset assms condition_decomp'[of \<C>]
  by blast 

lemma fibre_subset_imp_cell_subset'':
  assumes "C0 \<subseteq> fibre_set \<C>"
  assumes "is_cell_condition \<C>"
  assumes "x \<in> condition_to_set \<C>"
  assumes "tl x \<in> C0"
  shows "x \<in> condition_to_set (refine_fibres \<C> C0)"
  apply(rule cell_condition_set_memI[of _ "arity \<C>" _ C0 "center \<C>" "l_bound \<C>" "u_bound \<C>" "boundary_condition \<C>"])
  using assms cell_condition_set_memE(1) condition_decomp' apply blast
  using refine_fibres_def apply blast
  using assms apply blast  
  using assms cell_condition_set_memE(3) condition_decomp' by blast 

lemma partition_to_cell_decomp:
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond n C c a1 a2 I"
  assumes "Cs partitions C"
  assumes "are_semialgebraic n Cs"
  assumes "finite Cs"
  shows "is_cell_decomp n (refine_fibres \<C> ` Cs) (condition_to_set \<C>) "
proof(rule is_cell_decompI)
  show "finite (refine_fibres \<C> ` Cs)"
    using assms by blast
  show 0: "condition_to_set ` refine_fibres \<C> ` Cs partitions condition_to_set \<C>"
  proof(rule is_partitionI)
    show "disjoint (condition_to_set ` refine_fibres \<C> ` Cs)"
    proof(rule disjointI)
      fix A B assume A: "A \<in> condition_to_set ` refine_fibres \<C> ` Cs" 
                        "B \<in> condition_to_set ` refine_fibres \<C> ` Cs"
                        "A \<noteq>  B"
      show "A \<inter> B = {}"
      proof-
        obtain a where a_def: "a \<in> Cs \<and> A = condition_to_set (Cond n a c a1 a2 I)"
          using A(1) unfolding assms refine_fibres_def  arity.simps  l_bound.simps
          u_bound.simps boundary_condition.simps center.simps by auto 
        obtain b where b_def: "b \<in> Cs \<and> B = condition_to_set (Cond n b c a1 a2 I)"
          using A(2) unfolding assms refine_fibres_def  arity.simps  l_bound.simps
          u_bound.simps boundary_condition.simps center.simps by auto        
        have "a \<inter> b = {}" using a_def b_def assms 
          using A(3) disjointE is_partitionE(1) by blast
        thus ?thesis using disj_fibres_imp_disj_cells a_def b_def by blast
      qed
    qed
    show "\<Union> (condition_to_set ` refine_fibres \<C> ` Cs) = condition_to_set \<C>"
    proof
      show "\<Union> (condition_to_set ` refine_fibres \<C> ` Cs) \<subseteq> condition_to_set \<C>"
      proof fix x assume A: " x \<in> \<Union> (condition_to_set ` refine_fibres \<C> ` Cs)"
        then obtain C' where C'_def: "C' \<in> Cs \<and> x \<in> condition_to_set (refine_fibres \<C> C')"
          by blast 
        have 0: "C' \<subseteq> C"
          using C'_def  assms is_partitionE[of Cs C] 
          by blast
        then show "x \<in> condition_to_set \<C>"
          using assms  fibre_subset_imp_cell_subset'[of C' \<C>] C'_def fibre_set.simps by blast
      qed
      show "condition_to_set \<C> \<subseteq> \<Union> (condition_to_set ` refine_fibres \<C> ` Cs)"
      proof fix x assume A: "x \<in> condition_to_set \<C> "
        then have 0: "tl x \<in> C"
          using assms(1) assms(2) cell_condition_set_memE(2) by blast
        then obtain C0 where C0_def: "C0 \<in> Cs \<and> tl x \<in> C0"
          using assms is_partitionE(2) 
          by (metis (no_types, lifting) Union_iff)
        then have 0: "x \<in> condition_to_set (refine_fibres \<C> C0)"
          using fibre_subset_imp_cell_subset'' 
          by (metis (no_types, lifting) A assms(1) assms(2) assms(3) assms(5) fibre_set.simps is_partitionE(2) le_cSup_finite)
        show "x \<in> \<Union> (condition_to_set ` refine_fibres \<C> ` Cs)"
          using C0_def 0 by blast 
      qed
    qed
  qed
  show "\<And>s. s \<in> refine_fibres \<C> ` Cs \<Longrightarrow> is_cell_condition s \<and> arity s = n"
    using are_semialgebraicE assms(1) assms(2) assms(4) refine_fibres_def by force
  show "condition_to_set \<C> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    by (simp add: assms(2) cell_subset)    
  show "\<And>s s'. s \<in> refine_fibres \<C> ` Cs \<Longrightarrow> s' \<in> refine_fibres \<C> ` Cs \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
  proof- fix s s' assume A: "s \<in> refine_fibres \<C> ` Cs" "s' \<in> refine_fibres \<C> ` Cs" "s \<noteq> s'"
    then obtain a where a_def: "a \<in> Cs \<and> s = refine_fibres \<C> a"
      by blast
    obtain b where b_def: "b \<in> Cs \<and> s' = refine_fibres \<C> b" 
      using A(2) by blast
    have a_neq_b: "a \<noteq> b"
      using A a_def b_def by meson
    have "a \<inter> b = {}"
      using A a_def b_def assms is_cell_decompE 
      by (meson a_neq_b disjointE is_partitionE(1))      
    thus  "condition_to_set s \<inter> condition_to_set s' = {}"
      using a_neq_b a_def b_def condition_to_set.simps  unfolding refine_fibres_def cell_def 
      using disj_fibres_imp_disj_cells[of a b s _ _ _ _ _ s'] 
      by presburger
  qed
qed

text\<open>This lemma establishes that if we have a function which maps each cell in a cell decomposition 
to a cell decomposition of itself, we can assemble all of these into a cell decomposition of the 
larger set. \<close>

lemma cell_decomp_parametric_refinement:
  assumes "is_cell_decomp n S U"
  assumes "\<And>\<C>. \<C> \<in> S \<Longrightarrow> is_cell_decomp n (F \<C>) (condition_to_set \<C>)"
  shows "is_cell_decomp n (\<Union> (F`S))  U"
proof(rule is_cell_decompI)
  show "finite (\<Union> (F ` S))"
  proof-
    have 0: "finite S"
      using assms is_cell_decompE(1) by blast
    have 1: "\<And>\<C>. \<C> \<in> S \<Longrightarrow> finite (F \<C>)"
      using assms is_cell_decompE(1) by blast
    show ?thesis using 0 1 
      by blast
  qed
  show 0: "condition_to_set ` \<Union> (F ` S) partitions U"
  proof(rule is_partitionI)
    show "disjoint (condition_to_set ` \<Union> (F ` S))"
    proof(rule disjointI)
      fix A  B assume A: "A \<in> condition_to_set ` \<Union> (F ` S)" "B \<in> condition_to_set ` \<Union> (F ` S) "
                         "A \<noteq> B"
      obtain C0 C1 where C_def: "C0 \<in> S \<and> C1 \<in> (F C0) \<and> A = condition_to_set C1"
        using A(1) by blast 
      obtain D0 D1 where D_def: "D0 \<in> S \<and> D1 \<in> (F D0) \<and> B = condition_to_set D1"
        using A(2) by blast 
      have 0: "A \<subseteq> condition_to_set C0"
        using C_def assms is_cell_decomp_subset by blast
      have 1: "B \<subseteq> condition_to_set D0"
        using D_def assms is_cell_decomp_subset by blast 
      show "A \<inter> B = {}"
      proof(cases "C0 = D0")
        case True
        then have T0: "C1 \<noteq> D1" using A 
          using C_def D_def by blast
        have T1: "D1 \<in> (F C0)"
          using True D_def by blast 
        show ?thesis using T0 T1 assms  assms(2)[of C0] 
          unfolding is_cell_decomp_def disjointE  
          by (metis C_def D_def True)
      next
        case False
        have F0: "disjoint (condition_to_set ` S)"
          using assms is_cell_decompE(2) is_partitionE(1) by blast
        then have "condition_to_set C0  \<inter> condition_to_set D0 = {}"
          using C_def D_def disjointE[of "condition_to_set ` S" "condition_to_set C0"  "condition_to_set C1"]
          False 
          by (meson assms is_cell_decomp_pairwise_disjoint)
        then show ?thesis using 0 1  
          by blast        
      qed
    qed
    show "\<Union> (condition_to_set ` \<Union> (F ` S)) = U"
    proof 
      show "\<Union> (condition_to_set ` \<Union> (F ` S)) \<subseteq> U"
      proof fix x assume A: "x \<in> \<Union> (condition_to_set ` \<Union> (F ` S))"
        then obtain s where s_def: "s \<in> \<Union> (F ` S) \<and> x \<in> condition_to_set s"
          by blast 
        have "condition_to_set s \<subseteq> U"
          by (metis (no_types, lifting) UN_E assms dual_order.trans is_cell_decomp_subset s_def)
        thus "x \<in> U " using s_def by blast 
      qed
      show "U \<subseteq> \<Union> (condition_to_set ` \<Union> (F ` S))"
      proof fix x assume A: "x \<in> U"
        then obtain s where s_def: "s \<in> \<Union> (F`S) \<and> x \<in> condition_to_set s"
          by (metis (mono_tags, lifting) UN_E UN_I assms is_cell_decompE(2) is_partitionE(2))
        then show "x \<in> \<Union> (condition_to_set ` \<Union> (F ` S))"
          by blast 
      qed
    qed
  qed
  show "\<And>s. s \<in> \<Union> (F ` S) \<Longrightarrow> is_cell_condition s \<and> arity s = n"
    using assms 
    by (meson UN_E is_cell_decomp_def)
  show "U \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    using assms is_cell_decompE(6) by blast      
  show " \<And>s s'.
       s \<in> \<Union> (F ` S) \<Longrightarrow>
       s' \<in> \<Union> (F ` S) \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
  proof- fix s s'
    assume A: "s \<in> \<Union> (F ` S)" " s' \<in> \<Union> (F ` S)" "s \<noteq> s'"
    show "condition_to_set s \<inter> condition_to_set s' = {}"
    proof-
      obtain a where a_def: "a \<in> (F ` S) \<and> s \<in> a"
        using A by blast
      obtain b where b_def: "b \<in> (F ` S) \<and> s' \<in> b"
        using A by blast   
      show ?thesis 
      proof(cases "a = b")
        case True
        then show ?thesis using A 
          by (metis a_def assms b_def image_iff is_cell_decomp_pairwise_disjoint)
      next
        case False
        obtain A where A_def: "A \<in> S \<and> a = F A"
          using a_def by blast
        obtain B where B_def: "B \<in> S \<and> b = F B"
          using b_def by blast 
        have "A \<noteq> B"
          using A_def B_def False by blast
        then have "condition_to_set A \<inter> condition_to_set B = {}"
          using A_def B_def assms is_cell_decomp_pairwise_disjoint by blast
        then show ?thesis 
          using is_cell_decomp_subset[of n "F A" "condition_to_set A" s] 
                is_cell_decomp_subset[of n "F B" "condition_to_set B" s']
                A_def B_def a_def assms b_def disjoint_iff_not_equal  subsetD 
          unfolding F_def 
          by auto
      qed
    qed
  qed
qed

text\<open>This builds on the previous lemma to give us our most fundamental tool for building cell 
decompositions with special properties. It says that in order to show that a set $A$ can be 
decomposed into cells, each of which has a special property, it suffices to decompose $A$ into a 
collection of cells, then show that each of these cells can be further decomposed into cells with 
the desired property. This rule will frequently be invoked iteratively in our proofs to build finer 
and finer decompositions until the desired property has been achieved.\<close>
lemma refine_each_cell:
  assumes "is_cell_decomp m S A"
  assumes "\<And>C. C \<in> S \<Longrightarrow> \<exists>S'. is_cell_decomp m S' (condition_to_set C) \<and> (\<forall>B \<in> S'. P B)"
  shows "\<exists>S'. is_cell_decomp m S' A \<and> (\<forall>B \<in> S'. P B)"
proof- 
  have A_closed: "A \<subseteq> carrier (Q\<^sub>p\<^bsup>(Suc m)\<^esup>)"
    using assms unfolding is_cell_decomp_def by blast 
  obtain F where F_def: "F = (\<lambda> C. (SOME S'. is_cell_decomp m S' (condition_to_set C) \<and> (\<forall>B \<in> S'. P B)))"
    by blast 
  have 0: "\<And>C. C \<in> S \<Longrightarrow> is_cell_decomp m (F C) (condition_to_set C) \<and> (\<forall>B \<in> (F C). P B)"
  proof- fix C assume A: "C \<in> S"
    obtain S' where S'_def: "is_cell_decomp m S' (condition_to_set C) \<and> (\<forall>B \<in> S'. P B)"
      using assms  A by blast 
    show "is_cell_decomp m (F C) (condition_to_set C) \<and> (\<forall>B \<in> (F C). P B)"
      apply(rule SomeE[of "F C" _ S'])
      unfolding F_def apply blast
      by(rule S'_def)
  qed
  have A_semialg: "is_semialgebraic (Suc m) A"
    using assms  cell_decomp_imp_semialgebraic by blast
  have 1: "is_cell_decomp m (\<Union> (F ` S)) A"
    apply(rule cell_decomp_parametric_refinement)
    apply (simp add: assms(1)) using 0  
     by blast 
  have 2: "(\<forall>B \<in> (\<Union> (F ` S)). P B)"
    using 0 by blast
  show ?thesis using 1 2 by blast 
qed

text\<open>This is just a special version of the above theorem. If we can decompose each piece of a binary 
partition of $A$ into cells with property $P$, then we can combine those to obtain a decomposition 
of $A$ with the same property.\<close>
lemma binary_refinement: 
  assumes "is_cell_decomp m S A"
  assumes "\<And>C. C \<in> S \<Longrightarrow> \<exists>C0. is_semialgebraic (Suc m) C0 \<and> C0 \<subseteq> condition_to_set C \<and>
                          (\<exists>S'. is_cell_decomp m S' C0 \<and> (\<forall>B \<in> S'. P B)) \<and>
                          (\<exists>S'. is_cell_decomp m S' (condition_to_set C - C0) \<and> (\<forall>B \<in> S'. P B))"
  shows "\<exists>S'. is_cell_decomp m S' A \<and> (\<forall>B \<in> S'. P B)"
  apply(rule refine_each_cell[of _ _ ], rule assms)
proof- fix C assume A0: "C \<in> S"
  obtain C0 where C0_def: "is_semialgebraic (Suc m) C0 \<and> C0 \<subseteq> condition_to_set C \<and>
                          (\<exists>S'. is_cell_decomp m S' C0 \<and> (\<forall>B \<in> S'. P B)) \<and>
                          (\<exists>S'. is_cell_decomp m S' (condition_to_set C - C0) \<and> (\<forall>B \<in> S'. P B))"
    using A0 assms by blast 
  obtain S0 where S0_def: " is_cell_decomp m S0 C0 \<and> (\<forall>B \<in> S0. P B)"
    using C0_def by blast 
  obtain S1 where S1_def: "is_cell_decomp m S1 (condition_to_set C - C0) \<and> (\<forall>B \<in> S1. P B)"
    using C0_def by blast 
  have 0: "is_cell_decomp m (S0 \<union> S1) (condition_to_set C)"
    apply(rule is_cell_decompI)
    using S0_def S1_def is_cell_decompE apply blast
  proof(rule is_partitionI, rule disjointI)
    fix A B assume A1: "A \<in> condition_to_set ` (S0 \<union> S1)" "B \<in> condition_to_set ` (S0 \<union> S1)" "A \<noteq> B"
    obtain a where a_def: "a \<in> S0 \<union> S1 \<and> A = condition_to_set a"
      using A1 by blast 
    obtain b where b_def: "b \<in> S0 \<union> S1 \<and> B = condition_to_set b"
      using A1 by blast 
    have a_neq_b: "a \<noteq> b"
      using A1 a_def b_def by blast 
    show "A \<inter> B = {}"
      apply(cases "a \<in> S0 \<and> b \<in> S0")
      using S0_def a_def b_def is_cell_decompE(5)[of m S0 _ a  b] a_neq_b apply blast
      apply(cases "a \<in> S1 \<and> b \<in> S1")
      using S1_def a_def b_def is_cell_decompE(5)[of m S1 _ a  b] a_neq_b apply blast
      apply(cases "a \<in> S0 \<and> b \<in> S1")
      using S1_def S0_def a_def b_def is_partitionE
            is_cell_decompE(2)[of m S1 "condition_to_set C - C0"]
            is_cell_decompE(2)[of m S0 "C0"]  apply blast
      using S1_def S0_def a_def b_def is_partitionE
            is_cell_decompE(2)[of m S1 "condition_to_set C - C0"]
            is_cell_decompE(2)[of m S0 "C0"]        
      by blast 
  next
    show "\<Union> (condition_to_set ` (S0 \<union> S1)) = condition_to_set C"
      using S1_def S0_def  
            is_cell_decompE(2)[of m S1 "condition_to_set C - C0"]  is_partitionE(2)[of "condition_to_set ` S1" "(condition_to_set C - C0)"]
            is_cell_decompE(2)[of m S0 "C0"] is_partitionE(2)[of "condition_to_set ` S0" "C0"]
      by (metis C0_def Diff_partition Sup_union_distrib image_Un)
  next 
    fix s assume A0: "s \<in> S0 \<union> S1"
    show "is_cell_condition s \<and> arity s = m"
      apply(cases "s \<in> S0")
      using S0_def is_cell_decompE apply blast
      using A0 S1_def is_cell_decompE by blast
  next
    show "condition_to_set C \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A0 assms(2) is_cell_decompE(2)[of m S A] is_partitionE(2) assms(1) 
            cell_condition_to_set_subset is_cell_decompE(4) by blast       
  next
    fix a b assume A1: "a \<in> S0 \<union> S1" "b \<in> S0 \<union> S1" "a \<noteq> b"
    show "condition_to_set a \<inter> condition_to_set b = {}"
      apply(cases "a \<in> S0 \<and> b \<in> S0")
      using S0_def A1 is_cell_decompE(5)[of m S0 _ a  b]  apply blast
      apply(cases "a \<in> S1 \<and> b \<in> S1")    
      using S1_def A1 is_cell_decompE(5)[of m S1 _ a  b] apply blast
      apply(cases "a \<in> S0 \<and> b \<in> S1")
      using S1_def S0_def A1 is_partitionE
            is_cell_decompE(2)[of m S1 "condition_to_set C - C0"]
            is_cell_decompE(2)[of m S0 "C0"]  apply blast
      using S1_def S0_def A1 is_partitionE
            is_cell_decompE(2)[of m S1 "condition_to_set C - C0"]
            is_cell_decompE(2)[of m S0 "C0"]        
      by blast 
  qed
  have 1: " (\<forall>B\<in>(S0 \<union> S1). P B)"
    using S0_def S1_def by blast 
  show "\<exists>S'. is_cell_decomp m S' (condition_to_set C) \<and> (\<forall>B\<in>S'. P B)"
    using 0 1 by blast 
qed

text\<open>This is another variant of \texttt{refine\_each\_cell} where the starting decomposition of $A$ 
is not necessarily a cell decomposition, but just a partition of $A$ into semialgebraic sets.\<close>
lemma decomp_partition_elements:
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>(Suc m)\<^esup>)"
  assumes "As partitions A"
  assumes "finite As"
  assumes "\<And>C. C \<in> As \<Longrightarrow> \<exists>S. is_cell_decomp m S C \<and> (\<forall>B \<in> S. P B)"
  shows "\<exists>S'. is_cell_decomp m S' A \<and> (\<forall>B \<in> S'. P B)"
proof- 
  obtain F where F_def: "F = (\<lambda> C. (SOME S. is_cell_decomp m S C \<and> (\<forall>B \<in> S. P B)))"
    by blast 
  have 0: "\<And>C. C \<in> As \<Longrightarrow> is_cell_decomp m (F C) C \<and> (\<forall>B \<in> (F C). P B)"
  proof- fix C assume A: "C \<in> As"
    obtain S' where S'_def: "is_cell_decomp m S' C \<and> (\<forall>B \<in> S'. P B)"
      using assms(4)[of C] A by blast 
    show "is_cell_decomp m (F C) C \<and> (\<forall>B\<in>F C. P B)"
      apply(rule SomeE[of "F C" _ S'])
      unfolding F_def apply blast
      by(rule S'_def)
  qed
  have As_semialg: "\<And>C. C \<in> As \<Longrightarrow> is_semialgebraic (Suc m) C"
    using assms  cell_decomp_imp_semialgebraic by blast
  have 1: "condition_to_set ` \<Union> (F ` As) partitions A"
  proof(rule is_partitionI, rule disjointI)
    fix a b assume A: "a \<in> condition_to_set ` \<Union> (F ` As)" "b \<in> condition_to_set ` \<Union> (F ` As)" "a \<noteq> b"
    obtain a0 a1 where as_def: "a0 \<in> As \<and> a1 \<in> F a0 \<and> a = condition_to_set  a1"
      using A by blast 
    obtain b0 b1 where bs_def: "b0 \<in> As \<and> b1 \<in> F b0 \<and> b = condition_to_set  b1"
      using A by blast 
    show "a \<inter> b = {}"
      apply(cases "a0 = b0")
      using A as_def bs_def is_cell_decompE(5)[of m "F a0" a0 a1 b1] 0[of a0] apply blast
      using assms(2) is_partitionE(1)[of As A] disjointE[of As a0 b0] as_def bs_def A 
            0[of a0] 0[of b0] is_cell_decomp_subset[of m "F a0" a0 a1] 
                is_cell_decomp_subset[of m "F b0" b0 b1] 
      by (metis (no_types, lifting) IntD1 disjoint_iff_not_equal inf.absorb_iff2)
  next
    show "\<Union> (condition_to_set ` \<Union> (F ` As)) = A"
    proof(rule equalityI')
      show "\<And>x. x \<in> \<Union> (condition_to_set ` \<Union> (F ` As)) \<Longrightarrow> x \<in> A"
      proof- fix x assume A: "x \<in> \<Union> (condition_to_set ` \<Union> (F ` As))"
        then obtain a c where defs: "a \<in> As \<and> c \<in> (F a) \<and> x \<in> condition_to_set c"
          by blast 
        have c_sub: "condition_to_set c \<subseteq> a"
          apply(rule is_cell_decomp_subset[of m "F a" a])
          using defs 0 apply blast
          using defs by blast 
        have a_sub: "a \<subseteq> A"
          using defs assms is_partitionE by blast 
        show "x \<in> A"
          using defs c_sub a_sub by blast 
      qed
    next
      fix x assume A: "x \<in> A"
      then obtain a where a_def: "a \<in> As \<and> x \<in> a"
        using assms is_partitionE by blast 
      obtain c where c_def: "c \<in> F a \<and> x \<in> condition_to_set c"
        using a_def 0[of a] is_cell_decompE(2)[of m "F a" a] is_partitionE(2)[of "condition_to_set ` F a" a]
        by blast 
      show "x \<in> \<Union> (condition_to_set ` \<Union> (F ` As))"
        using a_def c_def by blast 
    qed
  qed
  have 2: "is_cell_decomp m (\<Union> (F ` As)) A"
    apply(rule is_cell_decompI)
    using assms is_cell_decompE(1) 0 apply blast
    using 1 apply blast
    using 0 is_cell_decompE apply blast
    using assms apply blast
  proof- fix s s' assume A: "s \<in> \<Union> (F ` As) ""s' \<in> \<Union> (F ` As)"" s \<noteq> s'"
    obtain a b where defs: "a = condition_to_set s" "b = condition_to_set s'" 
      using A by blast
    obtain a0 where as_def: "a0 \<in> As \<and> s \<in> F a0"
      using defs A by blast 
    obtain b0 where bs_def: "b0 \<in> As \<and> s' \<in> F b0"
      using defs A by blast
    show "condition_to_set s \<inter> condition_to_set s' = {}"
      apply(cases "a0 = b0")
      using A as_def bs_def is_cell_decompE(5)[of m "F a0" a0 s s'] 0[of a0] 
      unfolding defs  apply blast
      using assms(2) is_partitionE(1)[of As A] disjointE[of As a0 b0] as_def bs_def A 
            0[of a0] 0[of b0] is_cell_decomp_subset[of m "F a0" a0 s] 
                is_cell_decomp_subset[of m "F b0" b0 s'] 
      by (metis (no_types, lifting) IntD1 disjoint_iff_not_equal inf.absorb_iff2)
  qed
  have "(\<forall>B\<in>(\<Union> (F ` As)). P B)"
    using 0 by blast 
  thus ?thesis using 2 by blast 
qed

lemma cell_decomp_union:
  assumes "A \<subseteq> B"
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  assumes "is_cell_decomp m S A" 
  assumes "is_cell_decomp m S' (B - A)"
  shows "is_cell_decomp m (S \<union> S') B"
proof(rule is_cell_decompI)
  show "finite (S \<union> S')"
    using assms is_cell_decompE by blast
  have 0: "B = A \<union> (B - A)"
    using assms(1) by blast 
  have 1: "A = \<Union> (condition_to_set ` S)"
    using is_cell_decompE(2)[of m S A] is_partitionE(2)[of "condition_to_set ` S" A] assms 
    by blast 
  have 2: "B - A = \<Union> (condition_to_set ` S')"
    using  is_cell_decompE(2)[of m S' "B - A"] assms
        is_partitionE(2)[of "condition_to_set ` S'" "B - A"]
    by blast 
  have 3: "\<And>A B. A \<in> (condition_to_set ` S) \<Longrightarrow> B \<in> (condition_to_set ` S') \<Longrightarrow> A \<inter> B = {}"
    using 1 2 0 by blast 
  have 4: "disjoint (condition_to_set ` (S \<union> S'))"
  proof(rule disjointI) fix C D
    assume A: "C \<in> condition_to_set ` (S \<union> S')"
              "D \<in> condition_to_set ` (S \<union> S')" "C \<noteq> D"
    show "C \<inter> D = {}"
      apply(cases "C \<in> (condition_to_set ` S)")
      apply(cases "D \<in> (condition_to_set ` S)")
      apply(metis A(3) assms(3) is_cell_decompE(2) is_partitionE(1) disjointE)
       apply(rule 3) apply blast using A apply blast
      apply(cases "D \<in> (condition_to_set ` S)")
      using 3[of D C] A apply blast 
      apply(rule disjointE[of "condition_to_set ` S'" C D])
      using A assms is_cell_decompE(2)[of m S' "B - A"] 
            is_partitionE(1)[of "condition_to_set ` S'" "(B - A)"]  
         apply blast 
      using A(1) 1 2 apply blast
      using A(2) 1 2 apply blast
      using A(3) by blast 
  qed
  show "condition_to_set ` (S \<union> S') partitions B"
     apply(rule is_partitionI)  
    using 4 apply blast 
    using 0 1 2 by blast 
  show "\<And>s. s \<in> S \<union> S' \<Longrightarrow> is_cell_condition s \<and> arity s = m"
    using assms is_cell_decompE by blast
  show "B \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" using assms by blast  
  show "\<And>s s'.
       s \<in> S \<union> S' \<Longrightarrow>
       s' \<in> S \<union> S' \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
  proof- fix s s' assume A: "s \<in> S \<union> S'" "s' \<in> S \<union> S'" "s \<noteq> s'"
    show "condition_to_set s \<inter> condition_to_set s' = {}"
      apply(cases "s \<in> S")  apply(cases "s' \<in> S")
      using assms is_cell_decompE(5)[of m S A s s'] A(3) apply blast 
      using A 0 1 2  apply blast 
      apply(cases "s' \<in> S")
      using A 0 1 2  apply blast 
      using assms is_cell_decompE(5)[of m S' "B - A" s s'] A by blast 
  qed
qed 
end


end

