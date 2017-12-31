theory Comp_Indist
imports "../Cyclic_Group_SPMF" Negligible 
begin

text {* A probability ensemble is a family of random variables indexed by 
  some input of arbitrary type and a natural number security size parameter.  
  The space of events considered depends on the \emph{view}. *}

type_synonym ('a,'v) ensemble = "'a \<Rightarrow> nat \<Rightarrow> 'v spmf"

text {* A polynomial time distinguisher probablistically "characterises" an arbitrary SPMF.
  We assume a family of constants giving us a set of all polytime distinguishers for 
  every type \<alpha>, indexed by a size parameter n \<in> nat. *}
consts polydist :: "nat \<Rightarrow> ('v spmf \<Rightarrow> bool spmf) set"

text {* This is close to Lindell although seems convoluted.  
  Lindell quantifies over all D, then asserts \<epsilon> and quantifies over 
  inputs and n.  Then he later says he assumes D is polytime in n.  *}
  
definition comp_indist :: "('a,'v) ensemble \<Rightarrow> ('a,'v) ensemble \<Rightarrow> bool" 
where "comp_indist X Y \<equiv> 
   \<forall> (D :: 'v spmf \<Rightarrow> bool spmf).
    \<exists> (\<epsilon> :: nat \<Rightarrow> real). negligible \<epsilon> \<and>
       (\<forall> (a :: 'a) (n :: nat). 
            (D \<in> polydist n) \<longrightarrow>
              \<bar>spmf (D (X a n)) True - spmf (D (Y a n)) True\<bar> \<le> \<epsilon> n)"

lemma neg_ex: "\<forall> D. \<exists> \<epsilon>. negligible \<epsilon> \<and> (\<forall>n. D \<in> polydist n \<longrightarrow> 0 \<le> \<epsilon> n)"
by(rule allI, rule_tac x = "0" in exI, simp)

lemma eq_comp_in[simp]: "comp_indist X X"
by(simp add: comp_indist_def neg_ex)

lemma comp_in_order: "comp_indist X Y \<longleftrightarrow> comp_indist Y X"
by(simp add: comp_indist_def Groups.ordered_ab_group_add_abs_class.abs_minus_commute)

lemma comp_in_trans: "\<lbrakk>comp_indist X Y;comp_indist Y Z\<rbrakk> \<Longrightarrow> comp_indist X Z"
apply(simp add: comp_indist_def, rule allI)
apply(erule_tac x="D" in allE, erule exE, erule conjE)+
apply(rule_tac x="\<lambda>n. \<epsilon> n + \<epsilon>' n" in exI)
apply(rule conjI, simp add: Negligible.negligible_plus)
apply(rule allI, rule allI, rule impI)
apply(erule_tac x="a" in allE, erule_tac x="n" in allE)+
by auto

end