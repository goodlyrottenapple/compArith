theory CompArithDefs
imports Main

begin

fun bool2nat :: "bool \<Rightarrow> nat" ("\<lbrakk> _ \<rbrakk>\<^sub>N" 70) where
"\<lbrakk> True \<rbrakk>\<^sub>N = 1" |
"\<lbrakk> False \<rbrakk>\<^sub>N = 0"

fun bool2int :: "bool \<Rightarrow> int" ("\<lbrakk> _ \<rbrakk>\<^sub>Z" 70) where
"\<lbrakk> True \<rbrakk>\<^sub>Z = 1" |
"\<lbrakk> False \<rbrakk>\<^sub>Z = 0"

lemma bool2int_eq_bool2nat : "int (\<lbrakk> x \<rbrakk>\<^sub>N) = \<lbrakk> x \<rbrakk>\<^sub>Z" by(cases x, simp_all)


fun nat2bool :: "nat \<Rightarrow> bool" ("\<lbrakk> _ \<rbrakk>\<^sub>B" 70) where
"\<lbrakk> 0 \<rbrakk>\<^sub>B = False" |
"\<lbrakk> (Suc 0) \<rbrakk>\<^sub>B = True" |
"\<lbrakk> _ \<rbrakk>\<^sub>B = undefined"


fun DAplus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list \<times> bool" ("DA\<^sup>+") where
"DA\<^sup>+ [] [] = ([] , False)" |
"DA\<^sup>+ (_ # _) [] = undefined" |
"DA\<^sup>+ [] (_ # _) = undefined" |
"DA\<^sup>+ (a # as) (b # bs) = 
  ( \<lbrakk>(\<lbrakk>a\<rbrakk>\<^sub>N + \<lbrakk>b\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B # fst (DA\<^sup>+ as bs) , 
    \<lbrakk>(\<lbrakk>a\<rbrakk>\<^sub>N + \<lbrakk>b\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B )"


fun DAminus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list \<times> bool" ("DA\<^sup>-") where
"DA\<^sup>- [] [] = ([] , True)" |
"DA\<^sup>- (_ # _) [] = undefined" |
"DA\<^sup>- [] (_ # _) = undefined" |
"DA\<^sup>- (a # as) (b # bs) = 
  ( \<lbrakk>(\<lbrakk>a\<rbrakk>\<^sub>N + \<lbrakk>\<not>b\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>- as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B # fst (DA\<^sup>- as bs) , 
    \<lbrakk>(\<lbrakk>a\<rbrakk>\<^sub>N + \<lbrakk>\<not>b\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>- as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B )"



definition uplus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "+\<^sub>U" 90) where
"as +\<^sub>U bs = fst (DA\<^sup>+ (False # as) (False # bs))"

fun splus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "+\<^sub>S" 90) where
"[] +\<^sub>S [] = []" |
"as +\<^sub>S bs = fst (DA\<^sup>+ (hd as # as) (hd bs # bs))"

definition tplus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "\<oplus>" 90) where
"as \<oplus> bs = fst (DA\<^sup>+ as bs)"


definition uminus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "-\<^sub>U" 90) where
"as -\<^sub>U bs = fst (DA\<^sup>- (False # as) (False # bs))"

fun sminus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "-\<^sub>S" 90) where
"[] -\<^sub>S [] = []" | 
"as -\<^sub>S bs = fst (DA\<^sup>- (hd as # as) (hd bs # bs))"

definition tminus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "\<ominus>" 90) where
"as \<ominus> bs = fst (DA\<^sup>- as bs)"


fun ueval :: "bool list \<Rightarrow> nat" ("\<lbrakk> _ \<rbrakk>") where
"\<lbrakk> [] \<rbrakk> = 0" |
"\<lbrakk> a # as \<rbrakk> = \<lbrakk>a\<rbrakk>\<^sub>N * 2 ^ length as + \<lbrakk>as\<rbrakk>"


lemma ueval_upper_bound: "\<lbrakk> l \<rbrakk> \<le> 2 ^ (length l) - 1"
  apply(induct l)
   apply simp
  unfolding ueval.simps
  apply (case_tac a)
  by simp_all

lemma ueval_upper_bound2 : "length a = k \<Longrightarrow> \<lbrakk> a \<rbrakk> \<le> (2 ^ k) - 1"
  apply (induct a arbitrary: k)
   apply simp_all
  apply (case_tac a1)
  by fastforce+

lemma ueval_upper_bound3 : "\<lbrakk> l \<rbrakk> < 2 ^ (length l)"
  apply(induct l)
   apply simp
  unfolding ueval.simps
  apply (case_tac a)
  by simp_all


fun seval :: "bool list \<Rightarrow> int" ("\<lparr> _ \<rparr>") where
"\<lparr> [] \<rparr> = 0" |
"\<lparr> a # as \<rparr> = - int (\<lbrakk>a\<rbrakk>\<^sub>N * 2 ^ length as) + int \<lbrakk>as\<rbrakk>"


lemma seval_upper_bound: "\<lparr> (x#xs) \<rparr> \<le> 2 ^ (length xs) - 1"
  unfolding seval.simps
  apply (cases x)
  apply simp_all
  apply(subst(3) nat_0_le[symmetric], simp)
  apply(subst transfer_int_nat_relations(2), subst nat_mult_distrib, simp_all, subst nat_power_eq, simp_all)
  using ueval_upper_bound3 apply (meson le_less le_less_trans one_less_numeral_iff power_less_power_Suc semiring_norm(76))
  apply(subst(3) nat_0_le[symmetric], simp, subst transfer_int_nat_relations(2), subst nat_power_eq, simp_all)
  using ueval_upper_bound3 by simp

lemma seval_lower_bound: "-(2 ^ (length xs)) \<le> \<lparr> (x#xs) \<rparr>"
 unfolding seval.simps
  apply (cases x)
  apply simp_all
  by (metis negative_zle of_nat_numeral of_nat_power)
  
lemma DAplus_eq_len : 
  fixes a b :: "bool list"
  shows "length a = length b \<Longrightarrow> length (fst (DA\<^sup>+ a b)) = length b"
by (induct a b rule: List.list_induct2) auto

lemma DAminus_eq_len : 
  fixes a b :: "bool list"
  shows "length a = length b \<Longrightarrow> length (fst (DA\<^sup>- a b)) = length b"
by (induct a b rule: List.list_induct2) auto


lemma plus_DA : 
  fixes a b :: "bool list"
  shows "length a = length b \<Longrightarrow> (fst (DA\<^sup>+ (False # a) (False # b))) = (snd (DA\<^sup>+ a b)) # (fst (DA\<^sup>+ a b))"
proof (induct a b rule: List.list_induct2)
case Nil thus ?case by simp
next
case (Cons a as b bs) 
  thus ?case 
  unfolding DAplus.simps prod.sel(1) prod.sel(2)
  apply (induct a ; induct b ; induct "(snd (DA\<^sup>+ as bs))")
  by simp+
qed

lemma to_from_div_id3: "\<And> a b c. \<lbrakk> \<lbrakk>(\<lbrakk>a\<rbrakk>\<^sub>N + \<lbrakk>b\<rbrakk>\<^sub>N + \<lbrakk>c\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = (\<lbrakk>a\<rbrakk>\<^sub>N + \<lbrakk>b\<rbrakk>\<^sub>N + \<lbrakk>c\<rbrakk>\<^sub>N) div 2"
  apply (induct_tac a ; induct_tac b ; induct_tac c) unfolding bool2nat.simps nat2bool.simps by auto

lemma to_from_mod_id3: "\<And> a b c. \<lbrakk> \<lbrakk>(\<lbrakk>a\<rbrakk>\<^sub>N + \<lbrakk>b\<rbrakk>\<^sub>N + \<lbrakk>c\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = (\<lbrakk>a\<rbrakk>\<^sub>N + \<lbrakk>b\<rbrakk>\<^sub>N + \<lbrakk>c\<rbrakk>\<^sub>N) mod 2"
  apply (induct_tac a ; induct_tac b ; induct_tac c) unfolding bool2nat.simps nat2bool.simps by auto


    
definition sigma :: "bool list \<Rightarrow> bool" ("\<sigma>") where
  "sigma = hd"



lemma to_from_mod_id2: "\<And> a :: nat. \<lbrakk> \<lbrakk> a mod 2 \<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = a mod 2"
  by (case_tac "a mod 2", simp , case_tac nat) auto


lemma to_from_mod_id: "\<And> a. \<lbrakk> \<lbrakk> a \<rbrakk>\<^sub>N mod 2 \<rbrakk>\<^sub>B = a" apply (induct_tac a) by auto


lemma to_from_mod_id': "\<And> a. \<lbrakk> \<lbrakk> \<lbrakk> a \<rbrakk>\<^sub>N mod 2 \<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = \<lbrakk> a \<rbrakk>\<^sub>N" apply (induct_tac a) by auto
lemma to_from_div_False: "\<And> a. \<lbrakk> \<lbrakk> \<lbrakk> a \<rbrakk>\<^sub>N div 2 \<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = \<lbrakk> False \<rbrakk>\<^sub>N" apply (induct_tac a) by auto

lemma eval_eq_seval: "\<And> a. int \<lbrakk> a \<rbrakk> = \<lparr> False # a \<rparr>" unfolding seval.simps by simp

lemma DAplus_DAminus_compl: "length x = length y \<Longrightarrow> snd (DA\<^sup>+ (fst (DA\<^sup>- x y)) y) = (\<not> (snd (DA\<^sup>- x y)))"
apply (induct x y rule:List.list_induct2)
   apply simp
  unfolding DAminus.simps DAplus.simps prod.sel
    apply(case_tac x; case_tac y ; case_tac "snd (DA\<^sup>- xs ys)")
  by auto
    
lemma DAminus_DAplus_compl: "length x = length y \<Longrightarrow> snd (DA\<^sup>- (fst (DA\<^sup>+ x y)) y) = (\<not> (snd (DA\<^sup>+ x y)))"
apply (induct x y rule:List.list_induct2)
   apply simp
  unfolding DAminus.simps DAplus.simps prod.sel
    apply(case_tac x; case_tac y ; case_tac "snd (DA\<^sup>- xs ys)")
         by auto


definition triple :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool" where
"triple a b r as bs rs = (a = hd as \<and> b = hd bs \<and> r = hd rs)"

definition bot ("\<bottom>") where "bot = False"
lemma bot_unfold[simp]: "\<bottom> = False" unfolding bot_def by simp
definition top ("\<top>") where "top = True" 
lemma top_unfold[simp]: "\<top> = True" unfolding top_def by simp

  
end