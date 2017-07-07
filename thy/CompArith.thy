theory CompArith 
imports Main (*"~~/src/HOL/Library/Numeral_Type"*)

begin

fun bool2nat :: "bool \<Rightarrow> nat" ("\<lbrakk> _ \<rbrakk>\<^sub>N" 70) where
"\<lbrakk> True \<rbrakk>\<^sub>N = 1" |
"\<lbrakk> False \<rbrakk>\<^sub>N = 0"


fun nat2bool :: "nat \<Rightarrow> bool" ("\<lbrakk> _ \<rbrakk>\<^sub>B" 70) where
"\<lbrakk> 0 \<rbrakk>\<^sub>B = False" |
"\<lbrakk> _ \<rbrakk>\<^sub>B = True"


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

definition splus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "+\<^sub>S" 90) where
"as +\<^sub>S bs = fst (DA\<^sup>+ (hd as # as) (hd bs # bs))"

definition tplus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "\<oplus>" 90) where
"as \<oplus> bs = fst (DA\<^sup>+ as bs)"


definition uminus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "-\<^sub>U" 90) where
"as -\<^sub>U bs = fst (DA\<^sup>- (False # as) (True # bs))"

definition sminus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "-\<^sub>S" 90) where
"as -\<^sub>S bs = fst (DA\<^sup>- (hd as # as) (hd bs # bs))"

definition tminus :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" (infixl "\<ominus>" 90) where
"as \<ominus> bs = fst (DA\<^sup>- as bs)"


fun ueval :: "bool list \<Rightarrow> nat" ("\<lbrakk> _ \<rbrakk>") where
"\<lbrakk> [] \<rbrakk> = 0" |
"\<lbrakk> a # as \<rbrakk> = \<lbrakk>a\<rbrakk>\<^sub>N * 2 ^ length as + \<lbrakk>as\<rbrakk>"


fun seval :: "bool list \<Rightarrow> int" ("\<lparr> _ \<rparr>") where
"\<lparr> [] \<rparr> = 0" |
"\<lparr> a # as \<rparr> = - int (\<lbrakk>a\<rbrakk>\<^sub>N * 2 ^ length as) + int \<lbrakk>as\<rbrakk>"


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

lemma one :
  fixes a b :: "bool list"
  shows "length a = length b \<Longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>U b\<rbrakk>"
unfolding uplus_def 
apply (subst plus_DA , simp)
proof (induct a b rule: List.list_induct2)
case Nil thus ?case by simp
next
case (Cons a as b bs)
  have subst1: "\<And> a b as bs :: nat. a + as + (b + bs) = a + b + (as + bs)" by simp
  show ?case unfolding ueval.simps Cons(1)  
  apply (subst DAplus_eq_len , simp add: Cons)
  apply (subst subst1)
  unfolding DAplus.simps prod.sel(1) prod.sel(2) to_from_div_id3 to_from_mod_id3 ueval.simps Cons(2)
  apply (subst DAplus_eq_len , simp add: Cons)+
  apply (induct a ; induct b ; induct "(snd (DAplus as bs))")
  by simp+
qed


lemma to_from_mod_id2: "\<And> a :: nat. \<lbrakk> \<lbrakk> a mod 2 \<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = a mod 2"
by(case_tac "a mod 2") auto

lemma to_from_mod_id: "\<And> a. \<lbrakk> \<lbrakk> \<lbrakk> a \<rbrakk>\<^sub>N mod 2 \<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = \<lbrakk> a \<rbrakk>\<^sub>N" apply (induct_tac a) by auto
lemma to_from_div_False: "\<And> a. \<lbrakk> \<lbrakk> \<lbrakk> a \<rbrakk>\<^sub>N div 2 \<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = \<lbrakk> False \<rbrakk>\<^sub>N" apply (induct_tac a) by auto

      
lemma one_iff_three : "(\<forall>a b. length a = length b \<longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>U b\<rbrakk>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>S b\<rparr>)"
apply rule+
apply (case_tac a ; case_tac b)
apply (subst splus_def) apply simp
apply (simp, simp)
defer
apply rule+
proof goal_cases
case (1 a b)
  then have "length (False # a) = length (False # b)" by simp
  with 1 have subst2: "\<lparr> False # a \<rparr> + \<lparr> False # b \<rparr> = \<lparr> (False # a) +\<^sub>S (False # b) \<rparr>" by blast
  have subst1: "\<And> a. int \<lbrakk> a \<rbrakk> = \<lparr> False # a \<rparr>" unfolding seval.simps by simp
  show ?case
  apply (rule int_int_eq[THEN subst])
  apply (rule Nat_Transfer.transfer_int_nat_functions(1)[THEN subst])
  apply (subst subst1 , subst subst1)
  apply (subst subst2)
  unfolding seval.simps splus_def list.sel(1)
  apply simp
  apply (subst to_from_mod_id)+
  apply (subst to_from_div_False)
  unfolding uplus_def DAplus.simps bool2nat.simps
  apply simp
  apply (subst to_from_mod_id)
  by simp
next
  case (2 xs ys a as b bs)
  then have subst2: "length as = length bs" by simp
  have subst1: "\<And> a b as bs :: int. a + as + (b + bs) = a + b + (as + bs)" by simp
  show ?case 
    unfolding 2 seval.simps
    apply (subst subst1)
    apply (subst Nat_Transfer.transfer_int_nat_functions(1))
    apply (subst 2(1))
    using 2 apply simp
    unfolding uplus_def splus_def list.sel(1) DAplus.simps prod.sel
    apply simp
    unfolding to_from_div_id3 to_from_mod_id3 subst2
    apply(subst to_from_mod_id)+
    apply(subst to_from_mod_id2)
    apply(subst DAplus_eq_len , simp add:subst2)+
    apply(cases a ; cases b ; cases "snd (DA\<^sup>+ as bs)")
    by auto
qed   


lemma two_iff_four : "(\<forall>a b. length a = length b \<longrightarrow> \<lbrakk>a\<rbrakk> - \<lbrakk>b\<rbrakk> = \<lbrakk>a -\<^sub>U b\<rbrakk>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>S b\<rparr>)"
sorry
    
end