theory CompArith 
imports Main (*"~~/src/HOL/Library/Numeral_Type"*)

begin

fun bool2nat :: "bool \<Rightarrow> nat" ("\<lbrakk> _ \<rbrakk>\<^sub>N" 70) where
"\<lbrakk> True \<rbrakk>\<^sub>N = 1" |
"\<lbrakk> False \<rbrakk>\<^sub>N = 0"


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
  by (case_tac "a mod 2", simp , case_tac nat) auto

lemma to_from_mod_id: "\<And> a. \<lbrakk> \<lbrakk> \<lbrakk> a \<rbrakk>\<^sub>N mod 2 \<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = \<lbrakk> a \<rbrakk>\<^sub>N" apply (induct_tac a) by auto
lemma to_from_div_False: "\<And> a. \<lbrakk> \<lbrakk> \<lbrakk> a \<rbrakk>\<^sub>N div 2 \<rbrakk>\<^sub>B \<rbrakk>\<^sub>N = \<lbrakk> False \<rbrakk>\<^sub>N" apply (induct_tac a) by auto

lemma eval_eq_seval: "\<And> a. int \<lbrakk> a \<rbrakk> = \<lparr> False # a \<rparr>" unfolding seval.simps by simp


lemma one_iff_three : "(\<forall>a b. length a = length b \<longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>U b\<rbrakk>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>S b\<rparr>)"
apply rule+
   apply (case_tac a ; case_tac b)
    unfolding splus.simps
apply (simp , simp , simp)
defer
apply rule+
proof goal_cases
case (1 a b)
  then have "length (False # a) = length (False # b)" by simp
  with 1 have subst2: "\<lparr> False # a \<rparr> + \<lparr> False # b \<rparr> = \<lparr> (False # a) +\<^sub>S (False # b) \<rparr>" by blast
  show ?case
  apply (rule int_int_eq[THEN subst])
  apply (rule Nat_Transfer.transfer_int_nat_functions(1)[THEN subst])
  apply (subst eval_eq_seval , subst eval_eq_seval)
  apply (subst subst2)
  unfolding seval.simps splus.simps list.sel(1)
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
    unfolding uplus_def splus.simps list.sel(1) DAplus.simps prod.sel
    apply simp
    unfolding to_from_div_id3 to_from_mod_id3 subst2
    apply(subst to_from_mod_id)+
    apply(subst to_from_mod_id2)
    apply(subst DAplus_eq_len , simp add:subst2)+
    apply(cases a ; cases b ; cases "snd (DA\<^sup>+ as bs)")
    by auto
qed

lemma two_iff_four : "(\<forall>a b. length a = length b \<longrightarrow> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a -\<^sub>U b\<rparr>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>S b\<rparr>)"
apply rule+
apply (case_tac a ; case_tac b)
unfolding sminus.simps
apply (simp , simp , simp)
defer
apply rule+
proof goal_cases
  case (1 a b)
  then have "length (False # a) = length (False # b)" by simp
  with 1 have subst1: "\<lparr> False # a \<rparr> - \<lparr> False # b \<rparr> = \<lparr> (False # a) -\<^sub>S (False # b) \<rparr>" by blast
  
  show ?case
  apply (subst eval_eq_seval , subst eval_eq_seval)
  apply (subst subst1)
  unfolding seval.simps sminus.simps list.sel(1) uminus_def
  apply simp
  apply (cases "snd (DA\<^sup>- a b)")
  by simp_all
next
  case (2 xs ys a as b bs)
  then have subst2: "length as = length bs" by simp
  have subst1: "\<And> a b as bs :: int. - a + as - (- b + bs) = - a + b + (as - bs)" by simp
  show ?case 
    unfolding 2 seval.simps
    apply (subst subst1)
    apply (subst 2(1))
    using 2 apply simp
    unfolding uminus_def sminus.simps list.sel(1) DAminus.simps prod.sel
    apply simp
    apply(subst DAminus_eq_len , simp add:subst2)+
    unfolding to_from_div_id3 to_from_mod_id3 subst2
    apply(cases a ; cases b ; cases "snd (DA\<^sup>- as bs)")
    by auto
qed

(*fun compl :: "bool list \<Rightarrow> bool list" where
  "compl [] = []" |
  "compl (x # xs) = (\<not> x) # compl xs"

  
fun one :: "nat \<Rightarrow> bool list" where
  "one 0 = []" |
  "one (Suc 0) = [ True ]" |
  "one (Suc (Suc x)) = False # (one (Suc x))"

lemma cons_inj :  "a = b \<Longrightarrow> a # as = b # as" by simp*)

    
    
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
    
lemma one_iff_two : "(\<forall>a b. length a = length b \<longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>U b\<rbrakk>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a -\<^sub>U b\<rparr>)"
  apply rule+
  defer
  apply rule+
proof goal_cases
  case (2 a b)
  have subst1: "\<And> a b c :: int. a = c + b \<Longrightarrow> a - b = c" by simp
  have subst2: "\<And> a b c :: int. a + c + b = a + (c + b)" by simp
  from 2(1) have subst3: "\<forall>a b. length a = length b \<longrightarrow> int \<lbrakk> a \<rbrakk> + int \<lbrakk> b \<rbrakk> = int \<lbrakk> a +\<^sub>U b \<rbrakk>"
    by fastforce
      
  have 4: "length a = length b \<Longrightarrow> fst (DA\<^sup>+ (fst (DA\<^sup>- a b)) b) = a"
    apply (induct a b rule:List.list_induct2)
     apply simp
    apply (case_tac x ; case_tac y)
       apply simp_all
       by (subst DAplus_DAminus_compl, simp, case_tac "snd (DA\<^sup>- xs ys)", simp, simp)+

  show ?case
    apply (rule subst1)
    unfolding uminus_def DAminus.simps prod.sel seval.simps
    apply (subst subst2)
    apply (subst subst3)
    using DAminus_eq_len 2 apply simp
    apply(subst DAminus_eq_len , simp add:2(2))+
    apply simp
    unfolding uplus_def DAplus.simps
    apply simp
    apply(subst DAplus_eq_len)
     apply(subst DAminus_eq_len)
    using 2 apply simp
     apply simp
    apply (subst DAplus_DAminus_compl)
      using 2 apply simp
    apply (cases "snd (DA\<^sup>- a b)")
       apply simp_all
        using 4 2 by simp+

next
  case (1 a b)
  have subst1: "\<And> a b c :: nat. int a + int b = int c \<Longrightarrow> a + b = c" by simp
  have subst2: "\<And> a b c :: int. a = c - b \<Longrightarrow> a + b = c" by simp
  have subst3: "\<And> a b. int \<lbrakk> b \<rbrakk> = int \<lbrakk> (False # b) \<rbrakk>" by simp

  have 2: "length a = length b \<Longrightarrow> fst (DA\<^sup>- (fst (DA\<^sup>+ a b)) b) = a"
    apply (induct a b rule:List.list_induct2)
     apply simp
    apply (case_tac x ; case_tac y)
       apply simp_all
    by (subst DAminus_DAplus_compl, simp, case_tac "snd (DA\<^sup>+ xs ys)", simp, simp)+
 
 
  show ?case
    apply (subst subst1, simp_all)
    apply (subst subst2, simp_all)
    apply (subst(3) subst3)
    apply(subst 1(1))
    unfolding uplus_def
     apply(rule DAplus_eq_len)
    using 1 apply simp

    unfolding uminus_def DAminus.simps prod.sel seval.simps
           apply(subst DAminus_eq_len, subst DAplus_eq_len, simp add:1, simp)
      unfolding not_False_eq_True bool2nat.simps DAplus.simps DAminus.simps prod.sel
      apply simp
      apply(subst DAminus_eq_len, subst DAplus_eq_len, simp add:1, simp)
      apply(subst DAminus_DAplus_compl, simp add: 1)+

  apply(cases "snd (DA\<^sup>+ a b)")
  apply simp_all
   using 1 2 by simp+
qed
  
  
  
lemma ueval_range : "length a = k \<Longrightarrow> \<lbrakk> a \<rbrakk> \<le> (2 ^ k) - 1"
  apply (induct a arbitrary: k)
   apply simp_all
  apply (case_tac a1)
  by fastforce+

    
lemma tplus_ueval_iff_carry : 
  "length a = length b \<Longrightarrow> 
    \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a \<oplus> b\<rbrakk> \<longleftrightarrow> snd (DA\<^sup>+ a b) = False"
apply rule
apply (rule ccontr)
proof goal_cases
case 1
  then have 2: "snd (DA\<^sup>+ a b) = True" by simp
  have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>" using one 1 by simp
  with 1 have "\<lbrakk> a \<oplus> b \<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>" by simp
  with 1 have "\<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk>"
    unfolding uplus_def tplus_def using plus_DA
    by presburger
  with 2 have "\<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> True # fst (DA\<^sup>+ a b) \<rbrakk>" by simp
  then show ?case by simp
next
  case 2
  have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>" using one 2 by simp
  then have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk>"
    unfolding uplus_def using 2 plus_DA
    by presburger
  with 2 have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> False # fst (DA\<^sup>+ a b) \<rbrakk>" by simp
  then show ?case unfolding tplus_def ueval.simps bool2nat.simps by simp
qed

lemma tplus_ueval_iff_range : 
  "length a = length b \<Longrightarrow> 
    \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a \<oplus> b\<rbrakk> \<longleftrightarrow> (0 \<le> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<and> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<le> 2 ^ (length a) - 1)"
  apply rule+
proof goal_cases
  case 1
  show ?case unfolding 1
    apply(rule ueval_range)
    unfolding tplus_def
    apply (rule DAplus_eq_len)
    using 1 by simp
next
  case 2
  then have 3: "\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<le> 2 ^ length a - 1" by simp
  have "\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>" using one 2 by simp
  with 3 have "\<lbrakk>a +\<^sub>U b\<rbrakk> \<le> 2 ^ length a - 1" by simp
  then have "\<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk> \<le> 2 ^ length a - 1" 
    unfolding uplus_def tplus_def using plus_DA 2 by simp
  then have "\<lbrakk> snd (DA\<^sup>+ a b) \<rbrakk>\<^sub>N * 2 ^ length a + \<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> \<le> 2 ^ length a - 1" 
    unfolding ueval.simps using DAplus_eq_len 2 by simp
  then have "snd (DA\<^sup>+ a b) = False" by (rule_tac ccontr, simp)
  then show ?case
  apply (subst tplus_ueval_iff_carry)
  using 2 by simp_all
qed


lemma tplus_seval_iff_range:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
    \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a \<oplus> b\<rparr> \<longleftrightarrow> (- (2 ^ k) \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> 2 ^ k - 1)"
  apply rule+
    proof goal_cases
      case 1
        have 2: "\<And> x y. 0 \<le> x \<Longrightarrow> - x \<le> int y" by simp
      show ?case
        apply (cases a ; cases b)
        using 1 apply simp_all
        unfolding tplus_def DAplus.simps prod.sel seval.simps
        apply (subst DAplus_eq_len, simp)
        using assms apply simp
        apply (case_tac aa; case_tac aaa; case_tac "snd (DA\<^sup>+ list lista)")
               apply simp_all
        apply(rule 2)
          by simp
    next
      case 2
        
      have 3: "\<And> xs k. \<lbrakk> xs \<rbrakk> \<le> 2 ^ k - 1 \<Longrightarrow> int \<lbrakk> xs \<rbrakk> \<le> 2 ^ k - 1"
      proof -
        fix xs :: "bool list" and ka :: nat
        assume "\<lbrakk> xs \<rbrakk> \<le> 2 ^ ka - 1"
        then have "int \<lbrakk> xs \<rbrakk> + - 1 * int (2 ^ ka - 1) \<le> 0"
          by simp
        then show "int \<lbrakk> xs \<rbrakk> \<le> 2 ^ ka - 1"
          by (simp add: of_nat_diff)
      qed
          
      have 4: "\<And> a b c k. c \<ge> 0 \<Longrightarrow> length a = k \<Longrightarrow> int \<lbrakk> a \<rbrakk> - int b * c < 2 ^ k"
        proof goal_cases
          case (1 a b c k)
          show ?case 
            apply(rule zle_diff1_eq[THEN subst])
            apply (subst diff_le_eq)
            apply(rule order_class.order.trans)
            apply (rule 3[where k = k])
            using ueval_range 1 by (simp_all add: 1)
        qed
          
          
      show ?case unfolding 2 using assms
        apply (cases a ; cases b)
        using 2 apply simp_all
        unfolding tplus_def DAplus.simps prod.sel seval.simps
        apply (subst DAplus_eq_len, simp)
        apply(case_tac aa ; case_tac aaa ; case_tac "snd (DA\<^sup>- list lista)")
        apply simp_all
        by (rule 4 , simp, subst DAplus_eq_len, simp, simp)+          
    next
      case 3
      have subst1: "\<And> a b. length a = length b \<Longrightarrow> 0 \<le> \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> \<and> \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> \<le> 2 ^ length a - 1 \<Longrightarrow> \<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk>" 
        using tplus_ueval_iff_range unfolding tplus_def by fastforce
      show ?case
        apply (cases a; cases b)
        unfolding tplus_def apply simp
        using 3 apply (simp,simp)          
          proof goal_cases
            case (1 a as b bs)
            with 3 have len_eq: "length as = length bs" by simp
                from 3 assms 1 have k_def: "k = length as" by simp
                have subst3: "\<And> a b c d :: int.  a + b + (c + d) = a + c + (b + d)" by simp
                                        
                have subst1: "- int (\<lbrakk> a \<rbrakk>\<^sub>N * 2 ^ length as) + int \<lbrakk> as \<rbrakk> + (- int (\<lbrakk> b \<rbrakk>\<^sub>N * 2 ^ length bs) + int \<lbrakk> bs \<rbrakk>) = 
                      - int (\<lbrakk> a \<rbrakk>\<^sub>N * 2 ^ length as) - int (\<lbrakk> b \<rbrakk>\<^sub>N * 2 ^ length as) + int (\<lbrakk> snd (DA\<^sup>+ as bs) \<rbrakk>\<^sub>N) * 2 ^ length as + int \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk>"
                  apply(subst subst3)
                apply(subst Nat_Transfer.transfer_int_nat_functions(1))
                apply(subst one, simp add: len_eq)
                unfolding uplus_def DAplus.simps
                  apply simp
                  apply (subst DAplus_eq_len, simp add: len_eq)+
                by (simp add: len_eq to_from_mod_id)
              
              then have hyps: "- (2 ^ length as) \<le> - int (\<lbrakk> a \<rbrakk>\<^sub>N * 2 ^ length as) - int (\<lbrakk> b \<rbrakk>\<^sub>N * 2 ^ length as) + int (\<lbrakk> snd (DA\<^sup>+ as bs) \<rbrakk>\<^sub>N) * 2 ^ length as + int \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk>" 
                "- int (\<lbrakk> a \<rbrakk>\<^sub>N * 2 ^ length as) - int (\<lbrakk> b \<rbrakk>\<^sub>N * 2 ^ length as) + int (\<lbrakk> snd (DA\<^sup>+ as bs) \<rbrakk>\<^sub>N) * 2 ^ length as + int \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk> \<le> 2 ^ length as - 1"
                using 3 unfolding 1 k_def seval.simps by simp_all

              have hyps2: "0 \<le> int \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk>" "int \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk> \<le> 2 ^ length as - 1" 
                 apply simp
                apply(rule nat_0_le[THEN subst])
                 apply simp
                apply (subst Nat_Transfer.transfer_int_nat_relations(3))
                  apply(rule order_class.order.trans)
                    apply(rule ueval_range, simp_all)
                  apply(subst DAplus_eq_len, simp add: len_eq)
                  apply(subst len_eq)
                proof -
                  have f1: "Suc (nat (- 1 + 2 ^ length bs)) = nat (2 ^ length bs)"
                    by (simp add: Suc_nat_eq_nat_zadd1)
                  have "(0::int) \<le> 2"
                    by auto
                  then have "Suc (nat (- 1 + 2 ^ length bs)) = 2 ^ length bs"
                    using f1 nat_2 nat_power_eq numeral_2_eq_2 by presburger
                  then show "2 ^ length bs - Suc 0 \<le> nat (2 ^ length bs - 1)"
                    by linarith
                qed
                  
              show ?case unfolding 1 DAplus.simps prod.sel seval.simps
                apply(subst subst3)
                apply(subst Nat_Transfer.transfer_int_nat_functions(1))
                apply(subst one, simp add: len_eq)
                unfolding uplus_def DAplus.simps
                apply simp
                apply (subst DAplus_eq_len, simp add: len_eq)+
                apply (cases a ; cases b; cases "snd (DA\<^sup>+ as bs)") apply (simp_all add:len_eq)
                using hyps hyps2 by simp+
            qed
qed

lemma tminus_ueval_iff_range:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
    int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a \<ominus> b\<rparr> \<longleftrightarrow> (- (2 ^ k) \<le>  int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> \<and> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> \<le> 2 ^ k - 1)"
  apply rule+
    proof goal_cases
      case 1
      have 2: "\<And> x y. 0 \<le> x \<Longrightarrow> - x \<le> int y" by simp
      show ?case unfolding 1 using assms
        apply (cases a ; cases b)
        using 1 apply simp_all
        unfolding tminus_def DAminus.simps prod.sel seval.simps
        apply (subst DAminus_eq_len, simp)
        apply(case_tac aa ; case_tac aaa ; case_tac "snd (DA\<^sup>- list lista)") by (simp_all add:2)
    next
      case 2
      have 3: "\<And> xs k. \<lbrakk> xs \<rbrakk> \<le> 2 ^ k - 1 \<Longrightarrow> int \<lbrakk> xs \<rbrakk> \<le> 2 ^ k - 1"
      proof -
        fix xs :: "bool list" and ka :: nat
        assume "\<lbrakk> xs \<rbrakk> \<le> 2 ^ ka - 1"
        then have "int \<lbrakk> xs \<rbrakk> + - 1 * int (2 ^ ka - 1) \<le> 0"
          by simp
        then show "int \<lbrakk> xs \<rbrakk> \<le> 2 ^ ka - 1"
          by (simp add: of_nat_diff)
      qed
          
      have 4: "\<And> a k. length a = k \<Longrightarrow> int \<lbrakk> a \<rbrakk> < 2 ^ k"
        proof goal_cases
          case (1 a k)
          show ?case 
            apply(rule zle_diff1_eq[THEN subst])
            apply(rule 3)
              using ueval_range 1 by simp
        qed
          
          
      show ?case unfolding 2 using assms
        apply (cases a ; cases b)
        using 2 apply simp_all
        unfolding tminus_def DAminus.simps prod.sel seval.simps
        apply (subst DAminus_eq_len, simp)
        apply(case_tac aa ; case_tac aaa ; case_tac "snd (DA\<^sup>- list lista)")
        apply simp_all 
        by ((rule 4 , subst DAminus_eq_len, simp, simp) | (rule Orderings.order_class.order.strict_trans, rule 4 , subst DAminus_eq_len, simp, simp, simp))+

    next
      case 3
      then show ?case sorry
    qed

end