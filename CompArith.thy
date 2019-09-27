theory CompArith 
imports Main CompArithDefs (*"~~/src/HOL/Library/Numeral_Type"*)

begin
    
    
(* Lemma 1.2 *)
    
lemma lemma_1_2 : 
  fixes x :: "bool list"
  assumes "length x > 0" and "\<sigma> x = True" 
  shows "\<lparr> x \<rparr> < 0"
  using assms proof (induct x)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have subst: "x = True" unfolding sigma_def by simp
      show ?case unfolding subst unfolding seval.simps
        apply simp
        apply (rule le_less_trans)
         apply(rule ueval_upper_bound)
        by simp
      qed

(* Lemma 2.1 *)
lemma lem_2_1 : 
  fixes a_i b_i c_i :: "bool"
  defines c_suci_def: "c_suci \<equiv> \<lbrakk>(\<lbrakk>a_i\<rbrakk>\<^sub>N + \<lbrakk>b_i\<rbrakk>\<^sub>N + \<lbrakk>c_i\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" 
      and r_i_def: "r_i \<equiv> \<lbrakk>(\<lbrakk>a_i\<rbrakk>\<^sub>N + \<lbrakk>b_i\<rbrakk>\<^sub>N + \<lbrakk>c_i\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" 
    shows "\<lbrakk>a_i\<rbrakk>\<^sub>N + \<lbrakk>b_i\<rbrakk>\<^sub>N + \<lbrakk>c_i\<rbrakk>\<^sub>N = 2 * (\<lbrakk>c_suci\<rbrakk>\<^sub>N) + \<lbrakk>r_i\<rbrakk>\<^sub>N"
  unfolding c_suci_def r_i_def by (cases a_i; cases b_i; cases c_i, simp_all)


(* Theorem 3.1 *)
(* 1: done *)
(* 1 \<longleftrightarrow> 3 : done *)
(* 2 \<longleftrightarrow> 4 : done *)
(* 1 \<longleftrightarrow> 2 : done *)

lemma thm_3_1_1 :
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


lemma thm_3_1_1_alt :
  fixes a_k b_k :: "bool" and as bs :: "bool list"
  defines a_def: "a \<equiv> a_k # as" and b_def: "b \<equiv> b_k # bs"
  assumes len_eq: "length as = length bs"
  shows "\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>U b\<rbrakk>"
  unfolding a_def b_def 
  using len_eq 
proof (induct as bs arbitrary: a_k b_k rule: List.list_induct2)
  case Nil 
  thus ?case unfolding uplus_def DAplus.simps
    by (cases a_k; cases b_k; simp_all)  
next
  case (Cons a_km1 as b_km1 bs)
  (*define a_k' ("a\<^sub>k") where "a\<^sub>k = a_k"
  define k_k'("b\<^sub>k") where "b\<^sub>k = b_k"*)
  define ak ("a\<^sup>k") where ak_def[simp]: "a\<^sup>k = a_km1 # as"
  define bk ("b\<^sup>k") where bk_def[simp]: "b\<^sup>k = b_km1 # bs"
  define a b where a_def: "a = a_k # a\<^sup>k" and b_def: "b = b_k # b\<^sup>k"
  define b_km1' ("b\<^sup>k\<^sup>-\<^sup>1") where "b\<^sup>k\<^sup>-\<^sup>1 = b_km1"
  define rk ("r\<^sup>k") where rk_def: "r\<^sup>k = fst (DA\<^sup>+ a\<^sup>k b\<^sup>k)"
  define c_kp1 ("c\<^sub>k\<^sub>+\<^sub>1") where c_kp1_def: "c\<^sub>k\<^sub>+\<^sub>1 = snd (DA\<^sup>+ a\<^sup>k b\<^sup>k)"
  define r_kp1 ("r\<^sub>k\<^sub>+\<^sub>1") where r_kp1_def: "r\<^sub>k\<^sub>+\<^sub>1 = \<lbrakk> (\<lbrakk> a_k \<rbrakk>\<^sub>N + \<lbrakk> b_k \<rbrakk>\<^sub>N + \<lbrakk> c\<^sub>k\<^sub>+\<^sub>1 \<rbrakk>\<^sub>N) mod 2 \<rbrakk>\<^sub>B"
  define c_kp2 ("c\<^sub>k\<^sub>+\<^sub>2") where c_kp2_def: "c\<^sub>k\<^sub>+\<^sub>2 = \<lbrakk> (\<lbrakk> a_k \<rbrakk>\<^sub>N + \<lbrakk> b_k \<rbrakk>\<^sub>N + \<lbrakk> c\<^sub>k\<^sub>+\<^sub>1 \<rbrakk>\<^sub>N) div 2 \<rbrakk>\<^sub>B"

  have len_ak_eq_bk: "length a\<^sup>k = length b\<^sup>k" unfolding ak_def bk_def using Cons(1) by simp
  have len_bk: "length b\<^sup>k = length r\<^sup>k" unfolding rk_def ak_def bk_def by (subst DAplus_eq_len, simp_all add: Cons)
  from Cons have ih: "\<lbrakk> a\<^sup>k \<rbrakk> + \<lbrakk> b\<^sup>k \<rbrakk> = \<lbrakk> a\<^sup>k +\<^sub>U b\<^sup>k \<rbrakk>" by simp
  then have ih': "\<lbrakk> a\<^sup>k \<rbrakk> + \<lbrakk> b\<^sup>k \<rbrakk> = \<lbrakk> c\<^sub>k\<^sub>+\<^sub>1 # r\<^sup>k \<rbrakk>" 
    unfolding rk_def c_kp1_def uplus_def DAplus.simps bool2nat.simps add_0 fst_conv snd_conv to_from_mod_id by simp

  show "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>"
    unfolding a_def b_def uplus_def DAplus.simps fst_conv snd_conv rk_def[symmetric] c_kp1_def[symmetric] bool2nat.simps add_0 
      r_kp1_def[symmetric] c_kp2_def[symmetric] to_from_mod_id
    unfolding ueval.simps apply(subst semiring_normalization_rules(20))
    apply (subst ih')
    unfolding ueval.simps len_ak_eq_bk len_bk apply simp
    unfolding semiring_normalization_rules(1) semiring_normalization_rules(18) apply(rule mult_right_cancel[THEN iffD2], simp)
    unfolding c_kp2_def r_kp1_def 
    by (cases a_k; cases b_k; cases "c\<^sub>k\<^sub>+\<^sub>1", simp_all)
qed

lemma nat_transfer: "\<And>x y. (int x) + (int y) = int (x + y)" by simp

lemma thm_3_1_1_iff_3 : "(\<forall>a b. length a = length b \<longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>U b\<rbrakk>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>S b\<rparr>)"
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
    apply simp
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
    apply (subst nat_transfer(1))
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

lemma thm_3_1_3: "length a = length b \<Longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>S b\<rparr>"
  using thm_3_1_1_iff_3 thm_3_1_1 by simp

lemma thm_3_1_2_iff_4 : "(\<forall>a b. length a = length b \<longrightarrow> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a -\<^sub>U b\<rparr>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>S b\<rparr>)"
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
    

lemma thm_3_1_1_iff_2 : "(\<forall>a b. length a = length b \<longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>U b\<rbrakk>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a -\<^sub>U b\<rparr>)"
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

lemma thm_3_1_2: "length a = length b \<Longrightarrow> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a -\<^sub>U b\<rparr>"
  using thm_3_1_1_iff_2 thm_3_1_1 by simp


lemma thm_3_1_4: "length a = length b \<Longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>S b\<rparr>"
  using thm_3_1_1_iff_2 thm_3_1_2_iff_4 thm_3_1_1 by simp


(* Theorem 3.2 *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 1 \<longleftrightarrow> 4 : done *)
(* 1 \<longleftrightarrow> 2 : done *)


lemma thm_3_2_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) \<oplus> (b#bs))"
  shows "snd (DA\<^sup>+ (a#as) (b#bs)) = \<bottom> \<longleftrightarrow> 
    (triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<top>)"
  unfolding triple'_def triple_def
proof(rule , goal_cases)
  case 1
  then show ?case unfolding tplus_def
    by (cases a; cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)
next
  case 2
  then show ?case unfolding tplus_def
    by (cases a; cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)
qed

(*
lemma thm_2_9_4_iff_3 :
  fixes a b :: "bool list"
  assumes "length a = length b" and "length a > 0"
  defines "triple' x y z \<equiv> triple x y z a b (a \<oplus> b)"
  shows "snd (DA\<^sup>+ a b) = \<bottom> \<longleftrightarrow> (triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<top>)" (*\<and> 
   \<not>(triple' True True True \<or> triple' True True False \<or> triple' True False False \<or> triple' False True False)"*)
  unfolding triple'_def triple_def
proof (rule, goal_cases)
  case 1
  note carry_impl_sign = 1
  show ?case
  apply(cases a)
  using assms apply simp
  apply(cases b)
  using assms apply simp
  unfolding tplus_def
  apply (cases "fst (DA\<^sup>+ a b)")
  using assms DAplus_eq_len apply simp
  apply(case_tac aa;case_tac aaa;case_tac ab)
  proof goal_cases
    case (1 ak as bk bs rk rs)
    then have "snd (DA\<^sup>+ a b) = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
    then have "snd (DA\<^sup>+ a b) = \<lbrakk>(2 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" using 1 by simp
    then have "snd (DA\<^sup>+ a b) = True" by (cases "snd (DA\<^sup>+ as bs)", simp_all)
    with carry_impl_sign have False by simp
    then show ?case by simp
  next
    case (2 ak as bk bs rk rs)
    then have "snd (DA\<^sup>+ a b) = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
    then have "snd (DA\<^sup>+ a b) = \<lbrakk>(2 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" using 2 by simp
    then have "snd (DA\<^sup>+ a b) = True" by (cases "snd (DA\<^sup>+ as bs)", simp_all)
    with carry_impl_sign have False by simp
    then show ?case by simp
  next
    case (3 ak as bk bs rk rs)
    then show ?case by simp
  next
    case (4 ak as bk bs rk rs)
    then have "snd (DA\<^sup>+ a b) = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
    then have 1: "snd (DA\<^sup>+ a b) = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" using 4 by simp
    from 4 have "rk = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" by simp
    then have "rk = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" using 4 by simp
    with carry_impl_sign 1 4 have "\<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" by simp
    then have False by (cases "snd (DA\<^sup>+ as bs)", simp_all)
    then show ?case by simp
  next
    case (5 ak as bk bs rk rs)
    then show ?case by simp
  next
    case (6 ak as bk bs rk rs)
    then have "snd (DA\<^sup>+ a b) = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
    then have 1: "snd (DA\<^sup>+ a b) = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" using 6 by simp
    from 6 have "rk = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" by simp
    then have "rk = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" using 6 by simp
    with carry_impl_sign 1 6 have "\<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" by simp
    then have False by (cases "snd (DA\<^sup>+ as bs)", simp_all)
    then show ?case by simp
  next
    case (7 ak as bk bs rk rs)
    then show ?case by simp
  next
    case (8 ak as bk bs rk rs)
    then show ?case by simp
  qed
next
  case 2
  note sign_impl_carry = 2
  then show ?case
    apply(cases a)
    using assms apply simp
    apply(cases b)
    using assms apply simp
    unfolding tplus_def
    apply (cases "fst (DA\<^sup>+ a b)")
    using assms DAplus_eq_len apply simp
    proof goal_cases
      case (1 ak as bk bs rk rs)
      then have 2: "\<bottom> = ak \<and> \<bottom> = bk \<and> \<bottom> = rk \<or>
                    \<bottom> = ak \<and> \<bottom> = bk \<and> \<top> = rk \<or> 
                    \<bottom> = ak \<and> \<top> = bk \<and> \<top> = rk \<or> 
                    \<top> = ak \<and> \<bottom> = bk \<and> \<top> = rk" by simp
      from 1 have 3: "snd (DA\<^sup>+ a b) = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
      { assume "\<bottom> = ak \<and> \<bottom> = bk \<and> \<bottom> = rk"
        with 3 have "snd (DA\<^sup>+ a b) = \<lbrakk>(\<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
        then have ?case by (cases "snd (DA\<^sup>+ as bs)", simp_all) }
      { assume "\<bottom> = ak \<and> \<bottom> = bk \<and> \<top> = rk"
        with 3 have "snd (DA\<^sup>+ a b) = \<lbrakk>(\<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
        then have ?case by (cases "snd (DA\<^sup>+ as bs)", simp_all) }
      { assume assms: "\<bottom> = ak \<and> \<top> = bk \<and> \<top> = rk"
        with 3 have 4: "snd (DA\<^sup>+ a b) = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
        from 1 have "rk = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" by simp
        with assms have "rk = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" by simp
        with assms have "snd (DA\<^sup>+ as bs) = \<bottom>" by auto
        with 4 have ?case by simp }
      { assume assms: "\<top> = ak \<and> \<bottom> = bk \<and> \<top> = rk"
        with 3 have 4: "snd (DA\<^sup>+ a b) = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) div 2\<rbrakk>\<^sub>B" by simp
        from 1 have "rk = \<lbrakk>(\<lbrakk>ak\<rbrakk>\<^sub>N + \<lbrakk>bk\<rbrakk>\<^sub>N + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" by simp
        with assms have "rk = \<lbrakk>(1 + \<lbrakk>snd (DA\<^sup>+ as bs)\<rbrakk>\<^sub>N) mod 2\<rbrakk>\<^sub>B" by simp
        with assms have "snd (DA\<^sup>+ as bs) = \<bottom>" by auto
        with 4 have ?case by simp  }
      then show ?case using 2
        \<open>\<bottom> = ak \<and> \<bottom> = bk \<and> \<bottom> = rk \<Longrightarrow> snd (DA\<^sup>+ a b) = \<bottom>\<close>
        \<open>\<bottom> = ak \<and> \<bottom> = bk \<and> \<top> = rk \<Longrightarrow> snd (DA\<^sup>+ a b) = \<bottom>\<close>
        \<open>\<bottom> = ak \<and> \<top> = bk \<and> \<top> = rk \<Longrightarrow> snd (DA\<^sup>+ a b) = \<bottom>\<close>
        \<open>\<top> = ak \<and> \<bottom> = bk \<and> \<top> = rk \<Longrightarrow> snd (DA\<^sup>+ a b) = \<bottom>\<close> by auto
    qed
qed
*)

lemma thm_3_2_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) \<oplus> (bk # bs))" and
          "rk \<equiv> hd ((ak # as) \<oplus> (bk # bs))"
  shows "\<lbrakk>ak\<rbrakk>\<^sub>Z + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk>ak\<rbrakk>\<^sub>Z + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
    (triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<top>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+



(*proof goal_cases
  case 1
  { assume "\<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = 0"
    then have ?case by (cases ak; cases bk; cases rk, simp_all) }
  { assume "\<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = - 1"
    then have ?case by (cases ak; cases bk; cases rk, simp_all) }
  then show ?case
    using "1" 
      \<open>\<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = 0 \<Longrightarrow> 
        False = ak \<and> False = bk \<and> False = rk \<or> 
        False = ak \<and> False = bk \<and> True = rk \<or> 
        False = ak \<and> True = bk \<and> True = rk \<or> 
        True = ak \<and> False = bk \<and> True = rk\<close> 
    by auto
next
  case 2
  { assume "False = ak \<and> False = bk \<and> False = rk"
    then have ?case by simp }
  { assume "False = ak \<and> False = bk \<and> True = rk"
    then have ?case by simp }
  { assume "False = ak \<and> True = bk \<and> True = rk"
    then have ?case by simp }
  { assume "True = ak \<and> False = bk \<and> True = rk"
    then have ?case by simp }
  then show ?case
    using "2" 
      \<open>False = ak \<and> False = bk \<and> False = rk \<Longrightarrow> \<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = - 1\<close> 
      \<open>False = ak \<and> False = bk \<and> True = rk \<Longrightarrow> \<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = - 1\<close> 
      \<open>False = ak \<and> True = bk \<and> True = rk \<Longrightarrow> \<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk> ak \<rbrakk>\<^sub>Z + \<lbrakk> bk \<rbrakk>\<^sub>Z - \<lbrakk> rk \<rbrakk>\<^sub>Z = - 1\<close> by blast
qed*)

  

lemma thm_3_2_1_iff_4 : 
  "length a = length b \<Longrightarrow> 
    \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a \<oplus> b\<rbrakk> \<longleftrightarrow> snd (DA\<^sup>+ a b) = False"
apply rule
apply (rule ccontr)
proof goal_cases
case 1
  then have 2: "snd (DA\<^sup>+ a b) = True" by simp
  have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>" using thm_3_1_1 1 by simp
  with 1 have "\<lbrakk> a \<oplus> b \<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>" by simp
  with 1 have "\<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk>"
    unfolding uplus_def tplus_def using plus_DA
    by presburger
  with 2 have "\<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> True # fst (DA\<^sup>+ a b) \<rbrakk>" by simp
  then show ?case by simp
next
  case 2
  have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>" using thm_3_1_1 2 by simp
  then have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk>"
    unfolding uplus_def using 2 plus_DA
    by presburger
  with 2 have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> False # fst (DA\<^sup>+ a b) \<rbrakk>" by simp
  then show ?case unfolding tplus_def ueval.simps bool2nat.simps by simp
qed

lemma thm_3_2_1_iff_2 : 
  "length a = length b \<Longrightarrow> 
    \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a \<oplus> b\<rbrakk> \<longleftrightarrow> (0 \<le> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<and> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<le> 2 ^ (length a) - 1)"
  apply rule+
proof goal_cases
  case 1
  show ?case unfolding 1
    apply(rule ueval_upper_bound2)
    unfolding tplus_def
    apply (rule DAplus_eq_len)
    using 1 by simp
next
  case 2
  then have 3: "\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<le> 2 ^ length a - 1" by simp
  have "\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk> a +\<^sub>U b \<rbrakk>" using thm_3_1_1 2 by simp
  with 3 have "\<lbrakk>a +\<^sub>U b\<rbrakk> \<le> 2 ^ length a - 1" by simp
  then have "\<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk> \<le> 2 ^ length a - 1" 
    unfolding uplus_def tplus_def using plus_DA 2 by simp
  then have "\<lbrakk> snd (DA\<^sup>+ a b) \<rbrakk>\<^sub>N * 2 ^ length a + \<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> \<le> 2 ^ length a - 1" 
    unfolding ueval.simps using DAplus_eq_len 2 by simp
  then have "snd (DA\<^sup>+ a b) = False" by (rule_tac ccontr, simp)
  then show ?case
  apply (subst thm_3_2_1_iff_4)
  using 2 by simp_all
qed


(* Theorem 3.4 *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 2 \<longrightarrow> 4 : done *)
(* 4 \<longrightarrow> 1 : done *)
(* 1 \<longleftrightarrow> 2 : done *)

lemma thm_3_4_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) \<oplus> (bk # bs))" and
          "rk \<equiv> hd ((ak # as) \<oplus> (bk # bs))"
  shows "-(\<lbrakk>ak\<rbrakk>\<^sub>Z) - \<lbrakk>bk\<rbrakk>\<^sub>Z + \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> -(\<lbrakk>ak\<rbrakk>\<^sub>Z) - \<lbrakk>bk\<rbrakk>\<^sub>Z + \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
    (triple' \<top> \<top> \<top> \<or> triple' \<top> \<bottom> \<top> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<bottom>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+


lemma thm_3_4_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) \<oplus> (b#bs))"
  shows "snd (DA\<^sup>+ (a#as) (b#bs)) = snd (DA\<^sup>+ as bs) \<longleftrightarrow> 
    (triple' \<top> \<top> \<top> \<or> triple' \<top> \<bottom> \<top> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<bottom>)"
  unfolding triple'_def triple_def
proof(rule , goal_cases)
  case 1
  then show ?case
    unfolding tplus_def
    by (cases a;cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)
next
  case 2
  then show ?case unfolding tplus_def
    by (cases a;cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)
qed



lemma thm_3_4_2_impl_4 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "(- (2 ^ k) \<le> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> \<le> 2 ^ k - 1) \<Longrightarrow> snd (DA\<^sup>+ (a#as) (b#bs)) = snd (DA\<^sup>+ as bs)"
  
proof goal_cases
  case 1
  then have "- (2 ^ k) \<le> \<lparr> (a # as) +\<^sub>S (b # bs) \<rparr> \<and> \<lparr> (a # as) +\<^sub>S (b # bs) \<rparr> \<le> 2 ^ k - 1"
    apply rule
    apply rule
    (*unfolding splus.simps list.sel(1)
    find_theorems "hd (?a#?as)"*)
    apply(subst thm_3_1_3[symmetric])
    using assms apply simp
    apply simp
    apply(subst thm_3_1_3[symmetric])
    using assms apply simp
    by simp
  (*then have "- (2 ^ k) \<le> \<lparr> fst (DA\<^sup>+ (a # a # as) (b # b # bs)) \<rparr> \<and> \<lparr> fst (DA\<^sup>+ (a # a # as) (b # b # bs)) \<rparr> \<le> 2 ^ k - 1"
    unfolding splus.simps list.sel(1) by simp*)
  then have "(\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>+ (a # as) (b # bs)) \<rbrakk>\<^sub>N) mod 2 = (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>+ as bs) \<rbrakk>\<^sub>N) mod 2"
  apply(cases a; cases b; cases "snd (DA\<^sup>+ (a # as) (b # bs))"; cases "snd (DA\<^sup>+ as bs)", simp_all)
  proof goal_cases
    case 1
    then have 2: "2 ^ k \<le> \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk>"
      apply (subst(2) nat_int[symmetric])
      apply(subst nat_le_iff)
      using DAplus_eq_len assms
      by simp
    have "\<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk> \<le> 2 ^ k - 1" using ueval_upper_bound DAplus_eq_len assms by metis
    then have "\<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk> < 2 ^ k"  using DAplus_eq_len assms ueval_upper_bound3 by metis
    with 2 show ?case by simp
      
  next
    case 2
    then have 1: "int \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk> < 0"
      using DAplus_eq_len assms
      by simp
    then show ?case by simp
  qed
  then show ?case by (cases a; cases b; cases "snd (DA\<^sup>+ (a # as) (b # bs))"; cases "snd (DA\<^sup>+ as bs)", simp_all)
qed


lemma thm_3_4_4_impl_1 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "snd (DA\<^sup>+ (a#as) (b#bs)) = snd (DA\<^sup>+ as bs) \<Longrightarrow> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> = \<lparr>(a#as) \<oplus> (b#bs)\<rparr>"
proof goal_cases
  case 1
  then show ?case 
    apply(subst thm_3_1_3)
    using assms apply simp
    unfolding splus.simps tplus_def seval.simps DAplus.simps prod.sel
    by simp
qed 
  

lemma thm_3_4_1_iff_2:
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
          using le_add_diff_inverse numeral_One of_nat_1 by force
      qed
          
      have 4: "\<And> a b c k. c \<ge> 0 \<Longrightarrow> length a = k \<Longrightarrow> int \<lbrakk> a \<rbrakk> - int b * c < 2 ^ k"
        proof goal_cases
          case (1 a b c k)
          show ?case 
            apply(rule zle_diff1_eq[THEN subst])
            apply (subst diff_le_eq)
            apply(rule order_class.order.trans)
            apply (rule 3[where k = k])
            using ueval_upper_bound2 1 by (simp_all add: 1)
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
        using thm_3_2_1_iff_2 unfolding tplus_def by fastforce
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
                apply(subst nat_transfer)
                apply(subst thm_3_1_1, simp add: len_eq)
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
                apply (subst Int.zle_int)
                  apply(rule order_class.order.trans)
                    apply(rule ueval_upper_bound, simp_all)
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
                apply(subst nat_transfer)
                apply(subst thm_3_1_1, simp add: len_eq)
                unfolding uplus_def DAplus.simps
                apply simp
                apply (subst DAplus_eq_len, simp add: len_eq)+
                apply (cases a ; cases b; cases "snd (DA\<^sup>+ as bs)") apply (simp_all add:len_eq)
                using hyps hyps2 by simp+
            qed
qed


(* Theorem 3.3 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 2 \<longrightarrow> 4 : done *)
(* 4 \<longrightarrow> 1 : done *)
(* 1 \<longrightarrow> 2 : done *)

lemma thm_3_3_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) \<oplus> (bk # bs))" and
          "rk \<equiv> hd ((ak # as) \<oplus> (bk # bs))"
  shows "-(\<lbrakk>ak\<rbrakk>\<^sub>Z) + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> -(\<lbrakk>ak\<rbrakk>\<^sub>Z) + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
    (triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<top> \<or> triple' \<top> \<top> \<bottom>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+

lemma thm_3_3_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) \<ominus> (b#bs))"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) \<noteq> hd (fst (DA\<^sup>- (a#as) (b#bs))) \<longleftrightarrow> 
    (triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<top> \<or> triple' \<top> \<top> \<bottom>)"
  unfolding triple'_def triple_def
proof(rule , goal_cases)
  case 1
  then show ?case
    unfolding tminus_def
    by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)
next
  case 2
  then show ?case unfolding tminus_def
    by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)
qed

lemma nat_transfer2: "(int x) * (int y) = int (x * y)" by simp

lemma thm_3_3_2_impl_4 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "(- (2 ^ k) \<le> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<and> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<le> 2 ^ k - 1) \<Longrightarrow> snd (DA\<^sup>- (a#as) (b#bs)) \<noteq> hd (fst (DA\<^sup>- (a#as) (b#bs)))"
  apply rule
proof goal_cases
  case 1
  have 2: "- (2 ^ k) \<le> \<lparr> (a # as) -\<^sub>U (b # bs) \<rparr> \<and> \<lparr> (a # as) -\<^sub>U (b # bs) \<rparr> \<le> 2 ^ k - 1"
    apply rule
    apply(subst thm_3_1_2[symmetric])
    using assms apply simp
    using 1 apply simp
    apply(subst thm_3_1_2[symmetric])
    using assms apply simp
    using 1 by simp

  have "\<lparr> fst (DA\<^sup>- (False # a # as) (False # b # bs)) \<rparr> = \<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # fst (DA\<^sup>- (a # as) (b # bs)) \<rparr>"
    apply (subst DAminus.simps)
    unfolding prod.sel bool2nat.simps
    apply (cases "snd (DA\<^sup>- (a # as) (b # bs))")
    by simp_all
  with 2 have 3: "- (2 ^ k) \<le>  \<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # hd (fst (DA\<^sup>- (a # as) (b # bs))) # tl (fst (DA\<^sup>- (a # as) (b # bs))) \<rparr> \<and> 
                  \<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # hd (fst (DA\<^sup>- (a # as) (b # bs))) # tl (fst (DA\<^sup>- (a # as) (b # bs))) \<rparr> \<le> 2 ^ k - 1" 
    unfolding uminus_def DAminus.simps prod.sel list.sel by simp
  show ?case proof (cases "snd (DA\<^sup>- (a # as) (b # bs))")
    case False
    then have false: "snd (DA\<^sup>- (a # as) (b # bs)) = False" by simp
    have "\<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # hd (fst (DA\<^sup>- (a # as) (b # bs))) # tl (fst (DA\<^sup>- (a # as) (b # bs))) \<rparr> \<le> - (2 ^ (k+1)) + (2 ^ k - 1)" 
      unfolding 1(2)[symmetric] seval.simps ueval.simps
      apply(rule add_mono)
      unfolding k_def list.size(4) length_tl 
       apply(subst DAminus_eq_len)
      using assms apply simp
      unfolding list.size(4) assms[symmetric] nat_transfer2[symmetric] 
      using False apply simp
      apply(subst DAminus_eq_len)
      using assms apply simp
      unfolding false bool2nat.simps mult_zero_class.mult_zero_left add_0 
      apply simp
      unfolding k_def using ueval_upper_bound3 DAminus_eq_len assms by metis

     (*   apply (subst(4) nat_0_le[symmetric])
       apply simp
      unfolding transfer_int_nat_relations(3) 
      apply(subst nat_diff_distrib')
        apply (simp,simp)
      unfolding nat_one_as_int[symmetric] 
      apply(subst nat_power_eq)
       apply simp
      unfolding transfer_nat_int_numerals(3)[symmetric]
      thm ueval_upper_bound2
      apply(rule ueval_upper_bound2)
      unfolding k_def using DAminus_eq_len assms by simp*)

      with 3 have contr1: "- (2 ^ k) \<le> - (2 ^ (k+1)) + (2 ^ k - (1 :: int))" by simp
      have contr2: "- (2 ^ (k+1)) + (2 ^ k - (1 :: int)) < - (2 ^ k)" by simp

      show ?thesis using contr1 contr2 by simp

  next
    case True
    then have true: "snd (DA\<^sup>- (a # as) (b # bs)) = True" by simp
    have "2 ^ k \<le> \<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # hd (fst (DA\<^sup>- (a # as) (b # bs))) # tl (fst (DA\<^sup>- (a # as) (b # bs))) \<rparr>"
      unfolding 1(2)[symmetric] seval.simps ueval.simps true not_True_eq_False bool2nat.simps mult_zero_left (* transfer_int_nat_numerals(1)[symmetric] *)
        minus_zero add_0 length_tl
      apply(subst DAminus_eq_len)
      using assms apply simp
      unfolding list.size(4) k_def assms by simp
    with 3 have"2 ^ k \<le> 2 ^ k - (1 :: int)" by simp
    then show ?thesis by simp
  qed
qed

lemma thm_3_3_4_impl_1 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) \<noteq> hd (fst (DA\<^sup>- (a#as) (b#bs))) \<Longrightarrow> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>(a#as) \<ominus> (b#bs)\<rparr>"
proof goal_cases
  case 1
  then show ?case 
    apply(subst thm_3_1_2)
    using assms apply simp
    unfolding uminus_def tminus_def seval.simps DAminus.simps prod.sel
    by auto
qed 

lemma thm_3_3_1_impl_2:
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>(a#as) \<ominus> (b#bs)\<rparr> \<Longrightarrow> (- (2 ^ k) \<le> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<and> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<le> 2 ^ k - 1)"
proof (rule, goal_cases)
  case 1
  then show ?case unfolding 1 k_def tminus_def DAminus.simps prod.sel using assms DAminus_eq_len seval_lower_bound
    by metis
next
  case 2
  then show ?case unfolding 2 k_def tminus_def DAminus.simps prod.sel using assms DAminus_eq_len seval_upper_bound
    by metis
qed

(*
(* Theorem 2.12 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 2 \<longrightarrow> 5 : - *)
(* 5 \<longrightarrow> 1 : - *)
(* 1 \<longrightarrow> 2 : done *)

lemma thm_2_12_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) \<ominus> (bk # bs))" and
          "rk \<equiv> hd ((ak # as) \<ominus> (bk # bs))"
  shows "\<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
    (triple' \<top> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<top> \<or> triple' \<top> \<top> \<bottom>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+

lemma thm_2_12_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) \<ominus> (b#bs))"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) = snd (DA\<^sup>- as bs) \<longleftrightarrow> 
    (triple' \<top> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<top> \<or> triple' \<top> \<top> \<bottom>)"
  unfolding triple'_def triple_def
proof(rule , goal_cases)
  case 1
  then show ?case
    unfolding tminus_def
    by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)
next
  case 2
  then show ?case unfolding tminus_def
    by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)
qed


lemma corollary_2_3_ominus: 
  "length as = length bs \<Longrightarrow> as \<ominus> bs = tl (as -\<^sub>S bs)"
  apply (induct as bs rule: List.list_induct2)
  unfolding tminus_def sminus.simps DAminus.simps
  by simp+

lemma thm_2_12_2_impl_5 : 
  fixes ak bk :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as" and rk_def: "rk \<equiv> hd ((ak # as) \<ominus> (bk # bs))"
  shows "- (2 ^ k) \<le> \<lparr>ak#as\<rparr> - \<lparr>bk#bs\<rparr> \<and> \<lparr>ak#as\<rparr> - \<lparr>bk#bs\<rparr> \<le> 2 ^ k - 1 \<Longrightarrow> \<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -1"
proof goal_cases
  case 1
  (*have 2: "- (2 ^ k) \<le> \<lparr> (ak # as) -\<^sub>S (bk # bs) \<rparr> \<and> \<lparr> (ak # as) -\<^sub>S (bk # bs) \<rparr> \<le> 2 ^ k - 1"
    apply rule
    apply(subst four[symmetric])
    using assms apply simp
    using 1 apply simp
    apply(subst four[symmetric])
    using assms apply simp
    using 1 by simp*)

  define alpha ("\<alpha>") where alpha_def: "\<alpha> \<equiv> \<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z"

  (*have unfold: "\<lparr>ak#as\<rparr> - \<lparr>bk#bs\<rparr> = - int (\<lbrakk>ak\<rbrakk>\<^sub>N * 2 ^ length as) + int \<lbrakk>as\<rbrakk> + int (\<lbrakk>bk\<rbrakk>\<^sub>N * 2 ^ length bs) - int \<lbrakk>bs\<rbrakk>"
    unfolding seval.simps by simp*)

  have "\<lparr>ak#as\<rparr> - \<lparr>bk#bs\<rparr> = \<lparr>(ak#as) -\<^sub>S (bk#bs)\<rparr>" using four assms
    by (metis list.size(4))


  have unfold: "\<lparr>ak#as\<rparr> - \<lparr>bk#bs\<rparr> = -(\<lbrakk> ak \<rbrakk>\<^sub>Z * 2 ^ length as) + int \<lbrakk> as \<rbrakk> + (\<lbrakk> bk \<rbrakk>\<^sub>Z * 2 ^ length bs) - int \<lbrakk> bs \<rbrakk>"
    unfolding seval.simps
    using bool2int_eq_bool2nat by auto

  have "(ak#as) -\<^sub>S (bk#bs) =  fst (DA\<^sup>- (ak # ak # as) (bk# bk# bs))" unfolding sminus.simps by simp

  have "(ak # as) \<ominus> (bk # bs) = tl (fst (DA\<^sup>- (ak # ak # as) (bk# bk# bs)))" sorry



  have unfold: "\<lparr> (ak # as) \<ominus> (bk # bs) \<rparr> = int \<lbrakk> fst (DA\<^sup>- as bs) \<rbrakk> - (\<lbrakk>rk\<rbrakk>\<^sub>Z * 2 ^ length bs)"
    unfolding sminus.simps list.sel 
    unfolding DAminus.simps 
    unfolding seval.simps prod.sel rk_def tminus_def DAminus.simps list.sel
    by (cases ak; cases bk; cases "snd (DA\<^sup>- as bs)", simp_all add: DAminus_eq_len assms) 
    

  show ?case sorry
qed

value "\<lparr>[True, False]\<rparr>"

(*lemma thm_2_12_4_impl_1 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) \<noteq> hd (fst (DA\<^sup>- (a#as) (b#bs))) \<Longrightarrow> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>(a#as) \<ominus> (b#bs)\<rparr>"
proof goal_cases
  case 1
  then show ?case 
    apply(subst two)
    using assms apply simp
    unfolding uminus_def tminus_def seval.simps DAminus.simps prod.sel
    by auto
qed *)

lemma thm_2_12_1_impl_2:
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "\<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> = \<lparr>(a#as) \<ominus> (b#bs)\<rparr> \<Longrightarrow> (- (2 ^ k) \<le> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<le> 2 ^ k - 1)"
proof (rule, goal_cases)
  case 1
  then show ?case unfolding 1 k_def tminus_def DAminus.simps prod.sel using assms DAminus_eq_len seval_lower_bound
    by metis
next
  case 2
  then show ?case unfolding 2 k_def tminus_def DAminus.simps prod.sel using assms DAminus_eq_len seval_upper_bound
    by metis
qed*)





(* Theorem 3.5 *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 2 \<longrightarrow> 4 : - *)
(* 4 \<longrightarrow> 1 : - *)
(* 1 \<longleftrightarrow> 2 : - *)

lemma thm_3_5_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) \<ominus> (bk # bs))" and
          "rk \<equiv> hd ((ak # as) \<ominus> (bk # bs))"
  shows "\<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
    (triple' \<top> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<top>  \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<bottom> \<or> triple' \<top> \<top> \<top>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+


lemma thm_3_5_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) \<ominus> (b#bs))"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) = snd (DA\<^sup>- as bs) \<longleftrightarrow> 
    (triple' \<top> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<top>  \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<bottom> \<or> triple' \<top> \<top> \<top>)"
  unfolding triple'_def triple_def
proof(rule , goal_cases)
  case 1
  then show ?case
    unfolding tminus_def
    by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)
next
  case 2
  then show ?case unfolding tminus_def
    by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)
qed



lemma thm_3_5_2_impl_4 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "(- (2 ^ k) \<le> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<le> 2 ^ k - 1) \<Longrightarrow> snd (DA\<^sup>- (a#as) (b#bs)) = snd (DA\<^sup>- as bs)"
  
proof goal_cases
  case 1  
  show ?case 
    apply (cases a; cases b; cases "snd (DA\<^sup>- (a # as) (b # bs))"; cases "snd (DA\<^sup>- as bs)", simp_all)
    sorry
qed


lemma thm_3_5_4_impl_1 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) = snd (DA\<^sup>- as bs) \<Longrightarrow> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> = \<lparr>(a#as) \<ominus> (b#bs)\<rparr>"
proof goal_cases
  case 1
  then show ?case 
    apply(subst thm_3_1_4)
    using assms apply simp
    unfolding sminus.simps tminus_def seval.simps DAminus.simps prod.sel
    by simp
qed 
  

lemma thm_3_5_1_iff_2:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
    \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a \<ominus> b\<rparr> \<longleftrightarrow> (- (2 ^ k) \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> 2 ^ k - 1)"
  apply rule+
    proof goal_cases
      case 1
        have 2: "\<And> x y. 0 \<le> x \<Longrightarrow> - x \<le> int y" by simp
      show ?case
        apply (cases a ; cases b)
        using 1 apply simp_all
        unfolding tminus_def DAminus.simps prod.sel seval.simps
        apply (subst DAminus_eq_len, simp)
        using assms apply simp
        apply (case_tac aa; case_tac aaa; case_tac "snd (DA\<^sup>- list lista)")
               apply simp_all
        by (simp add: "2")+
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
            using ueval_upper_bound2 1 by (simp_all add: 1)
        qed
          
          
      show ?case unfolding 2 using assms
        apply (cases a ; cases b)
        using 2 apply simp_all
        unfolding tminus_def DAminus.simps prod.sel seval.simps
        apply (subst DAminus_eq_len, simp)
        apply(case_tac aa ; case_tac aaa ; case_tac "snd (DA\<^sup>- list lista)")
               apply simp_all
        sorry
        (*by (rule 4 , simp, subst DAminus_eq_len, simp, simp)+  *)        
    next
      case 3
      have subst1: "\<And> a b. length a = length b \<Longrightarrow> 0 \<le> \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> \<and> \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> \<le> 2 ^ length a - 1 \<Longrightarrow> \<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk>" 
        using thm_2_9_1_iff_2 unfolding tplus_def by fastforce
      show ?case sorry
qed


end