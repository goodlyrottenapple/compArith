theory CompArith 
imports Main CompArithDefs

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
     apply (rule ueval_upper_bound)
    by simp
qed


(* Lemma 1.4 *)


lemma lemma_1_4_1 : 
  fixes k :: nat
  assumes "length x = Suc k"
  shows "length x = length y \<Longrightarrow> \<lbrakk> x \<rbrakk> = \<lbrakk> y \<rbrakk> \<Longrightarrow> x = y"
  apply (induct x y rule: List.list_induct2)
   apply simp
  apply(case_tac x; case_tac y, simp_all)
  by (metis not_add_less1 ueval_upper_bound3)+

lemma lemma_1_4_2 : 
  fixes k :: nat
  assumes "length x = Suc k"
  shows "length x = length y \<Longrightarrow> \<lparr> x \<rparr> = \<lparr> y \<rparr> \<Longrightarrow> x = y"
  apply (induct x y rule: List.list_induct2)
   apply simp
  apply(case_tac x; case_tac y, simp_all)
  using lemma_1_4_1 apply (metis Nitpick.size_list_simp(2))
    apply (metis diff_gt_0_iff_gt less_imp_of_nat_less minus_diff_eq not_int_zless_negative of_nat_less_numeral_power_cancel_iff pos_int_cases ueval_upper_bound3)
   apply (metis of_nat_less_0_iff less_iff_diff_less_0 numeral_power_eq_of_nat_cancel_iff of_nat_less_iff ueval_upper_bound3)
  by (metis Nitpick.size_list_simp(2) lemma_1_4_1)


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
  shows "length a = length b \<Longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>Z\<^sub>A b\<rbrakk>"
  unfolding uplus_def
  apply (subst plus_DA , simp)
proof (induct a b rule: List.list_induct2)
case Nil 
  thus ?case by simp
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
  shows "\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>Z\<^sub>A b\<rbrakk>"
  unfolding a_def b_def
  using len_eq
proof (induct as bs arbitrary: a_k b_k rule: List.list_induct2)
case Nil 
  thus ?case unfolding uplus_def DAplus.simps
    by (cases a_k; cases b_k; simp_all)
next
case (Cons a_km1 as b_km1 bs)
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
  from Cons have ih: "\<lbrakk> a\<^sup>k \<rbrakk> + \<lbrakk> b\<^sup>k \<rbrakk> = \<lbrakk> a\<^sup>k +\<^sub>Z\<^sub>A b\<^sup>k \<rbrakk>" by simp
  then have ih': "\<lbrakk> a\<^sup>k \<rbrakk> + \<lbrakk> b\<^sup>k \<rbrakk> = \<lbrakk> c\<^sub>k\<^sub>+\<^sub>1 # r\<^sup>k \<rbrakk>" 
    unfolding rk_def c_kp1_def uplus_def DAplus.simps bool2nat.simps add_0 fst_conv snd_conv to_from_mod_id by simp
  
  show "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> a +\<^sub>Z\<^sub>A b \<rbrakk>"
    unfolding a_def b_def uplus_def DAplus.simps fst_conv snd_conv rk_def[symmetric] c_kp1_def[symmetric] bool2nat.simps add_0 
              r_kp1_def[symmetric] c_kp2_def[symmetric] to_from_mod_id ueval.simps 
    apply(subst semiring_normalization_rules(20))
    apply (subst ih')
    unfolding ueval.simps len_ak_eq_bk len_bk apply simp
    unfolding semiring_normalization_rules(1) semiring_normalization_rules(18) apply(rule mult_right_cancel[THEN iffD2], simp)
    unfolding c_kp2_def r_kp1_def 
    by (cases a_k; cases b_k; cases "c\<^sub>k\<^sub>+\<^sub>1", simp_all)
qed


lemma thm_3_1_1_iff_3 : "(\<forall>a b. length a = length b \<longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>Z\<^sub>A b\<rbrakk>) \<longleftrightarrow> (\<forall>a b. length a = length b \<longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>S\<^sub>A b\<rparr>)"

  apply rule+
   apply (case_tac a ; case_tac b)
      unfolding splus.simps apply (simp , simp , simp)
   defer
   apply rule+
proof goal_cases
case (1 a b)
  then have "length (False # a) = length (False # b)" by simp
  with 1 have subst2: "\<lparr> False # a \<rparr> + \<lparr> False # b \<rparr> = \<lparr> (False # a) +\<^sub>S\<^sub>A (False # b) \<rparr>" by blast
  
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

lemma thm_3_1_3: "length a = length b \<Longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>S\<^sub>A b\<rparr>" using thm_3_1_1_iff_3 thm_3_1_1 by simp

lemma thm_3_1_2_iff_4 : "(\<forall>a b. length a = length b \<longrightarrow> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a -\<^sub>Z\<^sub>A b\<rparr>) \<longleftrightarrow> 
                         (\<forall>a b. length a = length b \<longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>S\<^sub>A b\<rparr>)"
  apply rule+
   apply (case_tac a ; case_tac b)
      unfolding sminus.simps apply (simp , simp , simp)
   defer
   apply rule+
proof goal_cases
case (1 a b)
  then have "length (False # a) = length (False # b)" by simp
  with 1 have subst1: "\<lparr> False # a \<rparr> - \<lparr> False # b \<rparr> = \<lparr> (False # a) -\<^sub>S\<^sub>A (False # b) \<rparr>" by blast

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
    unfolding uminus_def sminus.simps list.sel(1) DAminus.simps prod.sel apply simp
    apply(subst DAminus_eq_len , simp add:subst2)+
    unfolding to_from_div_id3 to_from_mod_id3 subst2
    apply(cases a ; cases b ; cases "snd (DA\<^sup>- as bs)")
    by auto
qed


lemma thm_3_1_1_iff_2 : "(\<forall>a b. length a = length b \<longrightarrow> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>Z\<^sub>A b\<rbrakk>) \<longleftrightarrow> 
                         (\<forall>a b. length a = length b \<longrightarrow> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a -\<^sub>Z\<^sub>A b\<rparr>)"
  apply rule+
   defer
   apply rule+
proof goal_cases
case (2 a b)
  have subst1: "\<And> a b c :: int. a = c + b \<Longrightarrow> a - b = c" by simp
  have subst2: "\<And> a b c :: int. a + c + b = a + (c + b)" by simp
  from 2(1) have subst3: "\<forall>a b. length a = length b \<longrightarrow> int \<lbrakk> a \<rbrakk> + int \<lbrakk> b \<rbrakk> = int \<lbrakk> a +\<^sub>Z\<^sub>A b \<rbrakk>"
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
    using DAminus_eq_len 2 
     apply simp
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
     unfolding uplus_def apply(rule DAplus_eq_len)
     using 1 apply simp
    unfolding uminus_def DAminus.simps prod.sel seval.simps
    apply(subst DAminus_eq_len, subst DAplus_eq_len, simp add:1, simp)
    unfolding not_False_eq_True bool2nat.simps DAplus.simps DAminus.simps prod.sel
    apply simp
    apply(subst DAminus_eq_len, subst DAplus_eq_len, simp add:1, simp)
    apply(subst DAminus_DAplus_compl, simp add: 1)+
    apply(cases "snd (DA\<^sup>+ a b)")
    using 1 2 by simp+
qed

lemma thm_3_1_2: "length a = length b \<Longrightarrow> int \<lbrakk>a\<rbrakk> - int \<lbrakk>b\<rbrakk> = \<lparr>a -\<^sub>Z\<^sub>A b\<rparr>" using thm_3_1_1_iff_2 thm_3_1_1 by simp


lemma thm_3_1_4: "length a = length b \<Longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>S\<^sub>A b\<rparr>" using thm_3_1_1_iff_2 thm_3_1_2_iff_4 thm_3_1_1 by simp


(* Theorem 3.2 *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 1 \<longleftrightarrow> 4 : done *)
(* 1 \<longleftrightarrow> 2 : done *)


lemma thm_3_2_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>+ (a#as) (b#bs)) = \<bottom> \<longleftrightarrow> 
         (triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<top>)"
  apply rule
  unfolding triple'_def triple_def tplus_def
  by (cases a; cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)+



lemma thm_3_2_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) +\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) +\<^sub>A (bk # bs))"
  shows "\<lbrakk>ak\<rbrakk>\<^sub>Z + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk>ak\<rbrakk>\<^sub>Z + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
         (triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<top>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+




lemma thm_3_2_1_iff_4 : 
"length a = length b \<Longrightarrow> 
\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>A b\<rbrakk> \<longleftrightarrow> snd (DA\<^sup>+ a b) = False"
  apply rule
   apply (rule ccontr)
proof goal_cases
case 1
  then have 2: "snd (DA\<^sup>+ a b) = True" by simp
  have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> a +\<^sub>Z\<^sub>A b \<rbrakk>" using thm_3_1_1 1 by simp
  with 1 have "\<lbrakk> a +\<^sub>A b \<rbrakk> = \<lbrakk> a +\<^sub>Z\<^sub>A b \<rbrakk>" by simp
  with 1 have "\<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk>"
  unfolding uplus_def tplus_def using plus_DA by presburger
  with 2 have "\<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> True # fst (DA\<^sup>+ a b) \<rbrakk>" by simp
  
  then show ?case by simp
next
case 2
  have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> a +\<^sub>Z\<^sub>A b \<rbrakk>" using thm_3_1_1 2 by simp
  then have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk>"
  unfolding uplus_def using 2 plus_DA by presburger
  with 2 have "\<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> = \<lbrakk> False # fst (DA\<^sup>+ a b) \<rbrakk>" by simp
  
  then show ?case unfolding tplus_def ueval.simps bool2nat.simps by simp
qed

lemma thm_3_2_1_iff_2 : 
"length a = length b \<Longrightarrow> 
\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>a +\<^sub>A b\<rbrakk> \<longleftrightarrow> (0 \<le> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<and> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<le> 2 ^ (length a) - 1)"
  apply rule+
proof goal_cases
case 1
  show ?case unfolding 1
    apply(rule ueval_upper_bound2)
    unfolding tplus_def apply (rule DAplus_eq_len)
    using 1 by simp
next
case 2
  then have 3: "\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<le> 2 ^ length a - 1" by simp
  have "\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk> a +\<^sub>Z\<^sub>A b \<rbrakk>" using thm_3_1_1 2 by simp
  with 3 have "\<lbrakk>a +\<^sub>Z\<^sub>A b\<rbrakk> \<le> 2 ^ length a - 1" by simp
  then have "\<lbrakk> snd (DA\<^sup>+ a b) # fst (DA\<^sup>+ a b) \<rbrakk> \<le> 2 ^ length a - 1" 
  unfolding uplus_def tplus_def using plus_DA 2 by simp
  then have "\<lbrakk> snd (DA\<^sup>+ a b) \<rbrakk>\<^sub>N * 2 ^ length a + \<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> \<le> 2 ^ length a - 1" 
  unfolding ueval.simps using DAplus_eq_len 2 by simp
  then have "snd (DA\<^sup>+ a b) = False" by (rule_tac ccontr, simp)
  
  then show ?case
    apply (subst thm_3_2_1_iff_4)
    using 2 by simp_all
qed


(* Theorem 3.2 Condition Set 2 *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 1 \<longleftrightarrow> 4 : done *)
(* 1 \<longleftrightarrow> 2 : done *)


lemma thm_3_2_cs2_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>+ (a#as) (b#bs)) = \<top> \<longleftrightarrow> 
         (triple' \<bottom> \<top> \<bottom> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<bottom> \<or> triple' \<top> \<top> \<top>)"
  apply rule
  unfolding triple'_def triple_def tplus_def
  by (cases a; cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)+



lemma thm_3_2_cs2_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) +\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) +\<^sub>A (bk # bs))"
  shows "\<lbrakk>ak\<rbrakk>\<^sub>Z + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 2 \<or> \<lbrakk>ak\<rbrakk>\<^sub>Z + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 1  \<longleftrightarrow> 
         (triple' \<bottom> \<top> \<bottom> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<bottom> \<or> triple' \<top> \<top> \<top>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+



lemma thm_3_2_cs2_1_iff_4 : 
"length a = length b \<Longrightarrow> 
\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>\<top>#(a +\<^sub>A b)\<rbrakk> \<longleftrightarrow> snd (DA\<^sup>+ a b) = \<top>"
  apply rule
  using thm_3_2_1_iff_4 apply fastforce
  by (simp add: thm_3_1_1 tplus_def uplus_def)


lemma thm_3_2_cs2_1_iff_2 : 
"length a = length b \<Longrightarrow> 
\<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> = \<lbrakk>\<top>#(a +\<^sub>A b)\<rbrakk> \<longleftrightarrow> 2 ^ (length a) \<le> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<and> \<lbrakk>a\<rbrakk> + \<lbrakk>b\<rbrakk> \<le> 2 * (2 ^ (length a) - 1)"
  apply rule+
    apply (simp add: DAplus_eq_len tplus_def)
   apply (metis add_le_mono mult_2 ueval_upper_bound)
  by (metis DAplus_eq_len not_less thm_3_2_1_iff_4 thm_3_2_cs2_1_iff_4 top_unfold tplus_def ueval_upper_bound3)



(* Theorem 3.3 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 2 \<longrightarrow> 4 : done *)
(* 4 \<longrightarrow> 1 : done *)
(* 1 \<longrightarrow> 2 : done *) 

lemma thm_3_3_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) +\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) +\<^sub>A (bk # bs))"
  shows "-(\<lbrakk>ak\<rbrakk>\<^sub>Z) + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> -(\<lbrakk>ak\<rbrakk>\<^sub>Z) + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
         (triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<top> \<or> triple' \<top> \<top> \<bottom>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+

lemma thm_3_3_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) \<noteq> hd (fst (DA\<^sup>- (a#as) (b#bs))) \<longleftrightarrow> 
         (triple' \<bottom> \<top> \<top> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<bottom> \<bottom> \<top> \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<top> \<or> triple' \<top> \<top> \<bottom>)"
  apply rule
  unfolding triple'_def triple_def tminus_def
  by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)+



lemma thm_3_3_2_impl_4 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "(- (2 ^ k) \<le> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<and> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<le> 2 ^ k - 1) \<Longrightarrow> snd (DA\<^sup>- (a#as) (b#bs)) \<noteq> hd (fst (DA\<^sup>- (a#as) (b#bs)))"
  apply rule
proof goal_cases
case 1
  have 2: "- (2 ^ k) \<le> \<lparr> (a # as) -\<^sub>Z\<^sub>A (b # bs) \<rparr> \<and> \<lparr> (a # as) -\<^sub>Z\<^sub>A (b # bs) \<rparr> \<le> 2 ^ k - 1"
    apply rule
     apply(subst thm_3_1_2[symmetric])
      using assms apply simp
     using 1 apply simp
    apply (subst thm_3_1_2[symmetric])
     apply (simp add: assms)
    using 1 by simp
  
  have "\<lparr> fst (DA\<^sup>- (False # a # as) (False # b # bs)) \<rparr> = \<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # fst (DA\<^sup>- (a # as) (b # bs)) \<rparr>"
    apply (subst DAminus.simps)
    unfolding prod.sel bool2nat.simps
    apply (cases "snd (DA\<^sup>- (a # as) (b # bs))")
    by simp_all
  
  with 2 have 3: "- (2 ^ k) \<le>  \<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # hd (fst (DA\<^sup>- (a # as) (b # bs))) # tl (fst (DA\<^sup>- (a # as) (b # bs))) \<rparr> \<and>
      \<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # hd (fst (DA\<^sup>- (a # as) (b # bs))) # tl (fst (DA\<^sup>- (a # as) (b # bs))) \<rparr> \<le> 2 ^ k - 1" 
    unfolding uminus_def DAminus.simps prod.sel list.sel by simp
  
  show ?case 
  proof (cases "snd (DA\<^sup>- (a # as) (b # bs))")
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
    
    with 3 have contr1: "- (2 ^ k) \<le> - (2 ^ (k+1)) + (2 ^ k - (1 :: int))" by simp
    have contr2: "- (2 ^ (k+1)) + (2 ^ k - (1 :: int)) < - (2 ^ k)" by simp
  
    show ?thesis using contr1 contr2 by simp
  next
  case True
    then have true: "snd (DA\<^sup>- (a # as) (b # bs)) = True" by simp
    have "2 ^ k \<le> \<lparr> (\<not> snd (DA\<^sup>- (a # as) (b # bs))) # hd (fst (DA\<^sup>- (a # as) (b # bs))) # tl (fst (DA\<^sup>- (a # as) (b # bs))) \<rparr>"
      unfolding 1(2)[symmetric] seval.simps ueval.simps true not_True_eq_False bool2nat.simps mult_zero_left
                minus_zero add_0 length_tl
      apply(subst DAminus_eq_len)
       using assms apply simp
      unfolding list.size(4) k_def assms by simp
    with 3 have "2 ^ k \<le> 2 ^ k - (1 :: int)" by simp
    
    then show ?thesis by simp
  qed
qed

lemma thm_3_3_4_impl_1 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) \<noteq> hd (fst (DA\<^sup>- (a#as) (b#bs))) \<Longrightarrow> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>(a#as) -\<^sub>A (b#bs)\<rparr>"
  apply (subst thm_3_1_2)
  using assms apply simp
  unfolding uminus_def tminus_def seval.simps DAminus.simps prod.sel by auto

 

lemma thm_3_3_1_impl_2:
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>(a#as) -\<^sub>A (b#bs)\<rparr> \<Longrightarrow> (- (2 ^ k) \<le> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<and> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<le> 2 ^ k - 1)"
  apply rule
  unfolding k_def tminus_def DAminus.simps prod.sel 
  using assms DAminus_eq_len seval_lower_bound seval_upper_bound by metis+


(* Theorem 3.3 Condition Set 2 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 2 \<longrightarrow> 3 : done *)
(* 3 \<longrightarrow> 1 : done *)
(* 1 \<longrightarrow> 2 : done *) 

lemma thm_3_3_cs2_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) -\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) -\<^sub>A (bk # bs))"
  shows "-(\<lbrakk>ak\<rbrakk>\<^sub>Z) + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 1 \<longleftrightarrow> triple' \<bottom> \<top> \<bottom>"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+

lemma thm_3_3_cs2_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) = \<bottom> \<and>  hd (fst (DA\<^sup>- (a#as) (b#bs))) = \<bottom> \<longleftrightarrow> triple' \<bottom> \<top> \<bottom>"
  apply rule
  unfolding triple'_def triple_def tminus_def
  by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)+



lemma thm_3_3_cs2_2_impl_3:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         - (2 ^ Suc k) + 1 \<le> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<and> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<le> - (2 ^ k) - 1 \<Longrightarrow> triple' \<bottom> \<top> \<bottom>"
proof goal_cases
case 1
  have "\<bottom> = a" "\<top> = b" "\<bottom> = hd ((a#as) -\<^sub>A (b#bs))"
      apply (smt "1"(1) "1"(2) assms(1) bot_unfold eval_eq_seval of_nat_add of_nat_less_0_iff seval.simps(2) seval_upper_bound ueval.simps(2))
     apply (smt "1"(1) "1"(2) assms(1) eval_eq_seval of_nat_add of_nat_less_0_iff seval.simps(2) seval_upper_bound top_unfold ueval.simps(2))
    by (smt "1"(1) "1"(2) assms(1) bool2nat.simps(1) bot_unfold comm_monoid_mult_class.mult_1 less_imp_of_nat_less list.sel(1) of_nat_add seval.simps(2) seval_lower_bound thm_3_3_1_impl_2 thm_3_3_4_iff_3 thm_3_3_4_impl_1 top_unfold triple_def ueval.simps(2) ueval_upper_bound3)
  
  then show ?case unfolding triple'_def triple_def by auto
qed

lemma thm_3_3_cs2_3_impl_1:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         triple' \<bottom> \<top> \<bottom> \<Longrightarrow> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>\<top>#((a#as) -\<^sub>A (b#bs))\<rparr> \<and> hd ((a#as) -\<^sub>A (b#bs)) = \<bottom>"
  apply(subst thm_3_1_2)
   using assms apply simp
  unfolding sminus.simps uminus_def tminus_def seval.simps ueval.simps DAminus.simps prod.sel triple'_def triple_def list.sel(1)
  using to_from_mod_id to_from_mod_id3 by auto



lemma thm_3_3_cs2_1_impl_2:
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>\<top>#((a#as) -\<^sub>A (b#bs))\<rparr> \<and> hd ((a#as) -\<^sub>A (b#bs)) = \<bottom> \<Longrightarrow> 
         - (2 ^ Suc k) + 1 \<le> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<and> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<le> - (2 ^ k) - 1"
  apply rule
  unfolding k_def tminus_def DAminus.simps prod.sel 
  using assms DAminus_eq_len seval_lower_bound seval_upper_bound
   apply (smt eval_eq_seval length_Cons of_nat_less_0_iff)
  by (smt DAminus_eq_len One_nat_def assms(1) bool2nat.simps(1) bool2nat.simps(2) bot_unfold comm_monoid_mult_class.mult_1 comm_semiring_class.distrib diff_Suc_1 int_nat_eq le_numeral_extra(4) length_Cons list.sel(1) mult_is_0 nat_2 numeral_2_eq_2 of_nat_add of_nat_diff of_nat_power semiring_normalization_rules(2) semiring_normalization_rules(27) seval.simps(2) seval_upper_bound top_unfold ueval.simps(2))



(* Theorem 3.3 Condition Set 3 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 2 \<longrightarrow> 3 : done *)
(* 3 \<longrightarrow> 1 : done *)
(* 1 \<longrightarrow> 2 : done *) 

lemma thm_3_3_cs3_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) -\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) -\<^sub>A (bk # bs))"
  shows "-(\<lbrakk>ak\<rbrakk>\<^sub>Z) + \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -2 \<longleftrightarrow> triple' \<top> \<bottom> \<top>"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+

lemma thm_3_3_cs3_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) = \<top> \<and> hd (fst (DA\<^sup>- (a#as) (b#bs))) = \<top> \<longleftrightarrow> triple' \<top> \<bottom> \<top>"
  apply rule
  unfolding triple'_def triple_def tminus_def
  by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)+



lemma thm_3_3_cs3_2_impl_3:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         2 ^ k \<le> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<and> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<le> (2 ^ Suc k) - 1 \<Longrightarrow> triple' \<top> \<bottom> \<top>"
proof goal_cases
case 1
  have "\<top> = a" "\<bottom> = b" "\<top> = hd ((a#as) -\<^sub>A (b#bs))" 
      apply (smt "1"(2) add_0_left assms(1) bool2nat.simps(2) eval_eq_seval mult_is_0 of_nat_less_0_iff seval_upper_bound top_unfold ueval.simps(2))
     apply (smt "1"(1) "1"(2) assms(1) bot_unfold eval_eq_seval of_nat_add of_nat_less_0_iff seval.simps(2) seval_upper_bound ueval.simps(2))
    by (smt "1"(1) "1"(2) assms(1) bot_unfold eval_eq_seval list.sel(1) of_nat_add of_nat_less_0_iff seval.simps(2) seval_upper_bound thm_3_3_1_impl_2 thm_3_3_4_impl_1 thm_3_3_cs2_4_iff_3 tminus_def top_unfold triple_def ueval.simps(2))

  then show ?case unfolding triple'_def triple_def by auto
qed

lemma thm_3_3_cs3_3_impl_1:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         triple' \<top> \<bottom> \<top> \<Longrightarrow> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>\<bottom>#((a#as) -\<^sub>A (b#bs))\<rparr> \<and> hd ((a#as) -\<^sub>A (b#bs)) = \<top>"
  apply(subst thm_3_1_2)
   using assms apply simp
  unfolding sminus.simps uminus_def tminus_def seval.simps ueval.simps DAminus.simps prod.sel triple'_def triple_def list.sel(1)
  using to_from_mod_id to_from_mod_id3 by auto



lemma thm_3_3_cs3_1_impl_2:
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> = \<lparr>\<bottom>#((a#as) -\<^sub>A (b#bs))\<rparr> \<and> hd ((a#as) -\<^sub>A (b#bs)) = \<top> \<Longrightarrow> 
         2 ^ k \<le> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<and> int \<lbrakk>a#as\<rbrakk> - int \<lbrakk>b#bs\<rbrakk> \<le> (2 ^ Suc k) - 1"
  apply rule
  unfolding k_def tminus_def DAminus.simps prod.sel
  using assms DAminus_eq_len seval_lower_bound seval_upper_bound
   apply simp
  by (smt DAminus_eq_len One_nat_def assms(1) bool2nat.simps(1) bool2nat.simps(2) bot_unfold comm_monoid_mult_class.mult_1 comm_semiring_class.distrib diff_Suc_1 int_nat_eq le_numeral_extra(4) length_Cons list.sel(1) mult_is_0 nat_2 numeral_2_eq_2 of_nat_add of_nat_diff of_nat_power semiring_normalization_rules(2) semiring_normalization_rules(27) seval.simps(2) seval_upper_bound top_unfold ueval.simps(2))

(* Theorem 3.4 *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 2 \<longrightarrow> 4 : done *)
(* 4 \<longrightarrow> 1 : done *)
(* 1 \<longleftrightarrow> 2 : done *)

lemma thm_3_4_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) +\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) +\<^sub>A (bk # bs))"
  shows "-(\<lbrakk>ak\<rbrakk>\<^sub>Z) - \<lbrakk>bk\<rbrakk>\<^sub>Z + \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> -(\<lbrakk>ak\<rbrakk>\<^sub>Z) - \<lbrakk>bk\<rbrakk>\<^sub>Z + \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
         (triple' \<top> \<top> \<top> \<or> triple' \<top> \<bottom> \<top> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<bottom>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+


lemma thm_3_4_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>+ (a#as) (b#bs)) = snd (DA\<^sup>+ as bs) \<longleftrightarrow> 
         (triple' \<top> \<top> \<top> \<or> triple' \<top> \<bottom> \<top> \<or> triple' \<top> \<bottom> \<bottom> \<or> triple' \<bottom> \<top> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<bottom>)"
  apply rule
  unfolding triple'_def triple_def tplus_def 
  by (cases a;cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)+



lemma thm_3_4_2_impl_4 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "(- (2 ^ k) \<le> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> \<le> 2 ^ k - 1) \<Longrightarrow> snd (DA\<^sup>+ (a#as) (b#bs)) = snd (DA\<^sup>+ as bs)"
proof goal_cases
case 1
  then have "- (2 ^ k) \<le> \<lparr> (a # as) +\<^sub>S\<^sub>A (b # bs) \<rparr> \<and> \<lparr> (a # as) +\<^sub>S\<^sub>A (b # bs) \<rparr> \<le> 2 ^ k - 1"
    apply rule
    apply rule
     apply(subst thm_3_1_3[symmetric])
      using assms apply simp
     apply simp
    apply(subst thm_3_1_3[symmetric])
     using assms apply simp
    by simp


  then have "(\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>+ (a # as) (b # bs)) \<rbrakk>\<^sub>N) mod 2 = (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>+ as bs) \<rbrakk>\<^sub>N) mod 2"
    apply(cases a; cases b; cases "snd (DA\<^sup>+ (a # as) (b # bs))"; cases "snd (DA\<^sup>+ as bs)", simp_all)
  proof goal_cases
  case 1
    then have 2: "2 ^ k \<le> \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk>"
      apply (subst(2) nat_int[symmetric])
      apply(subst nat_le_iff)
      using DAplus_eq_len assms by simp
    have "\<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk> \<le> 2 ^ k - 1" using ueval_upper_bound DAplus_eq_len assms by metis
    then have "\<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk> < 2 ^ k"  using DAplus_eq_len assms ueval_upper_bound3 by metis
    
    with 2 show ?case by simp
  next
  case 2
    then have 1: "int \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk> < 0"
      using DAplus_eq_len assms by simp
  
    then show ?case by simp
  qed
  
  then show ?case by (cases a; cases b; cases "snd (DA\<^sup>+ (a # as) (b # bs))"; cases "snd (DA\<^sup>+ as bs)", simp_all)
qed


lemma thm_3_4_4_impl_1 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "snd (DA\<^sup>+ (a#as) (b#bs)) = snd (DA\<^sup>+ as bs) \<Longrightarrow> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> = \<lparr>(a#as) +\<^sub>A (b#bs)\<rparr>"
  apply(subst thm_3_1_3)
   using assms apply simp
  unfolding splus.simps tplus_def seval.simps DAplus.simps prod.sel
  by simp
 


lemma thm_3_4_1_iff_2:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>A b\<rparr> \<longleftrightarrow> (- (2 ^ k) \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> 2 ^ k - 1)"
  apply rule+
proof goal_cases
case 1
  have 2: "\<And> x y. 0 \<le> x \<Longrightarrow> - x \<le> int y" by simp

  show ?case
    apply (cases a ; cases b)
       using 1 apply simp_all
    unfolding tplus_def DAplus.simps prod.sel seval.simps
    apply (subst DAplus_eq_len, simp)
    using assms
    apply simp
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
    then have "int \<lbrakk> xs \<rbrakk> + - 1 * int (2 ^ ka - 1) \<le> 0" by simp
    then show "int \<lbrakk> xs \<rbrakk> \<le> 2 ^ ka - 1"
    using le_add_diff_inverse numeral_One of_nat_1 by force
  qed

  have 4: "\<And> a b c k. c \<ge> 0 \<Longrightarrow> length a = k \<Longrightarrow> int \<lbrakk> a \<rbrakk> - int b * c < 2 ^ k"
  proof goal_cases
  case (1 a b c k)
    show ?case 
      apply (rule zle_diff1_eq[THEN subst])
      apply (subst diff_le_eq)
      apply (rule order_class.order.trans)
       apply (rule 3[where k = k])
      using ueval_upper_bound2 1
       apply auto[1]
      by (simp add: "1"(1))
  qed

  show ?case unfolding 2 using assms
    apply (cases a ; cases b)
       using 2 apply simp_all
    unfolding tplus_def DAplus.simps prod.sel seval.simps
    apply (subst DAplus_eq_len, simp)
    apply (case_tac aa ; case_tac aaa ; case_tac "snd (DA\<^sup>- list lista)")
           apply simp_all
    by (rule 4 , simp, subst DAplus_eq_len, simp, simp)+
next
case 3
  have subst1: "\<And> a b. length a = length b \<Longrightarrow> 0 \<le> \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> \<and> \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk> \<le> 2 ^ length a - 1 \<Longrightarrow> \<lbrakk> fst (DA\<^sup>+ a b) \<rbrakk> = \<lbrakk> a \<rbrakk> + \<lbrakk> b \<rbrakk>" 
    using thm_3_2_1_iff_2 unfolding tplus_def by fastforce
  
  show ?case
    apply (cases a; cases b)
    unfolding tplus_def
       apply simp
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
  
    then have hyps: 
      "- (2 ^ length as) \<le> - int (\<lbrakk> a \<rbrakk>\<^sub>N * 2 ^ length as) - int (\<lbrakk> b \<rbrakk>\<^sub>N * 2 ^ length as) + int (\<lbrakk> snd (DA\<^sup>+ as bs) \<rbrakk>\<^sub>N) * 2 ^ length as + int \<lbrakk> fst (DA\<^sup>+ as bs) \<rbrakk>" 
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
      have f1: "Suc (nat (- 1 + 2 ^ length bs)) = nat (2 ^ length bs)" by (simp add: Suc_nat_eq_nat_zadd1)
      have "(0::int) \<le> 2" by auto
      then have "Suc (nat (- 1 + 2 ^ length bs)) = 2 ^ length bs"
      using f1 nat_2 nat_power_eq numeral_2_eq_2 by presburger
      
      then show "2 ^ length bs - Suc 0 \<le> nat (2 ^ length bs - 1)" by linarith
    qed
      
    show ?case unfolding 1 DAplus.simps prod.sel seval.simps
      apply(subst subst3)
      apply(subst nat_transfer)
      apply(subst thm_3_1_1, simp add: len_eq)
      unfolding uplus_def DAplus.simps
      apply simp
      apply (subst DAplus_eq_len, simp add: len_eq)+
      apply (cases a ; cases b; cases "snd (DA\<^sup>+ as bs)") 
             apply (simp_all add:len_eq)
      using hyps hyps2 by simp+
  qed
qed


lemma thm_3_4_2_impl_1:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         (- (2 ^ k) \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> 2 ^ k - 1) \<Longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>A b\<rparr>"
  using thm_3_4_1_iff_2 assms by blast



(* Theorem 3.4 Condition Set 2 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 1 \<longrightarrow> 2 : done *)
(* 2 \<longrightarrow> 3 : done *)
(* 3 \<longrightarrow> 1 : done *)

lemma thm_3_4_cs2_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) +\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) +\<^sub>A (bk # bs))"
  shows "-(\<lbrakk>ak\<rbrakk>\<^sub>Z) - \<lbrakk>bk\<rbrakk>\<^sub>Z + \<lbrakk>rk\<rbrakk>\<^sub>Z = -2  \<longleftrightarrow> triple' \<top> \<top> \<bottom>"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+



lemma thm_3_4_cs2_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "(snd (DA\<^sup>+ (a#as) (b#bs)) = \<top> \<and> snd (DA\<^sup>+ as bs) = \<bottom>) \<longleftrightarrow> triple' \<top> \<top> \<bottom>"
  apply rule
  unfolding triple'_def triple_def tplus_def
  by (cases a;cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)+



lemma thm_3_4_cs2_1_impl_2:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         (\<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>\<top>#(a +\<^sub>A b)\<rparr> \<and> hd (a +\<^sub>A b) = \<bottom>) \<Longrightarrow> - (2 ^ (Suc k)) \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> - (2 ^ k) - 1"
  apply rule+
proof goal_cases
case 1
  then have "\<lparr>a\<rparr> + \<lparr>b\<rparr> = - int (2 ^ (Suc k)) + int \<lbrakk> a +\<^sub>A b \<rbrakk>" unfolding seval.simps
    using DAplus_eq_len assms tplus_def by auto
  
  then show ?case by simp
next
case 2
  then have 1: "\<lparr>a\<rparr> + \<lparr>b\<rparr> = - int (2 ^ (Suc k)) + int \<lbrakk> a +\<^sub>A b \<rbrakk>" unfolding seval.simps
    using DAplus_eq_len assms tplus_def by auto

  show ?case unfolding 1
    apply simp
    apply (cases "a +\<^sub>A b") 
     using assms 2 apply simp_all
    using ueval_upper_bound3
    by (metis DAplus_eq_len add_diff_cancel_left' length_Cons plus_1_eq_Suc tplus_def)
qed


lemma thm_3_4_cs2_2_impl_3:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         - (2 ^ (Suc k)) \<le> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> \<le> - (2 ^ k) - 1 \<Longrightarrow> triple' \<top> \<top> \<bottom>"
proof goal_cases
case 1
  have 2: "- (2 ^ (Suc k)) \<le> \<lparr> (a#as) +\<^sub>S\<^sub>A (b#bs) \<rparr> \<and> \<lparr> (a#as) +\<^sub>S\<^sub>A (b#bs) \<rparr> \<le> - (2 ^ k) - 1"
    apply rule
     apply(subst thm_3_1_3[symmetric])
      using 1 apply (simp,simp)
    apply (subst thm_3_1_3[symmetric])
    using 1 by simp_all

  define sig_r ("\<sigma>\<^sub>r") where "\<sigma>\<^sub>r \<equiv> \<lbrakk> (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>+ as bs) \<rbrakk>\<^sub>N) mod 2 \<rbrakk>\<^sub>B"
  define r_k_minus_one ("r\<^sup>k\<^sup>-\<^sup>1") where "r\<^sup>k\<^sup>-\<^sup>1 \<equiv> fst (DA\<^sup>+ as bs)"
  define R  where "R \<equiv> \<lbrakk> (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (\<sigma>\<^sub>r # r\<^sup>k\<^sup>-\<^sup>1, \<lbrakk> (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>+ as bs) \<rbrakk>\<^sub>N) div 2 \<rbrakk>\<^sub>B) \<rbrakk>\<^sub>N) mod 2 \<rbrakk>\<^sub>B"
  
  from 2 have 3: 
  "- (2 ^ (Suc k)) \<le> - int (\<lbrakk> R \<rbrakk>\<^sub>N) * (2 ^ (Suc k)) + int ((\<lbrakk>\<sigma>\<^sub>r\<rbrakk>\<^sub>N) * (2 ^ k) + \<lbrakk> r\<^sup>k\<^sup>-\<^sup>1 \<rbrakk>)"
  "- int (\<lbrakk> R \<rbrakk>\<^sub>N) * (2 ^ (Suc k)) + int ((\<lbrakk>\<sigma>\<^sub>r\<rbrakk>\<^sub>N) * (2 ^ k) + \<lbrakk> r\<^sup>k\<^sup>-\<^sup>1 \<rbrakk>) \<le> - (2 ^ k) - 1"
    unfolding splus.simps list.sel(1) DAplus.simps fst_conv sig_r_def 
    r_k_minus_one_def R_def seval.simps ueval.simps
    using DAplus_eq_len assms(1) 1(1) by simp_all
  
  from 3(2) have 4: "\<lbrakk> R \<rbrakk>\<^sub>N = 1"
    by (smt One_nat_def add_diff_cancel_left' bool2nat.elims le_numeral_extra(4) mult_minus_left of_nat_diff of_nat_less_0_iff plus_1_eq_Suc zero_le_power)
  then have 5: "R = \<top>" using bool2nat.elims by auto
  
  from 3(2) 4 have "int ((\<lbrakk>\<sigma>\<^sub>r\<rbrakk>\<^sub>N) * (2 ^ k) + \<lbrakk> r\<^sup>k\<^sup>-\<^sup>1 \<rbrakk>) \<le> (2 ^ k) - 1" by simp
  with 4 5 have "\<lbrakk>\<sigma>\<^sub>r\<rbrakk>\<^sub>N = 0"
    by (smt bool2nat.simps(2) int_nat_eq mult.left_neutral nat_2 numeral_2_eq_2 of_nat_add of_nat_power_eq_of_nat_cancel_iff seval.simps(2) seval_lower_bound top_unfold)
  then have 6: "\<sigma>\<^sub>r = \<bottom>" using bool2nat.elims by auto
  
  with 5 have "\<top> = a \<and> \<top> = b \<and> \<bottom> = hd ((a#as) +\<^sub>A (b#bs))"
    by (smt DAplus.simps(4) R_def add.right_neutral add_self_mod_2 bool2nat.simps(1) bool2nat.simps(2) bot_unfold fst_conv lem_2_1 list.sel(1) mult_2 nat.simps(3) one_div_two_eq_zero plus_1_eq_Suc sig_r_def snd_conv top_unfold tplus_def)
  
  then show ?case unfolding triple'_def triple_def by auto
qed


lemma thm_3_4_cs2_3_impl_1:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         triple' \<top> \<top> \<bottom> \<Longrightarrow> (\<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> = \<lparr>\<top>#((a#as) +\<^sub>A (b#bs))\<rparr> \<and> hd ((a#as) +\<^sub>A (b#bs)) = \<bottom>)"
  apply(subst thm_3_1_3)

   using assms apply simp
  unfolding splus.simps tplus_def seval.simps DAplus.simps prod.sel triple'_def triple_def list.sel(1)
  by (smt One_nat_def add_numeral_left add_self_div_2 bot_unfold mod_add_self1 nat2bool.simps(2) not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2 numeral_One one_mod_two_eq_one plus_1_eq_Suc semiring_norm(2) to_from_mod_id2 top_unfold)


lemma thm_3_4_cs2_2_impl_1:
fixes k :: nat
assumes "length a = Suc k"
shows "length a = length b \<Longrightarrow> 
       - (2 ^ (Suc k)) \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> - (2 ^ k) - 1 \<Longrightarrow> (\<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>\<top>#(a +\<^sub>A b)\<rparr> \<and> hd (a +\<^sub>A b) = \<bottom>)"
  using assms
  apply (cases a; cases b)
     apply (simp, simp, simp) 
proof goal_cases
case (1 a list aa lista)
  show ?case unfolding 1
    apply(rule thm_3_4_cs2_3_impl_1)
      using 1 apply (simp, simp)
    apply(rule thm_3_4_cs2_2_impl_3)
    using 1 by simp+
qed


lemma thm_3_4_cs2_2_impl_1':
fixes k :: nat
assumes "length a = Suc k"
shows "length a = length b \<Longrightarrow> 
       - (2 ^ (Suc k)) \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> - (2 ^ k) - 1 \<Longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>\<top>#(a +\<^sub>A b)\<rparr>"
  using thm_3_4_cs2_2_impl_1 assms by blast



(* Theorem 3.4 Condition Set 3 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 1 \<longrightarrow> 2 : done *)
(* 2 \<longrightarrow> 3 : done *)
(* 3 \<longrightarrow> 1 : done *)

lemma thm_3_4_cs3_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) +\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) +\<^sub>A (bk # bs))"
  shows "-(\<lbrakk>ak\<rbrakk>\<^sub>Z) - \<lbrakk>bk\<rbrakk>\<^sub>Z + \<lbrakk>rk\<rbrakk>\<^sub>Z = 1  \<longleftrightarrow> triple' \<bottom> \<bottom> \<top>"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+



lemma thm_3_4_cs3_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>+ (a#as) (b#bs)) = \<bottom> \<and> snd (DA\<^sup>+ as bs) = \<top> \<longleftrightarrow> triple' \<bottom> \<bottom> \<top>"
  apply rule
  unfolding triple'_def triple_def tplus_def
  by (cases a;cases b; cases "snd (DA\<^sup>+ as bs)", simp_all)+


lemma thm_3_4_cs3_1_impl_2:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         (\<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>\<bottom>#(a +\<^sub>A b)\<rparr> \<and> hd (a +\<^sub>A b) = \<top>) \<Longrightarrow> 2 ^ k \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> 2 ^ (Suc k) - 2"
  apply rule+
proof goal_cases
case 1
  then have 2: "\<lparr>a\<rparr> + \<lparr>b\<rparr> = int \<lbrakk> a +\<^sub>A b \<rbrakk>" unfolding seval.simps using DAplus_eq_len assms tplus_def by simp

  show ?case
    apply(subst 2)
    apply simp
    apply (cases "a +\<^sub>A b")
     using 1 DAplus_eq_len assms tplus_def apply force
    apply simp
    by (metis (mono_tags, lifting) 1 DAplus_eq_len add_diff_cancel_left' assms bool2nat.simps(1) length_Cons linorder_not_less list.sel(1) mult.left_neutral not_add_less1 plus_1_eq_Suc top_unfold tplus_def)
next
case 2
  then have 1: "\<lparr>a\<rparr> + \<lparr>b\<rparr> = int \<lbrakk> a +\<^sub>A b \<rbrakk>" unfolding seval.simps using DAplus_eq_len assms tplus_def by auto
  
  show ?case unfolding 1
    apply simp
    using assms 2 apply (cases "a +\<^sub>A b") 
     apply simp_all
    by (smt Suc_length_conv bool2nat.simps(1) comm_semiring_class.distrib int_ops(2) semiring_normalization_rules(2) seval_upper_bound)
qed


lemma thm_3_4_cs3_2_impl_3:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         2 ^ k \<le> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> \<le> 2 ^ (Suc k) - 2 \<Longrightarrow> triple' \<bottom> \<bottom> \<top>"
proof goal_cases
case 1
  have "\<bottom> = a" "\<bottom> = b" "\<top> = hd ((a#as) +\<^sub>A (b#bs))" 
      apply (smt 1 assms(1) bool2nat.simps(1) bot_unfold eval_eq_seval int_nat_eq mult.left_neutral nat_2 numeral_2_eq_2 of_nat_power seval.simps(2) seval_upper_bound)
     apply (smt "1"(2) assms(1) bool2nat.simps(1) bot_unfold eval_eq_seval int_nat_eq mult.left_neutral nat_2 numeral_2_eq_2 of_nat_power_eq_of_nat_cancel_iff seval.simps(2) seval_upper_bound)
    by (smt 1 DAplus_eq_len assms(1) bot_unfold lemma_1_2 length_Cons length_greater_0_conv list.sel(1) plus_DA seval_upper_bound sigma_def thm_3_3_3_iff_5 thm_3_4_4_impl_1 thm_3_4_cs2_3_iff_5 thm_3_4_cs2_4_iff_3 top_unfold tplus_def)
  
  then show ?case unfolding triple'_def triple_def by auto
qed


lemma thm_3_4_cs3_3_impl_1:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) +\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         triple' \<bottom> \<bottom> \<top> \<Longrightarrow> (\<lparr>a#as\<rparr> + \<lparr>b#bs\<rparr> = \<lparr>\<bottom>#((a#as) +\<^sub>A (b#bs))\<rparr> \<and> hd ((a#as) +\<^sub>A (b#bs)) = \<top>)"
  apply(subst thm_3_1_3)
   using assms apply simp
  unfolding splus.simps tplus_def seval.simps DAplus.simps prod.sel triple'_def triple_def list.sel(1)
  by (smt add_cancel_right_left bool2nat.simps(1) bool2nat.simps(2) bot_unfold nat2bool.simps(1) one_div_two_eq_zero to_from_mod_id' top_unfold)
 


lemma thm_3_4_cs3_2_impl_1:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         2 ^ k \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> 2 ^ (Suc k) - 2 \<Longrightarrow> (\<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>\<bottom>#(a +\<^sub>A b)\<rparr> \<and> hd (a +\<^sub>A b) = \<top>)"
  using assms
  apply (cases a; cases b)
   apply (simp, simp, simp)
proof goal_cases
case (1 a list aa lista)
  show ?case unfolding 1
    apply(rule thm_3_4_cs3_3_impl_1)
      using 1 apply (simp, simp)
    apply(rule thm_3_4_cs3_2_impl_3)
    using 1 by simp+
qed


lemma thm_3_4_cs3_2_impl_1':
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         2 ^ k \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> 2 ^ (Suc k) - 2 \<Longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>\<bottom>#(a +\<^sub>A b)\<rparr>"
  using thm_3_4_cs3_2_impl_1 assms by blast



(* Theorem 3.5 *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 2 \<longrightarrow> 4 : done *)
(* 4 \<longrightarrow> 1 : done *)
(* 1 \<longrightarrow> 2 : done *)


lemma thm_3_5_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)" 
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) -\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) -\<^sub>A (bk # bs))"
  shows "\<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 0 \<or> \<lbrakk>ak\<rbrakk>\<^sub>Z - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -1  \<longleftrightarrow> 
         (triple' \<top> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<top>  \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<bottom> \<or> triple' \<top> \<top> \<top>)"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+


lemma thm_3_5_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) = snd (DA\<^sup>- as bs) \<longleftrightarrow> 
         (triple' \<top> \<bottom> \<top> \<or> triple' \<bottom> \<top> \<bottom> \<or> triple' \<bottom> \<bottom> \<top>  \<or> triple' \<bottom> \<bottom> \<bottom> \<or> triple' \<top> \<top> \<bottom> \<or> triple' \<top> \<top> \<top>)"
  apply rule
  unfolding triple'_def triple_def tminus_def
  by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)+




lemma thm_3_5_2_impl_4 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "(- (2 ^ k) \<le> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<le> 2 ^ k - 1) \<Longrightarrow> 
         snd (DA\<^sup>- (a#as) (b#bs)) = snd (DA\<^sup>- as bs)"
proof goal_cases
case 1
  then have "- (2 ^ k) \<le> \<lparr> (a # as) -\<^sub>S\<^sub>A (b # bs) \<rparr> \<and> \<lparr> (a # as) -\<^sub>S\<^sub>A (b # bs) \<rparr> \<le> 2 ^ k - 1"
    apply rule
    apply rule
     apply(subst thm_3_1_4[symmetric])
      using assms apply simp
     apply simp
    apply(subst thm_3_1_4[symmetric])
     using assms apply simp
    by simp

  then have "(\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>- (a # as) (b # bs)) \<rbrakk>\<^sub>N) mod 2 = (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>- as bs) \<rbrakk>\<^sub>N) mod 2"
    apply(cases a; cases b; cases "snd (DA\<^sup>- (a # as) (b # bs))"; cases "snd (DA\<^sup>- as bs)", simp_all)
  proof goal_cases
  case 1
    then have 2: "2 ^ k \<le> \<lbrakk> fst (DA\<^sup>- as bs) \<rbrakk>"
      apply (subst(2) nat_int[symmetric])
      apply(subst nat_le_iff)
      using DAminus_eq_len assms by simp
    
    have "\<lbrakk> fst (DA\<^sup>- as bs) \<rbrakk> \<le> 2 ^ k - 1" using ueval_upper_bound DAminus_eq_len assms by metis
    then have "\<lbrakk> fst (DA\<^sup>- as bs) \<rbrakk> < 2 ^ k"  using DAminus_eq_len assms ueval_upper_bound3 by metis
    
    with 2 show ?case by simp
  next
  case 2
    then have 1: "int \<lbrakk> fst (DA\<^sup>- as bs) \<rbrakk> < 0" using DAminus_eq_len assms by simp
  
    then show ?case by simp
  qed

  then show ?case by (cases a; cases b; cases "snd (DA\<^sup>- (a # as) (b # bs))"; cases "snd (DA\<^sup>- as bs)", simp_all)
qed



lemma thm_3_5_4_impl_1 : 
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "k \<equiv> length as"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) = snd (DA\<^sup>- as bs) \<Longrightarrow> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> = \<lparr>(a#as) -\<^sub>A (b#bs)\<rparr>"
  apply(subst thm_3_1_4)
   using assms apply simp
  unfolding sminus.simps tminus_def seval.simps DAminus.simps prod.sel by simp


lemma thm_3_5_1_impl_2:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
  \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>A b\<rparr> \<Longrightarrow> (- (2 ^ k) \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> 2 ^ k - 1)"
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
  show ?case unfolding 2 using assms
    apply (cases a ; cases b)
       using 2 apply simp_all
    unfolding tminus_def DAminus.simps prod.sel seval.simps
    apply (subst DAminus_eq_len, simp)
    apply (case_tac aa ; case_tac aaa ; case_tac "snd (DA\<^sup>- list lista)")
           apply simp_all
           apply (metis DAminus_eq_len ueval_upper_bound3)
          apply (smt DAminus_eq_len eval_eq_seval of_nat_less_0_iff seval_upper_bound)
         apply (smt DAminus_eq_len eval_eq_seval seval_lower_bound seval_upper_bound)
        apply (metis DAminus_eq_len ueval_upper_bound3)
       apply (smt eval_eq_seval of_nat_less_0_iff seval_upper_bound)
      apply (metis DAminus_eq_len ueval_upper_bound3)
     apply (metis DAminus_eq_len ueval_upper_bound3)
    by (smt DAminus_eq_len eval_eq_seval of_nat_less_0_iff seval_upper_bound)
qed


lemma thm_3_5_2_impl_1:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
  - (2 ^ k) \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> 2 ^ k - 1 \<Longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>A b\<rparr>"
  using assms
  apply (cases a; cases b)
     apply (simp, simp, simp)
proof goal_cases
case (1 a list aa lista)
  show ?case unfolding 1
    apply(rule thm_3_5_4_impl_1)
     using 1 apply simp
    apply(rule thm_3_5_2_impl_4)
    using 1 by simp+
qed



(* Theorem 3.5 Condition Set 2 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 1 \<longrightarrow> 2 : done *)
(* 2 \<longrightarrow> 3 : done *)
(* 3 \<longrightarrow> 1 : done *)

lemma thm_3_5_cs2_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) -\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) -\<^sub>A (bk # bs))"
  shows "(\<lbrakk>ak\<rbrakk>\<^sub>Z) - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = 1  \<longleftrightarrow> triple' \<top> \<bottom> \<bottom>"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+



lemma thm_3_5_cs2_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "(snd (DA\<^sup>- (a#as) (b#bs)) = \<top> \<and> snd (DA\<^sup>- as bs) = \<bottom>) \<longleftrightarrow> triple' \<top> \<bottom> \<bottom>"
  apply rule
  unfolding triple'_def triple_def tminus_def
  by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)+


lemma thm_3_5_cs2_1_impl_2:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         (\<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<top>#(a -\<^sub>A b)\<rparr> \<and> hd (a -\<^sub>A b) = \<bottom>) \<Longrightarrow> - (2 ^ (Suc k)) \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> - (2 ^ k) - 1"
  apply rule+
proof goal_cases
case 1
  then have "\<lparr>a\<rparr> - \<lparr>b\<rparr> = - int (2 ^ (Suc k)) + int \<lbrakk> a -\<^sub>A b \<rbrakk>" unfolding seval.simps
    using DAminus_eq_len assms tminus_def by auto
  
  then show ?case by simp
next
case 2
  then have 1: "\<lparr>a\<rparr> - \<lparr>b\<rparr> = - int (2 ^ (Suc k)) + int \<lbrakk> a -\<^sub>A b \<rbrakk>" unfolding seval.simps
    using DAminus_eq_len assms tminus_def by auto
  
  show ?case unfolding 1
    apply simp
    apply (cases "a -\<^sub>A b") 
     using assms 2 apply simp_all
    using ueval_upper_bound3
    by (metis DAminus_eq_len add_diff_cancel_left' length_Cons plus_1_eq_Suc tminus_def)
qed


lemma thm_3_5_cs2_2_impl_3:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         - (2 ^ (Suc k)) + 1 \<le> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<le> - (2 ^ k) - 1 \<Longrightarrow> triple' \<top> \<bottom> \<bottom>"
proof goal_cases
case 1
  have 2: "- (2 ^ (Suc k)) \<le> \<lparr> (a#as) -\<^sub>S\<^sub>A (b#bs) \<rparr> \<and> \<lparr> (a#as) -\<^sub>S\<^sub>A (b#bs) \<rparr> \<le> - (2 ^ k) - 1"
    apply rule
     apply(subst thm_3_1_4[symmetric])
      using 1 apply (simp,simp)
    apply(subst thm_3_1_4[symmetric])
    using 1 by simp_all
  
  define sig_r ("\<sigma>\<^sub>r") where "\<sigma>\<^sub>r \<equiv> \<lbrakk> (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> \<not> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>- as bs) \<rbrakk>\<^sub>N) mod 2 \<rbrakk>\<^sub>B"
  define r_k_minus_one ("r\<^sup>k\<^sup>-\<^sup>1") where "r\<^sup>k\<^sup>-\<^sup>1 \<equiv> fst (DA\<^sup>- as bs)"
  define R  where "R \<equiv> \<lbrakk> (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> \<not> b \<rbrakk>\<^sub>N + \<lbrakk> snd (\<sigma>\<^sub>r # r\<^sup>k\<^sup>-\<^sup>1, \<lbrakk> (\<lbrakk> a \<rbrakk>\<^sub>N + \<lbrakk> \<not> b \<rbrakk>\<^sub>N + \<lbrakk> snd (DA\<^sup>- as bs) \<rbrakk>\<^sub>N) div 2 \<rbrakk>\<^sub>B) \<rbrakk>\<^sub>N) mod 2 \<rbrakk>\<^sub>B"
  
  from 2 have 3: 
    "- (2 ^ (Suc k)) \<le> - int (\<lbrakk> R \<rbrakk>\<^sub>N) * (2 ^ (Suc k)) + int ((\<lbrakk>\<sigma>\<^sub>r\<rbrakk>\<^sub>N) * (2 ^ k) + \<lbrakk> r\<^sup>k\<^sup>-\<^sup>1 \<rbrakk>)"
    "- int (\<lbrakk> R \<rbrakk>\<^sub>N) * (2 ^ (Suc k)) + int ((\<lbrakk>\<sigma>\<^sub>r\<rbrakk>\<^sub>N) * (2 ^ k) + \<lbrakk> r\<^sup>k\<^sup>-\<^sup>1 \<rbrakk>) \<le> - (2 ^ k) - 1"
    unfolding sminus.simps list.sel(1) DAminus.simps fst_conv sig_r_def
              r_k_minus_one_def R_def seval.simps ueval.simps
    using DAminus_eq_len assms(1) 1(1) by simp_all
  
  from 3(2) have 4: "\<lbrakk> R \<rbrakk>\<^sub>N = 1"
    by (smt One_nat_def add_diff_cancel_left' bool2nat.elims le_numeral_extra(4) mult_minus_left of_nat_diff of_nat_less_0_iff plus_1_eq_Suc zero_le_power)
  then have 5: "R = \<top>" using bool2nat.elims by auto
  
  from 3(2) 4 have "int ((\<lbrakk>\<sigma>\<^sub>r\<rbrakk>\<^sub>N) * (2 ^ k) + \<lbrakk> r\<^sup>k\<^sup>-\<^sup>1 \<rbrakk>) \<le> (2 ^ k) - 1" by simp
  with 4 5 have "\<lbrakk>\<sigma>\<^sub>r\<rbrakk>\<^sub>N = 0"
    by (smt bool2nat.simps(2) int_nat_eq mult.left_neutral nat_2 numeral_2_eq_2 of_nat_add of_nat_power_eq_of_nat_cancel_iff seval.simps(2) seval_lower_bound top_unfold)
  then have 6: "\<sigma>\<^sub>r = \<bottom>" using bool2nat.elims by auto
  
  with 5 have "\<top> = a" "\<bottom> = b" "\<bottom> = hd ((a#as) -\<^sub>A (b#bs))"
    unfolding tminus_def R_def sig_r_def r_k_minus_one_def
      apply (smt "1"(1) "1"(2) assms(1) eval_eq_seval of_nat_less_0_iff seval_upper_bound top_unfold)
     apply (smt "1"(2) One_nat_def add.commute add_0_left assms(1) bool2nat.simps(1) bot_unfold mult_is_0 nat_int_comparison(2) plus_1_eq_Suc semiring_normalization_rules(2) seval.simps(2) seval_lower_bound ueval_upper_bound3)
    using "6" sig_r_def by auto
  
  then show ?case unfolding triple'_def triple_def by auto
qed


lemma thm_3_5_cs2_3_impl_1:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         triple' \<top> \<bottom> \<bottom> \<Longrightarrow> (\<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> = \<lparr>\<top>#((a#as) -\<^sub>A (b#bs))\<rparr> \<and> hd ((a#as) -\<^sub>A (b#bs)) = \<bottom>)"
  apply(subst thm_3_1_4)
   using assms apply simp
  unfolding sminus.simps tminus_def seval.simps DAminus.simps prod.sel triple'_def triple_def list.sel(1)
  by (smt One_nat_def add_numeral_left add_self_div_2 bot_unfold mod_add_self1 nat2bool.simps(2) not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2 numeral_One one_mod_two_eq_one plus_1_eq_Suc semiring_norm(2) to_from_mod_id2 top_unfold)
 


lemma thm_3_5_cs2_2_impl_1:
fixes k :: nat
assumes "length a = Suc k"
shows "length a = length b \<Longrightarrow> 
       - (2 ^ (Suc k)) + 1 \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> - (2 ^ k) - 1 \<Longrightarrow> (\<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<top>#(a -\<^sub>A b)\<rparr> \<and> hd (a -\<^sub>A b) = \<bottom>)"
  using assms
  apply (cases a; cases b)
     apply (simp, simp, simp)
proof goal_cases
case (1 a list aa lista)
  show ?case unfolding 1
    apply(rule thm_3_5_cs2_3_impl_1)
      using 1 apply (simp, simp)
    apply(rule thm_3_5_cs2_2_impl_3)
    using 1 by simp+
qed


lemma thm_3_5_cs2_2_impl_1':
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         - (2 ^ (Suc k)) + 1 \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> - (2 ^ k) - 1 \<Longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<top>#(a -\<^sub>A b)\<rparr>"
  using thm_3_5_cs2_2_impl_1 assms by blast



(* Theorem 3.5 Condition Set 3 *)
(* 3 \<longleftrightarrow> 5 : done *)
(* 4 \<longleftrightarrow> 3 : done *)
(* 1 \<longrightarrow> 2 : done *)
(* 2 \<longrightarrow> 3 : done *)
(* 3 \<longrightarrow> 1 : done *)

lemma thm_3_5_cs3_3_iff_5 :
  fixes ak bk :: bool and as bs :: "bool list"
  assumes "length (ak # as) = length (bk # bs)"
  defines "triple' x y z \<equiv> triple x y z (ak # as) (bk # bs) ((ak # as) -\<^sub>A (bk # bs))" and
          "rk \<equiv> hd ((ak # as) -\<^sub>A (bk # bs))"
  shows "(\<lbrakk>ak\<rbrakk>\<^sub>Z) - \<lbrakk>bk\<rbrakk>\<^sub>Z - \<lbrakk>rk\<rbrakk>\<^sub>Z = -2  \<longleftrightarrow> triple' \<bottom> \<top> \<top>"
  apply rule
  unfolding triple'_def triple_def rk_def[symmetric] list.sel(1)
  by(cases ak; cases bk; cases rk, simp_all)+



lemma thm_3_5_cs3_4_iff_3 :
  fixes a b :: "bool" and as bs :: "bool list"
  assumes "length as = length bs"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "snd (DA\<^sup>- (a#as) (b#bs)) = \<bottom> \<and> snd (DA\<^sup>- as bs) = \<top> \<longleftrightarrow> triple' \<bottom> \<top> \<top>"
  apply rule
  unfolding triple'_def triple_def tminus_def
  by (cases a;cases b; cases "snd (DA\<^sup>- as bs)", simp_all)+



lemma thm_3_5_cs3_1_impl_2:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         (\<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<bottom>#(a -\<^sub>A b)\<rparr> \<and> hd (a -\<^sub>A b) = \<top>) \<Longrightarrow> 2 ^ k \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> 2 ^ (Suc k) - 1"
  apply rule+
proof goal_cases
case 1
  then have 2: "\<lparr>a\<rparr> - \<lparr>b\<rparr> = int \<lbrakk> a -\<^sub>A b \<rbrakk>" unfolding seval.simps
    using DAminus_eq_len assms tplus_def by simp
  
  show ?case
    apply(subst 2)
    apply simp
    apply (cases "a -\<^sub>A b")
     using 1 DAminus_eq_len assms tminus_def apply force
    apply simp
    by (metis (mono_tags, lifting) "1"(1) "1"(2) DAminus_eq_len add.right_neutral add_diff_cancel_left' assms bool2nat.simps(1) length_Cons linorder_not_less list.sel(1) mult_Suc mult_is_0 not_add_less1 plus_1_eq_Suc tminus_def top_unfold)
next
case 2
  then have 1: "\<lparr>a\<rparr> - \<lparr>b\<rparr> = int \<lbrakk> a -\<^sub>A b \<rbrakk>" unfolding seval.simps  by auto
  
  show ?case unfolding 1
    apply simp
    apply (cases "a -\<^sub>A b") 
     using assms 2 apply simp_all
    by (smt "2"(2) DAminus_eq_len bool2nat.simps(1) comm_semiring_class.distrib of_nat_1 power_Suc push_bit_eq_mult push_bit_of_1 seval_upper_bound tminus_def)
qed


lemma thm_3_5_cs3_2_impl_3:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         2 ^ k \<le> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<and> \<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> \<le> 2 ^ (Suc k) - 1 \<Longrightarrow> triple' \<bottom> \<top> \<top>"
proof goal_cases
case 1
  have "\<bottom> = a" "\<top> = b" "\<top> = hd ((a#as) -\<^sub>A (b#bs))" 
      apply (smt "1"(1) "1"(2) assms(1) bot_unfold lemma_1_2 length_greater_0_conv list.discI list.sel(1) seval_lower_bound sigma_def)
     apply (smt "1"(2) assms(1) eval_eq_seval of_nat_less_0_iff seval_upper_bound top_unfold)
    by (smt "1"(1) "1"(2) One_nat_def Suc_1 assms(1) bool2nat.simps(1) bot_unfold int_nat_eq less_imp_of_nat_less list.sel(1) mult.left_neutral nat_2 nat_power_eq of_nat_add of_nat_less_0_iff seval.simps(2) seval_lower_bound thm_3_3_2_impl_4 thm_3_3_4_iff_3 triple_def ueval.simps(2) ueval_upper_bound3)
  
  then show ?case unfolding triple'_def triple_def by auto
qed


lemma thm_3_5_cs3_3_impl_1:
  fixes k :: nat and a b :: bool and as bs :: "bool list"
  assumes "length as = k"
  defines "triple' x y z \<equiv> triple x y z (a#as) (b#bs) ((a#as) -\<^sub>A (b#bs))"
  shows "length as = length bs \<Longrightarrow> 
         triple' \<bottom> \<top> \<top> \<Longrightarrow> (\<lparr>a#as\<rparr> - \<lparr>b#bs\<rparr> = \<lparr>\<bottom>#((a#as) -\<^sub>A (b#bs))\<rparr> \<and> hd ((a#as) -\<^sub>A (b#bs)) = \<top>)"
  apply(subst thm_3_1_4)
   using assms apply simp
  unfolding sminus.simps tminus_def seval.simps DAminus.simps prod.sel triple'_def triple_def list.sel(1)
  by (smt add_cancel_right_left bool2nat.simps(1) bool2nat.simps(2) bot_unfold nat2bool.simps(1) one_div_two_eq_zero to_from_mod_id' top_unfold) 


lemma thm_3_5_cs3_2_impl_1:
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         2 ^ k \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> 2 ^ (Suc k) - 1 \<Longrightarrow> (\<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<bottom>#(a -\<^sub>A b)\<rparr> \<and> hd (a -\<^sub>A b) = \<top>)"
  using assms
  apply (cases a; cases b)
     apply (simp, simp, simp)
proof goal_cases
case (1 a list aa lista)
  show ?case unfolding 1
    apply (rule thm_3_5_cs3_3_impl_1)
      using 1 apply (simp, simp)
    apply (rule thm_3_5_cs3_2_impl_3)
    using 1 by simp+
qed


lemma thm_3_5_cs3_2_impl_1':
  fixes k :: nat
  assumes "length a = Suc k"
  shows "length a = length b \<Longrightarrow> 
         2 ^ k \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<and> \<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> 2 ^ (Suc k) - 1 \<Longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<bottom>#(a -\<^sub>A b)\<rparr>"
  using thm_3_5_cs3_2_impl_1 assms by blast


(* Theorem 3.6 *)


lemma thm_3_6_1_aux: "\<lbrakk> a \<rbrakk> + \<lbrakk> compl a \<rbrakk> = 2 ^ length a - 1" 
  by(induct a, simp, case_tac a1, simp+)

lemma thm_3_6_1_aux1a: "(int (a + b) + 1 = 2 ^ c) = (a + b + 1 = 2 ^ c)"
  by (metis int_ops(2) int_ops(5) real_of_nat_eq_numeral_power_cancel_iff)

lemma thm_3_6_1_aux1b: "(int a + (int b - 2 ^ c) = - 1) = (a + b + 1 = 2 ^ c)"
  using thm_3_6_1_aux1a by force

lemma thm_3_6_1_aux1c: "(int a - 2 ^ c + int b = - 1) = (a + b + 1 = 2 ^ c)"
  using thm_3_6_1_aux1a by force

lemma thm_3_6_1_aux2:
  fixes k :: nat
  assumes "length a = Suc (Suc k)"
  shows "\<lparr> compl a \<rparr> + \<lparr> a \<rparr> = -1"
  apply (cases a)
   using assms apply simp
  apply (case_tac aa)
   apply simp_all
   apply (subst thm_3_6_1_aux1b)
   using thm_3_6_1_aux apply (simp add: add.commute)
  apply (subst thm_3_6_1_aux1c)
  using thm_3_6_1_aux by (simp add: add.commute)

lemma thm_3_6_1: 
  fixes k :: nat
  assumes "length a = Suc (Suc k)"
  shows "-\<lparr>a\<rparr> = \<lparr>\<not>\<^sub>S\<^sub>A a\<rparr>"
  unfolding sneg_def
  apply (subst thm_3_1_3[symmetric])
  apply (rule length_comp_one)
  apply (subst one_seval)
   using assms apply simp
  using thm_3_6_1_aux2 assms by fastforce



lemma thm_3_6_2_aux: 
  fixes k :: nat
  assumes "length a = Suc k"
  shows "\<lparr> a \<rparr> = \<lparr> hd a # a \<rparr>"
  apply(cases a)
  using assms by simp_all

lemma thm_3_6_2: 
  fixes k :: nat
  assumes "length a = Suc (Suc k)"
  shows "length a = length b \<Longrightarrow> \<lparr>a -\<^sub>S\<^sub>A b\<rparr> = \<lparr>(hd a#a) +\<^sub>S\<^sub>A \<not>\<^sub>S\<^sub>A b\<rparr>"
  apply(subst thm_3_1_3[symmetric])
   apply simp
   apply(rule length_sneg[where k = "Suc k"])
   apply (simp add: assms length_sneg)
  apply(subst thm_3_1_4[symmetric], simp)
  apply(subst thm_3_6_1[symmetric, where k = k])
   apply (simp add: assms)
  using thm_3_6_2_aux assms by fastforce


lemma thm_3_6_3:
  fixes k :: nat
  assumes "length a = Suc (Suc k)"
  shows "length a = length b \<Longrightarrow> hd (a -\<^sub>S\<^sub>A b) # a -\<^sub>S\<^sub>A b = ((hd a#a) +\<^sub>S\<^sub>A \<not>\<^sub>S\<^sub>A b)"
  apply (rule lemma_1_4_2)
    apply (simp add:assms)
   apply simp
   apply (subst DAplus_eq_len)
    apply simp
    using length_sneg assms apply metis
   using length_sminus length_sneg assms apply presburger
  by (metis assms length_sminus thm_3_6_2 thm_3_6_2_aux)




lemma thm_3_6_4_aux: "length a = Suc k \<Longrightarrow> length a = length b \<Longrightarrow>
- (2 ^ k) \<le> \<lparr> a \<rparr> + \<lparr> b \<rparr> \<and> \<lparr> a \<rparr> + \<lparr> b \<rparr> \<le> 2 ^ k - 1 \<Longrightarrow> 
\<lparr> a \<rparr> + \<lparr> b \<rparr> = \<lparr> a +\<^sub>A b \<rparr>" 
  using thm_3_4_1_iff_2 by simp

lemma thm_3_6_4: 
  fixes k :: nat
  assumes "length a = Suc (Suc k)"
  shows "a \<noteq> True # \<zero>\<^sup>\<rightarrow> (Suc k) \<Longrightarrow> -\<lparr>a\<rparr> = \<lparr>\<not>\<^sub>A a\<rparr>"
  unfolding neg_def
  apply (subst thm_3_6_4_aux[symmetric, where k = "Suc k"])
     apply (simp add:assms)
    using length_comp_one apply simp
   defer
   apply(subst one_seval)
    using assms apply simp
   using thm_3_6_1_aux2 assms apply fastforce
proof goal_cases
case 1
  note top = 1
  have a: "\<And>list. - (2 * 2 ^ k) - 1 \<le> int \<lbrakk> compl list \<rbrakk>" 
  proof -
    fix list :: "bool list"
    have "- 1 + - int (Suc 1 * Suc 1 ^ k) \<le> int \<lbrakk> compl list \<rbrakk>" by linarith
    
    then show "- (2 * 2 ^ k) - 1 \<le> int \<lbrakk> compl list \<rbrakk>" by simp
  qed

  have b: "\<And> list. int \<lbrakk> compl list \<rbrakk> - 2 ^ length list \<le> 2 * 2 ^ k - 2"
  proof -
    fix aa :: bool and list :: "bool list"
    have f1: "\<lbrakk> compl list \<rbrakk> < nat 2 ^ length list"
      unfolding compl_def
      by (metis (no_types) length_map nat_2 numeral_2_eq_2 ueval_upper_bound3)
    have f2: "(1::int) \<le> 2 ^ k" by simp
    have "nat (2 ^ length list) = nat 2 ^ length list" by auto
    
    then show "int \<lbrakk> compl list \<rbrakk> - 2 ^ length list \<le> 2 * 2 ^ k - 2" using f2 f1 by linarith
  qed

  have "- (2 ^ Suc k) - 1 \<le> \<lparr> compl a \<rparr>"
  "\<lparr> compl a \<rparr> \<le> 2 ^ Suc k - 2"
     apply(cases a)
      using assms apply auto[1]
     apply simp
     apply(case_tac aa)
      apply simp
      using a apply simp
     using assms apply auto[1]
    apply(cases a)
    using assms 
     apply simp
    apply (case_tac aa, simp_all)
     defer
     using b apply simp
    apply (case_tac "int \<lbrakk> compl list \<rbrakk> < 2 * 2 ^ k - 1")
     apply simp_all
  proof goal_cases
  case (1 _ list)
    then have "int \<lbrakk> compl list \<rbrakk> \<ge> 2 * 2 ^ k - 1" by simp
    then have a: "\<lbrakk> compl list \<rbrakk> \<ge> 2 * 2 ^ k - 1" 
    proof -
      have "int (2 * 2 ^ k - 1) \<le> int \<lbrakk> compl list \<rbrakk>"
        by (metis (no_types) \<open>2 * 2 ^ k - 1 \<le> int \<lbrakk> compl list \<rbrakk>\<close> of_nat_1 of_nat_diff one_le_numeral one_le_power push_bit_of_1 push_bit_of_nat semiring_normalization_rules(27))
      
      then show ?thesis by simp
    qed

    have b: "\<And>l. \<lbrakk> \<one>\<^sup>\<rightarrow> l \<rbrakk> = 2 ^ l - 1" 
      apply(induct_tac l)
       apply simp
      unfolding ueval.simps by auto
    
    have c: "\<And>l. compl (\<one>\<^sup>\<rightarrow> l) = \<zero>\<^sup>\<rightarrow> l" by(induct_tac l, simp_all)
    have d: "\<And>l. compl (compl l) = l" by(induct_tac l, simp_all)

    have "\<lbrakk> compl list \<rbrakk> \<le> 2 * 2 ^ k - 1" using ueval_upper_bound
      by (metis "1"(1) One_nat_def Suc_inject a add_diff_cancel_left' add_diff_cancel_right' assms diff_Suc_eq_diff_pred diff_is_0_eq length_Cons semiring_normalization_rules(27) thm_3_6_1_aux)

    with a have "\<lbrakk> compl list \<rbrakk> = 2 * 2 ^ k - 1" by simp
    then have e: "\<lbrakk> compl list \<rbrakk> = 2 ^ (Suc k) - 1" by simp

    have "compl list = \<one>\<^sup>\<rightarrow> (Suc k)"
      apply(rule lemma_1_4_1[where k = k])
        using "1"(1) assms apply auto[2]
      using b e by metis

    then have "list = \<zero>\<^sup>\<rightarrow> (Suc k)" using c d by metis
    
    with top 1(1) show False by simp
  qed

  then show ?case by (simp add: assms one_seval)
qed


lemma thm_3_6_6_aux1a: "length list = k \<Longrightarrow> snd (DA\<^sup>- list (\<zero>\<^sup>\<rightarrow> k)) = True"
  apply (induct list arbitrary: k)
   apply simp
  by (case_tac k, simp_all, case_tac a, simp_all)


lemma thm_3_6_6_aux1b: "length list = k \<Longrightarrow> snd (DA\<^sup>+ list (\<zero>\<^sup>\<rightarrow> k)) = False"
  apply (induct list arbitrary: k)
   apply simp
  by (case_tac k, simp_all, case_tac a, simp_all)


lemma thm_3_6_6_aux1c: "length list = k \<Longrightarrow> fst (DA\<^sup>- list (\<zero>\<^sup>\<rightarrow> k)) = list"
  apply (induct list arbitrary: k)
   apply simp
  apply (case_tac k, simp_all)
  apply (fold zero_def)
  apply (subst thm_3_6_6_aux1a)
   apply simp
  by (case_tac a, simp_all)

lemma thm_3_6_6_aux1d: "length list = k \<Longrightarrow> fst (DA\<^sup>+ list (\<zero>\<^sup>\<rightarrow> k)) = list"
  apply (induct list arbitrary: k)
   apply simp
  apply (case_tac k, simp_all)
  apply (fold zero_def)
  apply (subst thm_3_6_6_aux1b)
   apply simp
  by (case_tac a, simp_all)


lemma thm_3_6_6_aux1: 
  fixes k :: nat
  assumes "length a = Suc (Suc k)" and "length a = length b" and "b = True # \<zero>\<^sup>\<rightarrow> (Suc k)"
  shows "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b"
  using assms apply (cases a, simp)
proof goal_cases
case (1 a list)
  have 2: "\<not>\<^sub>A b = b" unfolding assms(3) neg_def compl_def tplus_def
    apply (induct k)
     apply simp_all
    using to_from_mod_id by force
  
  show ?case
    apply (subst 2)
    unfolding 1 tminus_def tplus_def DAminus.simps DAplus.simps fst_conv list.inject
    apply rule
     apply (subst thm_3_6_6_aux1a)
      using 1 apply simp
     apply (subst thm_3_6_6_aux1b)
      using 1 apply simp
     apply simp
    apply (subst thm_3_6_6_aux1c)
     using 1 apply simp
    apply (subst thm_3_6_6_aux1d)
    using 1 by simp_all
qed




lemma thm_3_6_6_aux2a: "length a = Suc k \<Longrightarrow> length a = length b \<Longrightarrow> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>\<top>#(a +\<^sub>A b)\<rparr> \<or> \<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>\<bottom>#(a +\<^sub>A b)\<rparr>" 
  apply (cases "- (2 ^ k) \<le> \<lparr>a\<rparr> + \<lparr>b\<rparr>" ; cases "\<lparr>a\<rparr> + \<lparr>b\<rparr> \<le> 2 ^ k - 1")
proof goal_cases
case 1
  have "\<lparr>a\<rparr> + \<lparr>b\<rparr> = \<lparr>a +\<^sub>A b\<rparr>"
    apply (rule thm_3_4_2_impl_1)
    using 1 by simp+
  
  with 1 show ?case
    apply (cases "a +\<^sub>A b", simp)
    apply (case_tac aa)
    using sx_seval by simp+
next
case 2
  then have 1: "2 ^ k \<le> \<lparr> a \<rparr> + \<lparr> b \<rparr>" by simp
  
  show ?case
    apply (rule disjI2)
    apply (rule thm_3_4_cs3_2_impl_1')
      using 2 apply (simp, simp)
    apply rule
     using 1 apply simp
    by (smt 2 Suc_length_conv comm_semiring_class.distrib power_Suc semiring_normalization_rules(2) seval_upper_bound)
next
case 3
  then have 1: "\<lparr> a \<rparr> + \<lparr> b \<rparr> \<le> - (2 ^ k) - 1" by simp
  
  show ?case
    apply rule
    apply (rule thm_3_4_cs2_2_impl_1')
      using 3 apply (simp, simp)
    apply rule
     apply (smt "3"(1) "3"(2) Suc_length_conv comm_semiring_class.distrib power_Suc semiring_normalization_rules(2) seval_lower_bound)
    using 1 by simp
next
case 4
  then have \<bottom> by (smt one_le_power)
  
  then show ?case by simp
qed

lemma thm_3_6_6_aux2b: "length a = Suc k \<Longrightarrow> length a = length b \<Longrightarrow> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<top>#(a -\<^sub>A b)\<rparr> \<or> \<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<bottom>#(a -\<^sub>A b)\<rparr>"
apply (cases "- (2 ^ k) \<le> \<lparr>a\<rparr> - \<lparr>b\<rparr>" ; cases "\<lparr>a\<rparr> - \<lparr>b\<rparr> \<le> 2 ^ k - 1")
proof goal_cases
case 1
  have "\<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a -\<^sub>A b\<rparr>"
    apply (rule thm_3_5_2_impl_1)
    using 1 by simp+

  with 1 show ?case
    apply (cases "a -\<^sub>A b", simp)
    apply (case_tac aa)
    using sx_seval by simp+
next
case 2
  then have 1: "2 ^ k \<le> \<lparr> a \<rparr> - \<lparr> b \<rparr>" by simp

  show ?case
    apply (rule disjI2)
    apply (rule thm_3_5_cs3_2_impl_1')
      using 2 apply (simp, simp)
    apply rule
     using 1 apply simp
    by (smt "2"(1) "2"(2) Suc_length_conv comm_semiring_class.distrib power_Suc2 power_commutes semiring_normalization_rules(2) seval_lower_bound seval_upper_bound)
next
case 3
  then have 1: "\<lparr> a \<rparr> - \<lparr> b \<rparr> \<le> - (2 ^ k) - 1" by simp
 
  show ?case
    apply rule
    apply (rule thm_3_5_cs2_2_impl_1')
      using 3 apply (simp, simp)
    apply rule
     using 1 apply simp_all
    by (smt "3"(1) "3"(2) Suc_length_conv seval_lower_bound seval_upper_bound)
next
case 4
  then have \<bottom> by (smt one_le_power)

  then show ?case by simp
qed


lemma thm_3_6_6_aux2: 
  fixes k :: nat
  assumes "length a = Suc (Suc k)" and "length a = length b" and "b \<noteq> True # \<zero>\<^sup>\<rightarrow> (Suc k)"
  shows "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b"
proof -
  have 1: "\<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>a\<rparr> + \<lparr>\<not>\<^sub>A b\<rparr>" using assms thm_3_6_4 by simp
  have 2: "length (a -\<^sub>A b) = length (a +\<^sub>A \<not>\<^sub>A b)"
  using DAminus_eq_len DAplus_eq_len assms(2) length_comp_one neg_def tminus_def tplus_def by auto

  { assume 3: "\<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<top>#(a -\<^sub>A b)\<rparr>"
    { assume 4: "\<lparr>a\<rparr> + \<lparr>\<not>\<^sub>A b\<rparr> = \<lparr>\<top>#(a +\<^sub>A \<not>\<^sub>A b)\<rparr>"
      have "\<top>#(a -\<^sub>A b) = \<top>#(a +\<^sub>A \<not>\<^sub>A b)"
        apply (rule lemma_1_4_2)
        using assms 1 2 3 4 by simp+
      then have "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b" by simp }
    { assume 4: "\<lparr>a\<rparr> + \<lparr>\<not>\<^sub>A b\<rparr> = \<lparr>\<bottom>#(a +\<^sub>A \<not>\<^sub>A b)\<rparr>"
      have "\<top>#(a -\<^sub>A b) = \<bottom>#(a +\<^sub>A \<not>\<^sub>A b)" 
        apply (rule lemma_1_4_2)
        using assms 1 2 3 4 by simp+
      then have "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b" by simp }
    then have "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b"
      using 1 assms thm_3_6_6_aux2a \<open>\<lparr> a \<rparr> + \<lparr> \<not>\<^sub>A b \<rparr> = \<lparr> \<top> # a +\<^sub>A \<not>\<^sub>A b \<rparr> \<Longrightarrow> a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b\<close>
      by (metis DAplus_eq_len compl_def length_comp_one length_map neg_def tplus_def) }
  { assume 3: "\<lparr>a\<rparr> - \<lparr>b\<rparr> = \<lparr>\<bottom>#(a -\<^sub>A b)\<rparr>"
    { assume 4: "\<lparr>a\<rparr> + \<lparr>\<not>\<^sub>A b\<rparr> = \<lparr>\<top>#(a +\<^sub>A \<not>\<^sub>A b)\<rparr>"
      have "\<bottom>#(a -\<^sub>A b) = \<top>#(a +\<^sub>A \<not>\<^sub>A b)" 
        apply (rule lemma_1_4_2)
        using assms 1 2 3 4 by simp+
      then have "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b" by simp }
    { assume 4: "\<lparr>a\<rparr> + \<lparr>\<not>\<^sub>A b\<rparr> = \<lparr>\<bottom>#(a +\<^sub>A \<not>\<^sub>A b)\<rparr>"
      have "\<bottom>#(a -\<^sub>A b) = \<bottom>#(a +\<^sub>A \<not>\<^sub>A b)" 
        apply (rule lemma_1_4_2)
        using assms 1 2 3 4 by simp+
      then have "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b" by simp }
    then have "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b"
      using 1 assms thm_3_6_6_aux2a \<open>\<lparr> a \<rparr> + \<lparr> \<not>\<^sub>A b \<rparr> = \<lparr> \<top> # a +\<^sub>A \<not>\<^sub>A b \<rparr> \<Longrightarrow> a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b\<close>
      by (metis DAplus_eq_len compl_def length_comp_one length_map neg_def tplus_def) }
  
  then show "a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b"
    using thm_3_6_6_aux2b assms \<open>\<lparr> a \<rparr> - \<lparr> b \<rparr> = \<lparr> \<top> # a -\<^sub>A b \<rparr> \<Longrightarrow> a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b\<close> by blast
qed


lemma thm_3_6_5: 
  fixes k :: nat
  assumes "length a = Suc (Suc k)" and "length a = length b"
  shows "\<lparr>a -\<^sub>A b\<rparr> = \<lparr>a +\<^sub>A \<not>\<^sub>A b\<rparr>"
  apply (cases "b = True # \<zero>\<^sup>\<rightarrow> (Suc k)")
  using assms thm_3_6_6_aux1 thm_3_6_6_aux2 by simp_all



lemma thm_3_6_6: 
  fixes k :: nat
  assumes "length a = Suc (Suc k)"
  shows "length a = length b \<Longrightarrow> a -\<^sub>A b = a +\<^sub>A \<not>\<^sub>A b"
  using assms thm_3_6_6_aux1 thm_3_6_6_aux2 by blast


(* Theorem 3.7 *)


lemma thm_3_7_aux:
  fixes k :: nat
  assumes "length a = Suc k" and "length b = Suc k"
  shows "a +\<^sub>A b = tl (a +\<^sub>Z\<^sub>A b)"
  by (simp add: tplus_def uplus_def)

lemma thm_3_7_2: 
  fixes k :: nat
  assumes "length a = Suc k" and "length b = Suc k" and "length c = Suc k"
  shows "(\<bottom> # a) +\<^sub>Z\<^sub>A (b +\<^sub>Z\<^sub>A c) = (a +\<^sub>Z\<^sub>A b) +\<^sub>Z\<^sub>A (\<bottom> # c)"
  apply (rule lemma_1_4_1[where k = "Suc (Suc k)"], simp add: assms length_uplus, simp add: assms length_uplus)
  apply (subst thm_3_1_1[symmetric], simp add: assms length_uplus)+
  by simp


lemma thm_3_7_1: 
  fixes k :: nat
  assumes "length a = Suc k" and "length b = Suc k" and "length c = Suc k"
  shows "a +\<^sub>A (b +\<^sub>A c) = (a +\<^sub>A b) +\<^sub>A c"
proof -
  have 1: "\<And> a. a = tl (\<bottom> # a)" by simp

  have 2: "\<And> a b. length a = length b \<Longrightarrow> tl a +\<^sub>A tl b = tl (a +\<^sub>A b)"
    unfolding tplus_def by (case_tac a; case_tac b, simp_all)

  show ?thesis
    apply (subst (2) thm_3_7_aux, simp add: assms, simp add: assms)
    apply (subst 1)
    apply (subst 2, simp add: assms length_uplus)
    apply (subst thm_3_7_aux, simp add: assms, simp add: assms length_uplus)
    apply (subst thm_3_7_aux, simp add: assms, simp add: assms)
    apply (subst (14) 1)
    apply (subst 2, simp add: assms length_uplus)
    apply (subst thm_3_7_aux, simp add: assms length_uplus, simp add: assms)
    using thm_3_7_2 by (simp add: assms)
qed

end