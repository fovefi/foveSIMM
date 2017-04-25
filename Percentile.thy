theory Percentile

(* Version 0.1, started 2016-07-21, last changed 2017-04-12 
 * Copyright: fovefi ltd, all rights reserved 
 * In this file, the percentile function - as used in the OpenSimm implementation
 * https://github.com/OpenGamma/OpenSIMM  - is formalized. The function is used in
 * foveSIMM.thy and the corresponding examples
 *
 * The documents is structured into two parts, some background lemma on real list and real
 * number, and the main chapter on "percentile" with a definition on the main properties we show:
 * - boundedness
 * - monotonicity
 * - scalar multiplication property 
 * - Lipschitz property
 *)

imports 
  Complex_Main Complex 
begin

(* In this chapter we prove some auxiliary properties of lists  of real numbers such as:
 * - The minimum of a sorted list is its first element (assumed the list is not empty).
 * - The index of an element in a list xs moves by one when an element is concatenated.
 * Furthermore we introduce the difference list of a list of real numbers as in
 * [1, 4, 9, 16, 25, 36], the difference list is [4-1, 9-4, 16-9, 25-16, 36-25], that is,
 * [3, 5, 7, 9, 11] and some properties.
 * Finally we show some properties on the ceiling function and the interpolation of real numbers.
 *)
(*****************************************************************************************)
(*****************************************************************************************)
chapter \<open>Real Lists, difference lists, properties on real numbers\<close>
(*****************************************************************************************)
(*****************************************************************************************)

(* In this section we define the minimum and the maximum of a list of real numbers and show some
 * properties, in particular, in the relationship to sorted lists.
 *)
(*****************************************************************************************)
section \<open>Minimum, maximum, sort\<close>
(*****************************************************************************************)

(* In the following we state some general definitions and properties of lists of real number.
 *)
paragraph \<open>Definition member, minimum, maximum\<close>
  
fun member :: "real \<Rightarrow> (real list) \<Rightarrow> bool"
   where "member x [] = False" |
         "member x (y#xs) = (if (x = y) then True
                                        else (member x xs))"

fun minimum :: "(real list) \<Rightarrow> real"
  where "minimum (x#[]) = x" |
        "minimum (x#xs) = (if (x \<le> (minimum xs)) 
                                then x
                                else minimum xs)" |
        "minimum xs = undefined" (* case where xs = [] *)
        
fun maximum :: "(real list) \<Rightarrow> real"
  where "maximum (x#[]) = x" |
        "maximum (x#xs) = (if (x \<ge> (maximum xs)) 
                                then x
                                else maximum xs)" |
        "maximum xs = undefined" (* case where xs = [] *)       

(* We state some properties of the minimum of lists and sorted lists
 *)
paragraph \<open>Lemmas on the minimum and maximum of lists\<close>
(* The minimum of x#xs is x if xs is empty or x is less than or equal to the minimum of xs, else
   it is the minimum of xs *)
lemma minimum_cons[simp]: 
  shows "minimum (x#xs) = (if xs = [] then x else if (x \<le> minimum(xs)) then x else minimum xs)"
  by (cases xs) simp_all
   
(* The minimum of a list is a member of the list *)
lemma member_min:
  shows   "member (minimum (x # xs)) (x # xs)"
  by (induct xs) (simp_all split: if_splits)

(* The maximum of a list is a member of the list *)
lemma member_max:
  shows   "member (maximum (x # xs)) (x # xs)"
  apply (induct xs)
  apply simp
   by (metis Percentile.member.simps(2) maximum.simps(1) maximum.simps(2) member.elims(3))

(* If the list x#xs is sorted then xs is sorted *)
lemma sorted_sublist:
assumes "sorted ((x::real)#(xs:: (real list)))"
shows   "sorted xs"
  using assms sorted_Cons by blast

(* If x#xs is sorted then the minimum of x#xs is equal to x *)
lemma min_sorted:
assumes "sorted ((x::real)#(xs:: (real list)))"
shows  "(minimum (x#xs)) = x"
using assms(1) apply (induct xs) 
apply simp
using sorted_sublist 
      by (smt minimum_cons sorted_Cons sorted_many_eq)

(* Auxiliary lemma for lemma max_sorted *)
lemma max_sorted_aux:
assumes "sorted ((x::real)#(xs:: (real list)))"
        "xs \<noteq> []"
shows "(maximum (x#xs)) = maximum xs"
using sorted_sublist maximum.cases assms
      by (smt maximum.simps(1) maximum.simps(2) sorted.cases sorted_many_eq) 

(* The maximum of a sorted list x#xs is x if xs is empty, else it is the last element of xs. *)
lemma max_sorted:
assumes "sorted ((x::real)#(xs:: (real list)))"
shows  "(maximum (x#xs)) = (if (xs = []) then x else xs ! ((length xs) -1))"
using assms(1) apply (induct xs) 
  apply simp
  using sorted_sublist
  by (smt [[smt_timeout = 6]] last.simps last_conv_nth max_sorted_aux maximum.simps(1) 
      sorted_Cons sorted_many_eq)

(* The maximum of a sorted list x#xs is the last element of x#xs. *)
lemma max_sorted_last:
assumes "sorted ((x::real)#(xs:: (real list)))"
shows  "maximum (x#xs) = (x#xs) ! (length xs)" 
using assms(1) apply (induct xs)
apply simp
  by (metis length_greater_0_conv list.simps(3) max_sorted nth_Cons_pos)

(* Variant of the previous lemma. *)
lemma max_sorted_last_var:
assumes "length xs > 1"
        "sorted xs"
shows  "maximum xs = xs ! ((length xs) - 1)" 
using assms max_sorted_last
      by (metis le_less_trans length_tl list.sel(3) list.size(3) 
          nat_neq_iff sorted.cases zero_le_one)

(* Auxiliary lemma for the next lemma *)
lemma max_insort:
shows "maximum (insort x xs) = maximum (x#xs)"
apply (induct xs)
apply simp
proof -
  fix a :: real and xsa :: "real list"
  assume a1: "maximum (insort x xsa) = maximum (x # xsa)"
  have f2: "\<And>r rs. maximum (r # rs) = maximum rs \<or> [] = rs \<or> maximum rs \<le> r"
    by (metis maximum.simps(2) neq_Nil_conv)
  have "xsa = [] \<longrightarrow> x \<le> a \<or> \<not> x \<le> maximum (a # xsa) \<and> \<not> maximum (x # xsa) \<le> a \<and> 
        maximum (x # xsa) = x"
    using maximum.simps(1) by presburger
  then have "\<not> maximum (x # xsa) \<le> a \<and> maximum (x # a # xsa) = maximum (x # xsa) \<or> x \<le> a"
    using f2 by (metis linear maximum.simps(2) neq_Nil_conv order_trans)
  then show "maximum (insort x (a # xsa)) = maximum (x # a # xsa)"
    using f2 a1 by (metis (no_types) insort_key.simps(2) insort_not_Nil)
qed

(* The maximum of a list is invariant under sorting. *)
lemma max_equal_max_sorted:
shows   "maximum (sort (x#xs)) = maximum (x#xs)"
proof -
  have f1: "sort (x#xs) = insort x (sort xs)" by simp
  have f2: "maximum (sort (x#xs)) = maximum (insort x (sort xs))" using f1 by simp
  have f3: "maximum (sort (x#xs)) = maximum (x#(sort xs))" using max_insort f2 by simp
  show ?thesis
apply (induct xs)
apply simp
using f3 
proof -
  fix a :: real and xsa :: "real list"
  assume a1: "maximum (sort (x # xsa)) = maximum (x # xsa)"
  have f2: "\<And>r rs. maximum (r # rs) = r \<or> [] = rs \<or> \<not> maximum rs \<le> r"
    by (metis maximum.simps(2) neq_Nil_conv)
  have f3: "\<And>f r rs. sort_key (f::real \<Rightarrow> real) (r # rs) \<noteq> []"
    by simp
  have f4: "maximum (x # sort xsa) = maximum (x # xsa)"
    using a1 by (simp add: max_insort)
  have f5: "\<And>r rs. maximum (r # rs) = maximum rs \<or> [] = rs \<or> maximum rs \<le> r"
    by (metis (no_types) maximum.simps(2) neq_Nil_conv)
  have f6: "\<And>f rs. sort_key (f::real \<Rightarrow> real) rs = [] \<or> 0 < length rs"
    by fastforce
  have f7: "\<And>f rs n. sort_key (f::real \<Rightarrow> real) rs \<noteq> [] \<or> \<not> n < length rs"
    by (metis (no_types) length_0_conv length_sort not_less0)
  have f8: "maximum (sort xsa) = maximum (x # xsa) \<or> sort xsa = [] \<or> maximum (sort xsa) \<le> x"
    using f5 f4 by (metis (no_types))
  have f9: "maximum (x # xsa) = x \<or> \<not> maximum (sort xsa) \<le> x"
    using f4 f2 by (metis Percentile.member.simps(2) list.distinct(1) member.elims(2) member_max)
  have "x \<le> a \<longrightarrow> \<not> maximum (a # sort xsa) \<le> x \<and> maximum (a # sort xsa) = maximum (x # a # xsa) \<or>
        xsa = [] \<or> maximum (sort xsa) \<noteq> x \<and> sort xsa \<noteq> [] \<and> \<not> maximum (sort xsa) \<le> a \<and> 
        maximum (sort xsa) = maximum (x # a # xsa) \<and> x \<le> maximum (sort xsa) \<or> a \<le> x \<or> 
        (\<exists>r. \<not> r \<le> a \<and> r \<le> x)"
    using f5 f4 f2 by (metis (no_types) maximum.simps(1) neq_Nil_conv)
  then have "a \<le> x \<or> maximum (sort xsa) \<noteq> x \<and> sort xsa \<noteq> [] \<and> \<not> maximum (sort xsa) \<le> a \<and> 
       maximum (sort xsa) = maximum (x # a # xsa) \<and> x \<le> maximum (sort xsa) \<or> xsa = [] \<or> 
        \<not> maximum (a # sort xsa) \<le> x \<and> maximum (a # sort xsa) = maximum (x # a # xsa)"
    by (meson linear order_trans)
  moreover
  { assume "a \<le> x"
    moreover
    { assume "maximum xsa \<noteq> a \<and> a \<le> x"
      then have "maximum xsa = x \<and> a \<le> x \<or> maximum xsa \<le> a \<and> a \<le> x \<or> maximum xsa \<le> x \<and> 
        a \<le> x \<or> maximum (sort xsa) \<noteq> x \<and> sort xsa \<noteq> [] \<and> \<not> maximum (sort xsa) \<le> a \<and> 
        maximum (sort xsa) = maximum (x # a # xsa) \<and> x \<le> maximum (sort xsa) \<or> xsa = []"
        using f9 f5 f4 by (metis (no_types) linear list.distinct(1) maximum.simps(1))
      then have "maximum xsa \<le> a \<and> a \<le> x \<or> maximum xsa \<le> x \<and> a \<le> x \<or> xsa \<noteq> [] \<and> 
        maximum (x # xsa) = x \<and> maximum xsa \<le> a \<and> a \<le> x \<or> maximum (sort xsa) \<noteq> x \<and> 
        sort xsa \<noteq> [] \<and> \<not> maximum (sort xsa) \<le> a \<and> maximum (sort xsa) = maximum (x # a # xsa) \<and> 
        x \<le> maximum (sort xsa) \<or> \<not> maximum (a # xsa) \<le> x \<and> maximum (a # xsa) = maximum (x # xsa)
        \<and> maximum (a # xsa) = x \<and> a \<le> x \<or> xsa = [] \<or> maximum (x # xsa) = x \<and> 
        maximum (a # xsa) \<le> x \<and> a \<le> x"
        by fastforce }
    moreover
    { assume "maximum xsa \<le> a \<and> a \<le> x"
      then have "maximum xsa \<le> x \<and> a \<le> x \<or> \<not> maximum (a # xsa) \<le> x \<and> 
           maximum (a # xsa) = maximum (x # xsa) \<and> maximum (a # xsa) = x \<and> a \<le> x \<or> 
           xsa = [] \<or> maximum (sort xsa) \<noteq> maximum (x # xsa) \<and> maximum (x # a # xsa) = x \<and> a \<le> x
           \<or> (\<exists>f. maximum (x # a # xsa) = x \<and> sort_key (f::real \<Rightarrow> real) xsa = [] \<and> a \<le> x) \<or>
           sort xsa \<noteq> [] \<and> maximum (x # a # xsa) = x \<and> maximum (sort xsa) \<le> a \<and> a \<le> x"
        by auto }
    moreover
    { assume "maximum xsa \<le> x \<and> a \<le> x"
      then have "xsa \<noteq> [] \<and> maximum (x # xsa) = x \<and> maximum xsa \<le> a \<and> a \<le> x \<or> xsa = [] \<or> 
           maximum (x # xsa) = x \<and> maximum (a # xsa) \<le> x \<and> a \<le> x"
        using f5 f2 by (metis (no_types)) }
    ultimately have "maximum (sort xsa) \<noteq> x \<and> sort xsa \<noteq> [] \<and> \<not> maximum (sort xsa) \<le> a \<and> 
          maximum (sort xsa) = maximum (x # a # xsa) \<and> x \<le> maximum (sort xsa) \<or> xsa = [] \<or> 
          maximum (x # a # xsa) = maximum (x # xsa) \<and> maximum (x # a # xsa) = x \<and> a \<le> x \<or> 
          maximum (sort xsa) \<noteq> maximum (x # xsa) \<and> maximum (x # a # xsa) = x \<and> a \<le> x \<or> 
          (\<exists>f. maximum (x # a # xsa) = x \<and> sort_key (f::real \<Rightarrow> real) xsa = [] \<and> a \<le> x) \<or> 
          sort xsa \<noteq> [] \<and> maximum (x # a # xsa) = x \<and> maximum (sort xsa) \<le> a \<and> a \<le> x"
      using f2 by (metis (no_types) list.distinct(1) order_refl)
    then have "maximum (sort xsa) \<noteq> x \<and> sort xsa \<noteq> [] \<and> \<not> maximum (sort xsa) \<le> a \<and> 
         maximum (sort xsa) = maximum (x # a # xsa) \<and> x \<le> maximum (sort xsa) \<or> xsa = [] \<or> 
         \<not> maximum (a # sort xsa) \<le> x \<and> maximum (a # sort xsa) = maximum (x # a # xsa) \<or> 
         maximum (x # a # xsa) = x \<and> maximum (a # sort xsa) \<le> x"
      using f8 f7 f6 f5 f2 by (metis (no_types) maximum.simps(1)) }
  moreover
  { assume "xsa = []"
    then have "\<not> maximum (a # sort xsa) \<le> x \<and> maximum (a # sort xsa) = maximum (x # a # xsa) \<or> 
         maximum (x # a # xsa) = x \<and> maximum (a # sort xsa) \<le> x"
      by simp }
  moreover
  { assume "maximum (sort xsa) \<noteq> x \<and> sort xsa \<noteq> [] \<and> \<not> maximum (sort xsa) \<le> a \<and> 
         maximum (sort xsa) = maximum (x # a # xsa) \<and> x \<le> maximum (sort xsa)"
    then have "\<not> maximum (a # sort xsa) \<le> x \<and> maximum (a # sort xsa) = maximum (x # a # xsa)"
      using f5 by (metis (no_types) leD le_less) }
  ultimately have "\<not> maximum (a # sort xsa) \<le> x \<and> maximum (a # sort xsa) = maximum (x # a # xsa) 
          \<or> maximum (x # a # xsa) = x \<and> maximum (a # sort xsa) \<le> x"
    by fastforce
  then show "maximum (sort (x # a # xsa)) = maximum (x # a # xsa)"
    using f5 f3 f2 by (metis (no_types) max_insort sort_key_simps(2))
qed
qed

(* A variant of the previous lemma. *)
lemma max_equal_max_sorted_var:
assumes "length xs > 1"
shows   "maximum (sort xs) = maximum xs"
using max_equal_max_sorted by (metis One_nat_def Suc_length_conv Suc_less_eq2 assms)

(* A member in a non-empty list is smaller than or equal to the maximum of the list. *)
lemma maximum_lemma:
   shows "member a (x#xs) \<Longrightarrow> a \<le> maximum ((x::real)#xs)"
   apply (induction xs)
   apply (smt Percentile.member.simps(1) Percentile.member.simps(2) maximum.simps(1))
   by (smt [[smt_timeout = 10]] Percentile.member.simps(2) list.inject maximum.simps(1) 
       maximum.simps(2) member.elims(2) member.elims(3))

(* The lemma states that sorting a list does not change its length. *)
lemma length_invariance_sort:
fixes xs :: "real list"
shows "length values = length (sort values)"
apply (induct xs)
apply simp
by auto

(* The maximum of a list is greater than or equal to its first element. *)
lemma max_vs_first_element:
  fixes   xs :: "real list"
  assumes "length xs > 0"
  shows   "maximum xs \<ge> xs!0"
  proof -      
  have f1: "xs = [x] \<longrightarrow> maximum xs = xs!0" by simp
  show ?thesis using f1
       by (smt Suc_pred assms length_Suc_conv length_greater_0_conv maximum.simps(1) 
           maximum.simps(2) nth_Cons_0)
qed

(* For a sorted list the values of earlier indices are smaller (or equal) than the later *)
lemma sorted_index:
shows "\<forall>i.\<forall>j.\<forall> xs. sorted xs \<and> length xs = n \<longrightarrow> (i \<le> j \<and> j < length xs) \<longrightarrow> (xs!i \<le> xs!j)"
apply (induct n)
apply simp
by (simp add: sorted_nth_mono) 

(* A corollary for two adjacent indices *)
lemma sort_next:
   assumes "sorted (xs:: (real list))"
           "length xs > 1"
           "nat (i::int) < length xs"
   shows "xs!(nat (i-1)) \<le> xs!(nat i)"
by (simp add: assms(1) assms(3) sorted_nth_mono)

(* In a sorted list all elements are smaller than or equal to the last element. *)
lemma any_smaller_sorted_last:
assumes "sorted ((x::real)#(xs:: (real list)))"
        "0\<le> i & i \<le> length xs"
shows  "(x#xs) ! i \<le> (x#xs) ! (length xs)" 
using assms(1) assms(2) max_sorted_last apply (induct i)
apply simp
apply (metis (no_types, lifting) assms(2) length_Cons lessI nth_Cons_0 order_trans 
      sorted_equals_nth_mono)
using sorted_nth_mono by fastforce

(* A variant of the previous lemma *)
lemma any_smaller_sorted_last_var:
assumes "sorted (xs:: (real list))"
        "length xs > 1"
        "0\<le> i & i < length xs"
shows  "xs ! i \<le> xs ! ((length xs) -1)" 
using any_smaller_sorted_last
      by (metis One_nat_def Suc_leI Suc_pred assms(1) assms(3) diff_less le_0_eq nat.simps(3) 
          not_le sorted_equals_nth_mono)

(* sort is idempotent. *)
lemma sort_sort:
   shows "sort (sort (x#xs)) = sort (x#xs)"
   apply (induct xs)
   apply simp
   using sorted_sort sorted_sort_id by blast

(* Relationship between position in x#xs and xs *)
lemma list_down:
    assumes "i>0"
    shows "(x#xs)!i = xs!(i-1)"
    apply (induction xs)
    apply simp
    apply (simp add: assms)
    by (simp add: assms)

(* Length of x#xs is one more than length xs. *)
lemma length_add_one:
  fixes xs :: "real list"
  shows "length (x#xs) = Suc (length xs)" by simp

(* In the next section we define the difference list of an existing list of real numbers. 
 * For one-element lists we define it as the empty list. Note, the difference list is
 * a discrete analogon to the derivative of a continuous function.
 *)
(*****************************************************************************************)
section \<open>Difference Lists\<close>
(*****************************************************************************************)

(* Definition of the difference list *)
fun diff_list :: "(real list) \<Rightarrow> (real list)" where
   "diff_list ((x1::real)#(x2::real)#[]) = (x2 - x1) # []" |
   "diff_list ((x1::real)#(x2::real)#xs) = (x2 - x1) # (diff_list (x2 # xs))" |
   "diff_list xs = []" 
      (* Last case to make the specification complete, i.e., for the empty and 1-element list *)

(* An auxiliary lemma for the proof of the next lemma. *)
lemma diff_list_length_aux:
   shows "length (diff_list (x#y#xs)) = (length (x#xs))"
   proof -
   have f1: "\<forall> x y a u v. \<forall> xs. length (diff_list (a#x#y#xs)) = Suc (length (diff_list (u#v#xs)))"
         by (smt Suc_length_conv Suc_pred diff_list.simps(1) diff_list.simps(2)
             length_greater_0_conv linorder_not_le list.size(4))
   have f2: "\<forall> x a.  \<forall> xs. length (x#(a#xs)) = Suc(length (x#xs))" by auto 
   have f3: "\<forall> xs. xs \<noteq> [] \<longrightarrow> length (diff_list (x#y#a#xs)) = Suc (length (diff_list (x#y#xs)))" 
        using f1 by blast
   show ?thesis
   apply (induction xs)
   apply simp
   using f1 f2 f3 by metis
qed

(* The difference list of a non-empty list xs is one shorter than xs itself. *)
lemma diff_list_length:
   assumes "length xs \<ge> 1"
   shows "length (diff_list xs) = (length xs) -1" 
proof -
  {assume assumption: "length xs > 1"
  obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    f1: "\<forall>x0 x1. (\<exists>v2. x0 = Suc v2 \<and> x1 < v2) = (x0 = Suc (nn x0 x1) \<and> x1 < nn x0 x1)"
    by moura
  obtain rr :: "nat \<Rightarrow> real list \<Rightarrow> real" and rrs :: "nat \<Rightarrow> real list \<Rightarrow> real list" where
    "\<forall>x0 x1. (\<exists>v2 v3. x1 = v2 # v3 \<and> length v3 = x0) = 
               (x1 = rr x0 x1 # rrs x0 x1 \<and> length (rrs x0 x1) = x0)"
    by moura
  then have "\<forall>rs n. (length rs \<noteq> Suc n \<or> rs = rr n rs # rrs n rs \<and> length (rrs n rs) = n) \<and> 
             (length rs = Suc n \<or> (\<forall>r rsa. rs \<noteq> r # rsa \<or> length rsa \<noteq> n))"
    by (meson length_Suc_conv)
  then have "rr (nn (length xs) 0) xs # rr (nn (length xs) 0 - Suc 0) 
       (rrs (nn (length xs) 0) xs) # rrs (nn (length xs) 0 - Suc 0) 
       (rrs (nn (length xs) 0) xs) = xs"
    using f1 Suc_less_eq2 assumption by auto
  then have ?thesis
    by (metis diff_list_length_aux length_tl list.sel(3) list.size(4))
  }
   have f1: "length xs > 1 \<longrightarrow> ?thesis"
   using \<open>1 < length xs \<Longrightarrow> length (diff_list xs) = length xs - 1\<close> by blast
   have f2: "length xs = 1 \<longrightarrow> ?thesis"
     by (metis One_nat_def Suc_length_conv assms diff_is_0_eq diff_list.simps(4) length_0_conv)
   show ?thesis using assms f1 f2
     using nat_less_le by linarith
qed

(* The following lemma shows that the difference of an element in a list xs and its predecessor
 * are in the difference list of the list.
 *)
lemma diff_list_lemma:
   fixes xs :: "real list"
   assumes "length xs > 1"
           "i \<ge> 1"
           "i < length xs"
   shows "member (xs!i - xs!(i-1)) (diff_list xs)"
   using assms
proof (induct xs arbitrary: i rule: diff_list.induct)
(* print_cases *)
  case 1
  then show ?case by simp
next 
  case hyp: (2 x0 x1 a xs)
  thm hyp(3,4)
  then show ?case
proof -
  have f1: "length ([]::real list) < i"
    by (metis (no_types) Suc_eq_plus1 cancel_comm_monoid_add_class.diff_cancel hyp.prems(2) 
        le_imp_less_Suc less_diff_conv2 list.size(3) order_refl)
  have "\<And>n. member ((x1 # a # xs) ! n - (x1 # a # xs) ! (n - 1)) (diff_list (x1 # a # xs)) \<or> 
            \<not> n < length (x1 # a # xs) \<or> \<not> 1 \<le> n"
    by (meson hyp.hyps le_less_trans)
  moreover
  { assume "i - 1 \<noteq> 1 \<and> i \<noteq> length ([]::real list)"
    moreover
    { assume "i \<noteq> length ([]::real list) \<and> \<not> 1 \<le> i - 1"
      then have "i \<noteq> length ([]::real list) \<and> i < 1 + 1"
        by linarith
      then have "member ((x0 # x1 # a # xs) ! i - (x0 # x1 # a # xs) ! (i - 1)) 
                        ((x1 - x0) # diff_list (x1 # a # xs))"
        by force }
    ultimately have "length ([]::real list) < i - 1 \<and> 1 \<le> i - 1 \<or> 
                     member ((x0 # x1 # a # xs) ! i - (x0 # x1 # a # xs) ! (i - 1)) 
                            ((x1 - x0) # diff_list (x1 # a # xs))"
      by (metis (no_types) Suc_eq_plus1 Suc_lessD add.left_neutral le_eq_less_or_eq list.size(3)) }
  ultimately have "member ((x0 # x1 # a # xs) ! i - (x0 # x1 # a # xs) ! (i - 1)) 
                          ((x1 - x0) # diff_list (x1 # a # xs))"
    using f1 by (metis (no_types) Percentile.member.simps(2) Suc_eq_plus1 hyp.prems(2) 
                 hyp.prems(3) length_add_one less_diff_conv2 list.size(3) list_down not_le 
                 order_refl zero_less_one)
  then show ?thesis
    using diff_list.simps(2) by presburger
qed
next 
  case "3_1"
  then show ?case by simp
next 
  case "3_2"
  then show ?case by simp
qed

(* The first element of the difference list of a sorted list is not negative.
 * The lemma is used to prove that the maximum of the difference list of a
 * sorted list is non-negative.
 *)
lemma diff_list_non_negative:
   assumes "sorted (xs:: (real list))"
           "length xs > 1"
   shows   "(diff_list xs) ! 0 \<ge> 0"
   proof -
   def x0 \<equiv> "xs!0"
   def x1 \<equiv> "xs!1"
   have f1: "\<exists> y. (diff_list xs) = (x1 - x0) # y" using diff_list.cases
proof -
  obtain rr :: "real list \<Rightarrow> real" and rra :: "real list \<Rightarrow> real" and rrb :: "real list \<Rightarrow> real" 
         and rrs :: "real list \<Rightarrow> real list" where
    f1: "\<forall>rs. rs = [rr rs] \<or> rs = rra rs # rrb rs # rrs rs \<or> rs = []"
    using minimum.cases by moura
  have "[] \<noteq> xs"
    using assms(2) le_less_trans by blast
  then have "x0 # x1 # rrs xs = xs \<or> length xs = 1"
    using f1 by (metis (no_types) Suc_eq_plus1 add_0_left length_Cons list.size(3) nth_Cons_0 
                 nth_Cons_Suc x0_def x1_def)
  then show ?thesis
    using f1 by (metis (no_types) assms(2) diff_list.simps(1) diff_list.simps(2) 
                  linorder_not_le order_refl)
qed
   have f2: "(diff_list xs) !0 = x1 - x0" using f1 using less_numeral_extra(3) 
              nth_non_equal_first_eq by auto
   show ?thesis using assms(1) assms(2) f2 sorted_equals_nth_mono x0_def x1_def by auto
qed

(* The maximum of the difference list of a sorted list is non-negative.*)
lemma diff_list_max_non_negative:
   assumes "sorted (xs:: (real list))"
           "length xs > 1"
   shows   "maximum (diff_list xs) \<ge> 0"
   proof -
   have f1: "(diff_list xs)! 0 \<ge> 0" using diff_list_non_negative 
        using assms(1) assms(2) by blast
   have f2: "length (diff_list xs) > 0" using diff_list_length assms(2) zero_less_diff by auto
   have f3: "maximum (diff_list xs) \<ge> (diff_list xs)!0" 
            using max_vs_first_element using assms(2) f2 by blast
   show ?thesis using f1 f3 by linarith
qed

(* In the following paragraph some properties of finite sums are introduced. *)
paragraph \<open>Sums\<close>

(* The following two lemma show the monotonicity of addition, first for two summands, then for
 * arbitrary finite summands.
 *)
lemma mono_plus:
  assumes "(a :: real) \<le> 0"
          "(b :: real) \<le> 0"
  shows   "a + b \<le> 0"
  using assms(1) assms(2) by auto

lemma monotonicity_addition:
  fixes n :: nat
  shows "((\<forall>i. (0 < i \<and> i \<le> n) \<longrightarrow> ((f i) :: real) \<le> 0)) \<longrightarrow> (\<Sum> i \<in> {1..n}. (f i)) \<le> 0"
proof (induct n)
print_cases
  case 0
  then show ?case by (simp add: setsum_nonpos)
  case (Suc n) 
  {assume  assm: "(\<forall>i. 0 < i \<and> i \<le> n \<longrightarrow> f i \<le> 0) \<longrightarrow> setsum f {0..n} \<le> 0"
  have f1: "setsum f {1..Suc n} = setsum f {1..n} + (f (Suc n))"
       by (metis Icc_eq_Icc One_nat_def Suc_eq_plus1_left add_le_cancel_left atLeastatMost_empty 
           le0 nat.simps(3) setsum_cl_ivl_Suc zero_less_one)
  then have "(\<forall>i. 0 < i \<and> i \<le> (Suc n) \<longrightarrow>f i \<le> 0) \<longrightarrow> setsum f {1..(Suc n)} \<le> 0" 
       using assm f1 using le_Suc_eq zero_less_Suc Suc.hyps by force
  }
  then show ?case using Suc.hyps by auto
 qed

lemma monotonicity_addition_gen:
  fixes n m :: nat
  shows "((\<forall>i. (m \<le> i \<and> i \<le> n) \<longrightarrow> ((f i) :: real) \<le> 0)) \<longrightarrow> (\<Sum> i \<in> {m..n}. (f i)) \<le> 0"
proof (induct n)
print_cases
  case 0
  then show ?case by (simp add: setsum_nonpos)
  case (Suc n) 
  {assume  assm: "(\<forall>i. m \<le> i \<and> i \<le> n \<longrightarrow> f i \<le> 0) \<longrightarrow> setsum f {m..n} \<le> 0"
  have f1: "setsum f {0..Suc n} = setsum f {0..n} + (f (Suc n))"
       by (metis Icc_eq_Icc atLeastatMost_empty 
           le0 nat.simps(3) setsum_cl_ivl_Suc zero_less_one)
  then have "(\<forall>i. m \<le> i \<and> i \<le> (Suc n) \<longrightarrow>f i \<le> 0) \<longrightarrow> setsum f {m..(Suc n)} \<le> 0" 
       using assm f1 using le_Suc_eq zero_less_Suc Suc.hyps
       by (smt Icc_eq_Icc setsum_cl_ivl_Suc)
  }
  then show ?case using Suc.hyps by auto
 qed

(* The (finite) sum of differences is the difference of two sums. *) 
lemma sum_comm:
  fixes f g :: "nat \<Rightarrow> real"
  shows "(\<Sum> i \<in> {0..n::nat}. ((f i) - (g i))) = 
         (\<Sum> i \<in> {0..n}. (f i)) - (\<Sum> i \<in> {0..n}. (g i))"
proof (induct n)
print_cases
  case 0  
  then show ?case by simp
  case (Suc n)
  {assume assm: "(\<Sum> i \<in> {0..n::nat}. ((f i) - (g i))) = 
         (\<Sum> i \<in> {0..n}. (f i)) - (\<Sum> i \<in> {0..n}. (g i))"
  have "(\<Sum> i \<in> {0..(Suc n)}. ((f i) - (g i))) = (\<Sum> i \<in> {0..n}. ((f i) - (g i))) + ((f (Suc n)) - (g (Suc n)))"
               by simp
  then have "(\<Sum> i \<in> {0..(Suc n)}. ((f i) - (g i))) =  (\<Sum> i \<in> {0..n}. (f i)) - (\<Sum> i \<in> {0..n}. (g i)) + 
              ((f (Suc n)) - (g (Suc n)))" using assm by simp
  then have "(\<Sum> i \<in> {0..(Suc n)}. ((f i) - (g i))) =   
             (\<Sum> i \<in> {0..n}. (f i)) + (f (Suc n)) - (\<Sum> i \<in> {0..n}. (g i)) - (g (Suc n))" by linarith
  then have ?case by simp
  }
  then show ?case using Suc.hyps by blast
qed

(* As above, but with starting index 1 instead of 0.*)
lemma sum_comm_corr:
  fixes f g :: "nat \<Rightarrow> real"
  shows "(\<Sum> i \<in> {1..n::nat}. ((f i) - (g i))) = 
         (\<Sum> i \<in> {1..n}. (f i)) - (\<Sum> i \<in> {1..n}. (g i))"
  using sum_comm using setsum_subtractf by force

(* As above, but with arbitrary starting index. *)
lemma sum_comm_general:
  fixes f g :: "nat \<Rightarrow> real" and
        m n :: nat
  shows "(\<Sum> i \<in> {m..n}. ((f i) - (g i))) = 
         (\<Sum> i \<in> {m..n}. (f i)) - (\<Sum> i \<in> {m..n}. (g i))"
  using sum_comm using setsum_subtractf by force

(* If every summand of a sum of n elements is limited by a constant c
 * then the sum is limited by n*c. *)
lemma monotonicity_addition_corollary_constant:
  shows "0 \<le> (n ::nat) \<longrightarrow> ((\<forall>i. (0 < i \<and> i\<le>n) \<longrightarrow> ((f i) :: real)  \<le> c) \<longrightarrow> 
         (\<Sum> i \<in> {1..n}. (f i)) \<le> n * c)"
  proof - 
  have "0 \<le> (n ::nat) \<longrightarrow> ((\<forall>i. (0 < i \<and> i\<le>n) \<longrightarrow> ((f i) :: real) - c \<le> 0) \<longrightarrow> 
         (\<Sum> i \<in> {1..n}. ((f i) - c)) \<le> 0)"
        using monotonicity_addition by auto 
  then have f1: "0 \<le> (n ::nat) \<longrightarrow> ((\<forall>i. (0 < i \<and> i\<le>n) \<longrightarrow> ((f i) :: real)  \<le> c) \<longrightarrow> 
         (\<Sum> i \<in> {1..n}. ((f i) - c)) \<le> 0)" by auto
  have  "(\<Sum> i \<in> {1..n}. ((f i) - c)) = (\<Sum> i \<in> {1..n}. (f i)) - (\<Sum> i \<in> {1..n}. c)" using 
        sum_comm_corr[of "f" "\<lambda> i. c"] by blast
  then show ?thesis using f1 by auto
qed

(* If every summand of a first sum is smaller than or equal to a corresponding summand in 
 * a second sum (of the same length), then the first sum is small than or equal to the
 * second sum. *)
lemma monotonicity_addition_corollary:
  fixes n :: nat
  shows "(\<forall>i. (0 < i \<and> i\<le>n) \<longrightarrow> ((f i) :: real)  \<le> ((g i) :: real)) \<longrightarrow> 
         (\<Sum> i \<in> {1..n}. (f i)) \<le>  (\<Sum> i \<in> {1..n}. (g i))"
  proof - 
  have "(\<forall>i. (0 < i \<and> i\<le>n) \<longrightarrow> ((f i) - ((g i)) \<le> 0)) \<longrightarrow> 
         (\<Sum> i \<in> {1..n}. ((f i) - (g i))) \<le> 0"
        using monotonicity_addition[of concl: n "\<lambda>i.(f i) - (g i)"] by blast
  then have f1: "((\<forall>i. (0 < i \<and> i\<le>n) \<longrightarrow> ((f i) :: real)  \<le> (g i)) \<longrightarrow> 
         (\<Sum> i \<in> {1..n}. ((f i) - (g i))) \<le> 0)" by auto
  have  "(\<Sum> i \<in> {1..n}. ((f i) - (g i))) = (\<Sum> i \<in> {1..n}. (f i)) - (\<Sum> i \<in> {1..n}. (g i))" using 
        sum_comm_corr[of "f" "g"] by blast
  then show ?thesis using f1 by auto
qed

(* A sum with arbitrary starting index can be written as a difference of two sums starting with
 * index 1. *)
lemma sum_diff:
fixes n k :: nat and
      a :: "nat \<Rightarrow> real"
assumes "k \<ge> n"
        "n \<ge> 1"
shows "(\<Sum> i \<in> {n..k}. (a i)) =  (\<Sum> i \<in> {1..k}. (a i)) -  (\<Sum> i \<in> {1..(n-1)}. (a i))"
proof -
  have f1: "n \<noteq> 0"
    using assms(2) by linarith
  have "n \<le> Suc k"
    using assms(1) by linarith
  then show ?thesis
    using f1 by (metis One_nat_def Suc_pred assms(2) atLeastLessThanSuc_atLeastAtMost 
                 neq0_conv setsum_diff_nat_ivl)
qed

(* A sum from 1 to n plus a sum from (n+1) to m corresponds to a sum from 1 to m. *)
lemma sum_add:
   fixes n m :: nat and
         f :: "nat \<Rightarrow> real"
   assumes "m \<ge> n+1"
   shows "(\<Sum> i \<in> {1..n}. f i) + (\<Sum> i \<in> {(n+1)..m}. f i) = (\<Sum> i \<in> {1..m}. f i)"
   by (smt One_nat_def add_diff_cancel_right' assms(1) le0 le_add2 setsum_head_Suc sum_diff)

(* As previous lemma, but 1 to (n-1) and n to m results in 1 to m. *)
lemma sum_add_var:
   fixes n m :: nat and
         f :: "nat \<Rightarrow> real"
   assumes "m \<ge> n"
           "n \<ge>1"
   shows "(\<Sum> i \<in> {1..(n-1)}. f i) + (\<Sum> i \<in> {n..m}. f i) = (\<Sum> i \<in> {1..m}. f i)"
   using sum_add[of m "n-1"] by (smt assms(1) assms(2) sum_diff)

(* Summing up (n+1) times a real constant c results in (n+1)*c. *)
lemma sum_constant_aux:
  fixes n :: nat
  shows "(\<Sum> i \<in> {0..n}. c) = ((real n) + 1)*c"
  proof (induct n)
  case 0
  then show ?case by auto
  case (Suc n)
  then show ?case by simp
qed

(* Summing up n times a real constant c results in n*c. *)
lemma sum_constant_aux_corrolary:
  fixes n :: nat
  shows "(\<Sum> i \<in> {1..n}. c) = (real n)*c"
  proof (induct n)
  case 0
  then show ?case by auto
  case (Suc n)
  then show ?case by simp
qed

(* Summing up (n-m) times a real constant c results in (n-m)*c. *)
lemma sum_constant:
   fixes n m :: nat
   assumes "n \<ge> m"
           "m \<ge> 1"
   shows "(\<Sum> i \<in> {m..n}. c) = ((real n)- (real m) +1)*c"
   proof -
   have "(\<Sum> i \<in> {1..(m-1)}. c) + (\<Sum> i \<in> {m..n}. c) = (\<Sum> i \<in> {1..n}. c) " 
         using sum_add_var[of n m "\<lambda> i. c"] assms(1) assms(2) sum_add_var by blast
   then have "((real m) - 1) * c +  (\<Sum> i \<in> {m..n}. c) = (real n) * c"
        using sum_constant_aux_corrolary by (metis assms(2) of_nat_1 of_nat_diff)
   then show ?thesis by auto
qed

(* This lemma is a variant of the monotonicity_addition_corollary lemma, but since it makes
 * use of the sum_constant lemma, it must come in the document after it. *)
lemma monotonicity_addition_corollary_var:
  fixes n m :: nat and
        c :: real
  assumes "m \<le> n"
  shows "(\<forall>i. (m \<le> i \<and> i\<le>n) \<longrightarrow> ((f i) :: real)  \<le> c) \<longrightarrow> 
         (\<Sum> i \<in> {m..n}. (f i)) \<le> ((real n) -(real m) +1) * c"
  proof - 
  def g \<equiv> "\<lambda> i::nat. c"
  have "0 \<le> (n ::nat) \<longrightarrow> ((\<forall>i. (m \<le> i \<and> i\<le>n) \<longrightarrow> ((f i) :: real) - c \<le> 0) \<longrightarrow> 
         (\<Sum> i \<in> {m..n}. ((f i) - c)) \<le> 0)"
        using monotonicity_addition_gen by auto 
  then have f1: "0 \<le> (n ::nat) \<longrightarrow> ((\<forall>i. (m \<le> i \<and> i\<le>n) \<longrightarrow> ((f i) :: real)  \<le> c) \<longrightarrow> 
         (\<Sum> i \<in> {m..n}. ((f i) - c)) \<le> 0)" by auto
  have  "(\<Sum> i \<in> {m..n}. ((f i) - (g i))) = (\<Sum> i \<in> {m..n}. (f i)) - (\<Sum> i \<in> {m..n}. (g i))" using 
        sum_comm_general[of f g m n]  by auto 
  then have  "(\<Sum> i \<in> {m..n}. ((f i) - (g i))) = (\<Sum> i \<in> {m..n}. (f i)) - (\<Sum> i \<in> {m..n}. c)" using
        g_def by auto
  then have "(\<Sum> i \<in> {m..n}. ((f i) - (g i))) = (\<Sum> i \<in> {m..n}. (f i)) - (n - m + 1) * c" 
        using sum_constant assms by auto
  then have "(\<forall>i. (m \<le> i \<and> i\<le>n) \<longrightarrow> ((f i) :: real)  \<le> c) \<longrightarrow> 
         (\<Sum> i \<in> {m..n}. (f i)) \<le> (n -m +1) * c" 
        by (smt \<open>(\<Sum>i = m..n. f i - g i) = setsum f {m..n} - (\<Sum>i = m..n. c)\<close> 
            atLeastAtMost_iff setsum_mono)
  then show ?thesis by (metis assms of_nat_1 of_nat_add of_nat_diff)
qed

(* In a sum of differences where adjacent elements cancel only the last and the first remain. *)
lemma sum_of_differences:
   fixes m :: nat and
         f :: "nat \<Rightarrow> real"
   shows " (\<Sum> i \<in> {1..m}. ((f (i+1)) - (f i))) = (f (m+1)) - (f 1)"
   proof (induct m)
print_cases
  case 0 
    then show ?case by auto
  case (Suc m)
    then show ?case
         by (smt Icc_eq_Icc Suc_eq_plus1 atLeastatMost_empty le_add2 nat.simps(3) 
             setsum_cl_ivl_Suc setsum_head_Suc zero_less_one)
qed

(* Variant of the lemma above with arbitrary starting index. *)
lemma sum_of_differences_gen:
   fixes n m :: nat and
         f :: "nat \<Rightarrow> real"
   assumes "m \<ge> n+1"
   shows "(\<Sum> i \<in> {(n+1)..m}. ((f (i+1)) - (f i))) = (f (m+1)) - (f (n+1))"
   proof -
   have "(\<Sum> i \<in> {1..n}. ((f (i+1)) - (f i)))  + (\<Sum> i \<in> {(n+1)..m}. ((f (i+1)) - (f i))) =
         (\<Sum> i \<in> {1..m}. ((f (i+1)) - (f i)))"
         using sum_add using assms by blast
   then have "(\<Sum> i \<in> {(n+1)..m}. ((f (i+1)) - (f i))) = (\<Sum> i \<in> {1..m}. ((f (i+1)) - (f i))) -
                  (\<Sum> i \<in> {1..n}. ((f (i+1)) - (f i)))" by auto
   then show ?thesis using sum_of_differences
        using add_diff_cancel_right add_uminus_conv_diff by auto
qed

(* Variant of the previous lemma *)
lemma sum_of_differences_gen_var:
   fixes n m :: nat and
         f :: "nat \<Rightarrow> real"
   assumes "m \<ge> n"
           "n \<ge>1"
   shows "(\<Sum> i \<in> {n..m}. ((f (i+1)) - (f i))) = (f (m+1)) - (f n)"
   proof -
    have "(\<Sum> i \<in> {1..(n-1)}. ((f (i+1)) - (f i)))  + (\<Sum> i \<in> {n..m}. ((f (i+1)) - (f i))) =
         (\<Sum> i \<in> {1..m}. ((f (i+1)) - (f i)))"
         using sum_add_var using assms by blast
   then have "(\<Sum> i \<in> {n..m}. ((f (i+1)) - (f i))) = (\<Sum> i \<in> {1..m}. ((f (i+1)) - (f i))) -
                  (\<Sum> i \<in> {1..(n-1)}. ((f (i+1)) - (f i)))" by auto
   then have "(\<Sum> i \<in> {n..m}. ((f (i+1)) - (f i))) = ((f (m+1)) - (f 1)) - ((f n) -  (f 1))"
                 using sum_of_differences add.commute add_diff_cancel_left' assms(2) 
                 ordered_cancel_comm_monoid_diff_class.le_iff_add by auto
   then show ?thesis by auto
qed

(* Distributivity of finite summation and multiplication. *)
lemma sum_distributive:
   fixes m :: nat and 
         b :: real and
         f :: "nat \<Rightarrow> real"
   shows "(\<Sum> i \<in> {0..m}. (f i) * b) = (\<Sum> i \<in> {0..m}. (f i)) * b"
   proof (induct m)
print_cases
  case 0 
    then show ?case by auto
  case (Suc m)
    have f1: "(\<Sum>i = 0..(Suc m). f i * b) = (\<Sum>i = 0..m. f i * b) + f (Suc m) * b" by auto
    have "(\<Sum> i \<in> {0..(Suc m)}. (f i)) * b = ((\<Sum> i \<in> {0..m}. (f i)) + f (Suc m)) * b"
         using setsum_Suc by auto
    have f2: "((\<Sum> i \<in> {0..m}. (f i)) + (f (Suc m))) * b = ((\<Sum> i \<in> {0..m}. (f i)) * b) + (f (Suc m)) * b"
          using distrib_right by blast
    then show ?case
       by (simp add: Suc.hyps \<open>setsum f {0..Suc m} * b = (setsum f {0..m} + f (Suc m)) * b\<close> f1)
qed   

(* Variant of the previous lemma *)
lemma sum_distributive_corr:
   fixes m :: nat and 
         b :: real and
         f :: "nat \<Rightarrow> real"
   shows "(\<Sum> i \<in> {1..m}. (f i) * b) = (\<Sum> i \<in> {1..m}. (f i)) * b"
   using sum_distributive by (metis setsum_left_distrib) 


(* In the following section we show some properties of real number, in particular about
 * the ceiling and floor functions as well as a linear interpolation property for real numbers.
 *)
(*****************************************************************************************)
section \<open>Real numbers: ceiling, floor, and linear interpolation\<close>
(*****************************************************************************************)
(* In the definition of the percentile function we need the expression 
 * ceiling (x - 1/2) and need to compare it to x itself. This is done 
 * in the following five lemmas. Likewise we need some properties of
 * the floor function, in particular to bound the difference between 
 * the value and its function value and some monotonicity properties.
 *)
lemma ceiling_upper:
shows "x + 1/2.0 - (nat (ceiling (x - 1/2.0))) \<le> 1"
by linarith

lemma ceiling_lower:
shows "x + 1/2.0 - (ceiling (x - 1/2.0)) \<ge> 0"
by linarith

lemma floor_lower:
assumes "x \<ge> 0"
shows "(nat (floor ((x::real) - 1/2.0))) - 1/2.0 \<le> x"
using assms by linarith

lemma floor_upper:
assumes "(x::real) \<ge> 0"
shows "x < (floor x) + 1" using assms by simp

lemma floor_upper_plus_1:
shows "floor (x + 1) = (floor x) + 1" by simp 

lemma floor_ceiling:
shows "floor (x::real) + 1 \<ge> ceiling x"
by linarith

lemma floor_ceiling1:
shows "floor (x::real) \<le> ceiling x"
by linarith

lemma ceiling_floor:
shows "ceiling (x::real) - 1 \<le> floor x"
by linarith

lemma nat_ceiling:
fixes x :: real and
      n :: nat
assumes "x \<ge> 0"
        "x \<le> n"
shows "(ceiling x) \<le> n" using assms
using ceiling_mono ceiling_of_nat by linarith 

lemma ceiling_monotonic:
assumes   "x \<le> y"
shows "ceiling x \<le> ceiling y" by (simp add: assms ceiling_mono)

lemma floor_monotonic:
assumes   "x \<le> y"
shows "floor x \<le> floor y" by (simp add: assms floor_mono)

lemma floor_semi_monotonic_inv:
assumes   "floor x \<le> floor y"
shows "x \<le> y + 1" using assms by (smt floor_mono floor_one le_cases le_floor_add)

lemma ceiling_less:
  assumes "(s::real) > 0"
          "(p::real) \<le> 1 - (0.5/s)"
  shows "ceiling (s * p - 0.5) < s"
  proof -
  have f1: "s * p \<le> s - 0.5" using assms
       by (metis diff_divide_distrib divide_self_if mult.commute mult_eq_0_iff order_refl 
           pos_le_divide_eq)
  have f2: "s * p - 0.5 \<le> s -1" using f1
       using divide_pos_pos of_int_less_iff by linarith
  show ?thesis using f2
       using less_ceiling_iff by linarith
  qed


(* For two real numbers x and y with x \<le> y, the numbers z between x and y can be interpolated by 
 * a value \<alpha> between 0 and 1 (incl.) so that z = x + \<alpha> * (y - x).
 *)
lemma linear_interpolation:
fixes \<alpha> x y :: real
assumes "0 \<le> \<alpha> & \<alpha> \<le> 1"
        "x \<le> y"
shows "x \<le>  x + \<alpha> * (y - x)  \<and> x + \<alpha> * (y - x) \<le> y" 
       by (smt assms(1) assms(2) mult_left_le_one_le mult_nonneg_nonneg)


(* In the following chapter we define the percentile function, first in a form which is very close 
 * to the  Java implementation in the OpenSimm implementation. This definition has the problem that 
 * it is underspecified for confidence values close to 1. Accordingly, the Java implementation 
 * will throw an exception for such values.
 * Second, we extend the definition so that the percentile function is specified for all 
 * confidence values.
 * For this fully specified definition we show each in a different section important properties
 * (concretely, the boundedness, monotonicity, scalar multiplication property, and Lipschitz
 * property of the percentile function).
 *)
(*****************************************************************************************)
(*****************************************************************************************)
chapter \<open>Percentile\<close>
(*****************************************************************************************)
(*****************************************************************************************)

(* The definition of the percentile function. *)
(*****************************************************************************************)
section \<open>Definitions\<close>
(*****************************************************************************************)
paragraph \<open>The percentile definition close to the Java implementation\<close>
(*text \<open>
  See @{verbatim "SimmUtils.percentile()"} in
  @{file "../OpenSIMM/src/main/java/com/opengamma/opensimm/util/SimmUtils.java"}
\<close>
*)

(* In the Java code follows a check that the level is below 1 - 1/(2*size).
 * If not, it throws an exception. In the Isabelle implementation (there is no exception 
 * handling in Isabelle), the code is underspecified, that is, no specific values will be
 * returned for larger values. This will be fixed in the definition of the percentile function
 * in the next section. 
 *)
definition percentile_java :: "(real list) \<Rightarrow> real \<Rightarrow> real" 
  where
  "percentile_java values level =
    (let  (size :: real) = (real (length values));
           (sorted :: (real list)) = sort values;
           i = (ceiling (size * level - 0.5));
           (lower :: real) = (i - 0.5) / size;
           (upper ::real) = (i + 0.5) / size;  
           (* Note that we convert i to a nat since we want to use it
              as an index in a list. This means that we automatically 
              have values greater equal 0 *)
           (lower_value :: real)  = sorted ! (nat (i-1));
           (upper_value :: real)  = sorted ! (nat i)
    in lower_value + (level - lower) * (upper_value - lower_value) / (upper - lower))"

(* The following two values show the problem with the percentile_java definition.
 * For a 10-element list, the value is defined up to a confidence value of inclusively
 * 0.95 and the value is the biggest element in the list. That is, Isabelle evaluates the first
 * expression to 10.
 * For values larger than 0.95, the value is underspecified and Isabelle returns an underspecified
 * expression, taking the first element of the empty list. Concretely, it evaluates the 
 * expression to: "10 + 1 / 100 * ([] ! 0 - 10) / (1 / 10)".
 *) 
(*
value "percentile_java [1,2,3,4,5,6,7,8,9,10] 0.95"
value "percentile_java [1,2,3,4,5,6,7,8,9,10] 0.96"
*)

(* In the Java code, there is a check that the level is at most 1 - 1/(2*size)
 * if not, percentile_java throws an exception.
 * The following code covers the case that the level actually is at most the threshold.
 * Furthermore it is assumed that the list sorted_values is actually sorted.       
 *)
paragraph \<open>A fully specified percentile definition\<close>

(* The percentile is calculated as the interpolation of the values at positions (i-1) and
 * i, where i is defined as the ceiling of a scaled up (by the length of the
 * sorted_values) position corresponding to the level.  The interpolation is properly 
 * defined only for values below (or equal to) a particular threshold. This is taken care of
 * in the percentile_sorted function. *)
definition percentile_sorted_below ::  "(real list) \<Rightarrow> real \<Rightarrow> real" where
  "percentile_sorted_below sorted_values level =
     (let (size :: real) = (real (length sorted_values));
           i = ceiling (size * level - 0.5);
           (lower :: real) = (i - 0.5) / size;
           (upper ::real) = (i + 0.5) / size;  
           (* Note that by the conversion of i to nat, we get values \<ge> 0 *)
           (lower_value :: real)  = sorted_values ! (nat (i-1));
           (upper_value :: real)  = sorted_values ! (nat i);
           (\<alpha> :: real) = (level - lower) * size
    in lower_value +  \<alpha> * (upper_value - lower_value))"

(* percentile_sorted assumes that the list of real numbers is sorted. 
 * For values above the threshold we constantly extrapolate to 
 * the biggest value in the list sorted_values.
 *)
definition percentile_sorted_above :: "(real list) \<Rightarrow> real \<Rightarrow> real" where
  "percentile_sorted_above sorted_values level =
   sorted_values ! ((length sorted_values) -1)"

(* The variant below would not extend the values of the percentile function in a constant way
 * beyond the last value but with the same slope at the end. We used the variant to do some
 * experiments as to the work necessary to change the percentile function to fix any proofs.
 * In separate experiments we changed the function to the maximal slope in the historic values.
 *
 * In order to replace the percentile function accordingly, rename the previous definition
 * from percentile_sorted_above to percentile_sorted_above_var and the following to
 * percentile_sorted_above. Note, not all lemmas and theorems will hold after such a change. *)
definition percentile_sorted_above_var :: "(real list) \<Rightarrow> real \<Rightarrow> real" where
  "percentile_sorted_above_var sorted_values level =
      (let  (lower_value :: real)  = sorted_values !((length sorted_values) - 2);
            (upper_value :: real)  = sorted_values ! ((length sorted_values) - 1);
            (\<alpha> :: real) = (upper_value - lower_value)/ (real (length sorted_values))
      in upper_value +  \<alpha> * (1 - upper_value))"

(* The percentile_sorted assumes that the list sorted_values is sorted. The level is assumed to be
 * a value between 0 and 1 (both incl.).  Depending on whether the level is above the threshold
 * or not, the corresponding definition from above is taken. *)
definition percentile_sorted :: "(real list) \<Rightarrow> real \<Rightarrow> real" where
  "percentile_sorted sorted_values level =
    (let (size :: real) = (real (length sorted_values))
      in (if (level > 1 - 1/2/size)
          then percentile_sorted_above sorted_values level
          else percentile_sorted_below sorted_values level))"

(* In the percentile definition first the values are sorted and then
 * the corresponding percentile_sorted definition is used.
 *) 
definition percentile :: "(real list) \<Rightarrow> real \<Rightarrow> real" where
  "percentile values level =  
    (let  (sorted :: (real list)) = sort values
      in percentile_sorted sorted level)"

(* The following two values show that the problem above the threshold is fixed with the percentile 
 * definition. (Compare the corresponding values for the percentile_java function, above.)
 *) 
(*
value "percentile [1,2,3,4,5,6,7,8,9,10] 0.95"
value "percentile [1,2,3,4,5,6,7,8,9,10] 0.96"
*)

(* The first theorem states that the percentile function is bounded. This is proved
 * in the following section.
 *)
(*****************************************************************************************)
section \<open>Boundedness\<close>
(*****************************************************************************************)
(* First we show that the percentile_sorted function is bounded for values above the threshold,
 * namely by the last element (i.e., the biggest element) of the list.
 *)
lemma percentile_sorted_max_above:
assumes "level > 1 - 1/2/(length values)"
shows "percentile_sorted values level \<le> values ! ((length values) -1)"
using sort_sort max_sorted assms(1)
by (simp add: percentile_sorted_def percentile_sorted_above_def)

(* The lemma states that the percentile for sorted values is bounded
 * by the last element (i.e., the biggest element) of the list for the 
 * case that the level is below the threshold.
 *)
lemma percentile_sorted_max_below:
assumes "0 \<le> (level :: real)"
        "level \<le> 1 - (1/2)/(length values)"
        "sorted values"
        "length values > 1"
shows "percentile_sorted values level \<le> values ! ((length values) - 1)"
using sort_sort max_sorted assms(1)
proof -
def size \<equiv> "real (length values)"
def i \<equiv> "ceiling (size * level - 0.5)"
def lower \<equiv> "(i - 0.5) / size"
def upper \<equiv> "(i + 0.5) / size" 
def lower_value \<equiv> "values ! (nat (i-1))"
def upper_value  \<equiv> "values ! (nat i)"
def diff \<equiv> "(level - lower) * size"
have f1: "level \<le> 1" using assms(2) assms(4)
     by (smt divide_nonneg_nonneg of_nat_0_le_iff)
have f2: "size > 1" using size_def assms(4) by auto
have f3: "ceiling (size * level - 0.5) \<le> size" using nat_ceiling f2 
     by (smt divide_nonneg_nonneg f1 le_ceiling_iff mult_left_le of_nat_less_of_int_iff size_def)
have f4: "diff = level * size - lower * size" using left_diff_distrib diff_def by blast
have f5: "diff = size * level - (i -0.5)" using assms(4) f4 lower_def size_def by auto
have f6: "level \<le> 1 - (1/2)/size" using assms(2) size_def by blast
have f7: "i - 0.5 = (ceiling (size * level - 0.5)) - 0.5" using i_def by blast
have f8: "diff = size * level - (ceiling (size * level - 0.5)) + 0.5" using f5 f7
         by auto
have f9: "diff \<le> 1" using ceiling_upper f8 using add_divide_distrib ceiling_le_iff divide_self_if 
          by linarith 
have f10: "diff \<ge> 0" using f8 ceiling_lower add_divide_distrib divide_self_if 
          of_int_ceiling_diff_one_le by linarith
have f11: "0 \<le> diff & diff \<le> 1" using f9 f10 by auto
have f12: "nat (i -1) \<le> nat i" by simp
have f13: "length values > 0" using assms(4) by linarith
have f14: "(length values) * level \<le> (length values) *  (1 - (1/2)/(length values))" 
           using f13 assms(2) by simp
have f15: "(1 - (1/2)/(length values)) * (length values) = (length values) - 1/2" 
           using f13 by (simp add: Groups.mult_ac(2) right_diff_distrib)
have f16: "(length values) * level \<le> (length values) - 0.5" using f14 f15
           by (simp add: mult.commute)
have f17: "(real (length values)) * level \<le> (real (length values)) - 0.5" using f16 by blast
have f18: "nat i < size" using i_def f5 using assms(2) size_def f2 nat_le_iff
          by (smt assms(4) f14 f15 f5 f10 le_ceiling_iff mult.commute nat_less_real_le 
              of_nat_0_less_iff of_nat_1 of_nat_nat real_sum_of_halves zero_less_nat_eq)
have f19: "values ! (nat (i-1)) \<le> values ! (nat i)" using f18 size_def assms(3) assms(4) sort_next
          using of_nat_less_imp_less by blast
have f20: "lower_value \<le> upper_value" using lower_value_def upper_value_def using f19 by blast
have f21: "lower_value +  diff * (upper_value - lower_value) \<le> upper_value" using f11 f20 
          linear_interpolation by auto
have f22: "percentile_sorted_below values level = lower_value + diff * (upper_value - lower_value)" 
    using percentile_sorted_below_def size_def lower_def upper_def lower_value_def upper_value_def 
          diff_def i_def by (metis (no_types, hide_lams))
have f23: "percentile_sorted values level = lower_value + diff * (upper_value - lower_value)"
     using f22 assms(2) percentile_sorted_def by simp 
have f24: "percentile_sorted values level \<le> upper_value" using f21 f23  by simp 
have f25: "i < size" using f18 by linarith
show ?thesis using f24 f25 any_smaller_sorted_last_var upper_value_def
     using assms(3) assms(4) f18 le0 of_nat_less_imp_less order_trans size_def by blast
qed

(* The lemma states that the percentile_sorted function applied to a sorted list is bounded by 
 * the largest element in the list, that is, the last element. 
 *)
lemma percentile_sorted_upper_bound:
assumes "0 \<le> (level :: real)"
        "sorted values"
        "length values > 1"
shows "percentile_sorted values level \<le> values ! ((length values) - 1)"
      using percentile_sorted_max_above percentile_sorted_max_below
      using assms(1) assms(2) assms(3) not_le by blast

(* The following two lemmas show that the value of percentile_sorted at the boundary of values is 
 * the last value in the sorted list of values, or the maximum, respectively.
 *)
lemma value_percentile_sorted_at_boundary_aux:
assumes "0 \<le> (level :: real)"
        "sorted values"
        "length values > 1"
shows   "percentile_sorted values (1 - (1/2)/(length values)) = values ! ((length values) - 1)"
proof -
      def i \<equiv> "ceiling ((real (length values)) * (1 - (1/2)/(real (length values))) - 0.5)"
      def lower \<equiv> "(i - 0.5) / (real (length values))"
      def upper \<equiv> "(i + 0.5) / (real (length values))"
      def lower_value \<equiv> "values ! (nat (i-1))"
      def upper_value \<equiv> "values ! (nat i)"
      def \<alpha> \<equiv> "((1 - (1/2)/(real (length values))) - lower) * (real (length values))"
      have f1: "i = ceiling ((real (length values)) - 
                             (real (length values)) * (1/2)/(real (length values)) - 0.5)" 
            using i_def assms by (simp add: right_diff_distrib)
      have f2: "i = (length values) - 1" using f1 add_divide_distrib assms(3) divide_self_if 
           le_ceiling_iff mult.commute nat_less_le nat_less_real_le nonzero_eq_divide_eq 
           of_int_of_nat_eq of_nat_1 of_nat_diff by auto
      have f3: "percentile_sorted values (1 - (1/2)/(length values)) =
                percentile_sorted_below (sort values) (1 - (1/2)/(length values))"
           by (simp add: assms(2) percentile_sorted_def sorted_sort_id)
      have f4: "percentile_sorted_below values (1 - (1/2)/(length values)) = 
                 lower_value +  \<alpha> * (upper_value - lower_value)"
           by (metis \<alpha>_def i_def lower_value_def lower_def percentile_sorted_below_def 
               upper_value_def)
      have f5: "\<alpha> = (1 - (1/2)/(real (length values))) * (real (length values)) - 
                     (lower * (real (length values)))" using \<alpha>_def left_diff_distrib by blast
      have f6: "(1 - (1/2)/(real (length values))) * (real (length values)) - 
                     (lower * (real (length values))) = 
                (real (length values)) - (1/2)/(real (length values)) * (real (length values)) - 
                     (lower * (real (length values)))" 
            using assms(3) by (simp add: mult.commute right_diff_distrib)
      have f7: "\<alpha> =  (real (length values)) - (1/2) - (lower * (real (length values)))"
           using f5 f6 assms(3) nat_less_real_le nonzero_eq_divide_eq of_nat_le_0_iff by auto 
      have f8: "\<alpha> = (real (length values)) - (1/2) - (i - 0.5)"
           using assms(3) f7 lower_def by auto
      have f9: "\<alpha> = 1" using f8 f2 add_divide_distrib assms(3) divide_self_if nat_less_le 
           of_int_of_nat_eq of_nat_1 of_nat_diff by linarith
      have f10: "percentile_sorted_below values (1 - (1/2)/(length values)) = upper_value" 
           using f4 f9 by simp
      show ?thesis using f10 upper_value_def f2 percentile_sorted_def by auto
qed

lemma value_percentile_sorted_at_boundary:
assumes "0 \<le> (level :: real)"
        "sorted values"
        "length values > 1"
shows   "percentile_sorted values (1 - (1/2)/(length values)) = maximum values"
using value_percentile_sorted_at_boundary_aux max_sorted_last_var assms(2) assms(3) by auto

(* The lemma show that the value of percentile_sorted at the boundary of values is the 
 * last value in the sorted list of values.
 *)
lemma value_percentile_at_boundary:
assumes "0 \<le> (level :: real)"
        "length values > 1"
shows   "percentile values (1 - (1/2)/(length values)) = maximum values"
proof -
      have f1: "percentile values (1 - (1/2)/(length values)) =
                percentile_sorted (sort values) (1 - (1/2)/(length values))" 
           using percentile_def by auto
      have f2:  "percentile values (1 - (1/2)/(length values)) =  maximum (sort values)"
           using f1 value_percentile_sorted_at_boundary assms(2) length_invariance_sort 
           sorted_sort by fastforce
      show ?thesis using f2 max_equal_max_sorted_var assms(2) by auto
qed
 
(* The theorem states that the percentile function is bounded by the maximum of the list. *)
theorem percentile_upper_bound:
assumes "0 \<le> (level :: real)"
        "length values > 1"
shows "percentile values level \<le> maximum values" 
      using length_invariance_sort percentile_sorted_upper_bound member_max percentile_def 
            max_equal_max_sorted
       by (smt One_nat_def Suc_less_eq2 assms(1) assms(2) diff_Suc_1 length_Suc_conv 
           max_sorted_last sorted_sort)

(* The corollary shows that the percentile function is bounded by its value at the boundary
 * for the interpolation.
 *)
corollary percentile_bounded_by_boundary_value:
assumes "0 \<le> (level :: real)"
        "length values > 1"
shows "percentile values level \<le> percentile values (1 - (1/2)/(length values))"
      using percentile_upper_bound value_percentile_at_boundary assms(1) assms(2) by auto

(* In the following section we see that the percentile function is weakly 
 * monotonically increasing. *)
(*****************************************************************************************)
section \<open>Monotonicity\<close>
(*****************************************************************************************)

(* The lemma states that the percentile_sorted function is monotonic for all values p1, p2
 * below the threshold.
 *)
lemma percentile_sorted_monotonic_below:
assumes   "0 \<le> p1"
          "p1 \<le> p2"
          "p2 \<le> 1 - (1/2)/(length values)"
          "sorted values"
          "length values >1"
shows "percentile_sorted values p1 \<le> percentile_sorted values p2"
proof -
def size \<equiv> "real (length values)"
def i1 \<equiv> "ceiling (size * p1 - 0.5)"
def i2 \<equiv> "ceiling (size * p2 - 0.5)"
def lower1 \<equiv> "(i1 - 0.5) / size"
def lower2 \<equiv> "(i2 - 0.5) / size"
def upper1 \<equiv> "(i1 + 0.5) / size" 
def upper2 \<equiv> "(i2 + 0.5) / size" 
def lower_value1 \<equiv> "values ! (nat (i1-1))"
def lower_value2 \<equiv> "values ! (nat (i2-1))"
def upper_value1  \<equiv> "values ! (nat i1)"
def upper_value2  \<equiv> "values ! (nat i2)"
def diff1 \<equiv> "(p1 - lower1) * size"
def diff2 \<equiv> "(p2 - lower2) * size"
have f1: "p2 \<le> 1" using assms(3) assms(5)
     by (smt divide_nonneg_nonneg of_nat_0_le_iff)
have f2: "p1 \<le>1" using f1 assms(2) by auto
have f3: "size > 1" using size_def assms(5) by auto
have f4: "ceiling (size * p1 - 0.5) \<le> ceiling (size * p2 - 0.5)" using nat_ceiling f3 assms(3)
     by (smt assms(2) ceiling_mono real_mult_le_cancel_iff2) 
have f5: "i1 \<le> i2" using i1_def i2_def f4 by blast
have f6: "diff2 = size * p2 - (i2 - 0.5)" using assms(5) f3 lower2_def size_def
     by (metis diff2_def left_diff_distrib mult.commute nonzero_eq_divide_eq not_one_less_zero)
have f7: "i2 - 0.5 = (ceiling (size * p2 - 0.5)) - 0.5" using i2_def by blast
have f8: "diff2 = size * p2 - (ceiling (size * p2 - 0.5)) + 0.5" using f6 f7 diff2_def
         by auto
have f9: "diff2 \<ge> 0" using f8 ceiling_lower add_divide_distrib divide_self_if of_int_ceiling_diff_one_le by linarith
have f10: "nat (i2 -1) \<le> nat i2" by simp
have f11: "length values > 0" using assms(5) by linarith
have f12: "(length values) * p2 \<le> (length values) *  (1 - (1/2)/(length values))" using f11 assms(3)
           by simp
have f13: "(1 - (1/2)/(length values)) * (length values) = (length values) - 1/2" 
           using f11 by (simp add: Groups.mult_ac(2) right_diff_distrib)
have f14: "nat i2 < size"  using i2_def f6 
          by (smt assms(5) ceiling_correct f12 f13 f9 mult.commute nat_eq_iff nat_less_real_le 
              of_nat_le_0_iff of_nat_nat real_sum_of_halves size_def) 
have f15: "percentile_sorted_below values p1 = lower_value1 + diff1 * (upper_value1 - lower_value1)" 
         using  percentile_sorted_below_def size_def lower1_def upper1_def lower_value1_def 
                upper_value1_def  diff1_def i1_def by metis 
have f16: "percentile_sorted_below values p2 = lower_value2 + diff2 * (upper_value2 - lower_value2)" 
         using  percentile_sorted_below_def size_def lower2_def upper2_def lower_value2_def 
                upper_value2_def  diff2_def i2_def by metis 
{assume f17_1: "i1 = i2" 
 have   f17_2: "lower1 = lower2" using f17_1 lower1_def lower2_def by blast
 have   f17_3: "upper1 = upper2" using f17_1 upper1_def upper2_def by blast
 have   f17_4: "lower_value1 = lower_value2" using f17_1 lower_value1_def lower_value2_def by blast
 have   f17_5: "upper_value1 = upper_value2" using f17_1 upper_value1_def upper_value2_def by blast
 have   f17_6: "diff1 \<le> diff2"
        using assms(2) diff1_def diff2_def f3 f17_2 by auto
 have   f17_7: "lower_value1 \<le> upper_value1" using assms(4) lower_value1_def upper_value1_def sort_next
              using assms(5) f14 f17_1 of_nat_less_imp_less size_def by blast
 then have f17_8: ?thesis using f15 f16 f17_2 f17_3 f17_4 f17_5 f17_6 f17_7 
         using assms(2) assms(3) mult_right_mono percentile_sorted_def by fastforce
}
have f17: "i1 = i2 \<Longrightarrow> ?thesis"
     using \<open>i1 = i2 \<Longrightarrow> percentile_sorted values p1 \<le> percentile_sorted values p2\<close> by blast 

{assume f18_1: "i1 < i2" 
have f18_2: "ceiling (size * p1 - 0.5) \<le> size" using nat_ceiling f3
           by (smt ceiling_unique divide_nonneg_nonneg f1 f18_1 i1_def i2_def 
               le_ceiling_iff mult_left_le)

have f18_3: "diff1 = p1 * size - lower1 * size" using left_diff_distrib diff1_def by blast
have f18_4: "size > 0" using f3 by simp
have f18_5: "diff1 = size * p1 - (i1 -0.5)" using f18_3 lower1_def f18_4
           by (simp add: mult.commute nonzero_eq_divide_eq)
have f18_6: "p1 \<le> 1 - (1/2)/size" using assms(2) assms(3) size_def by simp
have f18_7: "i1 - 0.5 = (ceiling (size * p1 - 0.5)) - 0.5" using i1_def by blast
have f18_8: "diff1 = size * p1 - (ceiling (size * p1 - 0.5)) + 0.5" using f18_5 f18_7
         by auto
have f18_9: "diff1 \<le> 1" using ceiling_upper f18_8 
           using add_divide_distrib ceiling_le_iff divide_self_if by linarith 
have f18_10: "lower_value1 \<le> upper_value1" using assms(4) lower_value1_def upper_value1_def sort_next
              using assms(5) f14 f18_1 of_nat_less_imp_less size_def
              using dual_order.strict_trans2 f11 f5 le_less_linear nat_le_0 not_less_iff_gr_or_eq 
                    zero_less_nat_eq zless_nat_conj by auto
have f18_11: "lower_value1 + diff1 * (upper_value1 - lower_value1) \<le> upper_value1" 
               using f18_9 f18_10 linear_interpolation
               by (smt mult_less_cancel_right1)
have f18_12:  "percentile_sorted_below values p1 \<le> values ! (nat i1)" 
              using f15 f18_11 upper_value1_def by auto
have f18_13: "diff2 = p2 * size - lower2 * size" using left_diff_distrib diff2_def by blast
have f18_14: "diff2 = size * p2 - (i2 -0.5)" using f18_13 lower2_def f18_4
           by (simp add: mult.commute nonzero_eq_divide_eq)
have f18_15: "i2 - 0.5 = (ceiling (size * p2 - 0.5)) - 0.5" using i2_def by blast
have f18_16: "diff2 = size * p2 - (ceiling (size * p2 - 0.5)) + 0.5" using f18_14 f18_15
         by auto
have f18_17: "diff2 \<le> 1" using ceiling_upper f18_16 
           using add_divide_distrib ceiling_le_iff divide_self_if by linarith 
have f18_18: "lower_value2 \<le> upper_value2"  using assms(4) lower_value2_def upper_value2_def sort_next
              using assms(5) f14 of_nat_less_imp_less size_def by blast
have f18_19: "lower_value2 \<le> lower_value2 + diff2 * (upper_value2 - lower_value2)" 
             using f18_17 f18_18 linear_interpolation
             using f9 mult_nonneg_nonneg by blast
have f18_20:  "values ! (nat (i2 -1)) \<le> percentile_sorted_below values p2" 
              using f16 f18_19 lower_value2_def by auto
have f18_21: "nat i1 \<le> nat (i2-1)" using f18_1 by auto
have f18_22: "values ! (nat i1) \<le> values ! (nat (i2-1))" using f18_21 sorted_index
             assms(4) f10 f14 not_le of_nat_less_imp_less size_def sorted_nth_mono by fastforce
then have f18_23: ?thesis 
             using f18_12 f18_20 f18_22
             using assms(2) assms(3) percentile_sorted_def by auto
} 
have f18: "i1 < i2 \<Longrightarrow> ?thesis"
      using \<open>i1 < i2 \<Longrightarrow> percentile_sorted values p1 \<le> percentile_sorted values p2\<close> by blast
have f19: "i1 = i2 \<or> i1 < i2" using f5 by auto
show ?thesis using f17 f18 f19 by blast
qed

(* The lemma shows that the percentile_sorted function is monotonic if the bigger confidence
 * value is above the threshold.
 *) 
lemma percentile_sorted_monotonic_above:
assumes   "0 \<le> p1"
          "p1 \<le> p2"
          "p2 > 1 - (1/2)/(length values)"
          "sorted values"
          "length values >1"
          "p2 \<le> 1"
          "p2 \<le> (2*(real n)+1)/2/(length values)"
shows "percentile_sorted values p1 \<le> percentile_sorted values p2"
proof -
have f1: "percentile_sorted values p2 =  values ! ((length values) -1)" 
          using percentile_sorted_def percentile_sorted_above_def assms(3) by simp 
have f2: "p1 \<le>  1 - (1/2)/(length values) \<or> p1 >  1 - (1/2)/(length values)" by auto
{assume f3_1: "p1\<le>1 - (1/2)/(length values)"
 def size \<equiv> "real (length values)"
 def i1 \<equiv> "ceiling (size * p1 - 0.5)"
 def lower1 \<equiv> "(i1 - 0.5) / size"
 def upper1 \<equiv> "(i1 + 0.5) / size" 
 def lower_value1 \<equiv> "values ! (nat (i1-1))"
 def upper_value1  \<equiv> "values ! (nat i1)"
 def diff1 \<equiv> "(p1 - lower1) * size"
 have f3_2: "size > 1" using size_def assms(5) by auto
 have f3_3: "ceiling (size * p1 - 0.5) \<le> ceiling (size * p2 - 0.5)" using nat_ceiling f3_2 assms(3)
     by (smt assms(2) ceiling_mono real_mult_le_cancel_iff2) 
have f3_4: "length values > 0" using assms(5) by linarith
have f3_5: "(1 - (1/2)/(length values)) * (length values) = (length values) - 1/2" 
           using f3_4 by (simp add: Groups.mult_ac(2) right_diff_distrib)
have f3_6: "percentile_sorted_below values p1 = lower_value1 + diff1 * (upper_value1 - lower_value1)" 
         using  percentile_sorted_below_def size_def lower1_def upper1_def lower_value1_def 
                upper_value1_def  diff1_def i1_def by metis 
have f3_7: "diff1 = p1 * size - lower1 * size" using left_diff_distrib diff1_def by blast
have f3_8: "diff1 = size * p1 - (ceiling (size * p1 - 0.5)) + 0.5" using f3_7 i1_def
           assms(5) lower1_def mult.commute nonzero_eq_divide_eq not_one_less_zero of_nat_eq_0_iff 
           size_def by auto
have f3_9: "diff1 \<le> 1" using ceiling_upper f3_8 
           using add_divide_distrib ceiling_le_iff divide_self_if by linarith 
have f3_10: "nat (i1 - 1) \<le> nat i1" by simp
have f3_11: "diff1 = size * p1 - (i1 - 0.5)" using diff1_def i1_def f3_8 by linarith 
have f3_12: "size > 0" using size_def assms(5) by linarith
have f3_13: "size * p1 \<le> size *  (1 - (1/2)/size)"
           by (smt f3_1 f3_2 real_mult_le_cancel_iff2 size_def)
have f3_14: "size * p1 \<le> (1 - (1/2)/size) * size" using f3_13 by (simp add: mult.commute)
have f3_15: "size * p1 - 0.5 \<le> size -1" 
            using f3_14  add_divide_distrib divide_self_if f3_5 size_def by auto 
have f3_16: "i1 \<le> size - 1" using i1_def f3_1 size_def f3_15 ceiling_monotonic ceiling_of_int 
            of_int_1 of_int_diff of_int_le_iff of_int_of_nat_eq 
            by fastforce
have f3_17: "i1 < size" using f3_16 by simp
have f3_18: "values ! (nat (i1-1)) \<le> values ! (nat i1)" using f3_10 f3_17 assms(4) sorted_index
            assms(5) f3_16 nat_eq_iff nat_less_real_le of_nat_nat size_def sort_next by auto
have f3_19: "lower_value1 \<le> upper_value1" 
            using f3_12 f3_18 assms(4) lower_value1_def upper_value1_def sorted_index
            by blast
have f3_20: "lower_value1 + diff1 * (upper_value1 - lower_value1) \<le> upper_value1" 
             using f3_9 f3_19 linear_interpolation
             by (smt mult_less_cancel_right1)
have f3_21: "percentile_sorted_below values p1 \<le> values ! (nat i1)" 
                using f3_6 f3_20 upper_value1_def by auto
have f3_22: "percentile_sorted_below values p1 \<le> values ! ((length values) - 1)"
            using assms(4) any_smaller_sorted_last_var
            assms(1) assms(5) f3_1 percentile_sorted_def percentile_sorted_max_below by auto
have f3_23: ?thesis using f1 f3_22 using percentile_sorted_def percentile_sorted_above_def
              by auto
}
have f3: "p1 \<le>  1 - (1/2)/(length values) \<Longrightarrow> 
          percentile_sorted values p1 \<le> percentile_sorted values p2"
          using \<open>p1 \<le> 1 - 1 / 2 / real (length values) \<Longrightarrow> 
          percentile_sorted values p1 \<le> percentile_sorted values p2\<close> by blast
{assume f4_1: "p1 >  1 - (1/2)/(length values)"
 have   f4_2: "percentile_sorted values p1 = values ! ((length values) - 1)" 
        using f4_1 percentile_sorted_def percentile_sorted_above_def by auto
 have   f4_3: ?thesis using f1 f4_2 by linarith
}
have  f4: "p1 >  1 - (1/2)/(length values) \<Longrightarrow> 
           percentile_sorted values p1 \<le> percentile_sorted values p2"
          using \<open>1 - 1 / 2 / real (length values) < p1 \<Longrightarrow> 
          percentile_sorted values p1 \<le> percentile_sorted values p2\<close> by blast
show ?thesis using f2 f3 f4 by blast
qed

(* The lemma states that the percentile_sorted function is monotonic 
 * within the thresholds for p1 and p2. 
 *)
lemma percentile_sorted_monotonic:
assumes   "0 \<le> p1"
          "p1 \<le> p2"
          "sorted values"
          "length values >1"
shows "percentile_sorted values p1 \<le> percentile_sorted values p2"
using percentile_sorted_monotonic_below percentile_sorted_monotonic_above
      assms percentile_sorted_def percentile_sorted_upper_bound 
      percentile_sorted_above_def by auto

(* The theorem states that the percentile function is monotonic in the confidence values.
 *)
theorem percentile_monotonic: 
assumes   "0 \<le> p1"
          "p1 \<le> p2"
          "length values > 1"
shows "percentile values p1 \<le> percentile values p2"
using percentile_sorted_monotonic percentile_def assms by auto

(* The corollary states that the percentile function has as an upper bound its value at the
 * confidence level 1.
 *)
corollary percentile_upper_bound_var:
assumes "0 \<le> level"
        "level \<le> 1"
        "length values > 1"
shows "percentile values level \<le> percentile values 1"
using percentile_monotonic assms by blast

(* The corollary states that the percentile function has as a lower bound its value at the
 * confidence level 0.
 *)
corollary percentile_lower_bound:
assumes "0 \<le> level"
        "length values > 1"
shows "percentile values 0 \<le> percentile values level"
using percentile_monotonic assms(1) assms(2) by blast

(* In the next section we show that multiplying the list of values with a non-negative scalar
 * corresponds to multiplying the percentile function with that scalar.
 *)
(*****************************************************************************************)
section \<open>Scalar multiplication property\<close> 
(*****************************************************************************************)

(* Definition of multiplying a list of real values by a scalar t *)
definition scale :: "real \<Rightarrow> real list \<Rightarrow> real list"
  where "scale t xs = map (\<lambda>x. t * x) xs"

(* The lemma states that multiplying the empty list by a scalar gives back the empty list, else
 * multiplying by a scalar corresponds to multiplying the first element and a recursive call.
 *)
lemma scale_simps [simp]:
  "scale t [] = []"
  "scale t (x # xs) = t * x # scale t xs"
  by (simp_all add: scale_def)

(* The length of a list is invariant under multiplication by a scalar.*)
lemma scale_length: "length (scale t xs) = length xs"
  by (simp add: scale_def)

(* Multiplication by a scalar works component-wise. *)
lemma scale_pos: "i < length xs \<Longrightarrow> scale t xs ! i = t * (xs ! i)"
  by (simp only: scale_def nth_map)

(* For the statements we want to show, we assume in the following that the scalar by which 
 * we multiply is positive.
 *)
context fixes t :: real assumes "t > 0"
begin

(* Scaling a list received by inserting an element at the right position corresponds to inserting
 * the scaled element at the right position of the scaled list. This is an auxiliary lemma for
 * the following lemma about the commutativity of sorting and scaling.
 *)
lemma scale_insort: "scale t (insort x xs) = insort (t * x) (scale t xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "a \<le> b \<longleftrightarrow> t * a \<le> t * b" for a b
    using \<open>t > 0\<close> by auto
  with Cons show ?case by auto
qed

(* Scaling a sorted list corresponds to sorting a scaled list. Note that for this lemma the
 * context that t > 0 is important.
 *)
lemma scale_sort: "scale t (sort xs) = sort (scale t xs)"
  by (induct xs) (simp_all add: scale_insort)

(* Corollary of the previous that the elements are the same at each position. *)
lemma scalar_sort_pos:
   assumes "((t :: real) > 0)"
           "length xs > 0"
   shows "(sort (scale t xs)) ! (i::nat) = (scale t (sort xs)) !i"
   using scale_sort assms(1) assms(2) by auto
end

(* Auxiliary lemma for the next lemma. *)
lemma scalar_pos_aux:
   shows "\<forall> (i::nat). (i < length xs) \<longrightarrow> (scale t xs) ! i = t * (xs ! i)"
   apply (induct xs)
   apply simp
   by (simp add: nth_Cons')

(* An element of a list scaled by t at a particular position is the original element at the same
 * position multiplied by the scalar.
 *)    
lemma scalar_pos:
   assumes "(i::nat) < length xs"
   shows "(scale t xs) ! i = t * (xs ! i)"
   using assms scalar_pos_aux by blast

(* The following lemma states that the percentile_sorted_below function is linear with respect
 * to the confidence level. 
 *)
lemma homogeneity_below:
   assumes t: "(t :: real) > 0"
           "0 \<le> level"
           "level \<le> 1 - (0.5/(real (length values)))"
           "length values >1"
    shows "percentile_sorted_below (scale t values) level = 
          t * percentile_sorted_below values level"
     proof -
     def tvalues \<equiv> "scale t values"
     def size     \<equiv> "length values"
     def tsize    \<equiv> "real (length tvalues)"
     def i   \<equiv> "ceiling (size * level - 0.5)"
     def ti  \<equiv> "ceiling (tsize * level - 0.5)"
     def lower_value \<equiv> "values ! (nat (i -1))"
     def tlower_value \<equiv> "tvalues ! (nat (ti -1))"
     def upper_value \<equiv> "values ! (nat i)"
     def tupper_value \<equiv> "tvalues ! (nat ti)"
     def lower \<equiv> "(i - 0.5) / size"
     def tlower \<equiv> "(ti - 0.5) / tsize"
     def upper \<equiv> "(i + 0.5) / size"
     def tupper \<equiv> "(ti + 0.5) / tsize"
     def alpha \<equiv> "(level - lower)/(upper - lower)"
     def talpha \<equiv> "(level - tlower)/(tupper - tlower)"
     def lpercentile \<equiv> "lower_value + alpha * (upper_value - lower_value) "
     def tlpercentile \<equiv> "tlower_value + talpha * (tupper_value - tlower_value)"
     have f1: "size > 0" 
          using assms(4) size_def less_trans of_nat_0_less_iff of_nat_le_0_iff by auto
     have f2: "real (length values) > 0" using assms(4) by auto
     then have "level \<le> ((real (length values)) - 0.5)/(real (length values))" 
          using assms(3)
          by (simp add: diff_divide_distrib) 
     then have "level * (real (length values)) \<le> (real (length values)) - 0.5" 
          using assms(3) f2 pos_le_divide_eq by blast
     then have "(real (length values)) * level - 0.5 \<le> (real (length values)) - 1" 
          by (simp add: add_divide_distrib mult.commute)
     then have "ceiling ((real (length values)) * level - 0.5) < real (length values)" 
             using le_ceiling_iff by linarith
     then have f3: "i < size" using i_def size_def by (simp add: less_ceiling_iff)            
     have f4: "upper - lower = (i + 0.5)/size - (i - 0.5)/size" using upper_def lower_def by blast     
     have "(i + 0.5)/size - (i - 0.5)/size = (i+0.5 - (i-0.5))/size" 
           by (metis diff_divide_distrib)
     then have "upper - lower = 1/size" using f4
           by (simp add: add_divide_distrib divide_less_cancel)
     then have f5: "alpha = (level - lower) * size" using alpha_def by simp 
     have f6: "lower_value + (level - lower) * size * (upper_value - lower_value) = 
              percentile_sorted_below values level"
          using assms(4) percentile_sorted_below_def lower_value_def upper_value_def
                 lower_def i_def size_def by (metis (no_types, hide_lams))
     have "lpercentile = lower_value + alpha * (upper_value - lower_value)" 
          using lpercentile_def by blast
     then have f7: "percentile_sorted_below values level = lpercentile" using f5 f6 by auto
     have f8: "size = tsize"
          using size_def tsize_def scale_length tvalues_def by simp
     have f9: "length values = length (scale t values)"  using scale_length by auto
     have f10: "i = ti"
         using f8 i_def ti_def by blast
     have f11: "tvalues = scale t values"
           using assms scale_sort tvalues_def by blast
     have f12: "nat i < length values" using f1 f3 nat_eq_iff nat_less_iff size_def by linarith
     then have f13: "(nat (i-1)) < length values" using nat_le_0 nat_less_iff by linarith
     have f14: "((nat (i -1))  < length values) \<longrightarrow> 
                 (scale t values) ! (nat (i-1)) = t * (values ! (nat (i-1)))" 
          using scalar_pos by auto
     have "(scale t values) ! (nat (i-1)) = t * (values ! (nat (i-1)))"
        using f13 scalar_pos by blast
     then have f15: "tlower_value = t * lower_value"
        using f10 lower_value_def tlower_value_def tvalues_def by blast
     have "(scale t values) ! (nat i) = t * (values ! (nat i))"
        using f12 scalar_pos by blast
     then have "tupper_value = t * upper_value" 
                using f10 tupper_value_def upper_value_def tvalues_def by blast
     then have f16: "tupper_value - tlower_value = t * (upper_value - lower_value)"
        using f15 by (metis (mono_tags, lifting) right_diff_distrib')
     have "alpha = talpha"
         using alpha_def talpha_def lower_def tlower_def upper_def tupper_def f8 f10 by blast
     then have "talpha * (tupper_value - tlower_value) =
                 t *  alpha * (upper_value - lower_value)"
        using f16 f8 by auto
     then have  "tlower_value + talpha * (tupper_value - tlower_value)  =
                 t *  (lower_value + alpha * (upper_value - lower_value))"
           using f15
           by (metis (no_types, hide_lams) distrib_right mult.assoc mult.commute)
     then have f17: "tlpercentile = t * lpercentile"
           using lpercentile_def tlpercentile_def by metis
     have "tlower_value + (level - tlower) * tsize * (tupper_value - tlower_value) = 
              percentile_sorted_below (scale t values) level"
          using assms(4) percentile_sorted_below_def tlower_value_def tupper_value_def
                 tlower_def ti_def tsize_def by (metis (full_types) f11)
     then have "percentile_sorted_below (scale t values) level = tlpercentile"
         using tlpercentile_def talpha_def \<open>alpha = talpha\<close> f5 f8 i_def lower_def ti_def 
         tlower_def by auto
     then show ?thesis using f7 f17 by blast
qed

(* The lemma shows the homogeneity of the percentile_sorted function. *)
lemma homogeneity_sorted:
  assumes t: "(t :: real) > 0"
           "0 \<le> level"
           "sorted values"
           "length values >1"
    shows "percentile_sorted (scale t values) level = 
          t * percentile_sorted values level"
    proof -
    def size \<equiv> "(length values)"
    def p_bar \<equiv>  "1 - (0.5/(real (length values)))"
    have f1: "(level \<le>  p_bar) \<or> (level > p_bar)" 
             by auto
    {assume f2_1: "level \<le> p_bar"
     have f2_2:  "percentile_sorted_below (scale t values) level = 
          t * percentile_sorted_below values level" using f2_1 homogeneity_below p_bar_def
          using t(1) t(2) t(4) by blast
     have ?thesis using f2_1 f2_2 percentile_sorted_def
          by (simp add: assms(4) scalar_pos scale_length p_bar_def)  
   }
   have f2: "level \<le> p_bar \<longrightarrow> ?thesis"
        using \<open>level \<le> p_bar \<Longrightarrow> 
             percentile_sorted (scale t values) level = 
             t * percentile_sorted values level\<close> by blast
   {assume f3_1: "level > p_bar"
      have f3_2: "percentile_sorted values level = values ! (size -1)" 
            using f3_1 percentile_sorted_def size_def
            percentile_sorted_above_def by (simp add: add_divide_distrib p_bar_def)
      have f3_3: "percentile_sorted (scale t values) level = 
                 (scale t values) ! (size -1)" 
            using f3_1 percentile_sorted_def size_def
            using add_divide_distrib divide_cancel_right divide_self_if scale_length 
            percentile_sorted_above_def p_bar_def
            by auto
     have f3_4:  "percentile_sorted (scale t values) level = t * (values ! (size -1))"
          using f3_3 scalar_pos size_def t(4) by auto
     have f3_5: ?thesis using f3_2 f3_4  by auto
  }
  have f3:  "level > p_bar \<longrightarrow> ?thesis"
       using \<open>p_bar < level \<Longrightarrow> 
             percentile_sorted (scale t values) level = t * percentile_sorted values level\<close> 
             by blast
  show ?thesis using f1 f2 f3 by blast
qed

(* The theorem states the homogeneity of the percentile function *)
theorem percentile_homogeneity:
  assumes t: "(t :: real) > 0"
           "0 \<le> level"
           "length values > 1"
    shows "percentile (scale t values) level = 
          t * percentile values level"
    proof -
    def sorted_values \<equiv> "sort values"
    have f1: "percentile values level = percentile_sorted sorted_values level"
         using percentile_def sorted_values_def by auto
    have f2: "percentile (scale t values) level = 
              percentile_sorted (sort (scale t values)) level" 
         using percentile_def by auto
    have f3: "percentile_sorted (sort (scale t values)) level =
              percentile_sorted (scale t (sort values)) level"
         using scale_sort t by metis
    have f4: "percentile_sorted (scale t (sort values)) level =
              t * (percentile_sorted (sort values) level)" using homogeneity_sorted 
         using length_sort sorted_sort t(1) t(2) t(3) by auto 
    show ?thesis using f1 f2 f3 f4 by (simp add: sorted_values_def)
    qed

(* The following section is about the Lipschitz property of the percentile function. Once the
 * values are sorted and the maximal jump in going from one value to the next is determined, 
 * from this a Lipschitz constant can be determined which bounds the maximal slope of the
 * percentile function.
 *)
(*****************************************************************************************)
section \<open>Lipschitz Property\<close>
(*****************************************************************************************)
(* The following lemma states that two levels which are close enough lead to the same 
 * percentile interval 
 *)
lemma upperbound_bound_equivalence:
   fixes  p1 p2 :: real and
          size n :: nat
   assumes assm_p1_p2: "p1 \<le> p2" and
           assm_size: "size > 1" and
           assm_n_lower: "0 \<le> n" and
           assm_n_upper: "n \<le> size - 1" and
           assm_p1_below: "(2*(real n)-1)/2/(real size) < p1" and
           assm_p2_above: "p2 \<le> (2*(real n)+1)/2/(real size)"
   shows "ceiling (size * p1 - 0.5) =  ceiling (size * p2 - 0.5)"
proof -
have f1: "size > 0" using assm_size by simp
have f2: "size * p1 \<le>  size * p2" using assm_p1_p2 assm_size by simp
have f3: "(2*(real n) -1)/2 = (real n) - 0.5" by simp
have f4: "(real n) - 1 < size * p1 - 0.5" using f1 f2 assm_p1_below 
     by (simp add: mult.commute pos_divide_less_eq real_sum_of_halves)
have f5: "(real n) - 1 < size * p2 -0.5" using f2 f4 by auto
have f6: "size * p2 \<le> (2* (real n) + 1)/2" using f1 assm_p2_above 
     by (simp add: mult.commute pos_le_divide_eq)
have f7: "size * p2 - 0.5 \<le> (real n)" using f6 by (simp add: real_sum_of_halves)
have f8: "size * p1 - 0.5 \<le> (real n)" using f2 f7 by linarith
have f9: "ceiling (size * p1 - 0.5) = n" using f4 f8
     by (simp add: ceiling_unique) 
have f10: "ceiling (size * p2 - 0.5) = n" using f5 f7
     by (simp add: ceiling_unique)
show ?thesis using f9 f10 by simp
qed

(* The lemma states that for levels within the same interval [i,i+1] (both below the threshold),
 * the difference is bounded by the Lipschitz condition (provided p2 is not too small) for
 * sorted lists of values.
 *)
lemma upperbound_sorted_small_step_below:
   fixes    p1 p2 max_jump max_slope :: real and
            sorted_values :: "real list" and
            n :: nat
   assumes 
           (* max_jump is the maximum of the differences in the sorted list, 
            * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
           max_jump_def: "max_jump = maximum (diff_list sorted_values)" and
           max_slope_def: "max_slope = max_jump * (real (length sorted_values))" and
           assm_p1_p2: "p1 \<le> p2" and
           assm_length_gt_1: "length sorted_values > 1" and
           assm_max_n: " n \<le> (length (sorted_values::real list)) - 1" and
           assm_p1_lower: "(2*(real n)-1)/2/(real (length sorted_values)) < p1" and
           assm_p2_upper: "p2 \<le> (2*(real n)+1)/2/(real (length sorted_values))" and
           assm_values_sorted: "sorted sorted_values" and
           assm_threshold: "p2 \<le> 1 - 0.5/(real (length sorted_values))" and
           assm_p2_big: "(real (length sorted_values)) * p2 > 0.5"
   shows "(percentile_sorted_below sorted_values p2) - 
          (percentile_sorted_below sorted_values p1) \<le> 
                 (p2 - p1) * max_slope" 
   
  proof - 
   def size \<equiv> "(length sorted_values)"
   def i \<equiv> "ceiling ((real size) * p1 - 0.5)"
   def lower \<equiv> "(i - 0.5)/(real size)"
   def upper \<equiv> "(i + 0.5)/(real size)"
   def lower_value  \<equiv> "sorted_values ! (nat (i-1))"
   def upper_value  \<equiv> "sorted_values ! (nat i)"
   def diff1 \<equiv> "(p1 - lower) * (real size)"
   def diff2 \<equiv> "(p2 - lower) * (real size)"
   have f0: "0 \<le> n" by auto
   have f1: "size > 1" using assm_length_gt_1 size_def
        by (simp add: less_imp_of_nat_less)
   have f2: "n \<le> size -1" using assm_max_n size_def
        assm_length_gt_1 diff_less nat_less_real_le of_nat_le_iff zero_less_one by linarith
   have f3: "(2*(real n)-1)/2/(real size) < p1" using assm_p1_lower size_def by blast
   have f4: "p2 \<le> (2* (real n) + 1)/2/size" using assm_p2_upper size_def by blast 
   have f5: "ceiling ((real size) * p1 - 0.5) =  ceiling ((real size) * p2 - 0.5)" 
        using assm_p1_p2 f1 f2 f3 f4 upperbound_bound_equivalence by blast
   have f6: "percentile_sorted_below sorted_values p1 = 
             lower_value +  diff1 * (upper_value - lower_value)" 
        using  i_def lower_def upper_def lower_value_def upper_value_def diff1_def
        by (metis percentile_sorted_below_def size_def)
   have f7: "i = ceiling ((real size) * p2 - 0.5)" using f5 i_def by blast
   have f8: "0.5/(real (length sorted_values)) > 0" using assm_length_gt_1 f1 size_def by auto
   have f9: "p2 < 1" using assm_threshold f8
        using of_nat_1 of_nat_less_imp_less by linarith 
   have f10: "i < size" using ceiling_less f1 f7 assm_threshold size_def
         by (metis le0 linorder_not_less of_int_of_nat_eq of_nat_le_0_iff)
   have f11: "percentile_sorted_below sorted_values p2 = 
              lower_value +  diff2 * (upper_value - lower_value)" 
        using  f10 lower_def upper_def lower_value_def upper_value_def diff2_def
        by (metis (mono_tags, hide_lams) f7 percentile_sorted_below_def size_def)
   have f12: "(percentile_sorted_below sorted_values p2) - 
              (percentile_sorted_below sorted_values p1) = 
             (diff2 - diff1) * (upper_value - lower_value)" using f6 f11
        by (simp add: left_diff_distrib)
   have f13: "0<i" using i_def assm_p2_big 
        using divide_pos_pos f9 less_one mult_eq_0_iff of_nat_eq_0_iff
        ceiling_le_iff f7 of_int_0 size_def by fastforce
   have f14: "(nat i) - 1 = nat (i - 1)" using f13
        by (simp add: nat_diff_distrib transfer_nat_int_numerals(2))
   have f15: "nat i < length sorted_values" using f10 f13 size_def by auto
   have f16: "nat i \<ge> 1" using f13 by linarith
   have f17: "member (sorted_values! (nat i) - sorted_values! ((nat i) - 1))  
                     (diff_list sorted_values)" 
             using f15 f16 assm_length_gt_1 diff_list_lemma[of concl: "sorted_values"] by blast
   have f18: "member (upper_value - lower_value) (diff_list sorted_values)" 
             using f14 f17 lower_value_def upper_value_def
        by auto
   have f19: "upper_value - lower_value \<le> max_jump" 
             using upper_value_def lower_value_def assms(8) assms(3) assms(5) maximum_lemma 
             f18 by (metis max_jump_def member.elims(2))
   have f20: "diff2 - diff1 = (p2 - p1) * size" using diff1_def diff2_def
        using f9 by (simp add: left_diff_distrib)
   have f21: "(percentile_sorted_below sorted_values p2) - 
              (percentile_sorted_below sorted_values p1) = 
              (p2 - p1) * size * (upper_value - lower_value)" using f12 f20 by simp
   have f22: "(percentile_sorted_below sorted_values p2) - 
              (percentile_sorted_below sorted_values p1) \<le>
               (p2 -p1) * size * max_jump" 
              using f1 f19 f21 assm_p1_p2 
             linordered_field_class.sign_simps(38) real_mult_le_cancel_iff2
             by (simp add: mult_left_mono)
   show ?thesis using f22 using f9 
        by (metis Groups.mult_ac(1) max_slope_def mult.commute size_def) 
qed

(* At the boundary, the percentile function is equal to the last element in the list of sorted
 * values.
 *)
lemma upperbound_boundary:
   fixes   p max_jump :: real           and
           sorted_values :: "real list"
   assumes 
           "max_jump = maximum (diff_list sorted_values)"
           "length sorted_values > 1"
           "sorted sorted_values"
           "p = 1 - 0.5/(real (length sorted_values))"
           (* "(real (length sorted_values)) * p > 0.5" *)
   shows "(percentile_sorted sorted_values p) = sorted_values ! ((length sorted_values -1))"
   proof -
   def size \<equiv> "(length sorted_values)"
   def i \<equiv> "ceiling ((real size) * p - 0.5)"
   def lower \<equiv> "(i - 0.5)/(real size)"
   def upper \<equiv> "(i + 0.5)/(real size)"
   def lower_value  \<equiv> "sorted_values ! (nat (i-1))"
   def upper_value  \<equiv> "sorted_values ! (nat i)"
   def diff \<equiv> "(p - lower) * (real size)"
   have f1: "percentile_sorted_below sorted_values p = 
              lower_value +  diff * (upper_value - lower_value)" 
        by (metis (no_types) diff_def i_def lower_value_def lower_def percentile_sorted_below_def 
            size_def upper_value_def)
   have "p \<le> 1 - (1/2/(real size))" using size_def assms(4) 
        by (simp add: add_divide_distrib real_sum_of_halves)
   then have "percentile_sorted sorted_values p = percentile_sorted_below sorted_values p" 
        using assms(4) percentile_sorted_def by (simp add: size_def)
   then have f2: "percentile_sorted sorted_values p = lower_value + diff * (upper_value - lower_value)" 
        using assms(4) f1 by auto
   have f3: "real size > 0" using size_def assms(2) 
        using le_less_trans of_nat_0_less_iff zero_le_one by linarith
   have "p = 1 - 1/2/(real size)" by (simp add: assms(4) size_def)
   then have "(real size) * p = (real size) * (1 - 1/2/(real size))" 
        using size_def assms(2) by auto
   then have "(real size) * p = (real size) - (real size) * 1/2/(real size)" 
        by (simp add: right_diff_distrib)
   then have "(real size) * p - 1/2 = (real size) - 1" using f3 by auto
   then have "i = size - 1" using f3 i_def by linarith
   then have "upper = (size - 1/2)/size" using \<open>p = 1 - 1/2/real size\<close> assms(2) upper_def by auto
   then have f4:  "p = upper"
proof -
  have f1: "\<forall>r ra rb. (r::real) / rb + ra / rb + - 1 * ((ra + r) / rb) = 0"
    by (simp add: add_divide_distrib)
  have "- 1 * (1 / 2) + real_of_int (int size) + 1 / 2 = real_of_int (int size)"
    by auto
  then have f2: "1 / 2 / real_of_int (int size) + (- 1 * (1 / 2) + real_of_int (int size)) 
      / real_of_int (int size) + - 1 * (real_of_int (int size) / real_of_int (int size)) = 0"
       using f1 by (metis (no_types))
  have f3: "upper = (- 1 * (1 / 2) + real_of_int (int size)) / real_of_int (int size)"
    by (simp add: \<open>upper = (real size - 1 / 2) / real size\<close>)
  have "real_of_int (int size) / real_of_int (int size) = 1"
    using f3 assms(2) size_def by auto
  then show ?thesis
    using f3 f2 \<open>p = 1 - 1 / 2 / real size\<close> by linarith
qed
   then have "upper - lower = 1/(real size)" using upper_def lower_def
        by (simp add: \<open>p = 1 - 1 / 2 / real size\<close> add_divide_distrib assms(2) assms(4) 
        diff_divide_distrib f3 real_sum_of_halves size_def)
   then have f5: "diff = 1" using f4 using diff_def f3 nonzero_eq_divide_eq by auto
   then have "percentile_sorted sorted_values p = upper_value" using f2 by auto
   then show ?thesis by (simp add: \<open>i = int (size - 1)\<close> size_def upper_value_def)
qed

(* The percentile function is bounded below by the zeroth element in the list of sorted values *)
lemma lowerbound_boundary:
   fixes   p max_jump :: real           and
           sorted_values :: "real list"
   assumes 
           "max_jump = maximum (diff_list sorted_values)"
           "length sorted_values > 1"
           "sorted sorted_values"
           "(real (length sorted_values)) * p \<le> 0.5"
   shows "(percentile_sorted sorted_values p) = sorted_values ! 0"
   proof -
   have "real (length sorted_values) > 0" using assms(2) by linarith
   then have f1: "p \<le> 1/2/(real (length sorted_values))" using assms(2) assms(4)
        by (simp add: add_divide_distrib mult.commute pos_le_divide_eq)
   then have "1/2/(real (length sorted_values)) + 1/2/(real (length sorted_values)) \<le> 1" 
        using assms(2) nat_less_real_le by auto
   then have "p \<le> 1 - 1/2/(real (length sorted_values))" using f1 by linarith
   then have f0: "(percentile_sorted sorted_values p) = percentile_sorted_below sorted_values p" 
        using percentile_sorted_def by auto
    def size \<equiv> "(real (length sorted_values))"
    def i \<equiv>    "ceiling (size * p - 0.5)"
    def lower \<equiv> "(i - 0.5) / size"
    def upper \<equiv>  "(i + 0.5) / size"  
    def lower_value \<equiv> "sorted_values ! (nat (i-1))"
    def upper_value \<equiv> "sorted_values ! (nat i)"
    def \<alpha> \<equiv> "(level - lower) * size"
    have "size * p - 0.5 \<le>0" using assms(4) size_def by auto
    then have f1: "(nat i) = 0" by (simp add: i_def)
    then have f2: "(nat (i-1)) = 0" by simp
    have f3: "lower_value = sorted_values ! 0" using f2 lower_value_def by auto
    have f4: "upper_value = sorted_values ! 0" using f1 upper_value_def by auto
    have f5: "lower_value + \<alpha> * (upper_value - lower_value) = sorted_values ! 0" using f3 f4 by auto
    have f6: "percentile_sorted_below sorted_values p = lower_value + \<alpha> * (upper_value - lower_value)"
        using size_def i_def lower_def upper_def lower_value_def upper_value_def \<alpha>_def
        by (simp add: f3 f4 percentile_sorted_below_def)
   then show ?thesis using f0 f5 by simp
qed

(* The Lipschitz property holds for p1, p2 close to each other *)
lemma upperbound_sorted_small_step:
   fixes    p1 p2 max_jump max_slope :: real and
            sorted_values :: "real list"
   assumes 
           (* max_jump is the maximum of the differences in the sorted list, 
            * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
           max_jump_def: "max_jump = maximum (diff_list sorted_values)" and
           max_slope_def: "max_slope = max_jump * (real (length sorted_values))" and
           assm_p1_p2: "p1 \<le> p2" and
           assm_length_gt_1: "length sorted_values > 1" and
           ex_n: "\<exists> n. n \<le> (length sorted_values) - 1 \<and>
                 (2*(real n)-1)/2/(real (length sorted_values)) < p1 \<and>
                  p2 \<le> (2*(real n)+1)/2/(real (length sorted_values))" and
           assm_values_sorted: "sorted sorted_values" 
   shows "(percentile_sorted sorted_values p2) - 
          (percentile_sorted sorted_values p1) \<le> 
               (p2 - p1) *  max_slope"
   proof -
   {assume "p2 \<le> 1 - 0.5/(real (length sorted_values)) \<and> (real (length sorted_values)) * p2 > 0.5"
    then have ?thesis using upperbound_sorted_small_step_below
          assm_length_gt_1 ex_n assm_p1_p2 assm_values_sorted 
          max_jump_def max_slope_def percentile_sorted_def by auto
   }
   have f1: "p2 \<le> 1 - 0.5/(real (length sorted_values)) \<and> (real (length sorted_values)) * p2 > 0.5
             \<longrightarrow> ?thesis"
         using \<open>p2 \<le> 1 - 5 / 10 / real (length sorted_values) \<and> 
                5 / 10 < real (length sorted_values) * p2 \<Longrightarrow> 
                percentile_sorted sorted_values p2 - percentile_sorted sorted_values p1 \<le> 
                (p2 - p1) * max_slope\<close> by blast
   (* In case 2, p2 is above the threshold. *)
   {assume a2: "p2 > 1 - 0.5/(real (length sorted_values))"
    then have"percentile_sorted sorted_values p2 = 
               sorted_values!((length sorted_values) - 1)"
           using assm_values_sorted percentile_sorted_def  percentile_sorted_above_def by auto
     (* Case 2.1, p1 is above the threshold as well. *)
     {assume "p1 > 1 - 0.5/(real (length sorted_values))"
      then have "percentile_sorted sorted_values p1 = sorted_values!((length sorted_values) - 1)"
       using assm_values_sorted percentile_sorted_def  percentile_sorted_above_def by auto
      then have ?thesis
           using \<open>percentile_sorted sorted_values p2 = sorted_values ! (length sorted_values - 1)\<close> 
                  assm_length_gt_1 assm_p1_p2 assm_values_sorted diff_list_max_non_negative 
                  max_jump_def max_slope_def by auto
      }
      have "p1 > 1 - 0.5/(real (length sorted_values)) \<longrightarrow> ?thesis"
            using \<open>1 - 5 / 10 / real (length sorted_values) < p1 \<Longrightarrow> 
                    percentile_sorted sorted_values p2 - percentile_sorted sorted_values p1 \<le> 
                  (p2 - p1) * max_slope\<close> by blast
      (* Case 2.2, p1 is below the threshold *)
      {assume "p1 \<le>  1 - 0.5/(real (length sorted_values))"

       have f1: "(percentile_sorted sorted_values 
           (1 - 0.5/(real (length sorted_values)))) =  sorted_values ! ((length sorted_values -1))" 
             using assm_length_gt_1 assm_values_sorted upperbound_boundary by blast
       have f2: "real (length sorted_values) > 1" using assm_length_gt_1 by auto
       then have "(1 - 0.5/(real (length sorted_values))) > 0" using divide_less_eq_1_pos by force
       then have f3: "(real (length sorted_values)) * (1 - 0.5/(real (length sorted_values))) > 
                      (1 - 0.5/(real (length sorted_values)))" 
             using f2 divide_le_eq_1_pos pos_divide_less_eq by auto
       have "(1 - 0.5/(real (length sorted_values))) > 0.5" 
             using assm_length_gt_1 divide_less_eq_1_pos f2 by force
       then have f4: "(real (length sorted_values)) * (1 - 0.5/(real (length sorted_values))) > 0.5"
             using f3 by linarith
       have f5: "(percentile_sorted_below sorted_values 
                    (1 - 0.5/(real (length sorted_values)))) - (percentile_sorted_below sorted_values p1)
                     \<le> 
                    ((1 - 0.5/(real (length sorted_values))) - p1) * max_slope"
            using upperbound_sorted_small_step_below[of concl:  sorted_values 
                   "(1 - 0.5/(real (length sorted_values)))" p1] assms f4 
                    \<open>1 - 5/10/real (length sorted_values) < p2\<close> 
                    \<open>p1 \<le> 1 - 5/10/real (length sorted_values)\<close> by auto
       have "(percentile_sorted sorted_values 
                    (1 - 0.5/(real (length sorted_values))))-(percentile_sorted sorted_values p1) =
             (percentile_sorted_below sorted_values 
                    (1 - 0.5/(real (length sorted_values))))-(percentile_sorted sorted_values p1)"
             using percentile_sorted_def assms
             by (simp add: add_divide_distrib real_sum_of_halves)
       then have "(percentile_sorted sorted_values 
                    (1 - 0.5/(real (length sorted_values))))-(percentile_sorted sorted_values p1) =
                  (percentile_sorted sorted_values 
                    (1 - 0.5/(real (length sorted_values))))-(percentile_sorted sorted_values p1)"
             by blast
       then have f6: "(percentile_sorted sorted_values 
                    (1 - 0.5/(real (length sorted_values)))) - (percentile_sorted sorted_values p1)
                     \<le> 
                    ((1 - 0.5/(real (length sorted_values))) - p1) * max_slope" 
                  using f5 \<open>p1 \<le> 1 - 5 / 10 / real (length sorted_values)\<close> 
                     \<open>percentile_sorted sorted_values (1 - 5/10/real (length sorted_values)) - 
                      percentile_sorted sorted_values p1 = 
                      percentile_sorted_below sorted_values (1 - 5/10/real (length sorted_values)) - 
                      percentile_sorted sorted_values p1\<close> assm_length_gt_1 assm_values_sorted 
                      assms(1) diff_list_length diff_list_non_negative less_imp_le_nat max_slope_def 
                      max_vs_first_element mult_nonneg_nonneg of_nat_0_le_iff 
                     percentile_sorted_above_def percentile_sorted_def zero_less_diff 
                  by auto
       have "(percentile_sorted sorted_values  p2) = 
             (percentile_sorted sorted_values (1 - 0.5/(real (length sorted_values))))" 
             using \<open>percentile_sorted sorted_values p2 = sorted_values ! (length sorted_values - 1)\<close>
                    f1 by auto
       then have f7: "percentile_sorted sorted_values p2 - percentile_sorted sorted_values p1 \<le> 
                  ((1 - 0.5/(real (length sorted_values))) - p1) * max_slope" 
            using f6  by auto
       have "((1 - 0.5/(real (length sorted_values))) - p1) * max_slope \<le> (p2 - p1) * max_slope"
             by (smt a2 assm_length_gt_1 assm_values_sorted assms(1) diff_list_max_non_negative 
                 max_slope_def mult_cancel_right mult_nonneg_nonneg of_nat_0_le_iff 
                 real_mult_le_cancel_iff1)
      then have "percentile_sorted sorted_values p2 - percentile_sorted sorted_values p1 \<le> 
                  (p2 - p1) * max_slope" using f7 by linarith
     }
    then have ?thesis using \<open>1 - 5 / 10 / real (length sorted_values) < p2\<close>
         add_divide_distrib assm_length_gt_1 ex_n 
         divide_le_eq_1_pos less_imp_le_nat of_nat_1 of_nat_diff of_nat_le_iff real_sum_of_halves 
         \<open>1 - 5 / 10 / real (length sorted_values) < p1 \<longrightarrow> 
         percentile_sorted sorted_values p2 - percentile_sorted sorted_values p1 \<le> 
         (p2 - p1) * max_slope\<close> by linarith
   }
   have f2: "p2 > 1 - 0.5/(real (length sorted_values)) \<longrightarrow> ?thesis"
        using \<open>1 - 5 / 10 / real (length sorted_values) < p2 \<Longrightarrow> 
            percentile_sorted sorted_values p2 - percentile_sorted sorted_values p1 \<le> 
            (p2 - p1) * max_slope\<close> by blast
   {assume "(real (length sorted_values)) * p2 \<le> 0.5"
    then have "(real (length sorted_values)) * p1 \<le> 0.5"
          by (smt assm_length_gt_1 assm_p1_p2 less_trans mult_less_cancel_left_pos of_nat_0_less_iff 
              zero_less_one)
    then have "percentile_sorted sorted_values p2 = percentile_sorted sorted_values p1"
         using lowerbound_boundary[of concl: sorted_values p1] 
               lowerbound_boundary[of concl: sorted_values p2] 
               \<open>real (length sorted_values) * p2 \<le> 5 / 10\<close> assm_length_gt_1 assm_values_sorted 
         by auto
    then have ?thesis using assms
         by (simp add: diff_list_max_non_negative)
    }
   have f3: "(real (length sorted_values)) * p2 \<le> 0.5 \<longrightarrow> ?thesis"
        using \<open>real (length sorted_values) * p2 \<le> 5 / 10 \<Longrightarrow> 
        percentile_sorted sorted_values p2 - percentile_sorted sorted_values p1 \<le> 
        (p2 - p1) * max_slope\<close> by blast
        show ?thesis using f1 f2 f3 by auto
qed

(* The following lemma states that the Lipschitz condition also holds if p1 is the left border
 * of the interval to which p2 belongs, that is, for p1 and p2 leading to different ceilings.
 * The lemma is again for p2 below the threshold.
 *)
lemma upperbound_sorted_bigger_step_below:
  fixes  p1 p2 max_jump max_slope :: real and
         sorted_values :: "real list" and
         n :: nat
  assumes 
      (* max_jump is the maximum of the differences in the sorted list, 
       * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
      max_jump_def: "max_jump = maximum (diff_list (sorted_values::real list))" and
      assm_p1_p2: "(p1::real) < (p2::real)" and
      assm_length_gt_1: "length (sorted_values::real list) > 1" and
      assm_n: "0 < (n::nat)" and
      assm_max_n: "n \<le> (length (sorted_values::real list)) - 1" and
      assm_p1_lower: "p1 = ((real 2)*(real n)-(real 1))/(real 2)/(real (length sorted_values))" and
      assm_p2_upper: "p2 \<le> ((real 2)*(real n)+(real 1))/(real 2)/(real (length sorted_values))" and
      assm_values_sorted: "sorted sorted_values" and
      assm_threshold: "p2 \<le> (real 1) - 0.5/(real (length sorted_values))" and
      max_slope_def: "max_slope = max_jump * (real (length sorted_values))"
  shows "(percentile_sorted_below sorted_values p2) - (percentile_sorted_below sorted_values p1) \<le> 
          (p2 - p1) * max_slope"
  proof -
   def size \<equiv> "real (length sorted_values)"
   def i1 \<equiv> "ceiling (size * p1 - 0.5)"
   def lower1 \<equiv> "(i1 - 0.5)/size"
   def upper1 \<equiv> "(i1 + 0.5)/size"
   def lower_value1  \<equiv> "sorted_values ! (nat (i1-1))"
   def upper_value1  \<equiv> "sorted_values ! (nat i1)"
   def i2 \<equiv> "ceiling (size * p2 - 0.5)"
   def lower2 \<equiv> "(i2 - 0.5)/size"
   def upper2 \<equiv> "(i2 + 0.5)/size"
   def lower_value2  \<equiv> "sorted_values ! (nat (i2-1))"
   def upper_value2  \<equiv> "sorted_values ! (nat i2)"
   def diff1 \<equiv> "(p1 - lower1) * size"
   def diff2 \<equiv> "(p2 - lower2) * size"
   have f1: "percentile_sorted_below sorted_values p1 = 
             lower_value1 +  diff1 * (upper_value1 - lower_value1)" 
        using  i1_def lower1_def upper1_def lower_value1_def upper_value1_def diff1_def
        by (metis percentile_sorted_below_def size_def)
   have f2: "percentile_sorted_below sorted_values p2 = 
              lower_value2 +  diff2 * (upper_value2 - lower_value2)" 
        using i2_def lower2_def upper2_def lower_value2_def upper_value2_def diff2_def
        by (metis percentile_sorted_below_def size_def)
   have f3: "size > 1" using assm_length_gt_1 size_def
        by (simp add: less_imp_of_nat_less)
   have f4: "n \<le> size - 1" using assm_max_n size_def assm_length_gt_1 diff_less nat_less_real_le 
         of_nat_le_iff zero_less_one by linarith
   have f5: "((real 2)*(real n)-(real 1))/(real 2)/size = p1" using assm_p1_lower size_def by blast
   have "p2 \<le> ((real 2)* (real n) + (real 1))/(real 2)/size" using assm_p2_upper size_def by blast 
   then have "p2 - p1 \<le> (2*(real n)+1)/2/size - (2*(real n)-1)/2/size" using f5 by auto
   then have "p2 - p1 \<le> ((2*(real n)) + 1 - ((2 * (real n)) -1))/2/size"
             by (metis diff_divide_distrib)
   then have "p2 - p1 \<le> ((2*(real n)) + 1 - (2 * (real n)) +1)/2/size" by simp
   then have f6: "(p2 - p1) * size \<le> 1" 
        using divide_self_if f3 pos_le_divide_eq by force
   have f7: "p1 * size < p2 * size" 
        using assm_p1_p2 assm_length_gt_1 f3 mult_strict_right_mono by auto
   have "p2 * size \<le> p1 * size + 1" using f6 by (simp add: left_diff_distrib)
   then have f8: "size * p2 - 0.5 \<le> size * p1 - 0.5 + 1"
        by (simp add: mult.commute)
   have f9: "size * p1 = n - 0.5" using assm_p1_lower size_def
        using add_divide_distrib divide_self_if f3 mult.commute nonzero_eq_divide_eq 
        real_sum_of_halves by auto
   have "size * p1 - 0.5 = n - 1" using f9 assm_n
        by (simp add: f3 f5 real_sum_of_halves)
   then have f10: "ceiling (size *p1 - 0.5) = size * p1 - 0.5" by simp
   then have f11: "ceiling (size * p1 - 0.5) <  ceiling (size * p2 - 0.5)" 
          using f7 assm_values_sorted assm_threshold
          by (smt ceiling_le_iff mult.commute)
   have "ceiling (size * p2 - 0.5) \<le> ceiling (size * p1 - 0.5) + 1" 
          using f8
        using ceiling_le_iff of_int_1 of_int_add by linarith
   then have "ceiling (size * p2 - 0.5) = ceiling (size * p1 - 0.5) + 1" using f11 by auto
   then have f12: "i2 = i1 + 1" using i1_def i2_def by auto
   have f13:  "0.5/(real (length sorted_values)) > 0" using assms(3)
        using size_def by auto
   have f14: "p2 < 1" using assm_threshold f13
        using of_nat_1 of_nat_less_imp_less by linarith
   have f15: "i2 < size" using ceiling_less f3 i2_def assm_threshold size_def f14
        ceiling_correct divide_nonneg_nonneg f4 f9
        using divide_pos_pos f10 f12 i1_def of_int_1 of_int_diff by linarith
   have f16: "size * p1 - ((ceiling (size *p1 - 0.5)) + 0.5) = 0" using f10 by auto 
   have f17: "size * p1 - ((i1 + 0.5)) = 0" using f16 i1_def by auto
   have f18: "diff1 = size * p1 - (i1 -0.5)" using diff1_def lower1_def
        by (metis divide_less_cancel divide_self_if f7 left_diff_distrib mult.commute 
            mult_eq_0_iff nonzero_eq_divide_eq) 
   have f19: "diff1 = size * p1 - ((size * p1 - 0.5) - 0.5)" using f10 f18 i1_def by linarith
   then have f20: "diff1 = 1"
        by (simp add: f3 f9 mult.commute nonzero_eq_divide_eq real_sum_of_halves)
   then have "percentile_sorted_below sorted_values p1 = upper_value1"
        by (simp add: f1)
   then have f21: "(percentile_sorted_below sorted_values p2) - 
              (percentile_sorted_below sorted_values p1) =  
              lower_value2 +  diff2 * (upper_value2 - lower_value2) - upper_value1" 
              by (simp add: f2)
   have f22: "0\<le>i1" using i1_def
            \<open>size * p1 - 5 / 10 = real (n - 1)\<close> f10 of_int_0_le_iff of_nat_0_le_iff by auto
   have f23: "(nat i2) - 1 = (nat (i2 - 1))"
        by (simp add: nat_diff_distrib transfer_nat_int_numerals(2))
   have f24: "member ((sorted_values! (nat i2)) - (sorted_values! ((nat i2)-1)))  
                     (diff_list sorted_values)" 
            using f22 size_def diff_list_lemma assms(10) f15 f12
            by (simp add: assm_length_gt_1)
   have "member (upper_value2 - lower_value2) (diff_list sorted_values)" 
             using f24 f23 lower_value2_def upper_value2_def assms(10) f13 by auto
   then have f25: "upper_value2 - lower_value2 \<le> max_jump" 
             using upper_value2_def lower_value2_def assms(8) assms(3) assms(5) maximum_lemma
             by (metis max_jump_def member.elims(2))
   have f26: "diff2 - diff1 =  (p2 - p1 - (lower2 - lower1)) * size" 
        using diff1_def diff2_def by (simp add: left_diff_distrib)
   then have f27: "(lower2 - lower1) * size = lower2 *size - lower1 * size" 
        using left_diff_distrib by blast
   then have "(lower2 - lower1) * size = i2 - i1" 
        using lower1_def lower2_def f3 nonzero_eq_divide_eq of_int_diff by auto
   then have f28: "(lower2 - lower1) * size = 1" using f12 by simp
   then have f29: "diff2 - diff1 = (p2 - p1)* size - 1" 
            using f26
            by (simp add: f17 f27 left_diff_distrib' linordered_field_class.sign_simps(37) 
            linordered_field_class.sign_simps(39))
   have "upper_value1 = lower_value2"
        by (simp add: f12 lower_value2_def upper_value1_def)
   then have f30:  "(percentile_sorted_below sorted_values p2) - 
              (percentile_sorted_below sorted_values p1) =   diff2 * (upper_value2 - lower_value2)"
              using f21 by auto
   have "(percentile_sorted_below sorted_values p2) - 
         (percentile_sorted_below sorted_values p1) \<le> diff2 * max_jump" using f30 f25
        by (metis add.left_neutral assm_p1_p2 diff1_def diff2_def diff_add_cancel f20 f28
           linordered_field_class.sign_simps(40) mult.left_commute mult.right_neutral 
           mult_left_mono mult_nonneg_nonneg not_le of_nat_0_le_iff order.asym size_def)
   then have "(percentile_sorted_below sorted_values p2) - 
              (percentile_sorted_below sorted_values p1) \<le>
              (p2 -p1) * size * max_jump" 
              using f20 f29 by auto
   then show ?thesis by (metis max_slope_def mult.assoc mult.commute size_def)
qed

(* Lemma for p1 and p2 belonging to different by adjacent intervals. *)
lemma upperbound_one_step:
  fixes p1 p2 max_jump max_slope :: real and
        sorted_values :: "real list" and
        n :: nat
  assumes 
    (* max_jump is the maximum of the differences in the sorted list, 
     * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
    max_jump_def: "max_jump = maximum (diff_list (sorted_values::real list))" and
    assm_p1_p2: "(p1::real) < (p2::real)" and
    assm_length_gt_1: "length (sorted_values::real list) > 1" and
    assm_n: "0 < (n::nat)" and
    assm_max_n: "n \<le> (length (sorted_values::real list)) - 1" and
    assm_p1_lower: "p1 =  ((real 2)*(real n)-(real 1))/(real 2)/(real (length sorted_values))" and
    assm_p2_upper: "p2 = ((real 2)*(real n)+(real 1))/(real 2)/(real (length sorted_values))" and
    assm_values_sorted: "sorted sorted_values" and
    assm_threshold: "p2 \<le> (real 1) - 0.5/(real (length sorted_values))" and
    max_slope_def: "max_slope = max_jump * (real (length sorted_values))"
  shows "(percentile_sorted_below sorted_values p2) - (percentile_sorted_below sorted_values p1) \<le> 
                (p2 - p1) * max_slope"  
   using upperbound_sorted_bigger_step_below assm_length_gt_1 assm_max_n assm_n
         assm_p1_lower assm_p1_p2 assm_p2_upper assm_threshold assm_values_sorted max_jump_def 
         max_slope_def by (simp add: linordered_field_class.sign_simps(24))

(* Variant of the previous lemma for values below the threshold. *)
lemma upperbound_below_one_step_var:
   fixes    max_jump max_slope :: real and
            sorted_values :: "real list" and
            p :: "nat \<Rightarrow> real" and
            n :: nat
  assumes 
    (* max_jump is the maximum of the differences in the sorted list, 
     * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
    max_jump_def: "max_jump = maximum (diff_list (sorted_values::real list))" and
    assm_length_gt_1: "length (sorted_values::real list) > 1" and
    assm_values_sorted: "sorted sorted_values" and
    max_slope_def: "max_slope = max_jump * (real (length sorted_values))" and
    level: "p = (\<lambda> m::nat. ((real 2)*(real m)-(real 1))/(real 2)/(real (length sorted_values)))"
  shows "(0 < n \<and> n \<le> (length (sorted_values)) -1 \<and>
         (p (n+1)) \<le> 1 - 0.5/(real (length sorted_values)) (* \<and>
            (length sorted_values) * (p n) > 0.5 *) )
  \<longrightarrow>
         (percentile_sorted_below sorted_values (p (n+1))) - 
         (percentile_sorted_below sorted_values (p n))        \<le> 
         (p (n+1) - (p n)) * max_slope"
 proof -
   {assume assm: "0 < n \<and> n \<le> (length (sorted_values)) -1 \<and>
           (p (n+1)) \<le> 1 - 0.5/(real (length sorted_values)) (* \<and>
           (length sorted_values) * (p n) > 0.5 *)"
   have "p (n+1) =  (\<lambda> m::nat. ((real 2)*(real m)-(real 1))/(real 2)/
                        (real (length sorted_values))) (n+1)" 
           using level by auto
   then have f1: "p (n+1) = ((real 2)*(real (n+1))-(real 1))/(real 2)/
            (real (length sorted_values))" by auto
   then have "p n = (\<lambda> m::nat. ((real 2)*(real m)-(real 1))/(real 2)/
                        (real (length sorted_values))) n" using level by auto
   then have "p n =  ((real 2)*(real n)-(real 1))/(real 2)/
            (real (length sorted_values))" by auto
   then have "p (n+1) - p n = (real 2) * ((real (n+1))  - (real n)) / (real 2)/
                        (real (length sorted_values))" using f1
         by (simp add: add_divide_distrib diff_divide_distrib)
   then have f2: "p (n+1) - p n = (real 1)/(real (length sorted_values))" by simp
   have "2*(real n)-1 < 2*(real (n+1)) -1" by simp
   then have "((real 2)*(real n)-(real 1))/(real 2)/(real (length sorted_values)) < 
              ((real 2)*(real (n+1))-(real 1))/(real 2)/(real (length sorted_values))" 
              using assm_length_gt_1 by (simp add: divide_strict_right_mono nat_less_real_le)
   then have "p n < p (n+1)" using level by blast
   then have ?thesis 
              using assm assms upperbound_one_step[of concl: "sorted_values" "p (n+1)" "p n"] 
              by auto
   }
   then show ?thesis by blast
qed
 
(* Variant of the lemma upperbound_one_step *)
lemma upperbound_one_step_var:
   fixes    max_jump max_slope :: real and
            sorted_values :: "real list" and
            p :: "nat \<Rightarrow> real" and
            n :: nat
    assumes 
           (* max_jump is the maximum of the differences in the sorted list, 
            * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
           max_jump_def: "max_jump = maximum (diff_list (sorted_values::real list))" and
           assm_length_gt_1: "length (sorted_values::real list) > 1" and
           assm_values_sorted: "sorted sorted_values" and
           max_slope_def: "max_slope = max_jump * (real (length sorted_values))" and
           level: "p = (\<lambda> m::nat. ((real 2)*(real m)-(real 1))/(real 2)/(real (length sorted_values)))"
   shows "(0 < n \<and> n \<le> (length (sorted_values)) -1) \<longrightarrow>
            (percentile_sorted sorted_values (p (n+1))) -  (percentile_sorted sorted_values (p n))
            \<le> ((p (n+1)) - (p n)) * max_slope"
   proof -
   {assume assm: "p (n+1) \<le> 1 - 0.5/(real (length sorted_values))"
   have   "((real 2)*(real n)-(real 1)) \<le> ((real 2)*(real (n+1))-(real 1))" by simp
   then have "((real 2)*(real n)-(real 1))/(real 2)/(real (length sorted_values)) \<le> 
              ((real 2)*(real (n+1))-(real 1))/(real 2)/(real (length sorted_values))" 
             using assm_length_gt_1 by (simp add: divide_right_mono)
   then have "p n \<le> p (n+1)" using level by blast
   then have "p n \<le> 1 - 0.5/(real (length sorted_values))" using assm by auto
   then have "(percentile_sorted sorted_values (p (n+1))) - 
          (percentile_sorted sorted_values (p n)) = 
             (percentile_sorted_below sorted_values (p (n+1))) - 
          (percentile_sorted_below sorted_values (p n))" using percentile_sorted_def assm by simp
   then have "(p (n+1)) \<le> 1 - 0.5/(real (length sorted_values)) \<longrightarrow> ?thesis" using 
             upperbound_below_one_step_var
             using assm_length_gt_1 assm_values_sorted level max_jump_def max_slope_def by auto
   }   
   have f1: "p (n+1) \<le> 1 - 0.5/(real (length sorted_values)) \<longrightarrow> ?thesis"
         using \<open>p (n + 1) \<le> 1 - 5 / 10 / real (length sorted_values) \<Longrightarrow> 
               p (n + 1) \<le> 1 - 5 / 10 / real (length sorted_values) \<longrightarrow> 
               0 < n \<and> n \<le> length sorted_values - 1 \<longrightarrow> 
              percentile_sorted sorted_values (p (n + 1)) - percentile_sorted sorted_values (p n) 
              \<le> (p (n + 1) - p n) * max_slope\<close> by blast
   {assume assm: "p (n+1) > 1 - 0.5/(real (length sorted_values))"
      then have f2_1: "percentile_sorted sorted_values (p (n+1)) = 
                 sorted_values!((length sorted_values)-1)"
           by (simp add: add_divide_distrib percentile_sorted_def percentile_sorted_above_def)
      have "((real 2)*(real (n+1))-(real 1))/(real 2)/(real (length sorted_values)) > 
                  1 - 0.5/(real (length sorted_values))"
           using assm level by blast
      then have "((real 2)*(real (n+1))-(real 1))/(real 2)/(real (length sorted_values)) > 
                  1 - (real 1)/(real 2)/(real (length sorted_values))" by linarith
      have "(real 2) * (real (length sorted_values))/(real 2)/(real (length sorted_values)) = 1"
            using assm_length_gt_1 less_trans nonzero_mult_divide_cancel_left of_nat_0_less_iff 
            of_nat_le_0_iff rel_simps(76) right_inverse_eq by auto
      then have f2_2: "((real 2)*(real (n+1))-(real 1))/(real 2)/(real (length sorted_values)) > 
                  ((real 2)*(real (length sorted_values)) - 
                   (real 1))/(real 2)/(real (length sorted_values))"
                  using assm_length_gt_1
           by (metis \<open>1 - real 1 / real 2 / real (length sorted_values) < 
                     (real 2 * real (n + 1) - real 1) / real 2 / real (length sorted_values)\<close> 
               diff_divide_distrib)
      have "(real (length sorted_values)) > 0" using assm_length_gt_1 by auto 
      then have f2_3: "((real 2)*(real (n+1)) - (real 1))/(real 2) > 
                 ((real 2)*(real (length sorted_values)) - (real 1))/(real 2)" 
          using f2_2 divide_less_cancel by blast
      have "real 2 > 0" by simp 
      then have "((real 2)*(real (n+1)) - (real 1)) > 
                 ((real 2)*(real (length sorted_values)) - (real 1))" 
          using divide_less_cancel using f2_3 by blast
      then have "n > (length sorted_values) -1" using assm_length_gt_1 by auto
      then have ?thesis using linorder_not_le by blast
  } 
   have f2: "p (n+1) > 1 - 0.5/(real (length sorted_values)) \<longrightarrow> ?thesis"
        using \<open>1 - 5 / 10 / real (length sorted_values) < p (n + 1) \<Longrightarrow> 0 < n \<and> 
              n \<le> length sorted_values - 1 \<longrightarrow> 
        percentile_sorted sorted_values (p (n + 1)) - percentile_sorted sorted_values (p n) \<le> 
        (p (n + 1) - p n) * max_slope\<close> by blast
   show ?thesis using f1 f2 by linarith
qed

(* Other variant *)
lemma upperbound_one_step_variant:
  fixes    max_jump max_slope :: real and
            sorted_values :: "real list" and
            p :: "nat \<Rightarrow> real"
  assumes 
    (* max_jump is the maximum of the differences in the sorted list, 
     * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
     max_jump_def: "max_jump = maximum (diff_list (sorted_values::real list))" and
     assm_length_gt_1: "length (sorted_values::real list) > 1" and
     assm_values_sorted: "sorted sorted_values" and
     max_slope_def: "max_slope = max_jump * (real (length sorted_values))" and
     level: "p = (\<lambda> m::nat. ((real 2)*(real m)-(real 1))/(real 2)/(real (length sorted_values)))"
  shows "\<forall> n :: nat.((0 < n \<and> n \<le> (length (sorted_values)) -1) 
     \<longrightarrow> (percentile_sorted sorted_values (p (n+1))) - (percentile_sorted sorted_values (p n)) \<le> 
        ((p (n+1)) - (p n)) * max_slope)"
   proof -
   fix n
   show ?thesis using upperbound_one_step_var
        using assm_length_gt_1 assm_values_sorted level max_jump_def max_slope_def by blast
qed

(* Auxiliary lemma for the next lemma *)
lemma upperbound_many_steps_aux:
   fixes    max_jump max_slope :: real and
            sorted_values :: "real list" and
            p :: "nat \<Rightarrow> real"
    assumes 
           (* max_jump is the maximum of the differences in the sorted list, 
            * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
           m_def: "m = (length sorted_values) - 1" and
           assm_m: "m > 0" and
           max_jump_def: "max_jump = maximum (diff_list (sorted_values::real list))" and
           assm_length_gt_1: "length (sorted_values::real list) > 1" and
           assm_values_sorted: "sorted sorted_values" and
           max_slope_def: "max_slope = max_jump * (real (length sorted_values))" and
           level: "p = (\<lambda> i::nat. ((real 2)*(real i)-(real 1))/(real 2)/(real (length sorted_values)))"
   shows "((percentile_sorted sorted_values (p (m+1))) - 
            (percentile_sorted sorted_values (p 1)) \<le> 
           ((p (m+1)) - (p 1)) * max_slope)"
   proof -
   {fix i
   {assume "(0 < i \<and> i \<le> (length (sorted_values)) -1 \<and>
            (p i) \<le> (real 1) - 0.5/(real (length sorted_values)) \<and>
            (real (length sorted_values)) * (p i) > 0.5)"
   then have "(percentile_sorted sorted_values (p (i+1))) - 
          (percentile_sorted sorted_values (p i)) \<le> ((p (i+1)) - (p i)) * max_slope"
          using assms upperbound_one_step_variant by blast
   }
   then have "(0 < i \<and> i \<le> (length (sorted_values)) -1 \<and>
            (p i) \<le> (real 1) - 0.5/(real (length sorted_values)) \<and>
            (real (length sorted_values)) * (p i) > 0.5) \<longrightarrow> 
          (percentile_sorted sorted_values (p (i+1))) - 
          (percentile_sorted sorted_values (p i)) \<le> ((p (i+1)) - (p i)) * max_slope "
          by blast
   }
   then have "\<forall> i :: nat.(0 < i \<and> i \<le> (length (sorted_values)) -1 
            (* (real (length sorted_values)) * (p i) > 0.5)*) \<longrightarrow>
            (percentile_sorted sorted_values (p (i+1))) - 
          (percentile_sorted sorted_values (p i)) \<le> ((p (i+1)) - (p i)) * max_slope)"
        using assms(3) assms(4) assms(5) assms(6) assms(7) upperbound_one_step_variant by auto
   then have "(\<Sum> i \<in> {1..m}. ((percentile_sorted sorted_values (p (i+1))) - 
                               (percentile_sorted sorted_values (p i)))) \<le> 
               (\<Sum> i \<in> {1..m}.((p (i+1)) - (p i)) * max_slope)" 
              using monotonicity_addition_corollary by (simp add: m_def)
   then have "(\<Sum> i \<in> {1..m}. ((percentile_sorted sorted_values (p (i+1))) - 
                               (percentile_sorted sorted_values (p i)))) \<le> 
               (\<Sum> i \<in> {1..m}.((p (i+1)) - (p i))) * max_slope" 
               using sum_distributive_corr  by auto
  then have f1: "(\<Sum> i \<in> {1..m}. ((percentile_sorted sorted_values (p (i+1))) - 
                            (percentile_sorted sorted_values (p i)))) \<le> 
           ((p (m+1)) - (p 1)) * max_slope"  using sum_of_differences by (metis (full_types))
  have "(\<Sum> i \<in> {1..m}. ((percentile_sorted sorted_values (p (i+1))) - 
                            (percentile_sorted sorted_values (p i)))) =
        ((percentile_sorted sorted_values (p (m+1))) - 
            (percentile_sorted sorted_values (p 1)))" 
        using sum_of_differences[of "\<lambda> i. percentile_sorted sorted_values (p i)"] by blast
  then show ?thesis using sum_of_differences f1 by auto
qed

(* Lemma to show the Lipschitz property for levels which are at the interval boundaries. *)
lemma  upperbound_many_step_n_k:
   fixes    max_jump max_slope :: real and
            sorted_values :: "real list" and
            m n k :: nat and
            p :: "nat \<Rightarrow> real"
    assumes 
         (* max_jump is the maximum of the differences in the sorted list, 
          * e.g., for [1, 3, 4, 9] the diff_list is [2,1,5] with maximum 5 *)
         m_def: "m = (length sorted_values) - 1" and
         assm_m: "m > 0" and
         max_jump_def: "max_jump = maximum (diff_list (sorted_values::real list))" and
         assm_length_gt_1: "length (sorted_values::real list) > 1" and
         assm_values_sorted: "sorted sorted_values" and
         max_slope_def: "max_slope = max_jump * (real (length sorted_values))" and
         level: "p = (\<lambda> i::nat.((real 2)*(real i)-(real 1))/(real 2)/(real (length sorted_values)))" 
                and
         k_prop: "k \<le> m \<and> k > 0" and
         n_prop: "n \<le> k \<and> n > 0"
   shows  "(percentile_sorted sorted_values (p (k+1))) - (percentile_sorted sorted_values (p n)) 
            \<le> ((p (k+1)) - (p n)) * max_slope"
   proof -
   {fix i:: nat
   {assume "(n \<le> i \<and> i \<le> k (* \<and> *)
            (* (p i) \<le> (real 1) - 0.5/(real (length sorted_values)) *) (* \<and>
            (real (length sorted_values)) * (p i) > 0.5 *)  )"
   then have "i \<le> (length (sorted_values)) -1" using k_prop le_trans m_def by blast
   then have "(percentile_sorted sorted_values (p (i+1))) - 
          (percentile_sorted sorted_values (p i)) \<le> max_slope"
          using assms upperbound_one_step_variant[of max_jump sorted_values max_slope] \<open>n \<le> i \<and> i \<le> k\<close> 
          sorry
   }
   then have "(n \<le> i \<and> i \<le> k) \<longrightarrow> 
          (percentile_sorted sorted_values (p (i+1))) - 
          (percentile_sorted sorted_values (p i)) \<le> max_slope"
          by blast
   }
   then have f1: "\<forall> i :: nat.(n \<le> i \<and> i \<le> k
            (* (real (length sorted_values)) * (p i) > 0.5*) ) \<longrightarrow>
            (percentile_sorted sorted_values (p (i+1))) - 
          (percentile_sorted sorted_values (p i)) \<le> max_slope"
        using assms upperbound_one_step_variant by blast
   then have f2: "(\<Sum> i \<in> {n..k}. ((percentile_sorted sorted_values (p (i+1))) - 
                            (percentile_sorted sorted_values (p i)))) \<le> 
           ((real k) - (real n) + 1) * max_slope"
    using n_prop monotonicity_addition_corollary_var 
       by (metis (no_types, lifting))
    have "k+1 > n" using assms by auto
    then have f3: "k \<ge> n" by auto

    have f4: "n\<ge>1" using n_prop by auto

   have  "(\<Sum> i \<in> {n..k}. ((percentile_sorted sorted_values (p (i+1))) - 
                            (percentile_sorted sorted_values (p i)))) = 
          (percentile_sorted sorted_values (p (k+1))) -
          (percentile_sorted sorted_values (p n))" 
            using sum_of_differences_gen_var[of n k "\<lambda>x.(percentile_sorted sorted_values (p x))"] 
            f3 f4 by blast
   then show ?thesis using f2 sorry
qed

lemma percentile_lipschitz_sorted_continuity:
   fixes p1 p2 max_jump max_slope :: real and
         sorted_values :: "real list"
   assumes 
           max_jump_def: "max_jump = maximum (diff_list sorted_values)" and
           max_slope_def: "max_slope = max_jump * (real (length sorted_values))" and
           assm_p1_p2: "p1 \<le> p2" and
           assm_p2_lt_1: "p2 \<le> 1" and
           assm_p1_gt_0: "0 \<le> p1" and
           assm_length_gt_1: "length sorted_values > 1" and
           assm_values_sorted: "sorted sorted_values" and
           (* assm_threshold: "p2 \<le> (real 1) - 0.5/(real (length sorted_values))" and *)
           level: "p = (\<lambda> i::nat. (2.0 *(real i) - 1.0)/2.0/(real (length sorted_values)))"
   shows "(percentile_sorted sorted_values p2) - 
          (percentile_sorted sorted_values p1) \<le> 
                (p2 - p1) * max_slope " 
   proof -
   def p1n \<equiv> "(nat (floor ((real (length sorted_values)) * p1 - 1.0/2.0))) + 1" 
              (* let p1n be the smallest i such that (p i) \<ge> p1 *)
   def p2n \<equiv> "(nat (floor ((real (length sorted_values)) * p2 - 1.0/2.0)))"   
              (* let p2n be the biggest i such that (p i) \<le> p2 *)
   def p1r \<equiv> "p p1n"(* "(of_real p1n) /(real (length sorted_values))" *)
   def p2r \<equiv> "p p2n" (* (of_real p2n) /(real (length sorted_values))" *)
   def m \<equiv> "(length sorted_values) -1"

   have a111: "(real (nat (floor ((real (length sorted_values)) * p2 - 1.0/2.0))))- 1.0/2.0 \<le>  
               (real (length sorted_values)) * p2"
         using floor_lower assm_length_gt_1 assm_p1_gt_0 assm_p1_p2 divide_pos_pos 
               int_distrib(4) le_floor_iff le_mult_floor nat_eq_iff nat_less_real_le 
               of_int_of_nat_eq of_nat_0_le_iff of_nat_1 of_nat_le_0_iff by auto
   have a112: "real (length sorted_values) > 0" using assm_length_gt_1 by linarith
   have a113: "(real (nat (floor ((real (length sorted_values)) * p2 - 1.0/2.0)))) - 1.0/2.0 = 
      (2.0 * (real (nat (floor ((real (length sorted_values)) * p2 - 1.0/2.0)))) - 1.0)/2.0" by auto
   then have a114: "(2.0 * (real (nat (floor ((real (length sorted_values)) * p2 - 1.0/2.0)))) - 
                     1.0)/2.0/(real (length sorted_values)) \<le> p2"
        using a111 a112 by (simp add: mult.commute pos_divide_le_eq)
   then have a11: "p2r \<le> p2" using p2r_def p2n_def level by blast
   
   have a12: "p1 \<le> p1r" sorry

    have f1: "\<forall> (x::nat). \<forall> (y::nat). x < y \<longrightarrow>
          (2.0*(real x)-1.0) < 
          (2.0*(real y)-1.0)" by auto 
    have "\<forall> (x::nat). \<forall> (y::nat). (2.0*(real x)-1.0) < 
          (2.0*(real y)-1.0) \<longrightarrow>
          (2.0*(real x)-1.0)/2.0/(real (length sorted_values)) < 
          (2.0*(real y)-1.0)/2.0/(real (length sorted_values))" using assm_length_gt_1
          by (simp add: divide_strict_right_mono nat_less_real_le) 
    then have "\<forall> (x::nat). \<forall> (y::nat). x < y \<longrightarrow> (p x) < (p y)" using f1 level
          by simp
    then have f2: "\<forall> (x::nat). \<forall> (y::nat). (p x) \<ge> (p y) \<longrightarrow> x \<ge> y" by (meson not_less)
    then have f3: "\<forall> (x::nat). \<forall> (y::nat). (p y) \<le> (p x) \<longrightarrow> y \<le> x" by auto 
    then have "\<forall> (x::nat). \<forall> (y::nat). (p x) = (p y) \<longrightarrow> x = y" using f2 assm_length_gt_1 level 
         by auto
    then have f4: "\<forall> (x::nat). \<forall> (y::nat). (p y) < (p x) \<longrightarrow> y < x" using f3 nat_less_le by auto
   {assume a1: "p1r < p2r"
    have "p p1n < p p2n" using a1 by (simp add: p1r_def p2r_def)
    then have f5: "p1n < p2n" using f4 by blast 

 
    have "(length sorted_values) * p2 - 0.5 < length sorted_values"
          by (smt assm_p2_lt_1 divide_pos_pos mult_left_le of_nat_0_le_iff)
    then have f6: "(floor ((real (length sorted_values)) * p2 - 1.0/2.0)) < (length sorted_values)"
         by linarith
    then have f00: "p1n \<le> (length sorted_values)" using p1n_def
         \<open>real (length sorted_values) * p2 - 5 / 10 < real (length sorted_values)\<close> f5 p2n_def 
          by linarith
     
    have f7: "p2 - p1 = (p2 - p2r) + (p2r - p1r) + (p1r - p1)"
        by auto
    
    have f001: "((real 2)*((floor ((real (length sorted_values)))) * p2 - 0.5) - (real 1)) \<le>
          (real 2) * (real (length sorted_values)) * p2" by simp
    then have  "(floor ((real (length sorted_values)) * p2 - 0.5)) \<le> length sorted_values"
         using \<open>real (length sorted_values) * p2 - 5 / 10 < real (length sorted_values)\<close> by linarith

    then have f03: "p2n  \<le> (length sorted_values)" using f7 by (simp add: p2n_def)

    have p2r_lower_aux: "(2*(real p2n)-1)/2/(real (length sorted_values)) \<le> p2r" 
         using p2r_def p2n_def by (simp add: level)

    have p2r_lower_add:  "(2*(real p2n)-1)/2/(real (length sorted_values)) \<noteq> p2r" using f5 sorry
    then have p2r_lower: "(2*(real p2n)-1)/2/(real (length sorted_values)) < p2r" 
         using p2r_lower_aux by auto
    have p2_upper: "p2 \<le> (2*(real p2n)+1)/2/(real (length sorted_values))" 
         using level p2r_def p2r_lower by auto
    have f1: "(percentile_sorted sorted_values p2) - (percentile_sorted sorted_values p2r) \<le> 
                    (p2 - p2r) * max_slope" 
              using upperbound_sorted_small_step[of max_jump sorted_values max_slope p2r p2]  
                    max_jump_def max_slope_def a11 assm_length_gt_1
             f03 p2r_lower p2_upper assm_values_sorted
            using level of_nat_1 of_nat_numeral order_less_irrefl p2r_def by fastforce
    have f2_11: "p2n < m" using level p2r_def p2r_lower by auto
    have f2_1: "p2n < m \<and> p2n > 0" using f2_11 f5 by auto
    have f2_3: "p1n \<ge> 0" using assm_p1_gt_0 p1n_def by blast
    then have f2_4: "p1n \<le> p2n \<and> p1n \<ge> 0" using f5 by auto
    have f2_5: "m > 0" using assm_length_gt_1 m_def by auto
    have f2: "(percentile_sorted sorted_values (p p2n)) - (percentile_sorted sorted_values (p p1n))
           \<le> ((p p2n) - (p p1n)) * max_slope" 
           using upperbound_many_step_n_k[of m sorted_values max_jump max_slope p p2n p1n] m_def 
                 f2_3 max_jump_def assm_length_gt_1 assm_values_sorted max_slope_def level f2_1 f5 
                 of_nat_1 of_nat_numeral p2r_def p2r_lower_add sorry

    have f3: "(real (length sorted_values)) * p1 \<le> 
              (ceiling ((real (length sorted_values)) * p1 + 0.5))" 
         using a12 by linarith
    have "p1 \<le> (of_real (nat (ceiling ((real (length sorted_values)) * p1 - 0.5)))) 
              /(real (length sorted_values))"
          using a1 level p2r_def p2r_lower by auto
    have p1_lower: "(2*(real p1n)-1)/2/(real (length sorted_values)) < p1" 
          using level p2r_def p2r_lower_add by auto
    have  p1r_upper: "p1r \<le> (2*(real p1n)+1)/2/(real (length sorted_values))"
          using level p2r_def p2r_lower by auto
    have f4: "(percentile_sorted sorted_values p1r) - (percentile_sorted sorted_values  p1)
            \<le> (p1r -p1) * max_slope" 
           using upperbound_sorted_small_step[of max_jump sorted_values max_slope p1 p1r] 
             a12 max_jump_def max_slope_def a1 assm_length_gt_1 a1 p1_lower p1r_upper 
             assm_values_sorted f2_1 f5 less_imp_le_nat less_trans m_def by force
    have f5: "(percentile_sorted sorted_values p2) - (percentile_sorted sorted_values p2r) + 
              (percentile_sorted sorted_values p2r) - (percentile_sorted sorted_values p1r) +
              (percentile_sorted sorted_values p1r) - (percentile_sorted sorted_values  p1) \<le> 
              (p2 - p2r) * max_slope +  (p2r - p1r) * max_slope +
              (p1r -p1) * max_slope" using f1 f2 f3 f4 p1r_def p2r_def by auto
    then have ?thesis by (simp add: linordered_field_class.sign_simps(39))
    }
    have f20: "p1r < p2r \<longrightarrow> ?thesis"
         using \<open>p1r < p2r \<Longrightarrow> percentile_sorted sorted_values p2 - 
            percentile_sorted sorted_values p1 \<le> (p2 - p1) * max_slope\<close> by auto
    {assume "\<not> (p1r < p2r)"
     then have "p1n \<ge> p2n" using level p1r_def p2r_def using f3 by auto
     then have "nat (floor ((real (length sorted_values)) * p1 - 1.0/2.0)) + 1 \<ge> 
                nat (floor ((real (length sorted_values)) * p2 - 1.0/2.0))"
          using p1n_def p2n_def by blast
     then have "(floor ((real (length sorted_values)) * p1 - 1.0/2.0)) + 1 \<ge> 
                (floor ((real (length sorted_values)) * p2 - 1.0/2.0))" 
          using  assm_p1_p2  assm_p2_lt_1 sorry
     then have "(floor ((real (length sorted_values)) * p1 + 1.0/2.0)) \<ge> 
                (floor ((real (length sorted_values)) * p2 - 1.0/2.0))" 
          using  floor_upper_plus_1 by linarith 
     then have "(real (length sorted_values)) * p1 + 1.0/2.0 + 1 \<ge> 
                ((real (length sorted_values)) * p2 - 1.0/2.0)" 
          using floor_semi_monotonic_inv by blast
     then have "(real (length sorted_values)) * p1 \<ge> (real (length sorted_values))* p2 - 2" by auto
     then have ?thesis sorry
    }
    have "\<not> (p1r < p2r) \<longrightarrow> ?thesis"  using \<open>\<not> p1r < p2r \<Longrightarrow> 
        percentile_sorted sorted_values p2 - percentile_sorted sorted_values p1 \<le> 
        (p2 - p1) * max_slope\<close> by blast
    then show ?thesis using f20 by auto
qed

(* Theorem that the percentile function is Lipschitz continuous, that is, that the values of
 *  different p-levels are limited by their difference multiplied with the Lipschitz constant
 *  that is given by the maximal slope in the sorted (historic) values.*)
theorem percentile_lipschitz_continuity:
   fixes p1 p2 max_jump max_slope :: real
   assumes 
           "max_jump = maximum (diff_list ((sort values::real list)))" and
           "max_slope = max_jump * (real (length values))" and
           "p1 \<le> p2" and
           "p2 \<le> 1" and
           "0 \<le> p1" and
           "length (values::real list) > 1" and
           level: "p = (\<lambda> i::nat. ((2.0 *(real i)- 1.0))/2.0/(real (length values)))"
   shows "(percentile values p2) - 
          (percentile values p1) \<le> 
                (p2 - p1) * max_slope" 
   proof -
   have f1: "(percentile values p2) - (percentile values p1) = 
         (percentile_sorted (sort values) p2) - (percentile_sorted (sort values) p1)"
             using percentile_def assms by auto
   have  "length (sort values) = length values" by auto
   then have f2: "max_slope = max_jump * (real (length (sort values)))" using assms(2) by auto 
   have "sorted (sort values)" by auto
   then show ?thesis using f1 f2 
        percentile_lipschitz_sorted_continuity[of max_jump "sort values" max_slope p1 p2] 
        length_invariance_sort assms
        by auto
qed
end
