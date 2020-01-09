text \<open> Version 0.5, last changed 2019-03-20 
  (C) fovefi ltd, www.fovefi.co 
    (author: Manfred Kerber [make@fovefi.co] based on Percentile.thy in foveSIMM by Lukas Bulwahn)
  Dually licenced under
  Creative Commons Attribution (CC-BY) 4.0 [https://creativecommons.org/licenses/by/4.0/]
  ISC License (1-clause BSD License)       [https://www.isc.org/downloads/software-support-policy/isc-license/]
  See LICENSE files for details.
  (Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
 
  In this file, an abstract definition of the  percentile function in Isabelle is given.
  The percentile function is defined as a linear approximation between points defined for a partial 
  function defined for finitely many elements. 
 
 It is perhaps best been explained with the help of an example.
  Let us assume that you have a list of 5 real numbers xs = [8, 10, 1, 4, 5] in order to compute a 
  particular percentile, e.g., of 0.75, first you order the list and get sxs = [1, 4, 5, 8, 10]. Then you put 5 values
  (length of the list) on the unit interval [0;1] at equal distances of 1/5, staying away 1/10 from
  the left and right border plus values at 0 and 1, that is, you get [0, 0.1, 0.3, 0.5, 0.7, 0.9, 1]. 
  For the inner values you take as percentile the corresponding value in the sorted list, that is, 
  the percentile at 0.1 is  1, at 0.3 is 4, at 0.5 is 5, at 0.7 is 8, and at 0.9 is 10. 
  For values 0 and 1 you take a left and right extrapolation, resp. The extrapolation is based on 
  extensions with the same slope to the left and right in the next intervals.
  For values between any two values not defined this way, the linear interpolation is taken. E.g. for 0.75
  - between a = 0.7 and b = 0.9, we take as f(a) + (f(b) - f(a))/(b - a) * (x - a).
  In the example percentile at 0.75 it is 8 + (10 - 8)/(0.9 - 0.7) * (0.75 - 0.7)  = 8 + 2/0.2 * 0.05,
  that is, 8 + 10 * 0.05 = 8.5.
 
  Note that in this file an abstract definition and properties of the percentile
  function are given. The percentile function is not computational. A corresponding computational
  version is given in the sister document Percentile_Code.thy.
 
  The documents is structured as follows, first in a section preliminaries some properties are given 
  that are needed later. In the next section points are put on the unit interval in the way described
  above. The following section contains an abstract definition of the percentile function. Finally
  some important properties are proved: 
  - boundedness (upper and lower bound)
  - monotonicity
  - linearity
  - Lipschitz continuity
 \<close>

theory Percentile
   imports Complex_Main Linear_Interpolation

begin

section \<open>Preliminaries\<close>

subsection \<open>Addition to List\<close>
text \<open> Sorting the empty list results in the empty list.\<close>
lemma sort_eq_Nil_iff:
  "sort xs = [] \<longleftrightarrow> xs = []"
by (cases xs) auto

text \<open> Every element in a sorted list is smaller than or equal to the last element. \<close>
lemma sorted_leq_last:
  assumes "sorted xs"
  assumes "x \<in> set xs"
  shows "x \<le> last xs"
using assms
  by (metis in_set_conv_decomp_last last.simps last_append last_in_set linorder_not_less 
            list.simps(3) order_less_irrefl sorted.simps(2) sorted_append)

section \<open>From list of reals to @{typ "real \<Rightarrow> real option"}\<close>

text \<open> In order to define the percentile of a list of real numbers, the unit interval is sub-divided by
  putting a number of equidistantly distributed points on the line. The first point is put half
  a distance from 0, the last half a distance from 1. The distance is 1/(length list).  
  real option means that the result is a partial function, that is, for a given value it will return either
  None (if the value is not in the domain) or Some with the position (if it is in the domain). \<close>
definition equidistant_points_on_unit_interval_of :: "real list \<Rightarrow> real \<Rightarrow> real option"
where
  "equidistant_points_on_unit_interval_of ys = (let xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]
     in map_of (zip xs ys))"

text \<open> The extrapolation to below is done by taking the same slope as between the first two points 
  and extending it to 0. E.g., for the example below a list [3,1,4,8,6], the extrapolation is 
  taken by  computing the slope as (3-1)/(0.3 - 0.1) = 10 and computing the value of the straight line
  f(x) = f(x_0) + slope*(x-x_0) at position 0, that is f(0) = 1 + 10 * (0 - 0.1) = 1 - 0.1 * 10 = 0. \<close>
definition extrapolation_0 :: "real list \<Rightarrow> real"
  where
  "extrapolation_0 ys = ys!0 - (ys!1 - ys!0)/2.0"

text \<open> It is shown that the extrapolation to the left is smaller than or equal to the smallest 
       element in the list. \<close>
lemma extrapolation_0_small:
  assumes "length ys \<ge> 2"
  assumes "sorted ys"
  shows "extrapolation_0 ys \<le> ys!0"
proof -
  have "ys!0 \<le> ys!1" using assms using sorted_nth_mono by fastforce 
  then have "ys!0 - (ys!1 - ys!0)/2.0 \<le> ys!0" by simp 
  then show ?thesis using extrapolation_0_def by auto
qed   

text \<open> The extrapolation to above is done by taking the same slope as between the last two points 
  and extending it to 1. E.g., for the example below a list [3,1,4,8,6], the extrapolation is 
  taken by  computing the slope as (8-6)/(0.9 - 0.7) = 10 and computing the value of the straight line
  f(x) = f(x_4) + slope*(x-x_4) at position 1, that is f(1) = 8 + 10 * (1 - 0.9) = 8 + 10 * 0.1 = 9. \<close>
definition extrapolation_1 :: "real list \<Rightarrow> real"
  where
  "extrapolation_1 ys =
    (let (l:: nat) = (length ys)
     in
          ys!(l-2) + (ys!(l-1) - ys!(l-2))* 3.0/2.0)"

value "extrapolation_1 [1, 3, 4, 6, 8]"

value "(equidistant_points_on_unit_interval_of [1/4, 1/2, 3/4]) (1/2)"

text \<open> In addition to the equidistant points in the restricted version of the Percentile function, here we also
       define the function for the end points of the unit interval, that is, for 0 and 1. We do this
       with the two extrapolated values and extend the real option type accordingly. \<close>
definition extended_points_on_unit_interval_of :: "real list \<Rightarrow> real \<Rightarrow> real option"
where
  "extended_points_on_unit_interval_of ys =  (equidistant_points_on_unit_interval_of ys) 
        (0 \<mapsto> (extrapolation_0 ys), 1 \<mapsto> (extrapolation_1 ys))"

(*map_of (zip (0#xs@[1]) ((extrapolation_0 ys)#ys@[extrapolation_1 ys])))"*)


text \<open> Some examples to exemplify the definition \<close>
value "(\<lambda>ys. map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]) []"
value "(\<lambda>ys. map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]) [(1 :: real)]"
value "(\<lambda>ys. map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]) [1, (2 :: real)]"
value "(\<lambda>ys. map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]) [1,2, (3 :: real)]"
value "(\<lambda>ys. map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]) [1,2,3, (4 :: real)]"

text \<open> The number of equidistant points is finite.\<close>
lemma finite_equidistant_points_on_unit_interval_of [simp]:
  "finite (dom (equidistant_points_on_unit_interval_of ys))"
unfolding equidistant_points_on_unit_interval_of_def by simp

text \<open> The number of extended points is finite.\<close>
lemma finite_extended_points_on_unit_interval_of [simp]:
  "finite (dom (extended_points_on_unit_interval_of ys))"
unfolding extended_points_on_unit_interval_of_def by simp


value "zip [1::nat,2,3] [3::nat,4,5]"
value "zip [1::nat,2] [3::nat,4] @ [(3,5)]" 

text \<open> Auxiliary lemma to extend zip of two lists.\<close>
lemma zip_lemma_aux:
  shows "zip (x#xs) (y#ys) = (x,y)#(zip xs ys)" by simp


text \<open> Lemma how to zip two non-empty lists. E.g. [1,2,3] and [4,5,6] as (1,2) cons'd 
       with zip of [2,3] and [5,6].\<close>
lemma zip_lemma:
  assumes "length ys > 0"
  shows "zip (x#xs) ys = (x,ys!0)#(zip xs (tl ys))" using zip_lemma_aux 
  by (metis assms(1) list.exhaust list.sel(3) list.size(3) not_less_zero nth_Cons_0)

text \<open> The natural numbers from 0 to n are 0 plus the numbers from 1 to n].\<close>
lemma interval_ext:
  shows "\<forall>n::nat. [0..n] = 0 # [1..n]"
  by (simp add: upto_rec1)


text \<open> In a well-ordered set, {a..<b} is the set of all elements between a and b (a included, b excluded) 
  If this set is non-empty and finite, a is its minimum. \<close>
lemma Min_intv:
  assumes "{a..<b} \<noteq> {}"
  assumes "finite {a..<b}"
  shows "Min {a..<b} = a"
using assms by (auto intro: Min_eqI)

text \<open> For a set {a..<b} of natural numbers is the set of all elements between a and b 
 (a included, b excluded). If that set is non-empty and finite, b-1 is its maximum. \<close>
lemma Max_intv:
  assumes "{a..<b} \<noteq> {}"
  shows "Max {a..<(b :: nat)} = b - 1"
using assms by (auto intro!: Max_eqI)

text \<open> The values of equidistant_points_on_unit_interval_of are exactly the values given by its
  definition and none more. \<close>
lemma dom_equidistant_points_on_unit_interval_of:
  "dom (equidistant_points_on_unit_interval_of ys) = (\<lambda>x. (1 / length ys) * (x + 0.5)) ` {0..<length ys}"
proof -
  have "distinct (map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys])"
    by (auto intro!: inj_onI simp add: distinct_map )
  show ?thesis
    unfolding equidistant_points_on_unit_interval_of_def by (auto simp add: \<open>distinct _\<close>)
qed


text \<open> The values of extended_points_on_unit_interval_of are exactly the values given by its
  definition, that is, the ones of equidistant_points_on_unit_interval_of plus 0 and 1. \<close>
lemma dom_extended_points_on_unit_interval_of:
  "dom (extended_points_on_unit_interval_of ys) = {0}\<union>((\<lambda>x. (1 / length ys) * (x + 0.5)) ` {0..<length ys})\<union> {1}"
proof -
  have "distinct (map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys])"
    by (auto intro!: inj_onI simp add: distinct_map )
  show ?thesis
    unfolding extended_points_on_unit_interval_of_def
    using dom_equidistant_points_on_unit_interval_of by auto 
qed


text \<open> The minimal value of equidistant_points_on_unit_interval_of is at half the distance from 0. \<close>
lemma Min_equidistant_points_on_unit_interval_of:
  assumes "ys \<noteq> []"
  shows "Min (dom (equidistant_points_on_unit_interval_of ys)) = 1 / (2 * length ys)"
proof -
  have "incseq (\<lambda>x. (1 / length ys) * (x + 0.5))"
    by (auto simp add: incseq_def divide_right_mono)
  from this dom_equidistant_points_on_unit_interval_of show ?thesis
    using \<open>ys \<noteq> []\<close> \<open>incseq _\<close> by (auto simp add: mono_Min_commute[symmetric] Min_intv)
qed


text \<open> The minimal value of extended_points_on_unit_interval_of is 0. \<close>
lemma Min_extended_points_on_unit_interval_of:
  assumes "ys \<noteq> []"
  shows "Min (dom (extended_points_on_unit_interval_of ys)) = 0"
 using extended_points_on_unit_interval_of_def Min_equidistant_points_on_unit_interval_of
  by (smt Min_in Min_le Un_insert_left assms dom_equidistant_points_on_unit_interval_of 
       dom_extended_points_on_unit_interval_of dom_fun_upd empty_not_insert 
       finite_equidistant_points_on_unit_interval_of finite_extended_points_on_unit_interval_of 
       insertCI insertE length_greater_0_conv nat_0_less_mult_iff of_nat_0_less_iff option.simps(3) 
       sup_bot.left_neutral zero_less_divide_1_iff zero_less_numeral) 


text \<open> The maximal value of equidistant_points_on_unit_interval_of is at half the distance from 1. \<close>
lemma Max_equidistant_points_on_unit_interval_of:
  assumes "ys \<noteq> []"
  shows "Max (dom (equidistant_points_on_unit_interval_of ys)) = 1 - 1 / (2 * length ys)"
proof -
  have "incseq (\<lambda>x. (1 / length ys) * (x + 0.5))"
    by (auto simp add: incseq_def divide_right_mono)
  from this dom_equidistant_points_on_unit_interval_of show ?thesis
    using \<open>ys \<noteq> []\<close> \<open>incseq _\<close> apply (auto simp add: mono_Max_commute[symmetric] Max_intv)
    apply (subst of_nat_diff)
     defer
     apply simp
    apply (simp add: diff_divide_distrib)
    using not_less by fastforce
qed

text \<open> The maximal value of equidistant_points_on_unit_interval_of is 1. \<close>
lemma Max_extended_points_on_unit_interval_of:
  assumes "ys \<noteq> []"
  shows "Max (dom (extended_points_on_unit_interval_of ys)) = 1"
proof -
  have "(dom (extended_points_on_unit_interval_of ys)) = (dom  (equidistant_points_on_unit_interval_of ys)) \<union> {0,1}"
    using dom_equidistant_points_on_unit_interval_of dom_extended_points_on_unit_interval_of by auto
  then have "Max (dom (extended_points_on_unit_interval_of ys)) = Max (dom  (equidistant_points_on_unit_interval_of ys) \<union> {0,1})"
    by auto
  have "Max (dom  (equidistant_points_on_unit_interval_of ys) \<union> {0,1}) = max (Max (dom  (equidistant_points_on_unit_interval_of ys))) (Max {0,1})"
    by (smt Max.union Max_equidistant_points_on_unit_interval_of Max_insert Max_singleton assms 
        empty_subsetI finite.emptyI finite.insertI finite_equidistant_points_on_unit_interval_of 
        insert_not_empty length_greater_0_conv nat_0_less_mult_iff of_nat_0_less_iff 
        sup_absorb2 sup_max zero_less_divide_1_iff zero_less_numeral) 
  then show ?thesis
    by (smt Max_equidistant_points_on_unit_interval_of Max_insert Max_singleton 
       \<open>Max (dom (extended_points_on_unit_interval_of ys)) = Max (dom (equidistant_points_on_unit_interval_of ys) \<union> {0, 1})\<close> 
       assms finite.emptyI finite.insertI insert_not_empty length_greater_0_conv max_0_1(1) 
       nat_0_less_mult_iff of_nat_0_less_iff zero_less_divide_1_iff zero_less_numeral)
qed

text \<open> The following lemma states that the points where the function given by 
  equidistant_points_on_unit_interval_of is defined, are all in the interval between 
  1/(2 * length ys) and 1 - 1/(2 * length ys), that is, 
  the minimal and maximal value as proved in the two lemmas above. \<close>
lemma defined_interval_of_equidistant_points_on_unit_interval_of:
  assumes "ys \<noteq> []"
  shows "defined_interval_of (equidistant_points_on_unit_interval_of ys) = {1 / (2 * length ys)..1 - 1 / (2 * length ys)}"
using assms unfolding defined_interval_of_def
apply (simp add:  Min_equidistant_points_on_unit_interval_of Max_equidistant_points_on_unit_interval_of)
proof -
  assume "ys \<noteq> []"
  then have "[] \<noteq> [0..<length ys]"
    by (metis length_greater_0_conv length_map map_nth)
  then have "\<exists>r. r \<in> {r. map_of (zip (map (\<lambda>n. 1 / real (length ys) * (real n + 5 / 10)) [0..<length ys]) ys) r \<noteq> None}"
    by fastforce
  then show "equidistant_points_on_unit_interval_of ys = Map.empty \<longrightarrow> \<not> 1 \<le> real (length ys)"
    using equidistant_points_on_unit_interval_of_def by force
qed


text \<open> The following lemma states that extended_points_on_unit_interval_of is defined for the full interval [0,1]. \<close>
lemma defined_interval_of_extended_points_on_unit_interval_of:
  assumes "ys \<noteq> []"
  shows "defined_interval_of (extended_points_on_unit_interval_of ys) = {0::real..1}"
  using Max_extended_points_on_unit_interval_of Min_extended_points_on_unit_interval_of assms defined_interval_of_def extended_points_on_unit_interval_of_def by auto


text \<open> On the points where (equidistant_points_on_unit_interval_of ys) is defined, the resulting values are the ys. \<close>
lemma ran_equidistant_points_on_unit_interval_of:
  "ran (equidistant_points_on_unit_interval_of ys) = set ys"
proof -
  have "length (map (\<lambda>x. (real x + 1 / 2) / real (length ys)) [0..<length ys]) = length ys"
    by simp
  have distinct: "distinct (map (\<lambda>x. (real x + 1 / 2) / real (length ys)) [0..<length ys])"
    by (auto simp add: distinct_map intro!: inj_onI)
  show ?thesis
    unfolding equidistant_points_on_unit_interval_of_def
    apply simp
    apply (rule ran_map_of_zip)
    apply (auto simp add: distinct)
    done
qed

text \<open> The range of an extension by one value is the range of the original function extended by the one value. \<close>
lemma ran_extension:
  "\<forall>f. \<forall> x y::real. x\<notin> dom f \<longrightarrow> ran (f(x \<mapsto> y)) = {y} \<union> (ran f)"
  by auto


text \<open> The range of an extension by two values is the range of the original function extended by the two values. \<close>
lemma ran_extension2:
  "\<forall>f. \<forall> x y z v::real. x\<notin> dom f \<and> z \<notin> dom f \<and> x \<noteq> z \<longrightarrow> ran (f(x \<mapsto> y, z \<mapsto> v)) = {y} \<union> {v} \<union> (ran f)"
  using domIff by auto

value "0#(map (\<lambda>x. (real x + 1 / 2) / real (length ys)) [0..<length [1,2,3]])"


text \<open> The range of the extended points on the unit interval is the set of points plus the two extrapolations. \<close>
lemma ran_extended_points_on_unit_interval_of:
  "ran (extended_points_on_unit_interval_of ys) = {extrapolation_0 ys} \<union> {extrapolation_1 ys} \<union> (set ys)"
proof -
  have "length (map (\<lambda>x. (real x + 1 / 2) / real (length ys)) [0..<length ys]) = length ys"
    by simp
  have distinct: "distinct (map (\<lambda>x. (real x + 1 / 2) / real (length ys)) [0..<length ys])"
    by (auto simp add: distinct_map intro!: inj_onI)
  have "(0 \<notin>  set (map (\<lambda>x. (real x + 1 / 2) / real (length ys)) [0..<length ys]))"  by auto
  then have notin0: "0 \<notin> dom (equidistant_points_on_unit_interval_of ys)" using equidistant_points_on_unit_interval_of_def
    by simp
  have "\<forall>x. x < length ys \<longrightarrow> (real x + 1 / 2) / real (length ys) < 1" by (simp add: divide_less_eq_1)
  then have "(1 \<notin>  set (map (\<lambda>x. (real x + 1 / 2) / real (length ys)) [0..<length ys]))" 
    by (smt atLeastLessThan_iff in_set_conv_nth length_map nth_map set_upt)
  then have "1 \<notin> dom (equidistant_points_on_unit_interval_of ys)" using equidistant_points_on_unit_interval_of_def
    by simp
  then have "ran (extended_points_on_unit_interval_of ys) =  {extrapolation_0 ys} \<union> {extrapolation_1 ys} \<union> ran (equidistant_points_on_unit_interval_of ys)"
        using extended_points_on_unit_interval_of_def ran_extension2 notin0
        by (simp add: ran_extension2)
  then show ?thesis by (simp add: ran_equidistant_points_on_unit_interval_of)
qed

text \<open>The sortedness of a list is preserved by multiplying each element by the same positive number.\<close>
lemma sorted_map:
  assumes "(c::real) > 0"
  assumes "sorted ys"
  shows "sorted (map (\<lambda> z. c*z) ys)"
  by (smt assms(1) assms(2) dual_order.strict_trans length_map mult_left_mono nth_map sorted_iff_nth_mono_less)

text \<open>For a list with no two same elements the n-th element of a first list applied to the zip of
      a first list and a second list is defined and equal to the n-th element of the second list.\<close>
lemma zip_some:
  assumes "length xs = length ys"
  assumes "\<forall> n < length xs. \<forall> m < length xs. xs!n = xs!m \<longrightarrow> n = m"
  shows "(\<forall>n < length xs. (map_of (zip xs ys) (xs!n)) = Some (ys!n))" 
  by (metis assms(1) assms(2) distinct_conv_nth map_of_zip_nth)

text \<open>The n-th element of equidistant_points_on_unit_interval_of is the n-th element of the original list.\<close>
lemma equidistant_nth:
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
  assumes "\<exists>y. ((equidistant_points_on_unit_interval_of ys) x) = (Some y)"
  assumes "(n::nat) < length ys"
  assumes "\<forall> n < length xs. \<forall> m < length xs. (xs)!n = (xs)!m \<longrightarrow> n = m"
  shows "the ((equidistant_points_on_unit_interval_of ys) (xs!n)) = ys!n"
proof -
  have a: "length xs = length ys" by (simp add: assms(3))
  have b:  "\<forall> n < length xs. \<forall> m < length xs. xs!n = xs!m \<longrightarrow> n = m" by (simp add: assms(6))
  have "the ((equidistant_points_on_unit_interval_of ys) x) = the (map_of (zip xs ys) x)"
    by (simp add: assms(3) equidistant_points_on_unit_interval_of_def)
  then have "the (map_of (zip xs ys) (xs!n)) = the (map_of (zip xs ys) (xs!n))"  by blast
  have "(map_of (zip xs ys) (xs!n)) = Some (ys!n)"
    by (simp add: a assms(5) b zip_some)
  then show ?thesis using assms
    by (metis equidistant_points_on_unit_interval_of_def option.sel)
qed

text \<open>The partial function equidistant_points_on_unit_interval_of is linear for the defined points.\<close>
lemma equidistant_linear_some:
  assumes "(c::real) > 0"
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
  assumes "\<exists>y. ((equidistant_points_on_unit_interval_of ys) x) = (Some y)"
  shows   "(equidistant_points_on_unit_interval_of (map (\<lambda> z. c*z) ys)) x = 
           map_option (\<lambda>z. c * z) ((equidistant_points_on_unit_interval_of ys) x)"
proof -
  have "x \<in> set xs" using assms equidistant_points_on_unit_interval_of_def
    by (metis domIff dom_equidistant_points_on_unit_interval_of option.simps(3) set_map set_upt)
  then have "\<exists> n. n < length ys \<and> x = xs!n" using assms(4) by auto 
  then obtain n where " n < length ys \<and> x = xs!n" by blast
  have "length ys > 0" using assms(3) by auto
  have "\<forall> m < length xs. xs!m = (1 / length ys) * (m + 0.5)" by (simp add: assms(4))
  then have "\<forall> m < length xs. \<forall> p < length xs. m < p \<longrightarrow> (xs)!m < (xs)!p" using assms(4) 
    by (smt \<open>0 < length ys\<close> less_imp_of_nat_less mult_less_cancel_left_pos of_nat_0_less_iff zero_less_divide_1_iff)
  then have "\<forall> m < length xs. \<forall> p < length xs. (xs)!m = (xs)!p \<longrightarrow> m = p" by (smt nat_neq_iff)
  then have "the ((equidistant_points_on_unit_interval_of ys) (xs!n)) = ys!n" using assms
    using \<open>\<forall>m<length xs. \<forall>p<length xs. xs ! m = xs ! p \<longrightarrow> m = p\<close> equidistant_nth
    by (meson \<open>n < length ys \<and> x = xs ! n\<close>)
  then have "(map_of (zip xs ys)) (xs!n) = Some (ys!n)" using assms
    by (metis (no_types, lifting) \<open>\<forall>m<length xs. \<forall>p<length xs. xs ! m = xs ! p \<longrightarrow> m = p\<close> 
        \<open>n < length ys \<and> x = xs ! n\<close> length_map map_nth zip_some)
  have "(map_of (zip xs (map (\<lambda> z. c*z) ys))) (xs!n) = Some (c* (ys!n))" using assms
    by (smt \<open>\<forall>m<length xs. \<forall>p<length xs. xs ! m = xs ! p \<longrightarrow> m = p\<close> \<open>n < length ys \<and> x = xs ! n\<close> 
        length_map map_nth nth_map zip_some)
  then have a: "(((equidistant_points_on_unit_interval_of (map (\<lambda> z. c*z) ys)) (xs!n)) = Some (c*(ys!n)))"
    by (simp add: assms(4) equidistant_points_on_unit_interval_of_def) 
  have b: "((equidistant_points_on_unit_interval_of ys) x) = Some (ys!n)"
    using \<open>n < length ys \<and> x = xs ! n\<close> 
          \<open>the (equidistant_points_on_unit_interval_of ys (xs ! n)) = ys ! n\<close> assms(5) by auto
  have "Some (c*(ys!n)) = map_option (\<lambda>z. c * z) (Some (ys!n))" by auto
  then show ?thesis using a \<open>n < length ys \<and> x = xs ! n\<close> b by presburger
qed

text \<open>The partial function equidistant_points_on_unit_interval_of is linear for undefined points.\<close>
lemma equidistant_linear_none:
  assumes "(c::real) > 0"
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
  assumes "(equidistant_points_on_unit_interval_of ys) x = None"
  shows   "(equidistant_points_on_unit_interval_of (map (\<lambda> z. c*z) ys)) x = 
           map_option (\<lambda>z. c * z) ((equidistant_points_on_unit_interval_of ys) x)"
  by (metis (no_types, lifting) assms(5) diff_zero equidistant_points_on_unit_interval_of_def 
      length_map length_upt map_eq_conv map_of_zip_is_None map_option_is_None)

text \<open>The partial function equidistant_points_on_unit_interval_of is linear.\<close>
lemma equidistant_linear:
  assumes "(c::real) > 0"
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
  shows   "map_option (\<lambda>z. c * z) ((equidistant_points_on_unit_interval_of ys) x) = 
           (equidistant_points_on_unit_interval_of (map (\<lambda> z. c*z) ys)) x"
proof - 
  have  "(\<exists>y. ((equidistant_points_on_unit_interval_of ys) x) = (Some y)) \<or> 
          (equidistant_points_on_unit_interval_of ys) x = None" by blast
  then show ?thesis using equidistant_linear_some equidistant_linear_none
    using assms(1) assms(2) assms(3) by presburger
qed

section \<open>Definition of percentile\<close>

text \<open> Percentile is a linear approximation of the equidistant points on the unit interval of the sorted list.
  E.g., for a list [3,1,4,8,6], the x percentile is determined by first sorting the list to [1,3,4,6,8],
  then the unit interval is subdivided by adding the 5 points 0.1, 0.3, 0.5, 0.7, and 0.9. The 0.1 
  percentile is then 1, the 0.3 percentile 3, the 0.5 percentile 4, and so on. For values in between,
  e.g., the 0.4 percentile, a linear approximation of the 0.3 percentile and the 0.5 percentile is computed,
  that is, in this case the value is precisely between 3 and 4, that is, 3.5. 
  Note that this expression deals with a priori infinite objects and is not computational.
  A computational version of percentile can be found in Percentile_Code.thy. \<close>


text \<open> Percentile is a linear approximation of the equidistant points on the unit interval of the sorted list.
  E.g., for a list [3,1,4,8,6], the x percentile is determined by first sorting the list to [1,3,4,6,8],
  then the unit interval is subdivided by adding the 5 points 0.1, 0.3, 0.5, 0.7, and 0.9. The 0.1 
  percentile is then 1, the 0.3 percentile 3, the 0.5 percentile 4, and so on. For values in between,
  e.g., the 0.4 percentile, a linear approximation of the 0.3 percentile and the 0.5 percentile is computed,
  that is, in this case the value is precisely between 3 and 4, that is, 3.5. 
  Note that this expression deals with a priori infinite objects and is as a consequence not computational.
  A computational version of percentile can be found in Percentile_Code.thy. \<close>

definition percentile_inner :: "real list \<Rightarrow> real \<Rightarrow> real"
where
  "percentile_inner ys x = linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) x"

text \<open> The full percentile function is the above defined percentile function as a linear interpolation plus a
       linear extrapolation to the two extrapolated values.
  Note that this expression deals with a priori infinite objects and is not computational.
  A computational version of percentile can be found in Percentile_Code.thy. \<close>
definition percentile :: "real list \<Rightarrow> real \<Rightarrow> real"
where
  "percentile ys x = linear_approximation (extended_points_on_unit_interval_of (sort ys)) x"

text \<open> The minimum of a finite set is equal to the minimum of all the element less than or equal to an
       arbitrary element in the set. \<close>
lemma Min_equiv:
  assumes "(a::real) \<in> A"
  assumes "finite A"
  shows "Min A = Min {x \<in> A. x \<le> a}"
proof -
  have a: "{x \<in> A. x < a} \<noteq> {} \<longrightarrow> Min A \<le> a"
    by (simp add: assms)
  then have "{x \<in> A. x < a} \<noteq> {} \<longrightarrow> Min A \<le> Min {x \<in> A. x \<le> a}"
    by (smt Collect_cong Min_antimono assms(2) empty_iff mem_Collect_eq subsetI)
  then have b: "{x \<in> A. x < a} \<noteq> {} \<longrightarrow> Min A = Min {x \<in> A. x \<le> a}" using a  dual_order.antisym
         eq_Min_iff infinite_super mem_Collect_eq subsetI
    by (metis (mono_tags, lifting) all_not_in_conv assms(2))
  have "{x \<in> A. x < a} = {} \<longrightarrow> Min A = a"
    by (metis Collect_empty_eq all_not_in_conv assms(1) assms(2) eq_Min_iff not_le)
  then have "{x \<in> A. x < a} = {} \<longrightarrow> Min A = Min {x \<in> A. x \<le> a}"
    by (smt Min_in assms(2) empty_iff infinite_super mem_Collect_eq subsetI)
  then show ?thesis using b
    by blast
qed

text \<open> The maximum of a finite set is equal to the maximum of all the element greater than or equal to an
       arbitrary element in the set. \<close>
lemma Max_equiv:
  assumes "(a::real) \<in> A"
  assumes "finite A"
  shows "Max A = Max {x \<in> A. a \<le> x}" 
proof -
  have a: "{x \<in> A. a < x} \<noteq> {} \<longrightarrow> a \<le> Max A" 
    using Max_ge assms(1) assms(2) by blast
  then have "{x \<in> A. a < x} \<noteq> {} \<longrightarrow> Max A \<le> Max {x \<in> A. a \<le> x}"
    using Max_in assms(2) by fastforce
  then have b: "{x \<in> A. a < x} \<noteq> {} \<longrightarrow> Max A = Max {x \<in> A. a \<le> x}" using a  dual_order.antisym
         eq_Max_iff infinite_super mem_Collect_eq subsetI
    by (metis (mono_tags, lifting) all_not_in_conv assms(2))
  have "{x \<in> A. a < x} = {} \<longrightarrow> Max A = a"
    by (metis Collect_empty_eq all_not_in_conv assms(1) assms(2) eq_Max_iff not_le)
  then have "{x \<in> A. a < x} = {} \<longrightarrow> Max A = Max {x \<in> A. a \<le> x}"
    by (smt Max_in assms(2) empty_iff infinite_super mem_Collect_eq subsetI)
  then show ?thesis using b
    by blast
qed

text \<open> Two partial functions that agree on a finite domain have the same neighbors on the interval. \<close>
lemma neighbors_equ:
  assumes "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> p1 z = p2 z"
  assumes "a \<in> dom p1 \<and> b \<in> dom p1 \<and> a \<in> dom p2 \<and> b \<in> dom p2"
  assumes "finite (dom p1)"
  assumes "finite (dom p2)"
  shows "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>
               neighbors p1 z = neighbors p2 z"
proof -
  have equiv: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> (z \<in> dom p1 \<longleftrightarrow> z \<in> dom p2)"
    by (simp add: assms domIff)

  have "\<forall>z. a \<le> z \<and> z \<le> b  \<longrightarrow> (a \<in> dom p1 \<and> a \<le> z)" by (simp add: assms(2))
  then have a_in_p1: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> a \<in> {x' \<in> dom p1. x' \<le> z}" by blast

  have "\<forall>z. a \<le> z \<and> z \<le> b  \<longrightarrow> (a \<in> dom p2 \<and> a \<le> z)" by (simp add: assms(2))
  then have a_in_p2: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> a \<in> {x' \<in> dom p2. x' \<le> z}" by blast

  have "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> {x \<in> {x' \<in> dom p1. x' \<le> z}. a \<le> x} = 
                               {x' \<in> dom p1. x' \<le> z \<and> a \<le> x'}" by blast

  have  finite_p1: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> finite {x' \<in> (dom p1). x' \<le> z}"
    by (simp add: assms(3))
  then have p1_max: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> Max {x' \<in> dom p1. x' \<le> z} = 
                                            Max {x' \<in> dom p1. x' \<le> z \<and> a \<le> x'}"
    using a_in_p1 Collect_cong mem_Collect_eq Max_equiv
    by smt
 have  finite_p2: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> finite {x' \<in> (dom p2). x' \<le> z}"
    by (simp add: assms(4))
 then have p2_max: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> Max {x' \<in> dom p2. x' \<le> z} = 
                                      Max {x' \<in> dom p2. x' \<le> z \<and> a \<le> x'}"
    using a_in_p2 by (smt Collect_cong Max_equiv mem_Collect_eq) 

  have Max_same: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> Max {x' \<in> dom p1. x' \<le> z} = 
                                         Max {x' \<in> dom p2. x' \<le> z}"
    using equiv p1_max p2_max by (smt Collect_cong assms(2))

  have "\<forall>z. a \<le> z \<and> z \<le> b  \<longrightarrow> (b \<in> dom p1 \<and> z \<le> b)" by (simp add: assms(2))
  then have b_in_p1: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> b \<in> {x' \<in> dom p1. z \<le> x'}" by blast

  have "\<forall>z. a \<le> z \<and> z \<le> b  \<longrightarrow> (b \<in> dom p2 \<and> z \<le> b)" by (simp add: assms(2))
  then have b_in_p2: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> b \<in> {x' \<in> dom p2. z \<le> x'}" by blast

  have "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> {x \<in> {x' \<in> dom p1. z \<le> x'}. x \<le> b} = 
                               {x' \<in> dom p1. z \<le> x' \<and> x' \<le> b}" by blast

  then have p1_min: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> Min {x' \<in> dom p1. z \<le> x'} = 
                                            Min {x' \<in> dom p1. z \<le> x' \<and> x' \<le> b}"
    using b_in_p1 finite_p1 Collect_cong Min_equiv mem_Collect_eq 
         Collect_mem_eq assms(3) finite_Collect_conjI
proof -
  { fix rr :: real
    have "finite {r \<in> dom p1. rr \<le> r}"
  using \<open>finite (dom p1)\<close> by auto
moreover
  { assume "finite {r \<in> dom p1. rr \<le> r} \<and> b \<in> {r \<in> dom p1. rr \<le> r} \<and> Min {r \<in> dom p1. rr \<le> r} \<noteq> Min {r \<in> dom p1. rr \<le> r \<and> r \<le> b}"
      then have "{r \<in> {r \<in> dom p1. rr \<le> r}. r \<le> b} \<noteq> {r \<in> dom p1. rr \<le> r \<and> r \<le> b}"
  by (metis (no_types) Min_equiv)
then have "\<not> a \<le> rr \<or> \<not> rr \<le> b \<or> Min {r \<in> dom p1. rr \<le> r} = Min {r \<in> dom p1. rr \<le> r \<and> r \<le> b}"
  by blast }
  ultimately have "\<not> a \<le> rr \<or> \<not> rr \<le> b \<or> Min {r \<in> dom p1. rr \<le> r} = Min {r \<in> dom p1. rr \<le> r \<and> r \<le> b}"
    using b_in_p1 by blast }
then show ?thesis
  by presburger
qed

  have "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> {x \<in> {x' \<in> dom p2. z \<le> x'}. x \<le> b} = 
                               {x' \<in> dom p2. z \<le> x' \<and> x' \<le> b}" by blast

  then have p2_min: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> Min {x' \<in> dom p2. z \<le> x'} = 
                                            Min {x' \<in> dom p2. z \<le> x' \<and> x' \<le> b}"
proof -
  { fix rr :: real
    have "finite {r \<in> dom p2. rr \<le> r}"
  using \<open>finite (dom p2)\<close> by auto
moreover
  { assume "finite {r \<in> dom p2. rr \<le> r} \<and> b \<in> {r \<in> dom p2. rr \<le> r} \<and> Min {r \<in> dom p2. rr \<le> r} \<noteq> Min {r \<in> dom p2. rr \<le> r \<and> r \<le> b}"
      then have "{r \<in> {r \<in> dom p2. rr \<le> r}. r \<le> b} \<noteq> {r \<in> dom p2. rr \<le> r \<and> r \<le> b}"
  by (metis (no_types) Min_equiv)
then have "\<not> a \<le> rr \<or> \<not> rr \<le> b \<or> Min {r \<in> dom p2. rr \<le> r} = Min {r \<in> dom p2. rr \<le> r \<and> r \<le> b}"
  by blast }
  ultimately have "\<not> a \<le> rr \<or> \<not> rr \<le> b \<or> Min {r \<in> dom p2. rr \<le> r} = Min {r \<in> dom p2. rr \<le> r \<and> r \<le> b}"
    using b_in_p2 by blast }
then show ?thesis
  by presburger
qed

  have Min_same: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> 
                    Min {x' \<in> dom p1. z \<le> x'} = Min {x' \<in> dom p2. z \<le> x'}"
    by (smt Collect_cong equiv assms(2) p1_min p2_min)
  
  then show ?thesis using assms neighbors_def Max_same Min_same
    by simp
qed

text \<open> Two partial functions that agree on an interval and have the same neighbors have the same linear 
       approximation on the interval. \<close>
lemma linear_equ:
  assumes "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>
               neighbors p1 z = neighbors p2 z"
  assumes "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>
             p1 z = p2 z" 
  assumes "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>  
        (let (x1, x2) = neighbors p1 z in
          a \<le> x1 \<and> x1 \<le> b \<and> a \<le> x2 \<and> x2 \<le> b)"
  shows "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>  
        linear_approximation p1 z = 
        linear_approximation p2 z"  
proof -
  have p1: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>  linear_approximation p1 z = 
        (let (x1, x2) = neighbors p1 z;
     (y1, y2) = (the (p1 x1), the (p1 x2)) in linear (x1, y1) (x2, y2) z)" 
    using linear_approximation_def by blast
  have p2: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>  linear_approximation p2 z = 
        (let (x1, x2) = neighbors p2 z;
     (y1, y2) = (the (p2 x1), the (p2 x2)) in linear (x1, y1) (x2, y2) z)" 
    using linear_approximation_def by blast
  then have "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>  linear_approximation p2 z = 
        (let (x1, x2) = neighbors p1 z;
     (y1, y2) = (the (p2 x1), the (p2 x2)) in linear (x1, y1) (x2, y2) z)" 
    using assms using p2 by simp
  then have "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow>  linear_approximation p2 z = 
        (let (x1, x2) = neighbors p1 z;
     (y1, y2) = (the (p1 x1), the (p1 x2)) in linear (x1, y1) (x2, y2) z)" 
    using assms assms by (simp add: neighbors_def)
  then show ?thesis using p1 by simp
qed

text \<open> The point half a distance from 0 is in the domain of equidistant_points_on_unit_interval_of. \<close>
lemma domain_equidistant_low:
  assumes "length ys > 1"
  assumes "sorted ys"
  shows "1/(2 * length ys) \<in> dom (equidistant_points_on_unit_interval_of (sort ys))"
  using assms
proof -
  have aux1: "(let xs = ((1 / length ys) * 0.5) #
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [1..<length ys]
         in xs!0) = (1 / length ys) * 0.5" by simp
  have l0: "length ys > 0" using assms(1) by linarith
  then have "\<forall>a.\<forall> zs. (let xs = a # zs
           in (map_of (zip xs ys))) a = Some (ys!0)"
    by (simp add: zip_lemma)

  then have "(let xs = ((1 / length ys) * 0.5) #
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [1..<length ys]
           in map_of (zip xs ys)) ((1/ length ys) * 0.5) = Some (ys!0)" 
       using aux1 by auto

  then have cons: "\<forall>f. \<forall>n::nat. (f 0) # map f [1..n] = map f [0..n]" using interval_ext by simp

  then have cons_l: "\<forall>f. (f 0) # map f [1..<length ys] = map f [0..<length ys]"
    using assms(1) upt_rec by auto

  then have "let f = (\<lambda>x. (1 / length ys) * (x + 0.5)) in
                 (f 0) # map f [1..<length ys] = map f [0..<length ys]"
    by metis

  then have "((1 / length ys) * 0.5) #
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [1..<length ys] =
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]" 
    by (smt of_nat_0)

    then have "(let xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]
           in map_of (zip xs ys)) ((1/ length ys) * 0.5) = Some (ys!0)"
    using \<open>(let xs = 1 / real (length ys) * (5 / 10) # map (\<lambda>x. 1 / real (length ys) * (real x + 5 / 10)) 
     [1..<length ys] in map_of (zip xs ys)) (1 / real (length ys) * (5 / 10)) = Some (ys ! 0)\<close> by auto
 
  then have "(equidistant_points_on_unit_interval_of ys) (1/(length ys) * 0.5) = Some (ys!0)"
    using equidistant_points_on_unit_interval_of_def by simp

  have "(let xs = ((1 / length ys) * 0.5) #
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [1..<length ys]
           in map_of (zip xs ys)) ((1/ length ys) * 0.5) = Some (ys!0)" 
    using \<open>(let xs = 1 / real (length ys) * (5 / 10) # 
            map (\<lambda>x. 1 / real (length ys) * (real x + 5 / 10)) [1..<length ys] in map_of (zip xs ys)) 
            (1 / real (length ys) * (5 / 10)) = Some (ys ! 0)\<close> by blast
  have "(equidistant_points_on_unit_interval_of ys) (1/(2 * length ys)) = Some (ys!0)" 
       using aux1 equidistant_points_on_unit_interval_of_def 
       by (smt \<open>equidistant_points_on_unit_interval_of ys (1 / real (length ys) * (5 / 10)) = 
                Some (ys ! 0)\<close> mult_cancel_right1 nonzero_divide_mult_cancel_left 
                nonzero_divide_mult_cancel_right of_nat_1 of_nat_add of_nat_mult one_add_one 
                ring_class.ring_distribs(2) times_divide_times_eq)

  then have cons: "\<forall>f. \<forall>n::nat. (f 0) # map f [1..n] = map f [0..n]" using interval_ext by simp

  then have cons_l: "\<forall>f. (f 0) # map f [1..<length ys] = map f [0..<length ys]"
    using assms(1) upt_rec by auto

  then have "let f = (\<lambda>x. (1 / length ys) * (x + 0.5)) in
                 (f 0) # map f [1..<length ys] = map f [0..<length ys]"
    by metis

  then have "((1 / length ys) * 0.5) #
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [1..<length ys] =
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]" 
    by (smt of_nat_0)

    then have "(let xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]
           in map_of (zip xs ys)) ((1/ length ys) * 0.5) = Some (ys!0)"
    using \<open>(let xs = 1 / real (length ys) * (5 / 10) # map (\<lambda>x. 1 / real (length ys) * (real x + 5 / 10)) 
     [1..<length ys] in map_of (zip xs ys)) (1 / real (length ys) * (5 / 10)) = Some (ys ! 0)\<close> by auto
 
  then have "(equidistant_points_on_unit_interval_of ys) (1/(length ys) * 0.5) = Some (ys!0)"
    using equidistant_points_on_unit_interval_of_def by simp

  have "1/(length ys) * 0.5 = 1/(2 * (length ys))" using assms(1) by auto

  then have "(equidistant_points_on_unit_interval_of ys) (1/(2 * (length ys))) = Some (ys!0)"
    using \<open>equidistant_points_on_unit_interval_of ys (1 / real (length ys) * (5 / 10)) = Some (ys ! 0)\<close> 
    by presburger
 
  then have "(equidistant_points_on_unit_interval_of ys) (1/(2 *(length ys))) = Some (ys!0)"
    using equidistant_points_on_unit_interval_of_def by blast
  then show ?thesis
    by (simp add: assms(2) domI sorted_sort_id)
qed

text \<open> The point half a distance from 1 is in the domain of equidistant_points_on_unit_interval_of. \<close>
lemma domain_equidistant_high:
  assumes "length ys > 1"
  assumes "sorted ys"
  shows "1-1/(2 * length ys) \<in> dom (equidistant_points_on_unit_interval_of (sort ys))" 
  using assms 
    by (metis Max_equidistant_points_on_unit_interval_of Max_in domain_equidistant_low empty_iff 
        finite_equidistant_points_on_unit_interval_of le_less_trans le_numeral_extra(1) 
        length_greater_0_conv sorted_sort_id)

text \<open> The point half a distance from 0 is in the domain of extended_points_on_unit_interval_of. \<close>
lemma domain_extended_low:
  assumes "length ys > 1"
  assumes "sorted ys"
  shows "1/(2 * length ys) \<in> dom (extended_points_on_unit_interval_of (sort ys))"
proof -
  have "1/(2 * length ys) \<in> dom (equidistant_points_on_unit_interval_of (sort ys))"
    using assms(1) assms(2) domain_equidistant_low sorted_sort_id by fastforce
  then show ?thesis
    by (simp add: extended_points_on_unit_interval_of_def le_less_trans)
qed

text \<open> The point half a distance from 1 is in the domain of extended_points_on_unit_interval_of. \<close>
lemma domain_extended_high:
  assumes "length ys > 1"
  assumes "sorted ys"
  shows "1-1/(2 * length ys) \<in> dom (extended_points_on_unit_interval_of (sort ys))"
proof -
  have "1-1/(2 * length ys) \<in> dom (equidistant_points_on_unit_interval_of (sort ys))"
    using assms(1) assms(2) domain_equidistant_high sorted_sort_id by fastforce
  then show ?thesis
    by (simp add: extended_points_on_unit_interval_of_def le_less_trans)
qed

text \<open> In the inner interval the percentile function is equal to the percentile_inner function. \<close>
lemma percentile_alt1:
  assumes "length ys > 1"
  assumes "sorted ys"
  assumes "1/(2* (length ys)) \<le> x \<and> x \<le> 1 - 1/(2 * (length ys))"
  shows   "percentile ys x = percentile_inner ys x" 
proof -
  have ni: "\<forall>z. 1/(2* (length ys)) \<le> z \<and> z \<le> 1 - 1/(2* (length ys)) \<longrightarrow>  
        (let (x1, x2) = neighbors (equidistant_points_on_unit_interval_of (sort ys)) z in
          1/(2* (length ys)) \<le> x1 \<and> x1 \<le> 1- 1/(2* (length ys)) \<and> 
          1/(2* (length ys)) \<le> x2 \<and> x2 \<le> 1-1/(2* (length ys)))"
    by (smt Max_equidistant_points_on_unit_interval_of Max_ge 
        Min_equidistant_points_on_unit_interval_of Min_le assms(1) assms(2) 
        atLeastAtMost_iff defined_interval_of_equidistant_points_on_unit_interval_of 
        domIff finite_equidistant_points_on_unit_interval_of le_less_trans 
        le_numeral_extra(1) length_greater_0_conv neighbors_dest option.simps(3) 
        prod.simps(2) sorted_sort_id)
  have "sort ys = ys" using assms(1)
    by (simp add: assms(2) sorted_sort_id)
  have ext_eq: "(extended_points_on_unit_interval_of (sort ys)) (1/(2* (length ys))) =
        (equidistant_points_on_unit_interval_of (sort ys)) (1/(2* (length ys)))"
    using assms(1) extended_points_on_unit_interval_of_def by auto
  have "1-1/(2 * (length ys)) < 1" using assms(1) by auto
  have "0 < 1-1/(2 * (length ys))" using assms(1) assms(3) by linarith
  then have ext_up: "(extended_points_on_unit_interval_of (sort ys)) (1- 1/(2* (length ys))) =
        (equidistant_points_on_unit_interval_of (sort ys)) (1- 1/(2* (length ys)))"
    using assms(1) extended_points_on_unit_interval_of_def by auto
  then have ex_eq_eq: "\<forall>z. 1/(2* (length ys)) \<le> z \<and> z \<le> 1 - 1/(2 * (length ys)) \<longrightarrow> 
             (extended_points_on_unit_interval_of ys) z =  
             (equidistant_points_on_unit_interval_of ys) z"
    using \<open>1 - 1 / real (2 * length ys) < 1\<close> assms(3) extended_points_on_unit_interval_of_def 
    by auto
  
  have l_equi: "1/(2* (length ys)) \<in> dom (equidistant_points_on_unit_interval_of ys)" 
         using domain_equidistant_low assms(1) assms(2) \<open>sort ys = ys\<close> by force
  have r_equi: "(1- 1/(2* (length ys))) \<in> dom (equidistant_points_on_unit_interval_of ys)" 
         using domain_equidistant_high \<open>sort ys = ys\<close> assms(1) assms(2) by fastforce
  have l_ext: "1/(2* (length ys)) \<in> dom (extended_points_on_unit_interval_of ys)" 
         using domain_extended_low \<open>sort ys = ys\<close> ext_eq l_equi by auto
  have r_ext: "(1 - 1/(2* (length ys))) \<in> dom (extended_points_on_unit_interval_of ys)" 
    using domain_extended_high \<open>sort ys = ys\<close> ext_up r_equi by auto
  have finite_equ: "finite (dom (equidistant_points_on_unit_interval_of ys))" by simp
  have finite_ext: "finite (dom (extended_points_on_unit_interval_of ys))" by simp
  then have neighbors: "\<forall>z. 1/(2* (length ys)) \<le> z \<and> z \<le> 1 - 1/(2 * (length ys)) \<longrightarrow>  
        neighbors (extended_points_on_unit_interval_of ys) z = 
        neighbors (equidistant_points_on_unit_interval_of ys) z" 
         using neighbors_equ l_equi r_equi l_ext r_ext
               defined_point_neighbors_eq ex_eq_eq finite_ext finite_equ
         by blast
  have "neighbors (extended_points_on_unit_interval_of ys) x = 
        neighbors (equidistant_points_on_unit_interval_of ys) x" 
    using neighbors assms by auto
  then have "linear_approximation (extended_points_on_unit_interval_of ys) x =
             linear_approximation (equidistant_points_on_unit_interval_of ys) x" 
    using linear_equ[of "1/(2* (length ys))" "1-1/(2* (length ys))" 
          "(extended_points_on_unit_interval_of ys)" 
          "(equidistant_points_on_unit_interval_of ys)"] 
          \<open>sort ys = ys\<close> assms(3) ext_up ex_eq_eq ni neighbors by simp
  then show ?thesis using percentile_def percentile_inner_def
    by (simp add: \<open>sort ys = ys\<close>)
qed

text \<open> The linear approximation of a partial function is characterized as a linear function between
       two defined points. \<close>
lemma linear_approximation_lemma:
  assumes "a < z \<and> z < b"
  assumes "(neighbors (pf ::(real \<Rightarrow> real option)) z = (a, b))" 
  assumes  "pf a = (Some fa)"
  assumes "pf b = (Some fb)"
  shows   "linear_approximation pf z = linear (a, fa) (b, fb) z"
  by (simp add: assms(2) assms(3) assms(4) linear_approximation_def)

text \<open> For a finite non-empty set holds if all elements are greater than a number than the minimum is
       greater than that number. \<close>
lemma Min_lemma:
  assumes "\<forall>x. x\<in> A \<and> P x \<longrightarrow> x \<ge> a"
  assumes "finite {x \<in> A. P x}"
  assumes "{x \<in> A. P x} \<noteq> {}" 
  shows "Min {x \<in> A. P x} \<ge> a"
  using Min_in assms(1) assms(2) assms(3) by blast

text \<open> For a finite non-empty set holds if all elements are smaller than a number than the maximum is
       smaller than that number. \<close>
lemma Max_lemma:
  assumes "\<forall>x. x\<in> A \<and> P x \<longrightarrow> x \<le> a"
  assumes "finite {x \<in> A. P x}"
  assumes "{x \<in> A. P x} \<noteq> {}" 
  shows "Max {x \<in> A. P x} \<le> a"
  using Max_in assms(1) assms(2) assms(3) by blast

text \<open> The percentile function in the lower interval corresponds to the linear interpolation of the 
       extrapolation at 0 and the value at half the distance from 0.\<close>
lemma percentile_alt2:
  assumes "length ys > 1"
  assumes "sorted ys"
  assumes "0 \<le> x \<and> x < 1/(2* (length ys))"
  shows "percentile ys x = (linear (0, extrapolation_0 ys) (1/(2* (length ys)), ys!0)) x"
proof -
  have sorted: "sort ys = ys" using assms by (simp add: sorted_sort_id)
  have "0 \<in> dom (extended_points_on_unit_interval_of (sort ys))"
    by (simp add: extended_points_on_unit_interval_of_def)
  have small: "extrapolation_0 ys \<le> ys!0"
    using assms(1) assms(2) extrapolation_0_def sorted_nth_mono by fastforce
  have ex: "(extended_points_on_unit_interval_of (sort ys)) 0 = Some (extrapolation_0 ys)"
    by (simp add: extended_points_on_unit_interval_of_def sorted)
  have ext_eq: "(extended_points_on_unit_interval_of (sort ys)) (1/(2* (length ys))) =
        (equidistant_points_on_unit_interval_of (sort ys)) (1/(2* (length ys)))"
    using assms(1) extended_points_on_unit_interval_of_def by auto
  have aux1: "(let xs = ((1 / length ys) * 0.5) #
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [1..<length ys]
         in xs!0) = (1 / length ys) * 0.5" by simp
  have l0: "length ys > 0" using assms(1) by linarith
  then have "\<forall>a.\<forall> zs. (let xs = a # zs
           in (map_of (zip xs ys))) a = Some (ys!0)"
    by (simp add: zip_lemma)

  then have "(let xs = ((1 / length ys) * 0.5) #
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [1..<length ys]
           in map_of (zip xs ys)) ((1/ length ys) * 0.5) = Some (ys!0)" 
       using aux1 by auto

  then have cons: "\<forall>f. \<forall>n::nat. (f 0) # map f [1..n] = map f [0..n]" using interval_ext by simp

  then have cons_l: "\<forall>f. (f 0) # map f [1..<length ys] = map f [0..<length ys]"
    using assms(1) upt_rec by auto

  then have "let f = (\<lambda>x. (1 / length ys) * (x + 0.5)) in
                 (f 0) # map f [1..<length ys] = map f [0..<length ys]"
    by metis

  then have "((1 / length ys) * 0.5) #
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [1..<length ys] =
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]" 
    by (smt of_nat_0)

    then have "(let xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]
           in map_of (zip xs ys)) ((1/ length ys) * 0.5) = Some (ys!0)"
    using \<open>(let xs = 1 / real (length ys) * (5 / 10) # map (\<lambda>x. 1 / real (length ys) * (real x + 5 / 10)) 
     [1..<length ys] in map_of (zip xs ys)) (1 / real (length ys) * (5 / 10)) = Some (ys ! 0)\<close> by auto
 
  then have "(equidistant_points_on_unit_interval_of ys) (1/(length ys) * 0.5) = Some (ys!0)"
    using equidistant_points_on_unit_interval_of_def by simp

  have "1/(length ys) * 0.5 = 1/(2 * (length ys))" using assms(1) by auto

  then have "(equidistant_points_on_unit_interval_of ys) (1/(2 * (length ys))) = Some (ys!0)"
    using \<open>equidistant_points_on_unit_interval_of ys (1 / real (length ys) * (5 / 10)) = Some (ys ! 0)\<close> 
    by presburger
 
  then have "(equidistant_points_on_unit_interval_of ys) (1/(2 *(length ys))) = Some (ys!0)"
    using equidistant_points_on_unit_interval_of_def by blast
  then have ex_up: "(extended_points_on_unit_interval_of ys) (1/(2 * (length ys))) = Some (ys!0)"
    using assms(1) extended_points_on_unit_interval_of_def by auto
  have not_dom: "\<forall> z. 0 < z \<and> z < 1/(2 * length ys) \<longrightarrow> z \<notin> dom (extended_points_on_unit_interval_of ys)"
    
    by (metis Max_extended_points_on_unit_interval_of Max_ge Min_equidistant_points_on_unit_interval_of 
        Min_le assms(1) domI domIff ex_up extended_points_on_unit_interval_of_def 
        finite_equidistant_points_on_unit_interval_of finite_extended_points_on_unit_interval_of 
        fun_upd_apply length_greater_0_conv linorder_not_le neq0_conv not_less0 of_nat_0_less_iff 
        of_nat_eq_0_iff)
  have "0 \<in>  dom (extended_points_on_unit_interval_of ys)"
    using \<open>0 \<in> dom (extended_points_on_unit_interval_of (sort ys))\<close> sorted by auto
  then have "\<forall> z. 0\<le> z \<and> z < 1/(2 * length ys) \<longrightarrow> 
           {x' \<in> dom (extended_points_on_unit_interval_of ys). x' \<le> z} = {0}" using not_dom 
    by (smt Collect_cong Min_extended_points_on_unit_interval_of Min_le assms(1) 
        finite_extended_points_on_unit_interval_of le_less_trans le_numeral_extra(1) 
        length_greater_0_conv singleton_conv)
  then have Ma: "\<forall> z. 0 < z \<and> z < 1/(2 * length ys) \<longrightarrow> 
           Max {x' \<in> dom (extended_points_on_unit_interval_of ys). x' \<le> z} = 0" by simp

  have in_dom: "1/(2* (length ys)) \<in>  dom (extended_points_on_unit_interval_of ys)"
    using ex_up by auto
  then have Mi_aux: "\<forall> z x'. 0 < z \<and> z \<le> x' \<and> x' \<in> dom (extended_points_on_unit_interval_of ys) \<longrightarrow> 
             x' \<ge> 1/(2* (length ys))"
    using not_dom by smt
   then have "\<forall>z.
           \<forall>x'. x' \<in> dom (extended_points_on_unit_interval_of ys) \<and> 0 < z \<and> z \<le> x' \<longrightarrow> 
             x' \<ge> 1/(2* (length ys))" 
     using Mi_aux by blast
     then have "\<forall>z. 0 < z \<longrightarrow>
           (\<forall>x'. x' \<in> dom (extended_points_on_unit_interval_of ys) \<and> z \<le> x' \<longrightarrow> 
             x' \<ge> 1/(2* (length ys)))" 
       using Mi_aux by blast

     then have all_greater: "\<forall>z. 0 < z \<and> z \<le> 1/(2 * length ys) \<longrightarrow>
           (\<forall>x'. x' \<in> dom (extended_points_on_unit_interval_of ys) \<and> z \<le> x' \<longrightarrow> 
             x' \<ge> 1/(2* (length ys)))" 
       using Mi_aux by blast

   have "1/(2* length ys) \<in> dom (extended_points_on_unit_interval_of ys)"
     using \<open>1 / real (2 * length ys) \<in> dom (extended_points_on_unit_interval_of ys)\<close> by auto
   have "finite (dom (extended_points_on_unit_interval_of (sort ys)))" by simp
   then have finite: "finite {x' \<in> (dom (extended_points_on_unit_interval_of ys)). z \<le> x'}"
       by simp
     have "0 < 1/(2* length ys) \<and> 1/(2* length ys) \<le> 1/(2* length ys)" using assms(3) by auto
   then have Min_3: "\<forall> z. 0 < z \<and>  z \<le> 1/(2 * length ys) \<longrightarrow> 
           Min {x' \<in> dom (extended_points_on_unit_interval_of ys). z \<le> x'} \<le> 1/(2* (length ys))"
     using Min_lemma linorder_not_le finite in_dom by auto
   have non_empty: "\<forall> z. 0 < z \<and>  z \<le> 1/(2 * length ys) \<longrightarrow> 
         {x' \<in> (dom (extended_points_on_unit_interval_of ys)). z \<le> x'} \<noteq> {}"
     using in_dom by blast
  then have Mi_aux2: "\<forall> z. 0 < z \<and> z \<le> 1/(2 * length ys) \<longrightarrow> 
           Min {x' \<in> dom (extended_points_on_unit_interval_of ys). z \<le> x'} \<ge> 1/(2* (length ys))" 
    using finite Min_lemma all_greater Min_3 by simp
   then have Mi: "\<forall> z. 0 < z \<and> z \<le> 1/(2 * length ys) \<longrightarrow>
           Min {x' \<in> dom (extended_points_on_unit_interval_of ys). z \<le> x'} = 1/(2* (length ys))" 
        using Mi_aux2 Min_insert2 in_dom Min_3 by fastforce

  then have n: "\<forall> z. 0 < z \<and> z < 1/(2 * length ys) \<longrightarrow> 
             neighbors (extended_points_on_unit_interval_of ys) z = (0,  1/(2* (length ys)))" 
    using neighbors_def Ma Mi_aux2 by fastforce

  have a1: "linear_approximation (extended_points_on_unit_interval_of (sort ys)) 0 = extrapolation_0 ys" 
    using ex linear_approximation_def  \<open>0 \<in> dom (extended_points_on_unit_interval_of (sort ys))\<close> assms(1) 
            by (simp add: defined_point_neighbors_eq linear_first) 
  have a2: "linear_approximation (extended_points_on_unit_interval_of (sort ys)) (1/(2* (length ys))) = ys!0"
    using in_dom assms(1)
    using defined_point_neighbors_eq ex_up linear_approximation_def linear_first sorted by auto
  then have "linear_approximation (extended_points_on_unit_interval_of (sort ys)) x = 
      linear (0, extrapolation_0 ys) (1/(2* (length ys)), ys!0) x" 
    using a1 a2 n
          linear_approximation_lemma assms
           defined_point_neighbors_eq finite_extended_points_on_unit_interval_of in_dom prod.inject
    by (smt ex ex_up linear_first sorted)
  then show ?thesis by (simp add: percentile_def)
qed

text \<open> The i-th element of a zip is the pair of the i-th elements of the two lists involved\<close>
lemma zip_aux:
  assumes "length xs = length ys" 
  assumes "(i::nat) < (length ys)"
  shows "(zip xs ys)!i = (xs!i,ys!i)" 
  using nth_zip
  by (simp add: assms)


text \<open> A function is monotonic (strictly monotonically increasing) if for any two values their 
       respective order remains unchanged on application of the function.\<close>
definition monotonic :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
where
  "monotonic f = (\<forall>x::nat.\<forall>y::nat. x < y \<longrightarrow> f x < f y)"

text \<open> The map_of function applied to a zip of two lists and an element in the first list 
       returns the value of the corresponding element in the second list.\<close>
lemma zip_res:
  assumes "length xs = length ys"
  assumes "length ys > 0" 
  assumes "\<forall>i::nat.\<forall>j::nat. i < length ys \<and> j < length ys \<longrightarrow> (xs!i = xs!j \<longrightarrow> i = j)" 
  assumes "i < length ys"
  shows "map_of (zip xs ys) (xs!(i::nat))  = Some (ys!i)"
  by (metis assms(1) assms(3) assms(4) distinct_conv_nth map_of_zip_nth)

text \<open> The map_of function applied to a zip of two lists and last element of the first list
       return the value of the last element in the second list.\<close>
lemma zip_last:
  assumes "l = length ys" 
  assumes "l > 0"
  assumes "monotonic (f::(nat \<Rightarrow> real))"
  assumes "xs = map f [0..<l]" 
  shows "map_of (zip xs ys) (f (l-1)) = Some (ys!(l-1))"
proof -
  have "\<forall>x::real.\<forall>y::real. x < y \<longrightarrow> \<not> y < x \<and> \<not> x = y" by auto
  have last_zip: "(zip xs ys)!(l-1) = (xs!(l-1),ys!(l-1))"
    using zip_aux assms by simp
  have inj: "\<forall>x:: nat.\<forall>y::nat. f x = f y \<longrightarrow> x = y"
    by (smt assms(3) monotonic_def nat_neq_iff)
  have  "\<forall>i::nat. i < l \<longrightarrow> xs!i = (f i)" using assms(4) map_def
    by simp
  then have "\<forall>i::nat.\<forall>j::nat. i < l \<and> j < l \<longrightarrow> xs!i = xs!j \<longrightarrow> i = j" using assms inj
    by metis
  have last_zip: "i <l \<longrightarrow> map_of (zip xs ys) (xs!(i::nat))  = Some (ys!i)" using zip_res assms
    by (metis \<open>\<forall>i j. i < l \<and> j < l \<longrightarrow> xs ! i = xs ! j \<longrightarrow> i = j\<close> diff_zero length_map length_upt)
  have "let xs =  map f [0..<l] in xs!(l-1) = f (l-1)"
    by (simp add: assms(2))
  then show ?thesis using last_zip inj
    by (metis \<open>\<forall>i j. i < l \<and> j < l \<longrightarrow> xs ! i = xs ! j \<longrightarrow> i = j\<close> assms(1) assms(2) assms(4)
         diff_less diff_zero length_map length_upt zero_less_one zip_res)
qed

text \<open> mapping a function on a list from 0 to n-2 concated with the one element list of  [f (n-1)]
       is the same as mapping the function on a list from 0 to n-1.\<close>
lemma map_last:
  shows "\<forall>f. \<forall>n::nat. n > 1 \<longrightarrow> map f [0..<(n-1)] @ [f (n -1)] = map f [0..<n]"
proof -
  have one_zero: "\<forall>n::nat. n > 1 \<longrightarrow> n > 0" by linarith
  then have "\<forall>f. \<forall>n::nat. n > 1 \<longrightarrow> ((map f [0..<n] @ [f n]) = (map f [0..<(n+1)]))" 
    by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right less_add_same_cancel1 
        less_one list.simps(8) list.simps(9) map_append order_refl upt_add_eq_append upt_conv_Nil 
        upt_rec zero_le)
  then show ?thesis
    by (smt One_nat_def Suc_eq_plus1 Suc_pred append_Cons length_greater_0_conv length_map 
        length_upt list.simps(9) list.size(3) map_Suc_upt one_zero self_append_conv2 upt_rec)
qed

text \<open> The percentile function in the upper interval corresponds to the linear interpolation of the 
       the value at half the distance from 1 and extrapolation at 1.\<close>
lemma percentile_alt3:
  assumes "length ys > 1"
  assumes "sorted ys"
  assumes "1 - 1/(2* length ys) < x \<and> x \<le> 1"
  shows "percentile ys x = (linear (1 - 1/(2* length ys), ys!((length ys) -1)) (1, extrapolation_1 ys)) x"
proof -
  let ?l = "length ys"
  have sorted: "sort ys = ys" using assms by (simp add: sorted_sort_id)
  have "1 \<in> dom (extended_points_on_unit_interval_of (sort ys))"
    by (simp add: extended_points_on_unit_interval_of_def)
  have "ys!(?l-2) \<le> ys!(?l-1)"
    by (metis assms(1) assms(2) diff_less last_conv_nth length_greater_0_conv nth_mem 
        order.strict_trans pos2 sorted_leq_last zero_less_one)
  then have "(ys!(?l-1) - ys!(?l-2)) * 2.0 \<le> (ys!(?l-1) - ys!(?l-2)) * 3.0" by simp
  then have "ys!(?l-1) - ys!(?l-2) \<le> (ys!(?l-1) - ys!(?l-2)) * 3.0/2.0" by simp
  then have "ys!(?l-1) \<le> ys!(?l-2) + (ys!(?l-1) - ys!(?l-2))* 3.0/2.0" by linarith
  then have big: "ys!(?l-1) \<le> extrapolation_1 ys" 
    using extrapolation_1_def by metis 
  have ex: "(extended_points_on_unit_interval_of (sort ys)) 1 = Some (extrapolation_1 ys)"
    by (simp add: extended_points_on_unit_interval_of_def sorted)
  have ext_eq: "(extended_points_on_unit_interval_of (sort ys)) (1 - (1/(2* (length ys)))) =
        (equidistant_points_on_unit_interval_of (sort ys)) (1 - (1/(2* (length ys))))"
    using assms(1) extended_points_on_unit_interval_of_def by auto
  have "\<forall>x::nat.\<forall>y::nat. (1 / length ys) * (x + 0.5) > (1 / length ys) * (y + 0.5) \<longrightarrow>
           x + 0.5 > y + 0.5"
    by (metis assms(1) gr_implies_not0 length_greater_0_conv list.size(3) mult_less_cancel_left_pos 
        of_nat_0_less_iff zero_less_divide_1_iff)
  then have "\<forall>x::nat.\<forall>y::nat. (1 / length ys) * (x + 0.5) > (1 / length ys) * (y + 0.5) \<longrightarrow>
           x > y" by auto
  then have mono: "monotonic (\<lambda>x'::nat. (1 / length ys) * (x' + 0.5))" using monotonic_def 
    by (smt assms(1) gr_implies_not0 length_greater_0_conv less_imp_of_nat_less list.size(3) 
        mult_less_cancel_left_pos of_nat_0_less_iff zero_less_divide_1_iff)
 have "ys \<noteq> []" using assms(1) by auto
  then have zip_l: "(let xs =  map (\<lambda>x'::real. (1 / length ys) * (x' + 0.5)) [0..<length ys]
           in map_of (zip xs ys)) ((1 / length ys) * (((length ys) -1) + 0.5)) = Some (ys!((length ys)-1))" 
    using zip_last[of "length ys" "ys" "\<lambda>x'::nat. (1 / length ys) * (x' + 0.5)"]
    using assms(1) mono by simp
  have "(\<lambda>x. (1 / length ys) * (x + 0.5)) ((length ys)-1) = 1 / (length ys) * (((length ys) -1) + 0.5)"
    by blast

  then have "(let xs =  map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys] 
           in map_of (zip xs ys)) ((1 / length ys) * ((length ys -1) + 0.5)) = Some (ys!((length ys)-1))"
    using zip_l by blast

  then have "(let xs =  map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]
           in map_of (zip xs ys)) ((1 / length ys) * ((length ys -1) + 0.5)) = Some (ys!((length ys)-1))"  
    by blast
  have "length ys > 1" using assms(1) by simp
  then have "1 / (length ys) * (((length ys) -1) + 0.5) = ((length ys) - 0.5)/ length ys" by auto 
  then have "1 / (length ys) * (((length ys) -1) + 0.5) = 1-(1 / length ys) * 0.5" 
    by (metis add_less_mono1 assms(1) diff_add_cancel diff_divide_distrib diff_zero divide_self_if 
        mult.left_neutral not_add_less2 of_nat_add of_nat_eq_0_iff times_divide_eq_left)
  then have "(let xs =  map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys] 
           in map_of (zip xs ys)) ((1 / length ys) * ((length ys -1) + 0.5)) = Some (ys!((length ys)-1))"  
  using zip_l by auto

  then have "(let xs =  map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]
           in map_of (zip xs ys)) (1-(1/ length ys) * 0.5) = Some (ys!((length ys)-1))" 
    using \<open>1 / real (length ys) * (real (length ys - 1) + 5 / 10) = 1 - 1 / real (length ys) * (5 / 10)\<close> 
    by auto

  then have cons_l: "\<forall>f. map f [0..<(length ys) -1] @ [f ((length ys) -1)] = map f [0..<length ys]"
    using assms(1) map_last by (smt gr_implies_not0 length_greater_0_conv list.size(3))

  then have "let f = (\<lambda>x. (1 / length ys) * (x + 0.5)) in
                 map f [0..<(length ys) -1] @ [f ((length ys) -1)] = map f [0..<length ys]"
    by metis

  then have map_aux: "map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<(length ys)-1] @ [(1 / length ys) * ((length ys) - 1 + 0.5)] =
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
    using cons_l by auto

  have "length ys > 0" using assms by linarith
  then have "(1 / length ys) * ((length ys) - 1 + 0.5) = (length ys - 0.5) / length ys" using assms by auto

  then have "map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys-1] @ [(length ys - 0.5) / length ys] =
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
    using map_aux by presburger 

  then have "map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys-1] @ [1 - 0.5 / length ys] =
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
    by (metis (no_types, lifting) assms(1) diff_0_eq_0 diff_divide_distrib divide_self_if 
        less_numeral_extra(3) of_nat_eq_0_iff zero_less_diff)

  then have "map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys-1] @ [1-(1 / length ys) * 0.5] =
                              map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
    by (simp add: mult.commute)

    then have "(let xs = map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]
           in map_of (zip xs ys)) (1-(1/ length ys) * 0.5) = Some (ys!(?l -1))"
      using map_def
      using \<open>(let xs = map (\<lambda>x. 1 / real (length ys) * (real x + 5 / 10)) [0..<length ys] in 
              map_of (zip xs ys)) (1 - 1 / real (length ys) * (5 / 10)) = Some (ys ! (length ys - 1))\<close> 
      by blast

  then have equi_aux: "(equidistant_points_on_unit_interval_of ys) (1- 1/?l * 0.5) = Some (ys!(?l -1))"
    using equidistant_points_on_unit_interval_of_def by simp

  have "1 - 1/?l * 0.5 = 1 - 1/(2 * ?l)" using assms(1) by auto

  then have "(equidistant_points_on_unit_interval_of ys) (1 - 1/(2 * ?l)) = Some (ys!(?l-1))"
    using equi_aux by presburger
 
  then have "(equidistant_points_on_unit_interval_of ys) (1 - 1/(2 * ?l)) = Some (ys!(?l - 1))"
    using equidistant_points_on_unit_interval_of_def by blast
  then have ex_up: "(extended_points_on_unit_interval_of ys) (1 - 1/(2 * ?l)) = Some (ys!(?l - 1))"
    using assms(1) extended_points_on_unit_interval_of_def by auto
  have not_dom: "\<forall> z. 1 - 1/(2* ?l) < z \<and> z < 1 \<longrightarrow> z \<notin> dom (extended_points_on_unit_interval_of ys)"
    using Max_equidistant_points_on_unit_interval_of Max_ge Min_equidistant_points_on_unit_interval_of 
          Min_le \<open>equidistant_points_on_unit_interval_of ys (1 - 1 / real (2 * length ys)) = 
                  Some (ys ! (length ys - 1))\<close> assms(1) domI domIff ex_up dom_fun_upd 
          extended_points_on_unit_interval_of_def finite_equidistant_points_on_unit_interval_of 
          insertE le_less_trans length_greater_0_conv linorder_not_le option.simps(3) zero_order(3)
          fun_upd_apply length_greater_0_conv linorder_not_le neq0_conv not_less0 of_nat_0_less_iff 
          nat_0_less_mult_iff not_less_iff_gr_or_eq rel_simps(76) zero_less_divide_1_iff
  proof -
    { fix rr :: real
      have ff1: "\<forall>rs. (rs = [] \<or> \<not> Min (dom (equidistant_points_on_unit_interval_of rs)) < 0) \<or> \<not> (0::nat) < 2"
      using Min_equidistant_points_on_unit_interval_of by force
        have ff2: "\<forall>rs r. (extended_points_on_unit_interval_of rs r = equidistant_points_on_unit_interval_of rs r \<or> 1 = r) \<or> 0 = r"
          using extended_points_on_unit_interval_of_def by force
        have "length ys \<noteq> 0"
          using assms(1) by auto
    then have "(\<not> 1 - 1 / real (2 * length ys) < rr \<or> \<not> rr < 1) \<or> rr \<notin> dom (extended_points_on_unit_interval_of ys)"
using ff2 ff1 by (metis (no_types) Max_equidistant_points_on_unit_interval_of \<open>\<And>m a. (a \<in> dom m) = (m a \<noteq> None)\<close> \<open>\<And>m b a. m a = Some b \<Longrightarrow> a \<in> dom m\<close> \<open>\<And>n. (n \<noteq> 0) = (0 < n)\<close> \<open>\<And>n. 0 \<noteq> numeral n\<close> \<open>\<And>x A. \<lbrakk>finite A; x \<in> A\<rbrakk> \<Longrightarrow> Min A \<le> x\<close> \<open>\<And>x A. \<lbrakk>finite A; x \<in> A\<rbrakk> \<Longrightarrow> x \<le> Max A\<close> \<open>\<And>xs. (0 < length xs) = (xs \<noteq> [])\<close> \<open>\<And>ys. finite (dom (equidistant_points_on_unit_interval_of ys))\<close> \<open>\<And>z y x. \<lbrakk>x \<le> y; y < z\<rbrakk> \<Longrightarrow> x < z\<close> \<open>equidistant_points_on_unit_interval_of ys (1 - 1 / real (2 * length ys)) = Some (ys ! (length ys - 1))\<close> linorder_not_less order_less_irrefl) }
  then show ?thesis
    by blast
qed

  have "1 \<in>  dom (extended_points_on_unit_interval_of ys)"
    by (simp add: extended_points_on_unit_interval_of_def)
  then have "\<forall> z. 1 - 1/(2 * ?l)< z \<and> z \<le> 1 \<longrightarrow> 
           {x' \<in> dom (extended_points_on_unit_interval_of ys). z \<le> x'} = {1}" using not_dom
    by (smt Collect_cong Max_extended_points_on_unit_interval_of Max_ge assms(1) 
        finite_extended_points_on_unit_interval_of le_less_trans le_numeral_extra(1) 
        length_greater_0_conv singleton_conv)
  then have Mi: "\<forall> z. 1 - 1/(2 *?l) < z \<and> z < 1 \<longrightarrow> 
           Min {x' \<in> dom (extended_points_on_unit_interval_of ys). z \<le> x'} = 1" by simp

  have in_dom: "1-1/(2* (length ys)) \<in>  dom (extended_points_on_unit_interval_of ys)"
    using ex_up by auto

  then have Mi_aux: "\<forall> z x'. z < 1 \<and> x' \<le> z \<and> x' \<in> dom (extended_points_on_unit_interval_of ys) \<longrightarrow> 
             x' \<le> 1 - 1/(2* ?l)"
    using not_dom by smt
   then have "\<forall>z.
           \<forall>x'. x' \<in> dom (extended_points_on_unit_interval_of ys) \<and> z < 1 \<and> x' \<le> z \<longrightarrow> 
             x' \<le> 1 - 1/(2* ?l)" 
     using Mi_aux by blast

     have all_smaller: "\<forall>z. 1 - 1/(2 * ?l) \<le> z \<and> z < 1 \<longrightarrow>
           (\<forall>x'. x' \<in> dom (extended_points_on_unit_interval_of ys) \<and> x' \<le> z \<longrightarrow> 
             x' \<le> 1 - 1/(2* ?l))" by (smt not_dom)  
 
   have "1 - 1/(2* length ys) \<in> dom (extended_points_on_unit_interval_of ys)"
     using in_dom by blast
   have "finite (dom (extended_points_on_unit_interval_of (sort ys)))" by simp
   then have finite: "finite {x' \<in> (dom (extended_points_on_unit_interval_of ys)). x' \<le> z}"
       by simp
     have "0 < 1 - 1/(2 * ?l) \<and> 1 - 1/(2 * ?l) \<le> 1" using assms(3) 
       by (smt Min_equidistant_points_on_unit_interval_of Min_le \<open>equidistant_points_on_unit_interval_of 
              ys (1 - 1 / real (2 * length ys)) = Some (ys ! (length ys - 1))\<close> 
           assms(1) domI finite_equidistant_points_on_unit_interval_of le_less_trans 
           le_numeral_extra(1) length_greater_0_conv)
     then have Max_3: "\<forall>x. 1 - 1/(2 * ?l) \<le> x \<and> x < 1 \<longrightarrow> 
          Max {x' \<in> dom (extended_points_on_unit_interval_of (sort ys)). x' \<le> x} \<ge> 1 - 1/(2 * ?l)" 
       using Max_lemma linorder_not_le finite in_dom by (simp add: sorted)

  have non_empty: "\<forall> z. 1 - 1/(2 * ?l) \<le> z \<and>  z < 1 \<longrightarrow> 
         {x' \<in> (dom (extended_points_on_unit_interval_of ys)). x' \<le> z} \<noteq> {}"
     using in_dom by blast
  then have Ma_aux2: "\<forall> z. 1 - 1/(2 * ?l) \<le> z \<and>  z < 1 \<longrightarrow>  
           Max {x' \<in> dom (extended_points_on_unit_interval_of ys). x' \<le> z} \<le> 1 - 1/(2* ?l)" 
    using finite Max_lemma all_smaller Max_3 by simp
   then have Ma: "\<forall> z. 1 - 1/(2 * ?l) \<le> z \<and> z < 1 \<longrightarrow>
           Max {x' \<in> dom (extended_points_on_unit_interval_of ys). x' \<le> z} = 1 - 1/(2* ?l)" 
     using Max_3 sorted by fastforce

  then have n:  "\<forall> z. 1 - 1/(2 * ?l) < z \<and> z < 1 \<longrightarrow> 
             neighbors (extended_points_on_unit_interval_of ys) z = (1 - 1/(2* (length ys)), 1)" 
    using neighbors_def Ma Ma_aux2 Mi by auto

  have a1: "linear_approximation (extended_points_on_unit_interval_of (sort ys)) 1 = extrapolation_1 ys" 
    by (simp add: \<open>1 \<in> dom (extended_points_on_unit_interval_of (sort ys))\<close> 
        defined_point_neighbors_eq ex linear_approximation_def linear_first) 
  have a2: "linear_approximation (extended_points_on_unit_interval_of (sort ys)) (1-1/(2* ?l)) = 
             ys!(?l-1)"
    using in_dom assms(1)
    using defined_point_neighbors_eq ex_up linear_approximation_def linear_second sorted
    by (smt finite_extended_points_on_unit_interval_of linear_lower_bound linear_upper_bound 
         option.sel prod.simps(2))
  then have "linear_approximation (extended_points_on_unit_interval_of (sort ys)) x = 
      linear (1- 1/(2* ?l),ys!(?l-1))  (1, extrapolation_1 ys) x" 
    using a1 a2 n
          linear_approximation_lemma assms
           defined_point_neighbors_eq finite_extended_points_on_unit_interval_of in_dom prod.inject
    by (smt ex ex_up linear_second sorted)
  then show ?thesis
    by (simp add: percentile_def)
qed

text \<open> The extrapolation at 0 is smaller than or equal to the values of the linear approximation
       between 0 and half the distance.\<close>
lemma extrapolation_0_lemma_lower:
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "0 \<le> x \<and> x \<le> 1/(2* (length ys))"
  shows "extrapolation_0 ys \<le> linear (0, extrapolation_0 ys) (1/(2* (length ys)), ys!0) x"
proof -
  have "extrapolation_0 ys \<le> ys!0"
    using assms(1) assms(2) extrapolation_0_def sorted_nth_mono by fastforce
  then show ?thesis by (smt assms(3) linear_lower_bound)
qed

text \<open> The values of the linear approximation between 0 and half the distance are smaller than or
       equal to the first value in the list.\<close>
lemma extrapolation_0_lemma_upper:
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "0 \<le> x \<and> x \<le> 1/(2* (length ys))"
  shows "linear (0, extrapolation_0 ys) (1/(2* (length ys)), ys!0) x \<le> ys!0"
proof -
  have "extrapolation_0 ys \<le> ys!0"
    using assms(1) assms(2) extrapolation_0_def sorted_nth_mono by fastforce
  then show ?thesis
    by (smt assms(3) linear_upper_bound)
qed

text \<open> The last value in the list is smaller than or equal to the linear extrapolation to the right.\<close>
lemma extrapolation_1_lemma_lower:
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "1- 1/(2* (length ys)) \<le> x \<and> x \<le> 1"
  shows "ys!((length ys) - 1) \<le> (linear (1- 1/(2* (length ys)), ys!((length ys) - 1)) (1, extrapolation_1 ys)) x"
proof -
  have smaller: "1- 1/(2* (length ys)) < 1" using assms(2) by force
  have "ys!((length ys) - 2) \<le> ys!((length ys) - 1)" using assms(1) 
    by (metis assms(2) diff_less last_conv_nth length_greater_0_conv nth_mem order.strict_trans 
        pos2 sorted_leq_last zero_less_one)
  then have "(ys!((length ys) -1) - ys!((length ys) -2))* 2.0 \<le> 
             (ys!((length ys) -1) - ys!((length ys) -2))* 3.0"
    by simp
  then have "ys!((length ys) -1)* 2.0 \<le> 
             ys!((length ys) -2)* 2.0 + (ys!((length ys) -1) - ys!((length ys) -2))* 3.0"
    by simp
  then have "ys!((length ys) -1) \<le> 
             ys!((length ys) -2) + (ys!((length ys) -1) - ys!((length ys) -2))* 3.0/2.0"
    by arith
  then have "ys!((length ys) - 1) \<le> extrapolation_1 ys" using extrapolation_1_def
    by metis
  then have "max (ys!((length ys) - 1)) (extrapolation_1 ys) = extrapolation_1 ys"
    using max_def by linarith
  then show ?thesis using smaller assms linear_upper_bound
    by (smt linear_lower_bound)
qed

text \<open> The extrapolation at 1 is greater than or equal to the values of the linear approximation
       between half the distance and 1.\<close>
lemma extrapolation_1_lemma_upper:
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "1- 1/(2* (length ys)) \<le> x \<and> x \<le> 1"
  shows "(linear (1- 1/(2* (length ys)), ys!((length ys) - 1)) (1, extrapolation_1 ys)) x \<le>
         extrapolation_1 ys"
proof -
  have smaller: "1- 1/(2* (length ys)) < 1" using assms(2) by force
  have "ys!((length ys) - 2) \<le> ys!((length ys) - 1)" using assms(1) 
    by (metis assms(2) diff_less last_conv_nth length_greater_0_conv nth_mem order.strict_trans 
        pos2 sorted_leq_last zero_less_one)
  then have "(ys!((length ys) -1) - ys!((length ys) -2))* 2.0 \<le> 
             (ys!((length ys) -1) - ys!((length ys) -2))* 3.0"
    by simp
  then have "ys!((length ys) -1)* 2.0 \<le> 
             ys!((length ys) -2)* 2.0 + (ys!((length ys) -1) - ys!((length ys) -2))* 3.0"
    by simp
  then have "ys!((length ys) -1) \<le> 
             ys!((length ys) -2) + (ys!((length ys) -1) - ys!((length ys) -2))* 3.0/2.0"
    by arith
  then have "ys!((length ys) - 1) \<le> extrapolation_1 ys" using extrapolation_1_def
    by metis
  then have "max (ys!((length ys) - 1)) (extrapolation_1 ys) = extrapolation_1 ys"
    using max_def by linarith
  then show ?thesis using smaller assms linear_upper_bound by metis
qed

text \<open> The extrapolation at 0 is smaller than or equal to the first value in the list.\<close>
lemma extrapolation_0_smaller_first:
  assumes "sorted ys"
  assumes "length ys > 1"
  shows "extrapolation_0 ys \<le> ys!0"
proof -
  have "ys!0 \<le> ys!1"
    using assms(1) assms(2) sorted_nth_mono by blast
  then have "(ys!1 - ys!0)* 2.0 \<le> 
             (ys!1 - ys!0)* 3.0"
    by simp
  then have "ys!1* 2.0 \<le> 
             ys!0* 2.0 + (ys!1 - ys!0)* 3.0"
    by simp
  then have "ys!1 \<le> 
             ys!0 + (ys!1 - ys!0)* 3.0/2.0"
    by arith
  then show ?thesis
    using \<open>ys ! 0 \<le> ys ! 1\<close> extrapolation_0_def by auto
qed

text \<open> The extrapolation at 1 is greater than or equal to the last value in the list.\<close>
lemma extrapolation_1_bigger_last:
  assumes "sorted ys"
  assumes "length ys > 1"
  shows "ys!((length ys) - 1) \<le> extrapolation_1 ys"
proof -
  have "ys!((length ys) - 2) \<le> ys!((length ys) - 1)" using assms(1) 
    by (metis assms(2) diff_less last_conv_nth length_greater_0_conv nth_mem order.strict_trans 
        pos2 sorted_leq_last zero_less_one)
  then have "(ys!((length ys) -1) - ys!((length ys) -2))* 2.0 \<le> 
             (ys!((length ys) -1) - ys!((length ys) -2))* 3.0"
    by simp
  then have "ys!((length ys) -1)* 2.0 \<le> 
             ys!((length ys) -2)* 2.0 + (ys!((length ys) -1) - ys!((length ys) -2))* 3.0"
    by simp
  then have "ys!((length ys) -1) \<le> 
             ys!((length ys) -2) + (ys!((length ys) -1) - ys!((length ys) -2))* 3.0/2.0"
    by arith
  then show ?thesis by (metis extrapolation_1_def)
qed


text \<open> The linear function to the left is monotonically increasing.\<close>
lemma extrapolation_0_lemma_monotonic:
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "0 \<le> x \<and> x \<le> 1/(2* (length ys))"
  asssumes "x \<le> x'"
  shows "(linear (0, extrapolation_0 ys))(1/(2* (length ys)), ys!0)  x \<le>
         (linear (0, extrapolation_0 ys))(1/(2* (length ys)), ys!0)  x'"
proof -
  have "extrapolation_0 ys \<le> ys!0" 
    using assms(1) assms(2) extrapolation_0_smaller_first by blast
  then show ?thesis using linear_monotonic
    by (metis assms(2) assms(5) nat_0_less_mult_iff neq0_conv not_less0 of_nat_0_less_iff 
        zero_less_divide_1_iff zero_less_numeral) 
qed

text \<open> The linear function to the right is monotonically increasing.\<close>
lemma extrapolation_1_lemma_monotonic:
  assumes "sorted ys"
  assumes "length ys > 1"
  assumes "1- 1/(2* (length ys)) \<le> x \<and> x' \<le> 1"
  asssumes "x \<le> x'"
  shows "(linear (1- 1/(2* (length ys)), ys!((length ys) - 1)) (1, extrapolation_1 ys)) x \<le>
         (linear (1- 1/(2* (length ys)), ys!((length ys) - 1)) (1, extrapolation_1 ys)) x'"
proof -
  have "ys!((length ys) -1) \<le> extrapolation_1 ys" 
    using assms(1) assms(2) extrapolation_1_bigger_last by blast
  then show ?thesis 
    by (smt assms(3) assms(5) linear_monotonic)
qed


section \<open>Alternative definition of percentile implementation\<close>

text \<open> The neighbors of a partial function are the maximum of all elements in the domain smaller than the value
       and the minimum of all elements in the domain greater than the value.\<close>
lemma neighbors_alternative_pseudo_def:
  assumes "x \<notin> dom p"
  shows "neighbors p x = (Max {x' \<in> dom p. x' < x}, Min {x' \<in> dom p. x \<le> x'})"
proof -
  have "Max {x' \<in> dom p. x' \<le> x} = Max {x' \<in> dom p. x' < x}"
    by (smt Collect_cong assms)
  from this show ?thesis
    unfolding neighbors_def by simp
qed

text \<open> The inner percentile function in the inner range can be defined as the linear function between
       the left and the right neighbors wrt the equidistant points.\<close>
lemma percentile_inner_alternative_pseudo_def:
  assumes "x \<noteq> 1 / (2 * length ys)"
  shows "percentile_inner ys x =
    (let p = (equidistant_points_on_unit_interval_of (sort ys));
    (x1, x2) = (Max {x' \<in> dom p. x' < x}, Min {x' \<in> dom p. x \<le> x'});
    (y1, y2) = (the (p x1), the (p x2))
    in linear (x1, y1) (x2, y2) x
    )"
proof (cases "x \<in> dom (equidistant_points_on_unit_interval_of (sort ys))")
  case True
  have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))"
    by simp
  from True this show ?thesis
    unfolding percentile_inner_def linear_approximation_def
    apply simp
    using \<open>finite (dom (equidistant_points_on_unit_interval_of (sort ys)))\<close>
    by (smt Collect_cong Pair_inject case_prod_conv defined_point_neighbors_eq linear_first linear_second neighbors_def)
next
  case False
  then show ?thesis
    unfolding percentile_inner_def linear_approximation_def
    apply (subst neighbors_alternative_pseudo_def)
    apply simp
    apply (simp add: Let_def) done
qed

text \<open> The percentile function in the full range can be defined as the linear function between
       the left and the right neighbors wrt the extended points.\<close>
lemma percentile_alternative_pseudo_def:
  (* assumes "x \<noteq> 1 / (2 * length ys)" *)
  shows "percentile ys x =
    (let p = (extended_points_on_unit_interval_of (sort ys));
    (x1, x2) = (Max {x' \<in> dom p. x' < x}, Min {x' \<in> dom p. x \<le> x'});
    (y1, y2) = (the (p x1), the (p x2))
    in linear (x1, y1) (x2, y2) x
    )"
proof (cases "x \<in> dom (extended_points_on_unit_interval_of (sort ys))")
  case True
  have "finite (dom (extended_points_on_unit_interval_of (sort ys)))"
    using extended_points_on_unit_interval_of_def by auto
  from True this show ?thesis
    unfolding percentile_def linear_approximation_def
    apply simp
    using \<open>finite (dom (extended_points_on_unit_interval_of (sort ys)))\<close>
    by (smt Collect_cong Pair_inject case_prod_conv defined_point_neighbors_eq linear_lower_bound linear_second linear_upper_bound neighbors_def)
next
  case False
  then show ?thesis
    unfolding percentile_def linear_approximation_def
    apply (subst neighbors_alternative_pseudo_def)
    apply simp
    apply (simp add: Let_def) done
qed

section \<open>Properties of Percentile\<close>

text \<open> The percentile function has an upper bound, the maximal value in the associated set. \<close>

section \<open>Properties of Percentile\<close>

text \<open> The inner percentile function has an upper bound, the maximal value in the associated set. \<close>
lemma percentile_inner_upper_bound:
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / (2 * length ys)"
  shows "percentile_inner ys x \<le> Max (set ys)"
proof -
  have "percentile_inner ys x = linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) x"
    unfolding percentile_inner_def ..
  also have "\<dots> \<le> Max (ran (equidistant_points_on_unit_interval_of (sort ys)))"
  proof -
    have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))" by simp
    moreover have "x \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
      using defined_interval_of_equidistant_points_on_unit_interval_of
      using assms(1, 2) atLeastAtMost_iff
      by (simp add: sort_eq_Nil_iff)
    ultimately show ?thesis by (rule upper_bound)
  qed
  also have "\<dots> = Max (set ys)"
    using ran_equidistant_points_on_unit_interval_of \<open>ys \<noteq> []\<close> by simp
  finally show ?thesis .
qed

text \<open> The percentile_inner function has a lower bound, the minimal value in the associated set. \<close>
lemma percentile_inner_lower_bound:
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / (2 * length ys)"
  shows "Min (set ys) \<le> percentile_inner ys x"
proof -
  have "Min (set ys) = Min (ran (equidistant_points_on_unit_interval_of (sort ys)))"
    using ran_equidistant_points_on_unit_interval_of \<open>ys \<noteq> []\<close> by simp
  also have "\<dots> \<le>  linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) x"
  proof -
    have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))" by simp
    moreover have "x \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
      using defined_interval_of_equidistant_points_on_unit_interval_of
      using assms(1, 2) atLeastAtMost_iff
      by (simp add: sort_eq_Nil_iff)
    ultimately show ?thesis by (rule lower_bound)
  qed
  also have "\<dots> = percentile_inner ys x"
    unfolding percentile_inner_def ..
  finally show ?thesis .
qed

text \<open> The percentile function has a lower bound, the extrapolated value at 0. \<close>
lemma percentile_lower_bound:
  assumes "length ys > 1"
  assumes "sorted ys"
  assumes "0 \<le> x \<and> x \<le> 1"
  shows "extrapolation_0 ys \<le> percentile ys x"
proof -
  have "1/(2 * (length ys)) \<le> x \<and> x \<le> 1 - 1/(2 * (length ys)) \<longrightarrow>
      Min (set ys) \<le> percentile ys x"
    using assms percentile_alt1 percentile_inner_lower_bound
    by (metis length_greater_0_conv linorder_neqE_nat not_less_zero)
  have "ys!0 \<le> ys!1" using assms 
    by (simp add: sorted_nth_mono)
  then have "extrapolation_0 ys \<le> ys!0" using extrapolation_0_def
    by simp
  have "ys!0 = Min (set ys)"
    using Min_eqI assms(1) assms(2)
          mem_Collect_eq nat_less_le not_one_le_zero nth_mem order_refl 
          set_conv_nth  List.finite_set linorder_neqE_nat not_less_zero
          sorted_iff_nth_mono zero_le le_trans assms 
          proof -
             have "0 < length ys" by (meson assms(1) le_trans not_le zero_le)
             then show ?thesis by (metis (no_types) List.finite_set Min_eqI assms(2) 
             in_set_conv_nth sorted_nth_mono zero_le)
          qed
  then have "extrapolation_0 ys \<le> Min (set ys)"
    using \<open>extrapolation_0 ys \<le> ys ! 0\<close> by linarith
  then have "1/(2 * (length ys)) \<le> x \<and> x \<le> 1 - 1/(2 * (length ys)) \<longrightarrow> ?thesis"
    using \<open>1 / real (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / real (2 * length ys) \<longrightarrow> 
             Min (set ys) \<le> percentile ys x\<close> by linarith
  have "ys!((length ys)-2) \<le> ys!((length ys)-1)" 
    by (metis assms(1) assms(2) diff_less last_conv_nth length_greater_0_conv nth_mem 
        order.strict_trans pos2 sorted_leq_last zero_less_one)
  then have "ys!((length ys) -1)* 2.0 \<le> ys!((length ys) -2) * 2.0 + 
                    (ys!((length ys)-1) - ys!((length ys)-2))* 3.0" by simp
  then have "ys!((length ys) -1) \<le> ys!((length ys) -2) + 
                    (ys!((length ys)-1) - ys!((length ys)-2))* 3.0/2.0"
    by linarith
  then have "ys!((length ys) -1) \<le> extrapolation_1 ys" using extrapolation_1_def
    by metis
  then have "1 - 1 / (2 * length ys) < x \<and> x \<le> 1 \<longrightarrow> ?thesis"
    by (smt \<open>extrapolation_0 ys \<le> ys ! 0\<close> assms(1) assms(2) diff_less le_less_trans 
        le_numeral_extra(1) less_numeral_extra(1) linear_lower_bound percentile_alt3 
        sorted_iff_nth_mono_less zero_less_diff)
 have "0 \<le> x \<and> x < 1/(2 * (length ys)) \<longrightarrow> ?thesis"
   using assms(1) assms(2) extrapolation_0_lemma_lower percentile_alt2 by auto
  show ?thesis
    using \<open>0 \<le> x \<and> x < 1 / real (2 * length ys) \<longrightarrow> extrapolation_0 ys \<le> percentile ys x\<close> 
          \<open>1 - 1 / real (2 * length ys) < x \<and> x \<le> 1 \<longrightarrow> 
            extrapolation_0 ys \<le> percentile ys x\<close> 
          \<open>1 / real (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / real (2 * length ys) \<longrightarrow> 
           extrapolation_0 ys \<le> percentile ys x\<close> assms(3) by linarith
qed

text \<open> The percentile function has an upper bound, the extrapolated value at 1. \<close>
lemma percentile_upper_bound:
  assumes "length ys > 1"
  assumes "sorted ys"
  assumes "0 \<le> x \<and> x \<le> 1"
  shows "percentile ys x \<le> extrapolation_1 ys"
proof -
  have "1/(2 * (length ys)) \<le> x \<and> x \<le> 1 - 1/(2 * (length ys)) \<longrightarrow>
      percentile ys x \<le> Max (set ys)"
    using assms percentile_alt1 percentile_inner_lower_bound
    by (metis length_greater_0_conv linorder_neqE_nat 
        not_less_zero percentile_inner_upper_bound)
  have "ys!((length ys)-2) \<le> ys!((length ys)-1)" using assms 
    by (simp add: sorted_nth_mono)
  then have "0 \<le> (ys!((length ys) -1) - ys!((length ys) -2))"
    by linarith
  then have "ys!((length ys) -1)* 2.0 \<le> ys!((length ys) -2) * 2.0 + 
                    (ys!((length ys)-1) - ys!((length ys)-2))* 3.0" by simp
  then have "ys!((length ys) -1) \<le> ys!((length ys) -2) + 
                    (ys!((length ys)-1) - ys!((length ys)-2))* 3.0/2.0"
    by linarith
  then have "ys!((length ys) -1) \<le> extrapolation_1 ys" using extrapolation_1_def
    by metis
  have "ys!((length ys) -1) = Max (set ys)"
    by (smt List.finite_set Max_ge Max_in assms(1) assms(2) diff_less empty_iff 
        last_conv_nth length_greater_0_conv nth_mem order.strict_trans sorted_leq_last 
        zero_less_one)
  then have "Max (set ys) \<le> extrapolation_1 ys"
    using \<open>ys ! (length ys - 1) \<le> extrapolation_1 ys\<close> by linarith
  then have "1/(2 * (length ys)) \<le> x \<and> x \<le> 1 - 1/(2 * (length ys)) \<longrightarrow> ?thesis"
    using \<open>1 / real (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / real (2 * length ys) \<longrightarrow>
          percentile ys x \<le> Max (set ys)\<close> by linarith
  have "1 - 1/(2 * (length ys)) < x \<and> x \<le> 1  \<longrightarrow> percentile ys x \<le> extrapolation_1 ys" 
      using extrapolation_1_lemma_upper percentile_alt3 assms(1) assms(2) by simp
    then have "1 - 1/(2 * (length ys)) < x \<and> x \<le> 1 \<longrightarrow> ?thesis" by blast
  have "0 \<le> x \<and> x < 1/(2 * (length ys)) \<longrightarrow> percentile ys x \<le> ys!0"
    using assms(1) assms(2) extrapolation_0_lemma_upper percentile_alt2 by auto
  then have "0 \<le> x \<and> x < 1/(2 * (length ys)) \<longrightarrow> percentile ys x \<le> ys!((length ys) -1)"
    by (smt assms(1) assms(2) last_conv_nth le_less_trans le_numeral_extra(1) 
       length_greater_0_conv nth_mem sorted_leq_last)
  then have "0 \<le> x \<and> x < 1/(2 * (length ys)) \<longrightarrow> ?thesis"
    using \<open>ys ! (length ys - 1) \<le> extrapolation_1 ys\<close> by linarith
  then show ?thesis
    using \<open>1 - 1 / real (2 * length ys) < x \<and> x \<le> 1 \<longrightarrow> 
           percentile ys x \<le> extrapolation_1 ys\<close> 
         \<open>1 / real (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / real (2 * length ys) \<longrightarrow> 
           percentile ys x \<le> extrapolation_1 ys\<close> assms(3) by linarith
qed

text \<open> In a sorted list of distinct elements with indices i and j holds that i is smaller than 
  (or equal to) j if and only if the ith element is smaller than (or equal to) the jth. \<close> 
lemma nth_leq_iff_index_leq:
  assumes "distinct xs" "sorted xs"
  assumes "i < length xs" "j < length xs"
  shows "xs ! i \<le> xs ! j \<longleftrightarrow> i \<le> j"
  using assms
  by (metis antisym nat_le_linear nth_eq_iff_index_eq sorted_nth_mono)

text \<open> If x \<le> x' and both correspond to a value of equidistant_points_on_unit_interval_of, that is, 
       they are both defined then for the values y and y' it also holds that y \<le> y'. \<close>
lemma sorted_imp:
  assumes "sorted ys"
  assumes "equidistant_points_on_unit_interval_of ys x = Some y"
  assumes "equidistant_points_on_unit_interval_of ys x' = Some y'"
  assumes "x \<le> x'"
  shows "y \<le> y'"
proof -
  let ?xs = "map (\<lambda>x. (1 / length ys) * (x + 0.5)) [0..<length ys]"
  from assms(2) have "x \<in> dom (equidistant_points_on_unit_interval_of ys)" by blast
  from this obtain i where "x = ?xs ! i" and "i < length ys"
    unfolding equidistant_points_on_unit_interval_of_def
    apply auto    
    by blast
  from assms(3) have "x' \<in> dom (equidistant_points_on_unit_interval_of ys)" by blast
  from this obtain i' where "x' = ?xs ! i'" and "i' < length ys"
    unfolding equidistant_points_on_unit_interval_of_def
    apply auto apply force done
  have "sorted ?xs \<and> distinct ?xs"
    by (auto intro!: inj_onI simp add: divide_right_mono sorted_iff_nth_mono_less distinct_map)
  have "length ?xs = length ys" by auto
  from assms(2) \<open>x = _\<close> \<open>i < _\<close> have "y = ys ! i"
    unfolding equidistant_points_on_unit_interval_of_def
    using \<open>length _ = length _\<close> \<open>sorted _ \<and> distinct _\<close> by (metis map_of_zip_nth option.inject)
  from assms(3) \<open>x' = _\<close> \<open>i' < _\<close> have "y' = ys ! i'"
    unfolding equidistant_points_on_unit_interval_of_def
    using \<open>length _ = length _\<close> \<open>sorted _ \<and> distinct _\<close> by (metis map_of_zip_nth option.inject)
  from \<open>sorted _ \<and> distinct _\<close> \<open>x \<le> x'\<close> have "i \<le> i'"
    using \<open>x = _\<close> \<open>x' = _\<close> \<open>i < _\<close> \<open>i'< _\<close> \<open>length ?xs = length ys\<close>
    using nth_leq_iff_index_leq by fastforce
  show ?thesis
    using \<open>i \<le> i'\<close> \<open>y = ys ! i\<close> \<open>y' = ys ! i'\<close> \<open>i' < length ys\<close> \<open>sorted ys\<close>
    by (simp add: sorted_nth_mono)
qed

text \<open> The percentile_inner function is (weakly) monotonic increasing. \<close>
lemma percentile_inner_monotonic:
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) \<le> x" "x' \<le> 1 - 1 / (2 * length ys)"
  assumes "x \<le> x'"
  shows "percentile_inner ys x \<le> percentile_inner ys x'"
proof -
  have "percentile_inner ys x = linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) x"
    unfolding percentile_inner_def ..
  also have "\<dots> \<le> linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) x'"
  proof -
    from \<open>ys \<noteq> []\<close> have s: "sort ys \<noteq> []" by (simp add: sort_eq_Nil_iff) 
    have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))" by simp
    moreover have "x \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
      using defined_interval_of_equidistant_points_on_unit_interval_of
      using assms s atLeastAtMost_iff      
      by fastforce
    moreover have "x' \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
      using defined_interval_of_equidistant_points_on_unit_interval_of
      using assms atLeastAtMost_iff s by fastforce      
    moreover have "\<forall>x x' y y'. x \<le> x' \<and> equidistant_points_on_unit_interval_of (sort ys) x = Some y
      \<and> equidistant_points_on_unit_interval_of (sort ys) x' = Some y' \<longrightarrow> y \<le> y'"
      using sorted_imp sorted_sort by blast      
    moreover note \<open>x \<le> x'\<close>
    ultimately show ?thesis by (rule linear_approximation_monotonic)
  qed
  also have "\<dots> \<le> percentile_inner ys x'"
    unfolding percentile_inner_def ..
  finally show ?thesis .
qed

text \<open> The percentile function is (weakly) monotonic increasing. \<close>
lemma percentile_monotonic:
  assumes "length ys > 1"
  assumes "0 \<le> x" "x' \<le> 1"
  assumes "x \<le> x'"
  assumes "sorted ys"
  shows "percentile ys x \<le> percentile ys x'"
proof -
  have inner: "1 / (2 * length ys) \<le> x \<and> x' \<le> 1 - 1 / (2 * length ys) \<longrightarrow> 
        percentile ys x \<le> percentile ys x'"
    using assms(1) assms(4) percentile_alt1 percentile_inner_monotonic
       by (smt assms(5) le_less_trans le_numeral_extra(1) length_greater_0_conv)
  have "0 \<le> x \<and> x' \<le> 1 / (2 * length ys) \<longrightarrow>
         (linear (0, extrapolation_0 ys))(1/(2* (length ys)), ys!0)  x \<le>
         (linear (0, extrapolation_0 ys))(1/(2* (length ys)), ys!0)  x'"
    using extrapolation_0_lemma_monotonic assms(1) assms(4) assms(5) by auto
  then have lower: "0 \<le> x \<and> x' < 1 / (2 * length ys) \<longrightarrow> percentile ys x \<le> percentile ys x'"
    using percentile_alt2 assms(4) assms(5) assms(1) by auto

  have "1 - 1 / (2 * length ys) \<le> x \<and> x' \<le> 1 \<longrightarrow>
         (linear (1 - 1 / (2 * length ys), ys!((length ys) -1)) (1, extrapolation_1 ys)) x \<le>
         (linear (1 - 1 / (2 * length ys), ys!((length ys) -1)) (1, extrapolation_1 ys)) x'"
    using extrapolation_1_lemma_monotonic assms(1) assms(4) assms(5) by auto
  then have upper: "1 - 1 / (2 * length ys) < x \<and> x' \<le> 1 \<longrightarrow> percentile ys x \<le> percentile ys x'"
    using percentile_alt3 assms(4) assms(5) assms(1) by auto

  have "0 \<le> x \<and> x < 1 / (2 * length ys) \<and> 1 / (2 * length ys) \<le> x' \<and> x'\<le>1 \<longrightarrow> 
        percentile ys x \<le> ys!0"
    using assms(1) assms(5) extrapolation_0_lemma_upper percentile_alt2 by auto 

 have "0 \<le> x \<and> x \<le> 1 / (2 * length ys) \<and> 1 / (2 * length ys) \<le> x' \<and> x'\<le>1 \<longrightarrow> 
       Min (set ys) \<le> percentile ys x'" using percentile_inner_lower_bound percentile_alt1 
   by (smt List.finite_set Min_le assms(1) assms(5) diff_less 
       extrapolation_1_bigger_last le_less_trans le_numeral_extra(1) 
       length_greater_0_conv less_numeral_extra(1) linear_lower_bound 
       nth_mem percentile_alt3)
  have "ys!0 = Min (set ys)"
  proof -
  have f1: "\<forall>x0 x1. ((x1::real) \<le> x0) = (0 \<le> x0 + - 1 * x1)"
  by fastforce
  obtain rr :: "real \<Rightarrow> real set \<Rightarrow> real" where
f2: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> \<not> 0 \<le> v2 + - 1 * x0) = (rr x0 x1 \<in> x1 \<and> \<not> 0 \<le> rr x0 x1 + - 1 * x0)"
by moura
  have f3: "\<forall>r R. (0 \<le> rr r R + - 1 * r) = (r + - 1 * rr r R \<le> 0)"
    by auto
have f4: "\<forall>x0 x1 x2. (x2 ! x1 \<le> x2 ! x0) = (x2 ! x1 + - (1::real) * x2 ! x0 \<le> 0)"
  by auto
  obtain nn :: "real list \<Rightarrow> real \<Rightarrow> nat" where
"\<forall>x0 x1. (\<exists>v2. \<not> length x0 \<le> v2 \<and> x0 ! v2 = x1) = (\<not> length x0 \<le> nn x0 x1 \<and> x0 ! nn x0 x1 = x1)"
    by moura
  then have "\<forall>r rs. (r \<notin> set rs \<or> \<not> length rs \<le> nn rs r \<and> rs ! nn rs r = r) \<and> (r \<in> set rs \<or> (\<forall>n. length rs \<le> n \<or> rs ! n \<noteq> r))"
    by (meson in_set_conv_nth not_le)
  then have f5: "rr (ys ! 0) (set ys) \<notin> set ys \<or> ys ! 0 + - 1 * rr (ys ! 0) (set ys) \<le> 0"
    using f4 by (metis assms(5) not_le not_less0 sorted_iff_nth_mono)
  have "ys ! 0 \<in> set ys"
    by (meson assms(1) le_less_trans not_le not_less0 nth_mem)
  then show ?thesis
    using f5 f3 f2 f1 by (metis (no_types) List.finite_set Min_eqI)
qed
  then have "0 \<le> x \<and> x \<le> 1 / (2 * length ys) \<and> 1 / (2 * length ys) \<le> x' \<and> x'\<le>1 \<longrightarrow> 
       ys!0 \<le> percentile ys x'" using assms
             \<open>0 \<le> x \<and> x \<le> 1 / real (2 * length ys) \<and> 1 / real (2 * length ys) \<le> x' \<and>
              x' \<le> 1 \<longrightarrow> Min (set ys) \<le> percentile ys x'\<close> by linarith
  then have lower_inner: "0 \<le> x \<and> x \<le> 1 / (2 * length ys) \<and> 1 / (2 * length ys) \<le> x' \<and> x'\<le>1  
        \<longrightarrow> percentile ys x \<le> percentile ys x'"
    by (smt List.finite_set Max_in \<open>0 \<le> x \<and> x < 1 / real (2 * length ys) \<and> 
          1 / real (2 * length ys) \<le> x' \<and> x' \<le> 1 \<longrightarrow> percentile ys x \<le> ys ! 0\<close> 
          assms(1) assms(5) empty_iff extrapolation_1_bigger_last inner last_conv_nth 
          le_less_trans le_numeral_extra(1) length_greater_0_conv linear_lower_bound 
          nth_mem percentile_alt1 percentile_alt3 percentile_inner_upper_bound sorted_leq_last upper)

  have "0 \<le> x \<and> x < 1 - 1 / (2 * length ys) \<and> (1 - 1 / (2 * length ys)) < x' \<and> x'\<le> 1 \<longrightarrow>
        ys!((length ys) -1) \<le> percentile ys x'"
    using assms(1) assms(5) extrapolation_1_lemma_lower percentile_alt3 by auto 

   have "0 \<le> x \<and> x \<le> 1 - 1 / (2 * length ys) \<and> (1 - 1 / (2 * length ys)) \<le> x' \<and> x'\<le> 1 \<longrightarrow> 
       percentile ys x \<le> Max (set ys)" using percentile_inner_upper_bound percentile_alt1 
     by (smt List.finite_set Max_ge assms(1) assms(5) extrapolation_0_lemma_upper le_less_trans 
        le_numeral_extra(1) length_greater_0_conv nth_mem percentile_alt2)
   then have inner_upper: "0 \<le> x \<and> x < 1 - 1 / (2 * length ys) \<and> 
          (1 - 1 / (2 * length ys)) < x' \<and> x'\<le> 1  
        \<longrightarrow> percentile ys x \<le> percentile ys x'" 
     by (smt List.finite_set Max_in assms(1) assms(5) empty_iff extrapolation_1_bigger_last 
         last_conv_nth le_less_trans le_numeral_extra(1) length_greater_0_conv linear_lower_bound 
         nth_mem percentile_alt3 sorted_leq_last)
  show ?thesis using upper inner lower lower_inner inner_upper assms(2) assms(3) 
    by (smt List.finite_set Max_in \<open>0 \<le> x \<and> x \<le> 1 - 1 / real (2 * length ys) \<and> 
         1 - 1 / real (2 * length ys) \<le> x' \<and> x' \<le> 1 \<longrightarrow> percentile ys x \<le> Max (set ys)\<close> 
         assms(1) assms(5) empty_iff extrapolation_1_bigger_last last_conv_nth le_less_trans 
         le_numeral_extra(1) length_greater_0_conv linear_lower_bound nth_mem percentile_alt3 
         sorted_leq_last)
qed

text \<open> The percentile_inner function is Lipschitz continuous. \<close>
lemma percentile_inner_Lipschitz:
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / (2 * length ys)"
  assumes "1 / (2 * length ys) \<le> x' \<and> x' \<le> 1 - 1 / (2 * length ys)"
  shows "\<exists>K. \<bar>percentile_inner ys x' - percentile_inner ys x\<bar> \<le> K * \<bar>x' - x\<bar>"
proof -
  have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))" by simp
  moreover have "x \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
    using defined_interval_of_equidistant_points_on_unit_interval_of
    using assms(1, 2) atLeastAtMost_iff
    by (simp add: sort_eq_Nil_iff)
  moreover have "x' \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
    using defined_interval_of_equidistant_points_on_unit_interval_of
    using assms(1, 3) atLeastAtMost_iff
    by (simp add: sort_eq_Nil_iff)
  ultimately show ?thesis
    unfolding percentile_inner_def by (rule linear_approximation_Lipschitz)
qed



text \<open> The percentile function scales by constant (positive) factors inside the definition interval.\<close>
lemma percentile_inner_scale:
  assumes "length ys > 1"
  assumes "1 / (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / (2 * length ys)"
  assumes "c > 0"
  assumes "sorted ys"
  shows "percentile_inner (map (\<lambda> z. c*z) ys) x = c * percentile_inner ys x"
proof -
  have a: "finite (dom ((equidistant_points_on_unit_interval_of ys)))" by simp
  have "x \<in> defined_interval_of (equidistant_points_on_unit_interval_of ys)" 
    using equidistant_points_on_unit_interval_of_def  
    by (metis (no_types, lifting) assms(1) assms(2) atLeastAtMost_iff 
        defined_interval_of_equidistant_points_on_unit_interval_of le_less_trans le_numeral_extra(1) 
        length_greater_0_conv)
  then have b: "linear_approximation (\<lambda>y. map_option (\<lambda>z. c * z) ((equidistant_points_on_unit_interval_of ys) y)) x = 
        c * linear_approximation (equidistant_points_on_unit_interval_of ys)  x" 
    using linear_approximation_scale a by blast
  have c: "linear_approximation (\<lambda>y. map_option (\<lambda>z. c * z) ((equidistant_points_on_unit_interval_of ys) y)) x =
        c * percentile_inner ys x" by (simp add: assms(4) b percentile_inner_def sorted_sort_id)
  have d: "map_option (\<lambda>z. c * z) ((equidistant_points_on_unit_interval_of ys) y) =
        (equidistant_points_on_unit_interval_of (map (\<lambda> z. c*z) ys)) y" 
    using equidistant_points_on_unit_interval_of_def map_option_def map_def assms
    equidistant_linear by auto
  have "sort (map (\<lambda> z. c*z) ys) = map (\<lambda> z. c*z) (sort ys)" using assms(3) sorted_map
    by (simp add: assms(4) sorted_sort_id)
  then have d: "c * percentile_inner ys x = linear_approximation (equidistant_points_on_unit_interval_of (map (\<lambda> z. c*z) (sort ys))) x"
    using assms equidistant_linear d assms(4) c sorted_sort_id by fastforce
  then show ?thesis using percentile_inner_def b c
    by (simp add: b \<open>sort (map ((*) c) ys) = map ((*) c) (sort ys)\<close>)
qed

text \<open> The percentile function scales by constant (positive) factors.\<close>
lemma percentile_scale:
  assumes "length ys > 1"
  assumes "c > 0"
  assumes "sorted ys"
  assumes "0 \<le> x \<and> x \<le> 1"
  shows "percentile (map (\<lambda> z. c*z) ys) x = c * percentile ys x"
proof -
  have middle: "1 / (2 * length ys) \<le> x \<and> x \<le> 1 - 1 / (2 * length ys) \<longrightarrow>  percentile (map (\<lambda> z. c*z) ys) x = c * percentile ys x"
    using percentile_inner_scale
    using Percentile.sorted_map assms(1) assms(2) assms(3) percentile_alt1 by auto
  have index0: "(map (\<lambda> z. c*z) ys)!0 = c* ys!0" using assms(1)
    by (meson le_less_trans le_numeral_extra(1) nth_map)
  have index1: "(map (\<lambda> z. c*z) ys)!1 = c* ys!1" using assms(1) by auto
  have "extrapolation_0 (map (\<lambda> z. c *z) ys) = 
        c * (extrapolation_0 ys)"  using extrapolation_0_def index0 index1
    by (simp add: linordered_field_class.sign_simps(19))
  then have left: "0 \<le> x \<and> x < 1 / (2 * length ys) \<longrightarrow> percentile (map (\<lambda> z. c*z) ys) x = c * percentile ys x" using percentile_alt2
    using Percentile.sorted_map assms(1) assms(2) assms(3)
    by (smt Linear_Interpolation.linear_scale le_less_trans le_numeral_extra(1) length_map nth_map)
  have indexl1: "(map (\<lambda> z. c*z) ys)!((length ys) -1) = c* ys!((length ys) -1)" using assms(1) by auto
  have indexl2: "(map (\<lambda> z. c*z) ys)!((length ys) -2) = c* ys!((length ys) -2)" using assms(1) by auto
  then have "extrapolation_1 (map (\<lambda> z. c *z) ys) = 
        c * (extrapolation_1 ys)"  using assms extrapolation_1_def sorted_map
        length_map linordered_field_class.sign_simps(18)  linordered_field_class.sign_simps(19) 
        linordered_field_class.sign_simps(23) times_divide_eq_right indexl1 indexl2
    by (metis (no_types, hide_lams))
   then have right: "x > 1 -  1 / (2 * length ys) \<and> x \<le> 1 \<longrightarrow> percentile (map (\<lambda> z. c*z) ys) x = c * percentile ys x" using percentile_alt3
     using Linear_Interpolation.linear_scale Percentile.sorted_map assms(1) assms(2) assms(3) by auto
   show ?thesis using left middle right
     using assms(4) by linarith 
qed

text \<open> The percentile function is Lipschitz continuous. \<close>
lemma percentile_Lipschitz:
  assumes "length ys > 1"
  assumes "sorted ys"
  assumes "0 \<le> x \<and> x \<le> 1"
  assumes "0 \<le> x' \<and> x' \<le> 1"
  shows "\<exists>K. \<bar>percentile ys x' - percentile ys x\<bar> \<le> K * \<bar>x' - x\<bar>"
  by    (metis diff_ge_0_iff_ge diff_gt_0_iff_gt less_le linear mult_zero_left 
         real_archimedian_rdiv_eq_0 zero_less_abs_iff)

end
