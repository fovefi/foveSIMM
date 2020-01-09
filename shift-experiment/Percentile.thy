text \<open> Version 0.4, last changed 2018-02-27 
  (C) fovefi ltd, www.fovefi.co 
  (author: Lukas Bulwahn [lubu@fovefi.co], comments by Manfred Kerber [make@fovefi.co])
 
  Dually licenced under
  Creative Commons Attribution (CC-BY) 4.0 [https://creativecommons.org/licenses/by/4.0/]
  ISC License (1-clause BSD License)       [https://www.isc.org/downloads/software-support-policy/isc-license/]
  See LICENSE files for details.
  (Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
 
  In this file, an abstract definition of the  percentile function in Isabelle is given.
  The percentile function is defined as a linear approximation between points defined for a partial 
  function defined for finitely many elements. 
 
  It is perhaps best been explained with the help of an example.
  Let us assume that you have a list of 5 real numbers xs = [7, 9, 1, 4, 5] in order to compute a 
  particular percentile, e.g., of 0.75, first you order the list and get sxs = [1, 4, 5, 8, 10]. Then you put 5 values
  (length of the list) on the unit interval [0;1] at equal distances of 1/5, staying away 1/10 from
  the left and right border, that is, you get [0.1, 0.3, 0.5, 0.7, 0.9]. For these values you take
  as percentile the corresponding value in the sorted list, that is, the percentile at 0.1 is  1, at
  0.3 is 4, at 0.5 is 5, at 0.7 is 8, and at 0.9 is 10. For values between any two values, the linear
  interpolation between a = 0.7 and b = 0.9 is taken, that is, as f(a) + (f(b) - f(a))/(b - a) * (x - a).
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

text \<open> Every element in a list is smaller than or equal to the last element. \<close>
lemma sorted_leq_last:
  assumes "sorted xs"
  assumes "x \<in> set xs"
  shows "x \<le> last xs"
using assms 
  by (metis eq_iff in_set_conv_decomp_last last.simps last_append last_in_set list.simps(3) sorted.simps(2) sorted_append)
 
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

text \<open> In a well-ordered set, {a..<b} is the set of all elements between a and b (a included, b excluded) 
  If this set is non-empty and finite, a is its minimum. \<close>
lemma Min_intv:
  assumes "{a..<b} \<noteq> {}"
 assumes "finite {a..<b}"
  shows "Min {a..<b} = a"
using assms by (auto intro: Min_eqI)

text \<open> For a set {a..<b} of natural numbers is the set of all elements between a and b 
 (a included, b excluded). If that set is non-empty and finite, b-1 is its maxumum. \<close>
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

text \<open> The minimal value of equidistant_points_on_unit_interval_of is at half the distant from 0. \<close>
lemma Min_equidistant_points_on_unit_interval_of:
  assumes "ys \<noteq> []"
  shows "Min (dom (equidistant_points_on_unit_interval_of ys)) = 1 / (2 * length ys)"
proof -
  have "incseq (\<lambda>x. (1 / length ys) * (x + 0.5))"
    by (auto simp add: incseq_def divide_right_mono)
  from this dom_equidistant_points_on_unit_interval_of show ?thesis
    using \<open>ys \<noteq> []\<close> \<open>incseq _\<close> by (auto simp add: mono_Min_commute[symmetric] Min_intv)
qed

text \<open> The maximal value of equidistant_points_on_unit_interval_of is at half the distant from 1. \<close>
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

text \<open> The following lemma states that the points where the function given by 
  equidistant_points_on_unit_interval_of is
  defined are all in the interval between 1/(2 * length ys) and 1 - 1/(2 * length ys), that is, 
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

section \<open>Definition of percentile\<close>

definition epsilon :: real
  where 
    "epsilon  = 1 / 10"

text \<open> Percentile is a linear approximation of the equidistant points on the unit interval of the sorted list.
  E.g., for a list [3,1,4,8,6], the x percentile is determined by first sorting the list to [1,3,4,6,8],
  then the unit interval is subdivided by adding the 5 points 0.1, 0.3, 0.5, 0.7, and 0.9. The 0.1 
  percentile is then 1, the 0.3 percentile 3, the 0.5 percentile 4, and so on. For values in between,
  e.g., the 0.4 percentile, a linear approximation of the 0.3 percentile and the 0.5 percentile is computed,
  that is, in this case the value is precisely between 3 and 4, that is, 3.5. 
  Note that this expression deals with a priori infinite objects and is as a consequence not computational.
  A computational version of percentile can be found in Percentile_Code.thy. \<close>
definition percentile :: "real list \<Rightarrow> real \<Rightarrow> real"
where
  "percentile ys x = linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) (x - epsilon)"

section \<open>Alternative definition of percentile implementation\<close>

lemma neighbors_alternative_pseudo_def:
  assumes "x \<notin> dom p"
  shows "neighbors p x = (Max {x' \<in> dom p. x' < x}, Min {x' \<in> dom p. x \<le> x'})"
proof -
  have "Max {x' \<in> dom p. x' \<le> x} = Max {x' \<in> dom p. x' < x}"
    by (smt Collect_cong assms)
  from this show ?thesis
    unfolding neighbors_def by simp
qed

lemma percentile_alternative_pseudo_def:
  assumes "x - epsilon \<noteq> 1 / (2 * length ys)"
  shows "percentile ys x =
    (let p = (equidistant_points_on_unit_interval_of (sort ys));
    (x1, x2) = (Max {x' \<in> dom p. x' < (x - epsilon)}, Min {x' \<in> dom p. (x - epsilon) \<le> x'});
    (y1, y2) = (the (p x1), the (p x2))
    in linear (x1, y1) (x2, y2) (x - epsilon)
    )"
proof (cases "(x - epsilon) \<in> dom (equidistant_points_on_unit_interval_of (sort ys))")
  case True
  have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))"
    by simp
  from True this show ?thesis
    unfolding percentile_def linear_approximation_def
    apply simp
    using \<open>finite (dom (equidistant_points_on_unit_interval_of (sort ys)))\<close>
    by (smt Collect_cong Pair_inject case_prod_conv defined_point_neighbors_eq linear_first linear_second neighbors_def)
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
lemma percentile_upper_bound:
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) \<le> (x - epsilon) \<and> (x - epsilon) \<le> 1 - 1 / (2 * length ys)"
  shows "percentile ys x \<le> Max (set ys)"
proof -
  have "percentile ys x = linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) (x - epsilon)"
    unfolding percentile_def ..
  also have "\<dots> \<le> Max (ran (equidistant_points_on_unit_interval_of (sort ys)))"
  proof -
    have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))" by simp
    moreover have "(x - epsilon) \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
      using defined_interval_of_equidistant_points_on_unit_interval_of
      using assms(1, 2) atLeastAtMost_iff
      by (simp add: sort_eq_Nil_iff)
    ultimately show ?thesis by (rule upper_bound)
  qed
  also have "\<dots> = Max (set ys)"
    using ran_equidistant_points_on_unit_interval_of \<open>ys \<noteq> []\<close> by simp
  finally show ?thesis .
qed

text \<open> The percentile function has a lower bound, the minimal value in the associated set. \<close>
lemma percentile_lower_bound:
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) \<le> (x - epsilon) \<and> (x - epsilon) \<le> 1 - 1 / (2 * length ys)"
  shows "Min (set ys) \<le> percentile ys x"
proof -
  have "Min (set ys) = Min (ran (equidistant_points_on_unit_interval_of (sort ys)))"
    using ran_equidistant_points_on_unit_interval_of \<open>ys \<noteq> []\<close> by simp
  also have "\<dots> \<le>  linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) (x - epsilon)"
  proof -
    have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))" by simp
    moreover have "(x - epsilon) \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
      using defined_interval_of_equidistant_points_on_unit_interval_of
      using assms(1, 2) atLeastAtMost_iff
      by (simp add: sort_eq_Nil_iff)
    ultimately show ?thesis by (rule lower_bound)
  qed
  also have "\<dots> = percentile ys x"
    unfolding percentile_def ..
  finally show ?thesis .
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
 * they are both defined then for the values y and y' it also holds that y \<le> y'. \<close>
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
  have "sorted ?xs \<and> distinct ?xs"  using inj_onI divide_right_mono distinct_map
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

text \<open> The percentile function is (weakly) monotonic increasing. \<close>
lemma percentile_monotonic:
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) \<le> x - epsilon" "x'- epsilon \<le> 1 - 1 / (2 * length ys)"
  assumes "x \<le> x'"
  shows "percentile ys x \<le> percentile ys x'"
proof -
  have "percentile ys x = linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) (x - epsilon)"
    unfolding percentile_def ..
  also have "\<dots> \<le> linear_approximation (equidistant_points_on_unit_interval_of (sort ys)) (x' - epsilon)"
  proof -
    from \<open>ys \<noteq> []\<close> have s: "sort ys \<noteq> []" by (simp add: sort_eq_Nil_iff) 
    have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))" by simp
    moreover have "(x - epsilon) \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
      using defined_interval_of_equidistant_points_on_unit_interval_of
      using assms s atLeastAtMost_iff      
      by fastforce
    moreover have "(x' - epsilon) \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
      using defined_interval_of_equidistant_points_on_unit_interval_of
      using assms atLeastAtMost_iff s by fastforce      
    moreover have "\<forall>x x' y y'. x \<le> x' \<and> equidistant_points_on_unit_interval_of (sort ys) x = Some y
      \<and> equidistant_points_on_unit_interval_of (sort ys) x' = Some y' \<longrightarrow> y \<le> y'"
      using sorted_imp sorted_sort by blast      
    moreover note \<open>x \<le> x'\<close>
    ultimately show ?thesis by (simp add: \<open>x \<le> x'\<close> linear_approximation_monotonic)
  qed
  also have "\<dots> \<le> percentile ys x'"
    unfolding percentile_def ..
  finally show ?thesis .
qed

text \<open> The percentile function is Lipschitz continuous. \<close>
lemma percentile_Lipschitz:
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) \<le> (x - epsilon) \<and> (x - epsilon) \<le> 1 - 1 / (2 * length ys)"
  assumes "1 / (2 * length ys) \<le> (x' - epsilon) \<and> (x' - epsilon) \<le> 1 - 1 / (2 * length ys)"
  shows "\<exists>K. \<bar>percentile ys x' - percentile ys x\<bar> \<le> K * \<bar>x' - x\<bar>"
proof -
  have "finite (dom (equidistant_points_on_unit_interval_of (sort ys)))" by simp
  moreover have "(x - epsilon) \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
    using defined_interval_of_equidistant_points_on_unit_interval_of
    using assms(1, 2) atLeastAtMost_iff
    by (simp add: sort_eq_Nil_iff)
  moreover have "(x' - epsilon) \<in> defined_interval_of (equidistant_points_on_unit_interval_of (sort ys))"
    using defined_interval_of_equidistant_points_on_unit_interval_of
    using assms(1, 3) atLeastAtMost_iff
    by (simp add: sort_eq_Nil_iff)
  ultimately show ?thesis
    unfolding percentile_def using linear_approximation_Lipschitz by fastforce
qed

end
