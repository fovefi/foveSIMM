text \<open> Version 0.4, last changed 2019-01-28 
  (C) fovefi ltd, www.fovefi.co 
  (author: Lukas Bulwahn [lubu@fovefi.co], comments by Manfred Kerber [make@fovefi.co])
 
  Dually licenced under
  Creative Commons Attribution (CC-BY) 4.0 [https://creativecommons.org/licenses/by/4.0/]
  ISC License (1-clause BSD License)       [https://www.isc.org/downloads/software-support-policy/isc-license/]
  See LICENSE files for details.
  (Rationale for this dual licence: http://arxiv.org/abs/1107.3212)

  In this file, a linear approximation (i.e., linear interpolation) is defined. The linear approximation
  of two given points (x1,y1) and (x2,y2) is a function f(x) = a*(x-b) + c with f(x1) = y1 and
  f(x2) = y2. This is the function with slope a = (y2 - y1)/(x2 - x1), b = x1, 
  and c = y1. There is a priori a problem if the two given points are the same. We implicitly assume
  in the following that they are not. Note that Isabelle's logic is total and 1/0 has been defined
  as 0.
 
  In addition to the definition, properties of the linear approximation are presented 
  such as about the maximum and minimum of the linear approximation. \<close>

theory Linear_Interpolation
  imports Complex_Main
begin

section \<open>Linear function defined by two points\<close>

text \<open> A linear function through two points (x1, y1) and (x2, y2) is defined as the unique 
      straight line through the points (assumed the points are different and x1 \<noteq> x2). \<close>
definition linear :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<Rightarrow> real"
where
  "linear xy1 xy2 = (case (xy1, xy2) of
    ((x1, y1), (x2, y2)) \<Rightarrow> (\<lambda>x. (y2 - y1) / (x2 - x1) * (x - x1) + y1))"

text \<open> Alternative description with explicit pair representation. \<close>
lemma linear_def':
  "linear (x1, y1) (x2, y2) = (\<lambda>x. (y2 - y1) / (x2 - x1) * (x - x1) + y1)"
unfolding linear_def by simp

text \<open> Alternative description of linear function. \<close>
lemma linear_eq:
  "linear (x1, y1) (x2, y2) x = y1 + (x - x1) * (y2 - y1) / (x2 - x1)"
unfolding linear_def by simp

text \<open> The linear function evaluates correctly at the first point. \<close>
lemma linear_first:
  "linear (x1, y1) (x2, y2) x1 = y1"
unfolding linear_def' by simp

text \<open> The linear function evaluates correctly at the second point, assumed the x-values are different \<close>
lemma linear_second:
  assumes "x1 \<noteq> x2"
  shows "linear (x1, y1) (x2, y2) x2 = y2"
using assms unfolding linear_def' by simp

text \<open> A linear function is bounded from above by the bigger of two values (for all values in between). \<close>
lemma linear_upper_bound:
  assumes "x1 \<le> x" "x \<le> x2"
  shows "linear (x1, y1) (x2, y2) x \<le> max y1 y2"
proof -
  have "linear (x1, y1) (x2, y2) x = (y2 - y1) / (x2 - x1) * (x - x1) + y1"
    unfolding linear_def' by simp
  also have "\<dots> \<le> max y1 y2"
  proof cases
    assume "y1 \<le> y2"
    have "(x - x1) / (x2 - x1) \<le> 1"
      using assms divide_le_eq_1 by force
    have "(y2 - y1) / (x2 - x1) * (x - x1) + y1 = y2 - ((1 - (x - x1) / (x2 - x1)) * (y2 - y1))"
      by algebra
    also have "\<dots> \<le> y2" by (simp add: \<open>(x - x1) / (x2 - x1) \<le> 1\<close> \<open>y1 \<le> y2\<close>)
    also have "\<dots> \<le> max y1 y2" by simp
    finally show ?thesis .
  next
    assume "\<not> y1 \<le> y2"
    from this have "(y2 - y1) / (x2 - x1) \<le> 0"
      using assms divide_le_0_iff by force
    from this have "(y2 - y1) / (x2 - x1) * (x - x1) + y1 \<le> y1"
      using assms(1) by (meson add_le_same_cancel2 diff_ge_0_iff_ge mult_le_0_iff)
    also have "\<dots> \<le> max y1 y2" by simp
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

text \<open> A linear function is bounded from below by the smaller of two values (for all values in between).\<close>
lemma linear_lower_bound:
  assumes "x1 \<le> x" "x \<le> x2"
  shows "min y1 y2 \<le> linear (x1, y1) (x2, y2) x"
proof -
  have "min y1 y2 \<le> (y2 - y1) / (x2 - x1) * (x - x1) + y1"
  proof cases
    assume "y1 \<le> y2"
    have "(y2 - y1) / (x2 - x1) \<ge> 0"
      using \<open>y1 \<le> y2\<close> assms(1) assms(2) by auto
    have "min y1 y2 \<le> y1" by simp
    also have "\<dots> \<le> (y2 - y1) / (x2 - x1) * (x - x1) + y1"
      using \<open>0 \<le> (y2 - y1) / (x2 - x1)\<close> assms(1) mult_nonneg_nonneg by fastforce
    finally show ?thesis .
  next
    assume "\<not> y1 \<le> y2"
    have "(x - x1) / (x2 - x1) \<le> 1"
      using assms divide_le_eq_1 by fastforce
    have "min y1 y2 \<le> y2" by simp
    also have "\<dots> \<le> y2 - ((1 - (x - x1) / (x2 - x1)) * (y2 - y1))"
      using \<open>(x - x1) / (x2 - x1) \<le> 1\<close> \<open>\<not> y1 \<le> y2\<close> mult_le_0_iff by fastforce
    also have "\<dots> = (y2 - y1) / (x2 - x1) * (x - x1) + y1" by algebra
    finally show ?thesis .
  qed
  also have "(y2 - y1) / (x2 - x1) * (x - x1) + y1 = linear (x1, y1) (x2, y2) x"
    unfolding linear_def' by simp
  finally show ?thesis .
qed

text \<open> Linear functions with the value at the 2nd point greater or equal the value at the 1st point
   are (weakly) monotonically increasing. \<close>
lemma linear_monotonic:
  assumes "x1 < x2" "y1 \<le> y2"
  assumes "x \<le> x'"
  shows "linear (x1, y1) (x2, y2) x \<le> linear (x1, y1) (x2, y2) x'"
proof -
  from \<open>x1 < x2\<close> \<open>y1 \<le> y2\<close> have "(y2 - y1) / (x2 - x1) \<ge> 0" by auto
  from this show ?thesis
    using assms unfolding linear_def'
    by (metis add.commute add_le_cancel_left diff_right_mono mult.commute mult_le_cancel_right not_le)
qed

text \<open> Linear functions scale by constant factors.\<close>
lemma linear_scale:
  "c * linear (x1, y1) (x2, y2) x = linear (x1, c * y1) (x2, c * y2) x"
unfolding linear_def'
by (simp add: distrib_left linordered_field_class.sign_simps(38) mult.commute mult.left_commute)

text \<open> Linear functions are Lipschitz continuous with the Lipschitz constant being the slope. \<close>  
lemma linear_Lipschitz:
  "\<bar>linear (x1, y1) (x2, y2) x' - linear (x1, y1) (x2, y2) x\<bar> = \<bar>(y2 - y1) / (x2 - x1)\<bar> * \<bar>x' - x\<bar>"
proof -
  have "\<bar>linear (x1, y1) (x2, y2) x' - linear (x1, y1) (x2, y2) x\<bar> =
     \<bar>(y2 - y1) / (x2 - x1) * (x' - x1) + y1 - ((y2 - y1) / (x2 - x1) * (x - x1) + y1)\<bar>"
    unfolding linear_def by simp
  also have "\<dots> = \<bar>(y2 - y1) / (x2 - x1) * (x' - x)\<bar>"
    by (simp add: linordered_field_class.sign_simps(38))
  also have "\<dots> = \<bar>(y2 - y1) / (x2 - x1)\<bar> * \<bar>x' - x\<bar>" by (simp add: abs_mult)
  finally show ?thesis .
qed

section \<open>Nearest rank method\<close>
text \<open> The nearest rank method assumes a partial function (concretely, a function with domain type 
  "real option"), which is defined only for some values. This is perhaps best been explained with 
  the help of an example.
 
  Let us assume that you have a list of 5 real numbers xs = [8, 10, 1, 4, 5] in order to compute a 
  particular rank, e.g., that of 0.75, first you order the list and get sxs = [1, 4, 5, 8, 10]. 
  Then you put 5 values (length of the list) on the unit interval [0;1] at equal distances of 1/5, 
  staying half the distance (i.e., 1/10) away from the left and right borders, that is, you get 
  [0.1, 0.3, 0.5, 0.7, 0.9]. For all other values it is undefined. The nearest rank is the biggest 
  defined position smaller than the position, e.g. for 0.75 it is 0.7.
 \<close>

definition nearest_rank :: "(real \<Rightarrow> real option) \<Rightarrow> real \<Rightarrow> real"
where
  "nearest_rank p x = the (p (Max {x'. p x' = Some x' \<and> x' \<le> x}))"

section \<open>Linear approximation of partial function\<close>

text \<open> Let p be a partial function and x be a real value, then the neighbors of x wrt p are two values,
  1) the biggest value - where p is defined - of the values smaller than or equal to x (as the 
  next smaller neighbor) and
  2) the smallest value - where p is defined - of the values bigger than or equal to x (as the 
  next bigger neighbor of x). \<close>
definition neighbors :: "(real \<Rightarrow> real option) \<Rightarrow> real \<Rightarrow> real \<times> real"
where
  "neighbors p x = (Max {x' \<in> dom p. x' \<le> x}, Min {x' \<in> dom p. x \<le> x'})"

text \<open> For a partial function p (i.e., a function of type real option), the defined interval of p is 
  defined as the interval between the minimal element in the domain and the maximal element
  in the domain, (assumed p is not completely undefined, in which case it is the empty set). \<close>
definition defined_interval_of :: "(real \<Rightarrow> real option) \<Rightarrow> real set"
where
  "defined_interval_of p = (if (p = Map.empty) then {} else {Min (dom p)..Max (dom p)})"

text \<open> The linear approximation of a partial (real) function p is defined as the linear function
  going through the left and right neighbors where p is defined. \<close>
definition linear_interpolation :: "(real \<Rightarrow> real option) \<Rightarrow> real \<Rightarrow> real"
where
  "linear_interpolation p x = (let (x1, x2) = neighbors p x;
     (y1, y2) = (the (p x1), the (p x2)) in linear (x1, y1) (x2, y2) x)"

subsection \<open>Basic Properties\<close>

text \<open> The domain of a partial function p is a subset of the defined interval of p. \<close>
lemma subseteq_defined_interval_of:
  assumes "finite (dom p)"
  shows "dom p \<subseteq> defined_interval_of p"
using assms by (simp add: defined_interval_of_def subset_iff)

text \<open> If the domain of a partial function p is finite and an element is in the defined interval of p then
  the minimum of the elements in the domain greater than or equal to the element is in the domain
  of p as well and greater than or equal to the element. \<close>
lemma defined_interval_of_Min_in:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p"
  shows "Min {x' \<in> dom p. x \<le> x'} \<in> {x' \<in> dom p. x \<le> x'}"
proof -
  from assms have "p \<noteq> Map.empty"
    unfolding defined_interval_of_def by auto
  from assms have "x \<in> {Min (dom p)..Max (dom p)}"
    by (simp add: \<open>p \<noteq> Map.empty\<close> defined_interval_of_def)    
  from this have "Max (dom p) \<in> {x' \<in> dom p. x \<le> x'}"
    using \<open>p \<noteq> Map.empty\<close> \<open>finite (dom p)\<close> by auto
  have "finite {x' \<in> dom p. x \<le> x'}"
    using \<open>finite (dom p)\<close> by auto
  have "\<exists>y. p (Min {x' \<in> dom p. x \<le> x'}) = Some y"
    using \<open>finite {x' \<in> dom p. _}\<close> \<open>_ \<in> {x' \<in> dom p. _}\<close> Min_in by blast
  moreover have "x \<le> Min {x' \<in> dom p. x \<le> x'}"
    using \<open>finite {x' \<in> dom p. _}\<close> \<open>_ \<in> {x' \<in> dom p. _}\<close> Min_in by blast
  ultimately show ?thesis by auto
qed

text \<open> If the domain of a partial function p is finite and an element is in the defined interval of p then
  the maximum of the elements in the domain smaller than or equal to the element is in the domain
  of p as well and smaller than or equal to the element. \<close>
lemma defined_interval_of_Max_in:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p"
  shows "Max {x' \<in> dom p. x' \<le> x} \<in> {x' \<in> dom p. x' \<le> x}"
proof -
  from assms have "p \<noteq> Map.empty"
    unfolding defined_interval_of_def by auto
  from assms have "x \<in> {Min (dom p)..Max (dom p)}"
    by (simp add: \<open>p \<noteq> Map.empty\<close> defined_interval_of_def)    
  from this have "Min (dom p) \<in> {x' \<in> dom p. x' \<le> x}"
    using \<open>p \<noteq> Map.empty\<close> \<open>finite (dom p)\<close> by auto
  have "finite {x' \<in> dom p. x' \<le> x}"
    using \<open>finite (dom p)\<close> by auto
  have "\<exists>y. p (Max {x' \<in> dom p. x' \<le> x}) = Some y"
    using \<open>finite {x' \<in> dom p. _}\<close> \<open>_ \<in> {x' \<in> dom p. _}\<close> Max_in by blast
  moreover have "Max {x' \<in> dom p. x' \<le> x} \<le> x"
    using \<open>finite {x' \<in> dom p. _}\<close> \<open>_ \<in> {x' \<in> dom p. _}\<close> Max_in by blast
  ultimately show ?thesis by auto
qed

text \<open> For a partial function p, the neighbors of two defined values are equal or the right neighbor
  of the smaller is less than or equal to the left neighbor of the bigger. \<close>
lemma neighbors_cases:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p" "x' \<in> defined_interval_of p"
  assumes "x \<le> x'"
  shows "(neighbors p x = neighbors p x') \<or> (snd (neighbors p x) \<le> fst (neighbors p x'))"
proof cases
  have "finite {x'' \<in> dom p. x \<le> x''}"
    by (simp add: \<open>finite (dom p)\<close>)
  assume "x' < Min {x'' \<in> dom p. x \<le> x''}"
  have "Min {x'' \<in> dom p. x' \<le> x''} = Min {x'' \<in> dom p. x \<le> x''}"
    using \<open>x \<le> x'\<close> \<open>x' < _\<close> \<open>finite {x'' \<in> dom p. _}\<close>
    by (metis (mono_tags, lifting) Min.bounded_iff eq_iff ex_in_conv less_eq_real_def mem_Collect_eq order_trans)
  moreover have "Max {x'' \<in> dom p. x'' \<le> x} = Max {x'' \<in> dom p. x'' \<le> x'}"
    using \<open>x \<le> x'\<close> \<open>x' < _\<close> \<open>finite {x'' \<in> dom p. _}\<close>
    by (smt Collect_cong Min_le mem_Collect_eq)
  ultimately show ?thesis
    unfolding neighbors_def by auto
next
  assume "\<not> x' < Min {x'' \<in> dom p. x \<le> x''}"
  have "Min {x'' \<in> dom p. x \<le> x''} \<in> {x'' \<in> dom p. x'' \<le> x'}"
    using assms(1, 2, 4) \<open>\<not> x' < _\<close> defined_interval_of_Min_in by auto
  have "Min {x'' \<in> dom p. x \<le> x''} \<le> Max {x'' \<in> dom p. x'' \<le> x'}"
    using \<open>finite _\<close> \<open>Min _ \<in> _\<close> by auto
  from this show ?thesis
    unfolding neighbors_def by auto
qed

text \<open> If the domain of a partial function is finite and x an element of the defined interval then
  there are neighbors of x such that x is between the neighbors (included). \<close>
lemma neighbors_dest:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p"
  obtains x1 y1 x2 y2 where "neighbors p x = (x1, x2)"
    and "p x1 = Some y1" and "p x2 = Some y2" and "x1 \<le> x" and "x \<le> x2"
proof -
  obtain x1 x2 where "neighbors p x = (x1, x2)" by fastforce
  from assms(1) have "finite {x' \<in> dom p. x' \<le> x}" by auto
  from this have "Max {x' \<in> dom p. x' \<le> x} \<in> {x' \<in> dom p. x' \<le> x}"
    using defined_interval_of_Max_in assms(1, 2) by auto
  from this obtain y1 where "p x1 = Some y1"
    using \<open>neighbors p x = (x1, x2)\<close> unfolding neighbors_def by auto
  from assms(1) have "finite {x' \<in> dom p. x \<le> x'}" by auto
  from this have "Min {x' \<in> dom p. x \<le> x'} \<in> {x' \<in> dom p. x \<le> x'}"
    using defined_interval_of_Min_in assms(1, 2) by auto
  from this obtain y2 where "p x2 = Some y2"
    using \<open>neighbors p x = (x1, x2)\<close> unfolding neighbors_def by auto
  have "x1 \<le> x" and "x \<le> x2"
    using \<open>Max {x' \<in> dom p. x' \<le> x} \<in> {x' \<in> dom p. x' \<le> x}\<close>
    using \<open>Min {x' \<in> dom p. x \<le> x'} \<in> {x' \<in> dom p. x \<le> x'}\<close>
    using \<open>neighbors p x = (x1, x2)\<close> unfolding neighbors_def by auto
  from that show thesis
    using \<open>neighbors p x = (x1, x2)\<close> \<open>p x1 = Some y1\<close> \<open>p x2 = Some y2\<close> \<open>x1 \<le> x\<close> \<open>x \<le> x2\<close> by blast
qed

subsection \<open>Boundedness\<close>

text \<open> The linear approximation of a partial function with finite domain is limited by the maximum of 
  the values of the partial function from above. \<close>
lemma upper_bound:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p"
  shows "linear_interpolation p x \<le> Max (ran p)"
proof -
  have "finite (ran p)"
    using assms(1) by (simp add: finite_ran)
  from assms obtain x1 y1 x2 y2 where
    "neighbors p x = (x1, x2)" and "p x1 = Some y1" and "p x2 = Some y2"
    and "x1 \<le> x" and "x \<le> x2"
    using neighbors_dest[of p x] by metis
  from this have "linear_interpolation p x = linear (x1, y1) (x2, y2) x"
    unfolding linear_interpolation_def by simp
  also have "\<dots> \<le> max y1 y2"
    using \<open>x1 \<le> x\<close> \<open>x \<le> x2\<close> by (simp add: linear_upper_bound)
  also have "\<dots> \<le> Max (ran p)"
    using Max_ge \<open>finite (ran p)\<close> \<open>p x1 = Some y1\<close> \<open>p x2 = Some y2\<close> ranI by fastforce
  finally show ?thesis .
qed

text \<open> The linear approximation of a partial function with finite domain is limited by the minimum of 
  the values of the partial function from below. \<close>
lemma lower_bound:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p"
  shows "Min (ran p) \<le> linear_interpolation p x"
proof -
  have "finite (ran p)"
    using assms(1) by (simp add: finite_ran)
  from assms obtain x1 y1 x2 y2 where
    "neighbors p x = (x1, x2)" and "p x1 = Some y1" and "p x2 = Some y2"
    and "x1 \<le> x" and "x \<le> x2"
    using neighbors_dest[of p x] by metis
  have "Min (ran p) \<le> min y1 y2"
    using Min_le \<open>finite (ran p)\<close> \<open>p x1 = Some y1\<close> \<open>p x2 = Some y2\<close> ranI by fastforce
  also have "\<dots> \<le> linear (x1, y1) (x2, y2) x"
    using \<open>x1 \<le> x\<close> \<open>x \<le> x2\<close> by (simp add: linear_lower_bound)
  also have "\<dots> = linear_interpolation p x"
    unfolding linear_interpolation_def
    using \<open>neighbors p x = (x1, x2)\<close> \<open>p x1 = Some y1\<close> \<open>p x2 = Some y2\<close> by simp
  finally show ?thesis .
qed

subsection \<open>Monotonicity\<close>

text \<open> If a partial function has finite domain and is (weakly) monotonically increasing for the values 
  where it is defined, then its linear approximation is (weakly) monotonically increasing.\<close>
lemma linear_interpolation_monotonic:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p" "x' \<in> defined_interval_of p"
  assumes "\<forall>x x' y y'. x \<le> x' \<and> p x = Some y \<and> p x' = Some y' \<longrightarrow> y \<le> y'"
  assumes "x \<le> x'"
  shows "linear_interpolation p x \<le> linear_interpolation p x'"
proof -
  from assms(1,2,5) obtain x1 y1 x2 y2
    where neighbors_x: "neighbors p x = (x1, x2)" "p x1 = Some y1" "p x2 = Some y2"
    and "x1 \<le> x" and "x \<le> x2"
    using neighbors_dest[of p x] by metis 
  from assms(1,3,5) obtain x1' y1' x2' y2'
    where neighbors_x': "neighbors p x' = (x1', x2')" "p x1' = Some y1'" "p x2' = Some y2'"
    and "x1' \<le> x'" and "x' \<le> x2'"
    using neighbors_dest[of p x'] by metis
  have "max y1 y2 = y2"
    using \<open>x \<le> x2\<close> \<open>x1 \<le> x\<close> assms(4) neighbors_x(2) neighbors_x(3)
    by (meson dual_order.trans max_absorb2)    
  have "min y1' y2' = y1'"
    using \<open>x' \<le> x2'\<close> \<open>x1' \<le> x'\<close> assms(4) neighbors_x'(2) neighbors_x'(3)
    by (metis dual_order.trans min.order_iff)
  from \<open>x \<le> x'\<close> have "(x1 = x1' \<and> x2 = x2') \<or> x2 \<le> x1'"
    using neighbors_cases[OF assms(1, 2, 3)]
    by (simp add: neighbors_x'(1) neighbors_x(1))
  from neighbors_x have "linear_interpolation p x = linear (x1, y1) (x2, y2) x"
    unfolding linear_interpolation_def by simp
  also from \<open>_ \<or> _\<close> have "linear (x1, y1) (x2, y2) x \<le> linear (x1', y1') (x2', y2') x'"
  proof
    assume a: "x1 = x1' \<and> x2 = x2'"
    from this have b: "y1 = y1' \<and> y2 = y2'"
      using neighbors_x'(2) neighbors_x'(3) neighbors_x(2) neighbors_x(3) by auto
    from \<open>max y1 y2 = y2\<close> have "y1 \<le> y2" by simp
    from a b this \<open>x \<le> x2\<close> \<open>x1 \<le> x\<close> \<open>x' \<le> x2'\<close> show ?thesis
      using linear_monotonic assms(5) by (metis (no_types, lifting) dual_order.trans eq_iff not_le)
  next
    assume "x2 \<le> x1'"
    have "linear (x1, y1) (x2, y2) x \<le> y2"
      using \<open>max y1 y2 = y2\<close> by (metis \<open>x \<le> x2\<close> \<open>x1 \<le> x\<close> linear_upper_bound)
    also from \<open>x2 \<le> x1'\<close> have "y2 \<le> y1'"
      using \<open>p x1' = Some y1'\<close> \<open>p x2 = Some y2\<close> assms(4) by blast
    also have "y1' \<le> linear (x1', y1') (x2', y2') x'"
      using \<open>x' \<le> x2'\<close> \<open>x1' \<le> x'\<close> \<open>min y1' y2' = y1'\<close> by (metis linear_lower_bound)
    finally show ?thesis .
  qed
  also have "linear (x1', y1') (x2', y2') x' = linear_interpolation p x'"
    unfolding linear_interpolation_def
    using neighbors_x' by simp
  finally show ?thesis .
qed

subsection \<open>Scalar multiplication\<close>

text \<open> Multiplying a partial function by a scalar does not change the neighbors. \<close>
lemma neighbors_scale_invariant:
   "neighbors (\<lambda>x. map_option (\<lambda>y. (c * y)) (p x)) x = neighbors p x" 
  unfolding neighbors_def by (simp add: domIff)

text \<open> Linear approximation of a partial function is linear with respect to multiplication. \<close>
lemma linear_interpolation_scale:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p"
  shows "linear_interpolation (\<lambda>x. map_option (\<lambda>y. c * y) (p x)) x = c * linear_interpolation p x"
proof -
  obtain x1 y1 x2 y2 where "neighbors p x = (x1, x2)" and "p x1 = Some y1" and "p x2 = Some y2"
    using assms neighbors_dest[of p x] by (metis (no_types, lifting))
  have "linear_interpolation (\<lambda>x. map_option (\<lambda>y. c * y) (p x)) x = linear (x1, c * the (p x1)) (x2, c * the (p x2)) x"
    using \<open>neighbors p x = (x1, x2)\<close> \<open>p x1 = Some y1\<close> \<open>p x2 = Some y2\<close>
    unfolding linear_interpolation_def by (simp add: neighbors_scale_invariant)
  also have "\<dots> = c * linear_interpolation p x"
    unfolding linear_interpolation_def
    using \<open>neighbors p x = (x1, x2)\<close> by (simp add: linear_scale)
  finally show ?thesis .
qed

subsection \<open>Lipschitz\<close>

text \<open> If for a partial function p there is no defined value between x and x' then
  the neighbors of x and x' are the same. \<close>
lemma neighbors_eq:
  assumes "x \<le> x'"
  assumes "\<forall>x''. x \<le> x'' \<and> x'' \<le> x' \<longrightarrow> p x'' = None"
  shows "neighbors p x = neighbors p x'"
proof -
  have "{x'' \<in> dom p. x'' \<le> x} = {x'' \<in> dom p. x'' \<le> x'}"
    using \<open>x \<le> x'\<close> \<open>\<forall>x''. x \<le> x'' \<and> x'' \<le> x' \<longrightarrow> p x'' = None\<close> linear by force
  moreover have "{x'' \<in> dom p. x \<le> x''} = {x'' \<in> dom p. x' \<le> x''}"
    using \<open>x \<le> x'\<close> \<open>\<forall>x''. x \<le> x'' \<and> x'' \<le> x' \<longrightarrow> p x'' = None\<close> by auto
  ultimately show ?thesis
    unfolding neighbors_def by simp
qed

text \<open> For a partial function with finite domain, the neighbors of a defined value are the point itself. \<close>
lemma defined_point_neighbors_eq:
  assumes "finite (dom p)"
  assumes "x \<in> dom p"
  shows "neighbors p x = (x, x)"
proof -
  from assms have "Max {x' \<in> dom p. x' \<le> x} = x"
    by (metis (mono_tags, lifting) Max_eqI infinite_super mem_Collect_eq order_refl subsetI)
  moreover from assms have "Min {x' \<in> dom p. x \<le> x'} = x"
    by (metis (mono_tags, lifting) Min_eqI infinite_super mem_Collect_eq order_refl subsetI)
  ultimately show ?thesis
    unfolding neighbors_def by auto
qed

text \<open> finite' defines in an inductive way on ordered sets, starting from the empty set inserting 
  elements smaller than all elements to a set. \<close>
inductive finite'
where
  "finite' {}"
| "finite' A \<Longrightarrow> a \<notin> A \<Longrightarrow> a < Min A \<or> A = {} \<Longrightarrow> finite' (insert a A)"

text \<open> On sets with a linear order the concept finite' is equivalent to the standard finite concept.\<close>
thm finite'.induct
lemma finite_eq_finite':
  fixes X :: "('a :: linorder) set"
  shows "finite X \<longleftrightarrow> finite' X"
proof
  show "finite X" if "finite' X"
    using that by (induct rule: finite'.induct) auto
  find_theorems "finite" name: induct
  thm finite_remove_induct
  show "finite' X" if "finite X" using that
  proof (induct rule: finite_remove_induct)
    show "finite' {}" by (rule finite'.intros)
  next
    case (remove A)
    let ?a' = "Min A"
    let ?A' = "A - {?a'}"
    from \<open>finite A\<close> \<open>A \<noteq> {}\<close> have "?a' \<in> A" by simp
    from \<open>?a' \<in> A\<close> have "insert ?a' ?A' = A" by auto
    from \<open>?a' \<in> A\<close> remove(4) have "finite' ?A'" by simp
    moreover have "?a' \<notin> ?A'" by blast
    moreover have "?a' < Min ?A' \<or> ?A' = {}"
      by (metis Min.remove Min_in \<open>Min A \<in> A\<close> calculation(2) finite_Diff min.strict_order_iff remove.hyps(1))
    ultimately have "finite' (insert ?a' ?A')" by (rule finite'.intros)
    from this \<open>insert ?a' ?A' = A\<close> show ?case by simp
  qed
qed

text \<open> On finite sets with minima, there is an induction principle based on adding elements smaller
   than the minimum. \<close>
lemma finite_Min_induct [consumes 1, case_names empty insert]:
  "finite X \<Longrightarrow> P {} \<Longrightarrow> (\<And>A a. finite A \<Longrightarrow> P A \<Longrightarrow> a \<notin> A \<Longrightarrow> a < Min A \<or> A = {} \<Longrightarrow> P (insert a A)) \<Longrightarrow> P X"
unfolding finite_eq_finite' by (rule finite'.induct)

text \<open> If a property holds for a two place partial function in all four cases depending on whether 
  the arguments are in the domain or not, the property holds in general. \<close>
lemma four_cases:
  assumes "x \<in> dom p \<and> x' \<in> dom p \<Longrightarrow> P p x x'"
  assumes "x \<in> dom p \<and> x' \<notin> dom p \<Longrightarrow> P p x x'"
  assumes "x \<notin> dom p \<and> x' \<in> dom p \<Longrightarrow> P p x x'"
  assumes "x \<notin> dom p \<and> x' \<notin> dom p \<Longrightarrow> P p x x'"
  shows "P p x x'"
using assms(1) assms(2) assms(3) assms(4) by blast

text \<open> The linear approximation of a partial function p is Lipschitz continuous in case that there is 
  no defined element between x and x'. \<close>
lemma empty_case:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p"
  assumes "x' \<in> defined_interval_of p"
  assumes "x \<le> x'"
  assumes "\<forall>x''. x < x'' \<and> x'' < x' \<longrightarrow> p x'' = None"
  shows "\<exists>K. \<bar>linear_interpolation p x' - linear_interpolation p x\<bar> \<le> K * \<bar>x' - x\<bar>"
proof cases
  assume "x = x'"
  from this show ?thesis by simp
next
  assume "x \<noteq> x'"
  text \<open> cases: TODO: check if we can reduce it to at most two cases, when we look at the larger proof!
     and hence refine the assumption! \<close>
  show ?thesis
  proof (rule four_cases[of x p x'])
    assume a: "x \<in> dom p \<and> x' \<in> dom p"
    from this \<open>finite _\<close> have 1: "neighbors p x = (x, x)"
      by (simp add: defined_point_neighbors_eq)
    from a \<open>finite _\<close> have "neighbors p x' = (x', x')"
      by (simp add: defined_point_neighbors_eq)
    from 1 this show ?thesis
      unfolding linear_interpolation_def apply simp
      apply (simp add: linear_first)
      by (metis abs_ge_self abs_minus_commute abs_of_nonneg assms(4) diff_ge_0_iff_ge mult.commute nonzero_mult_div_cancel_left right_minus_eq times_divide_eq_right)
  next
    assume "x \<in> dom p \<and> x' \<notin> dom p"
    from assms obtain x1 y1 x2 y2 where
      n: "neighbors p x' = (x1, x2)" and 1: "p x1 = Some y1" and 2: "p x2 = Some y2"
      and "x1 \<le> x'" and "x' \<le> x2"
      using neighbors_dest[of p x'] by metis
    have "x = x1"
      using \<open>x \<in> dom p \<and> x' \<notin> dom p\<close> assms
      by (smt "1" \<open>x1 \<le> x'\<close> defined_point_neighbors_eq domI domIff n neighbors_cases prod.sel(1) prod.sel(2))
    from this n 1 2 \<open>x \<in> dom p \<and> _\<close> \<open>finite _\<close> show ?thesis
      unfolding linear_interpolation_def
      apply (simp add: defined_point_neighbors_eq linear_first)
      by (metis (no_types, hide_lams) abs_eq_0 add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_diff_eq2 mult.commute nonzero_mult_div_cancel_left order_refl times_divide_eq_right)
  next
    assume "x \<notin> dom p \<and> x' \<in> dom p"
    from assms obtain x1 y1 x2 y2 where
      n: "neighbors p x = (x1, x2)" and 1: "p x1 = Some y1" and 2: "p x2 = Some y2"
      and "x1 \<le> x" and "x \<le> x2"
      using neighbors_dest[of p x] by metis
    have "x' = x2"
      by (smt \<open>x \<notin> dom p \<and> x' \<in> dom p\<close> assms defined_point_neighbors_eq domI domIff fst_conv n neighbors_cases neighbors_dest snd_conv)
    from this n 1 2 \<open>_ \<and> _\<close> \<open>finite _\<close> show ?thesis
      unfolding linear_interpolation_def
      apply (simp add: defined_point_neighbors_eq linear_first)
      by (metis (no_types, hide_lams) abs_eq_0 add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_diff_eq2 mult.commute nonzero_mult_div_cancel_left order_refl times_divide_eq_right)
  next
    assume a: "x \<notin> dom p \<and> x' \<notin> dom p"
    from assms obtain x1 y1 x2 y2 where
      "neighbors p x = (x1, x2)" and "p x1 = Some y1" and "p x2 = Some y2"
      and "x1 \<le> x" and "x \<le> x2"
      using neighbors_dest[of p x] by metis
    have n: "neighbors p x' = (x1, x2)"
      using neighbors_eq assms(5) a
      by (metis \<open>neighbors p x = (x1, x2)\<close> assms(4) domIff less_eq_real_def)
    from this have "x' \<le> x2"
      using assms(1) assms(3) n neighbors_dest by force
    from \<open>x \<noteq> x'\<close> \<open>x1 \<le> x\<close> \<open>x \<le> x'\<close> \<open>x' \<le> x2\<close> have "x1 < x2" by linarith
    have "linear_interpolation p x = linear (x1, y1) (x2, y2) x"
      using \<open>neighbors p x = (x1, x2)\<close> \<open>p x1 = _\<close> \<open>p x2 = _\<close>
      unfolding linear_interpolation_def by simp
    moreover have "linear_interpolation p x' = linear (x1, y1) (x2, y2) x'"
    proof -
      from n \<open>p x1 = _\<close> \<open>p x2 = _\<close> show ?thesis
        unfolding linear_interpolation_def apply auto done
    qed
    ultimately show "\<exists>K. \<bar>linear_interpolation p x' - linear_interpolation p x\<bar> \<le> K * \<bar>x' - x\<bar>"
      by (metis linear_Lipschitz order_refl)
  qed
qed

text \<open> The linear approximation of a partial function with finite domain is Lipschitz continuous on
  the defined interval. \<close>
lemma linear_interpolation_Lipschitz:
  assumes "finite (dom p)"
  assumes "x \<in> defined_interval_of p" "x' \<in> defined_interval_of p"
  shows "\<exists>K. abs (linear_interpolation p x' - linear_interpolation p x) \<le> K * abs (x' - x)"
proof -
  { fix x x' :: real
  (*assume with loss of generality *)
    assume "x \<le> x'"
  assume "x \<in> defined_interval_of p"
  assume "x' \<in> defined_interval_of p"
  have "finite {x''. \<exists>y. p x'' = Some y \<and> x < x'' \<and> x'' \<le> x'}"
    using \<open>finite (dom p)\<close>
    by (simp add: dom_def)
  { fix A
    have "finite A \<Longrightarrow> x \<le> x' \<Longrightarrow> x \<in> defined_interval_of p \<Longrightarrow> {x''. \<exists>y. p x'' = Some y \<and> x < x'' \<and> x'' \<le> x'} = A \<longrightarrow>
      (\<exists>K. abs (linear_interpolation p x' - linear_interpolation p x) \<le> K * abs (x' - x))"
    proof (induct A arbitrary: x rule: finite_Min_induct)
      case empty
      {
        assume "{x''. \<exists>y. p x'' = Some y \<and> x < x'' \<and> x'' \<le> x'} = {}"
        from this have "\<forall>x''. x < x'' \<and> x'' \<le> x' \<longrightarrow> p x'' = None" by auto
        from this have "\<exists>K. \<bar>linear_interpolation p x' - linear_interpolation p x\<bar> \<le> K * \<bar>x' - x\<bar>"
          using \<open>x \<le> x'\<close> empty_case \<open>finite (dom p)\<close> \<open>x \<in> defined_interval_of p\<close> \<open>x' \<in> defined_interval_of p\<close>
          by simp
      }
      then show ?case by auto
    next
      case (insert A a)
      {
        assume a: "{x''. \<exists>y. p x'' = Some y \<and> x < x'' \<and> x'' \<le> x'} = insert a A"
        from this have "x < a" and "a \<le> x'" by blast+
        have "a \<in> defined_interval_of p"
          using \<open>a \<le> x'\<close> \<open>x < a\<close> \<open>x' \<in> defined_interval_of p\<close> defined_interval_of_def insert.prems(2) by auto
        have "{x''. \<exists>y. p x'' = Some y \<and> a < x'' \<and> x'' \<le> x'} = A"
          using insert.hyps(1,3,4) a \<open>x < a\<close> Min.coboundedI by fastforce
        (* possible improvement: replace linear_interpolation p by an local abbreviation for shorter proofs *)
        from insert.hyps(2) \<open>a \<le> x'\<close> \<open>a \<in> _\<close> this obtain K where
          1: "\<bar>linear_interpolation p x' - linear_interpolation p a\<bar> \<le> K * \<bar>x' - a\<bar>" by auto
        have "{x''. \<exists>y. p x'' = Some y \<and> x < x'' \<and> x'' < a} = {}"
        proof -
          have "p x'' = None" if "x < x'' \<and> x'' < a" for x''
          proof (rule ccontr) 
            assume "p x'' \<noteq> None"
            from this have "x'' \<in> insert a A"
              using \<open>a \<le> x'\<close> a that by fastforce
            from this that show False
              using insert.hyps(1,3,4) Min_gr_iff by fastforce
          qed
          from this show ?thesis by auto
        qed
        from this have "\<forall>x''. x < x'' \<and> x'' < a \<longrightarrow> p x'' = None" by auto
        from this obtain K' where 2: "\<bar>linear_interpolation p a - linear_interpolation p x\<bar> \<le> K' * \<bar>a - x\<bar>"
          using empty_case \<open>x < a\<close> \<open>finite (dom p)\<close> \<open>x \<in> _\<close> \<open>a \<in> _\<close> by fastforce
        have "\<bar>linear_interpolation p x' - linear_interpolation p x\<bar> \<le>
          \<bar>linear_interpolation p x' - linear_interpolation p a\<bar> + \<bar>linear_interpolation p a - linear_interpolation p x\<bar>"
          by auto
        also have "\<dots> \<le> K * \<bar>x' - a\<bar> + K' * \<bar>a - x\<bar>" using 1 2 by simp
        also have "\<dots> \<le> max K K' * \<bar>x' - a\<bar> + max K K' * \<bar>a - x\<bar>"
          by (simp add: add_mono_thms_linordered_semiring(1) mult_le_cancel_right)
        also have "\<dots> \<le> max K K' * \<bar>x' - x\<bar>" (* todo: simpler proof or lemma *)
        proof -
          have f1: "\<bar>a - x'\<bar> = x' - a"
            by (simp add: \<open>a \<le> x'\<close>)
          have "\<bar>x' - x\<bar> = x' - x"
            by (simp add: insert.prems)
          then show ?thesis
            using f1
            by (metis (no_types) \<open>x < a\<close> abs_minus_commute abs_of_nonneg add.right_neutral add_diff_eq cancel_comm_monoid_add_class.diff_cancel diff_add_eq diff_ge_0_iff_ge distrib_left dual_order.strict_implies_order order_refl)
        qed
        finally have "\<exists>K. \<bar>linear_interpolation p x' - linear_interpolation p x\<bar> \<le> K * \<bar>x' - x\<bar>" by auto
      }
      then show ?case by auto
    qed
  }
  from this have "\<exists>K. \<bar>linear_interpolation p x' - linear_interpolation p x\<bar> \<le> K * \<bar>x' - x\<bar>"
    using \<open>finite {x''. \<exists>y. p x'' = Some y \<and> x < x'' \<and> x'' \<le> x'}\<close> \<open>x \<le> x'\<close> \<open>x \<in> _\<close> by blast
  } note derived_case = this
  show ?thesis
  proof cases
    assume "x \<le> x'"
    from this derived_case \<open>x \<in> _\<close> \<open>x' \<in> _\<close> show ?thesis by simp
  next
    assume "\<not> x \<le> x'"
    from this have "x' \<le> x" by simp
    from this derived_case[of x' x] \<open>x \<in> _\<close> \<open>x' \<in> _\<close> show ?thesis by (simp add: abs_minus_commute)
  qed
qed


lemma one_point_interpolation:
  assumes "finite (dom p)"
  assumes "x \<in> dom p"
  shows "linear_interpolation p x = the (p x)"
proof -
  have "neighbors p x = (x, x)"
    using defined_point_neighbors_eq assms by simp
  then show ?thesis
    by (simp add: linear_interpolation_def linear_first)
qed


end
