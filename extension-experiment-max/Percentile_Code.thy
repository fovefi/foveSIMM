text \<open> Version 0.5, last changed 2019-02-01
  (C) fovefi ltd, www.fovefi.co 
  (author: Manfred Kerber [make@fovefi.co] based on Percentile_Code.thy in foveSIMM by Lukas Bulwahn)
 
  Dually licenced under
  Creative Commons Attribution (CC-BY) 4.0 [https://creativecommons.org/licenses/by/4.0/]
  ISC License (1-clause BSD License)       [https://www.isc.org/downloads/software-support-policy/isc-license/]
  See LICENSE files for details.
  (Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
  
  In the following, an executable definition of the percentile function is given that is
  close to the one used in OpenSIMM, a system with a standard implementation for the computation
  of risk. Here, the percentile function is extended so that it is defined on the complete interval [0,1].
  The extension is done by taking a constant slope at the ends of the interval. To this end the original
  implementation was adjusted.
  \<close>

theory Percentile_Code
  imports Percentile
begin

section \<open>Code Generation of Percentile\<close>
paragraph \<open>The percentile definition close to the Java implementation\<close>

text \<open> In the Java code follows a check that the level is below 1 - 1/(2*size).
 * If not, it throws an exception. In the Isabelle implementation (there is no exception
 * handling in Isabelle), the code is underspecified, that is, no specific values will be
 * returned for larger values. This will be fixed in the definition of the percentile function
 * in the next section.
 \<close>

text \<open> An integer greater equal 0 considered as a real number is the same as the integer first considered
       as a natural number and this then considered as a real number. \<close>
lemma real_of_int:
  assumes "0 \<le> i"
  shows "real_of_int i = real (nat i)"
by (simp add: assms)

text \<open> The value of the minimum of the domain of equidistant point is determined. \<close>
lemma Min_equidistant_points_on_unit_interval_of_bounded:
  fixes x :: real
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) < x"
  assumes "x \<le> 1 - 1 / (2 * length ys)"
  shows "Min {x' \<in> dom (equidistant_points_on_unit_interval_of ys). x \<le> x'} = (ceiling (length ys * x - 0.5) + 0.5) / length ys"
  (is "Min ?A = ?expr") 
proof (rule Min_eqI)
  text \<open>let ?A = "{x' \<in> dom (equidistant_points_on_unit_interval_of ys). x \<le> x'}"\<close>
  show "finite ?A" by simp
  show "?expr \<le> y" if "y \<in> ?A" for y
  proof -
    from that \<open>ys \<noteq> []\<close> obtain n where "y = (real n + 1 / 2) / real (length ys)" and "x \<le> y"
      unfolding equidistant_points_on_unit_interval_of_def
      apply auto done
    obtain i where "i = int n" by auto
    from this \<open>y = _\<close> have y: "y = (real_of_int i + 1 / 2) / real (length ys)"
      by simp
    have "i \<ge> ceiling (length ys * x - 0.5)"
    proof -
      have "x \<le> (real_of_int i + 1 / 2) / real (length ys)"
        using \<open>x \<le> y\<close> y by blast
      from this have "length ys * x \<le> (real_of_int i + 1 / 2)"
        apply -
        apply (frule mult_left_mono[where c="real (length ys)"])
         apply simp
        by (simp add: assms(1)) 
        find_theorems "_ * _ \<le> _ * _"
      from this have "length ys * x - 1 / 2 \<le> real_of_int i" by linarith
      from this show ?thesis
        by (simp add: ceiling_le)
    qed
    from this y have "y \<ge> (real_of_int (ceiling (length ys * x - 0.5)) + 1 / 2) / real (length ys)"
      apply simp
      find_theorems "_ / _ \<le> _ / _"
      apply (rule divide_right_mono)
      apply simp
      apply simp
      done
    from this show ?thesis by simp
  qed
  show "?expr \<in> ?A"
  proof -
    from assms have "0 \<le> real (length ys) * x - 1 / 2"
      apply auto
      by (simp add: Groups.mult_ac(2) divide_less_eq)
    from this have "0 \<le> \<lceil>real (length ys) * x - 1 / 2\<rceil>" by simp
    from this have a: "real_of_int \<lceil>real (length ys) * x - 1 / 2\<rceil> = real (nat \<lceil>real (length ys) * x - 1 / 2\<rceil>)"
      by simp
    have b: "nat \<lceil>real (length ys) * x - 1 / 2\<rceil> \<in> {0..<length ys}"
    proof -
      have "real (length ys) * x - 1 / 2 \<le> (length ys - 1)"
      proof -
        have "real (length ys) * x - 1 / 2 \<le> real (length ys) * (1 - 1 / real (2 * length ys)) - 1 / 2"
          using assms(1, 3) by simp
        also have "\<dots> = real (length ys) - 1"
          apply auto
          apply (subst right_diff_distrib)
          apply simp
          by (simp add: assms(1))
        also have "\<dots> = real (length ys - 1)"
          by (metis One_nat_def Suc_pred assms(1) diff_Suc_Suc diff_is_0_eq length_greater_0_conv of_nat_1 of_nat_diff zero_diff)
        finally show ?thesis .
      qed
      text \<open>have "\<lceil>real (length ys) * x - 1 / 2\<rceil> \<ge> 0" s_orry\<close>
      from this have a: "\<lceil>real (length ys) * x - 1 / 2\<rceil> \<le> \<lceil>real (length ys - 1)\<rceil>"
        using ceiling_mono by blast    
      have "\<lceil>real (length ys - 1)\<rceil> = int (length ys - 1)" by simp       
      from a this have "nat \<lceil>real (length ys) * x - 1 / 2\<rceil> < length ys"
        by (smt assms(1) int_nat_eq length_greater_0_conv nat_less_le of_nat_0_less_iff of_nat_1 of_nat_diff of_nat_less_imp_less zero_less_diff)
      from this show ?thesis
        apply auto done
    qed
    have "(real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> + 5 / 10) / real (length ys)
      \<in> dom (equidistant_points_on_unit_interval_of ys)"
      unfolding dom_equidistant_points_on_unit_interval_of
      apply auto
      apply (subst a)
      apply (rule image_eqI)
       apply (rule refl)
      apply (rule b) done
      find_theorems "dom (equidistant_points_on_unit_interval_of _)"
    moreover have "x \<le> (real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> + 5 / 10) / real (length ys)"
    proof -
      have "real (length ys) > 0" (* only need \<ge> *)
        by (simp add: assms)
      have a: "real (length ys) * x - 5 / 10 \<le> real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil>"
        by linarith
      have "x \<le> ((real (length ys) * x - 5 / 10) + 5 / 10) / real (length ys)"
        using \<open>real (length ys) > 0\<close> by auto
      also have "\<dots> \<le> (real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> + 5 / 10) / real (length ys)"
        using \<open>real (length ys) > 0\<close> a
        apply -
        apply (rule divide_right_mono)
        apply linarith      
        apply simp done
      finally show ?thesis .
    qed
    ultimately show ?thesis by auto
  qed
qed

text \<open> A property of the ceiling function. \<close>
lemma ceiling_minus_leq:
  assumes "a + b \<ge> 1"
  shows "real_of_int \<lceil>x - a\<rceil> - b \<le> x"
using assms by linarith

text \<open> Relationship between floor and ceiling (floor plus 1 is less equal ceiling). \<close>
lemma floor_leq_ceiling:
  fixes x :: real
  assumes "x \<notin> real_of_int ` UNIV"
  shows "1 + real_of_int (floor x) \<le> real_of_int (ceiling x)"
using assms by (smt UNIV_I ceiling_correct image_eqI int_less_real_le le_floor_iff)

text \<open> If i < y for two integers then i \<le> y - 1 (when converted to real).\<close>
lemma less_to_leq:
  fixes y :: real
  assumes "real i < y"
  assumes "y \<in> real_of_int ` UNIV"
  shows "real i \<le> y - 1"
proof -
  from assms(2) obtain j where "y = real_of_int j"
    apply auto done
  obtain k where "j = int k"
    by (smt \<open>y = real_of_int j\<close> assms(1) int_less_real_le nat_0_le of_int_1 of_nat_0_le_iff)
  from this \<open>y = _\<close> assms(1) show ?thesis by auto
qed

text \<open> The value of the maximum of the domain of equidistant point is determined. \<close>
lemma Max_equidistant_points_on_unit_interval_of_bounded:
  fixes x :: real
  assumes "ys \<noteq> []"
  assumes "1 / (2 * length ys) < x" "x \<le> 1 - 1 / (2 * length ys)"
  shows "Max {x' \<in> dom (equidistant_points_on_unit_interval_of ys). x' < x} = (ceiling (length ys * x - 0.5) - 0.5) / length ys"
    (is "_ = ?expr")
proof -
  let ?A = "{x' \<in> (\<lambda>x. (1 / length ys) * (x + 0.5)) ` {0..<length ys}. x' < x}"
  have "Max ?A = ?expr"
  find_theorems "_ ` _" "Max"
  proof (rule Max_eqI)
    show "finite ?A" by simp
    show "y \<le> ?expr" if "y \<in> ?A" for y
    proof -
      show ?thesis
      proof (cases "real (length ys) * x - 1 / 2 \<in> range real_of_int")
        case True
          from that obtain i where "i \<in> {0..<length ys}"
            and y: "y = 1 / real (length ys) * (real i + 5 / 10)" and "y < x" by auto
          have "(real i + 5 / 10) < real (length ys) * x"
            by (metis \<open>y < x\<close> assms(1) divide_less_eq length_greater_0_conv mult.commute mult_numeral_1 numeral_One of_nat_0_less_iff times_divide_eq_right y) 
          from this have "real i < real (length ys) * x - 0.5"
            by linarith            
          from this have "real i \<le> real (length ys) * x - 1.5"
            apply -
            apply (frule less_to_leq)
            apply (simp add: True)
            by linarith     
          from this have "(real i + 5 / 10) \<le> real (length ys) * x - 1"
            apply simp done
          have "1 / real (length ys) > 0" by (simp add: assms(1)) 
          from this assms y have y2: "y \<le> 1 / real (length ys) * (real (length ys) * x - 1)"
            using \<open>real i + 5 / 10 \<le> real (length ys) * x - 1\<close> real_mult_le_cancel_iff2 by blast
          have "real (length ys) * x - 1 / 2 \<le> real_of_int \<lceil>real (length ys) * x - 1 / 2\<rceil>"
            by simp
          from this have "real (length ys) * x - 1 \<le> real_of_int \<lceil>real (length ys) * x - 1 / 2\<rceil> - 1 / 2"
          proof -
            have "real (length ys) * x - 1 = (real (length ys) * x - 1 / 2) - 1 / 2" by simp
            also have "\<dots> \<le> real_of_int \<lceil>real (length ys) * x - 1 / 2\<rceil> - 1 / 2"
              by linarith
            finally show ?thesis .
          qed
        from this y2 show ?thesis
          apply auto
          find_theorems "?a \<le> ?b \<Longrightarrow> ?b \<le> ?c \<Longrightarrow> ?a \<le> ?c"
          apply (rule order.trans)
          apply assumption
          apply (rule divide_right_mono)
          apply simp apply simp done
          find_theorems "_ / _ \<le> _ / _"
      next
        case False
        then show ?thesis
        proof -
          have "y \<le> 1 / real (length ys) * (real_of_int \<lfloor>real (length ys) * x - 5 / 10\<rfloor> + 5 / 10)"
          proof -
            from that obtain i where "i \<in> {0..<length ys}"
              and "y = 1 / real (length ys) * (real i + 5 / 10)" and "y \<le> x" by auto
            have "i \<le> \<lfloor>real (length ys) * x - 5 / 10\<rfloor>"
        proof -
          have a: "1 / real (length ys) * (real i + 5 / 10) \<le> x"
            using \<open>y = _\<close> \<open>y \<le> x\<close> by blast
          have "(real i + 5 / 10) \<le> real (length ys) * x"
          proof -
            have "(real i + 5 / 10) = real (length ys) * (1 / real (length ys) * (real i + 5 / 10))"
              by (simp add: assms(1)) 
            also have "\<dots> \<le> real (length ys) * x"
              using a mult_left_mono of_nat_0_le_iff by blast
            finally show ?thesis .
          qed
          from this have "real i \<le> real (length ys) * x - 5 / 10" by linarith
          from this show ?thesis by linarith
        qed
        from this \<open>y = _\<close> show ?thesis
        proof -
          have "real (length ys) > 0" by (simp add: assms(1))
          from \<open>i \<le> floor _\<close> have "(real i + 5 / 10) \<le> real_of_int \<lfloor>real (length ys) * x - 5 / 10\<rfloor> + 5 / 10"
            by linarith
          from this \<open>y = _\<close> \<open>real (length ys) > 0\<close> show ?thesis
            using real_mult_le_cancel_iff2 by fastforce
        qed
      qed
      also have "\<dots> \<le> (real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> - 5 / 10) / real (length ys)"
      proof -
        from False
        have "(real_of_int \<lfloor>real (length ys) * x - 5 / 10\<rfloor> + 5 / 10) \<le> (real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> - 5 / 10)"
          apply simp
          apply (rule floor_leq_ceiling)
          apply assumption
          done
        from this show ?thesis
          apply simp
          apply (rule divide_right_mono)
           apply simp apply simp done
      qed
      finally show ?thesis .
    qed
    qed qed
    show "?expr \<in> ?A"
    proof -
      have "?expr \<in> (\<lambda>x. 1 / real (length ys) * (real x + 5 / 10)) ` {0..<length ys}"
      proof
        have "real (length ys) * x - 1 / 2 > 0"
          by (metis assms(1) assms(2) diff_gt_0_iff_gt divide_divide_eq_left divide_less_eq length_greater_0_conv mult.commute of_nat_0_less_iff of_nat_mult of_nat_numeral)      
        from this have "nat \<lceil>real (length ys) * x - 1 / 2\<rceil> \<ge> 1"
          by linarith
        from this show "(real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> - 5 / 10) / real (length ys) =
          1 / real (length ys) * (real (nat \<lceil>real (length ys) * x - 5 / 10\<rceil> - 1) + 5 / 10)"
          using \<open>ys \<noteq> []\<close>
          apply auto done
        have "real (length ys) \<ge> 0" by auto
        have "x \<le> 1"
          by (smt assms(3) divide_less_0_1_iff of_nat_0_le_iff)
        from this have "real (length ys) * x \<le> length ys"
          by (simp add: mult_left_le)    
        from this \<open>real (length ys) \<ge> 0\<close> have "real (length ys) * x \<le> length ys + 1 / 2"
          by linarith          
        from this have "real (length ys) * x - 1 / 2 \<le> length ys"
          by fastforce
        from this show "nat \<lceil>real (length ys) * x - 5 / 10\<rceil> - 1 \<in> {0..<length ys}"
          apply auto
          using \<open>1 \<le> nat \<lceil>real (length ys) * x - 1 / 2\<rceil>\<close> by linarith
      qed
      moreover have "?expr < x"
      proof -
        have "real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> < real (length ys) * x + 5 / 10"
          by linarith
        then have "real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> < x * real (length ys) + 5 / 10"
          by (simp add: mult.commute)
        have "real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> - 5 / 10 < x * real (length ys)"
          using \<open>real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> < x * real (length ys) + 5 / 10\<close> by linarith          
        from this show "(real_of_int \<lceil>real (length ys) * x - 5 / 10\<rceil> - 5 / 10) / real (length ys) < x"
          apply auto
          by (simp add: assms(1) divide_less_eq)
      qed
      ultimately show ?thesis by auto
    qed
  qed
  from this show ?thesis
    unfolding equidistant_points_on_unit_interval_of_def by simp
qed

text \<open> The lemma determines the values of equidistant point on the unit interval. \<close>
lemma equidistant_points_on_unit_interval_of_eq_nth2:
  fixes i :: int
  assumes "0 \<le> i" "nat i < length ys"
  shows "the (equidistant_points_on_unit_interval_of ys ((real_of_int i + 5 / 10) / size ys)) = ys ! (nat i)"
proof -
  let ?xs = "map (\<lambda>x. (real x + 1 / 2) / real (length ys)) [0..<length ys]"
  have "distinct ?xs" by (auto intro!: inj_onI simp add: distinct_map)
  have eq: "(real_of_int i + 1 / 2) / real (length ys) = ?xs ! nat i"
    using assms by auto
  show ?thesis
    unfolding equidistant_points_on_unit_interval_of_def
    apply simp
    apply (subst eq)
    thm map_of_zip_nth
    apply (subst map_of_zip_nth)
       apply simp
      apply (rule \<open>distinct ?xs\<close>)
     apply (rule assms)
    apply simp done
qed

text \<open> The lemma gives an alternative characterization of the values of equidistant point on the unit interval. \<close>
lemma equidistant_points_on_unit_interval_of_eq_nth1:
  fixes i :: int
  assumes "1 \<le> i" "i \<le> length ys"
  shows "the (equidistant_points_on_unit_interval_of ys ((real_of_int i - 5 / 10) / size ys)) = ys ! nat (i - 1)"
proof -
  (* todo: size ys = real (length ys); which is better to write down? *)
  let ?f = "\<lambda>x. the (equidistant_points_on_unit_interval_of ys (x / size ys))"
  have "?f (real_of_int i - 5 / 10) = ?f (real_of_int (i - 1) + 5 / 10)" by force
  also have "\<dots> = ys ! nat (i - 1)"
    using assms by (simp only: equidistant_points_on_unit_interval_of_eq_nth2)
  finally show ?thesis .
qed

text \<open> The definition contains executable version of the percentile function which is close to the
       Java implementation in the OpenSIMM implementation. \<close>
definition percentile_impl_inner :: "real list \<Rightarrow> real \<Rightarrow> real"
where
  "percentile_impl_inner values level =
    (let  (size :: real) = (real (length values));
           (sorted :: (real list)) = sort values;
           i = (ceiling (size * level - 0.5));
           (lower :: real) = (i - 0.5) / size;
           (upper ::real) = (i + 0.5) / size;
           \<comment>\<open>Note that we convert i to a nat since we want to use it
              as an index in a list. This means that we automatically
              have values greater equal 0\<close>
           (lower_value :: real)  = sorted ! (nat (i-1));
           (upper_value :: real)  = sorted ! (nat i)
    in lower_value + (level - lower) * (upper_value - lower_value) / (upper - lower))"

definition percentile_impl :: "(real list) \<Rightarrow> real \<Rightarrow> real" where
  "percentile_impl values level =
    (let (size :: nat) = (length values);
         (sorted :: real list) = sort values
      in 
    (if (0 \<le> level \<and> level < 1/(2 *size))
       then (linear (0, (extrapolation_0 sorted)) (1/(2*size), sorted!0)) level
       else (if (1 - 1/(2 *size) < level \<and> level \<le> 1)
             then (linear (1 - 1/(2 *size), sorted!(size - 1)) (1, (extrapolation_1 sorted))) level
             else percentile_impl_inner sorted level)))" 

text \<open> The theorem states the equivalence of the abstract definition of the percentile function from
       the Percentile theory and the computational version in the standard interval. \<close>
theorem percentile_inner_java_equiv:
  assumes "sorted values" 
  assumes "length values > 1"
  assumes "1 / (2 * length values) < level" (* todo: lesseq instead of less *)
  assumes "level \<le> 1 - 1 / (2 * length values)"
  shows "Percentile.percentile values level = percentile_impl_inner values level"
proof -
  have non_empty: "values \<noteq> []" using assms(2) by auto
  have Percentile_inner_equ: "Percentile.percentile values level = Percentile.percentile_inner values level" 
    using percentile_alt1 using assms by simp 
  from assms(3) have "level \<noteq> 1 / real (2 * length values)" by blast
  let ?def = "(let p = equidistant_points_on_unit_interval_of (sort values);
         (x1, x2) = (Max {x' \<in> dom p. x' < level}, Min {x' \<in> dom p. level \<le> x'});
         (y1, y2) = (the (p x1), the (p x2))
     in linear (x1, y1) (x2, y2) level)"
  {
    fix size sorted i lower upper lower_value upper_value
    assume "size = real (length values)"
    assume "sorted = sort values"
    assume "i = \<lceil>size * level - 5 / 10\<rceil>"
    assume "lower = (real_of_int i - 5 / 10) / size"
    assume "upper = (real_of_int i + 5 / 10) / size"
    assume "lower_value = sorted ! nat (i - 1)"
    assume "upper_value = sorted ! nat i"
    have "length values = length sorted" and "sorted \<noteq> []" (* is this noteq Nil fact needed? *) and 
          "length sorted > 0"
      using \<open>sorted = _\<close> \<open>_ \<noteq> []\<close> apply auto
      by (metis length_0_conv length_sort) (* todo: find a better lemma *)
    have "lower_value + (level - lower) * (upper_value - lower_value) / (upper - lower) =
      linear (lower, lower_value) (upper, upper_value) level"
      apply (subst linear_eq[symmetric]) ..
    also have "\<dots> = ?def"
    proof -
      have b1: "0 \<le> \<lceil>real (length sorted) * level - 5 / 10\<rceil>"
      proof -
        have "- 1 / 2 \<le> real (length sorted) * level - 5 / 10"
          apply simp
          by (meson assms(3) le_less_trans less_eq_real_def of_nat_0_le_iff zero_le_divide_1_iff zero_le_mult_iff)
          (* strange proof? *)
        from this show ?thesis by linarith
      qed 
      have b2: "nat \<lceil>real (length sorted) * level - 5 / 10\<rceil> < length sorted"
      proof -
        have "real (length sorted) * level \<le> real (length sorted) - 1 / 2"
        proof -
          from assms(4) have "level \<le> 1 - 1 / real (2 * length sorted)"
            using \<open>length values = length sorted\<close> by simp
          from this have "real (length sorted) * level \<le> real (length sorted) * (1 - 1 / real (2 * length sorted))"
            using \<open>0 < length sorted\<close> by auto
          also have "\<dots> = real (length sorted) - 1 / 2"
            apply simp
            by (metis \<open>length values = length sorted\<close> \<open>size = real (length values)\<close> non_empty 
                      length_0_conv mult.commute mult.right_neutral mult_cancel_left 
                      nonzero_mult_divide_mult_cancel_left of_nat_eq_iff of_nat_mult 
                      right_diff_distrib' times_divide_eq_right)
          finally show ?thesis .
        qed
        from this show ?thesis
          using b1 by linarith
      qed
      have b3: "1 \<le> \<lceil>real (length sorted) * level - 5 / 10\<rceil>"
      proof -
        show ?thesis
          using assms(3) \<open>length _ = _\<close> \<open>length sorted > 0\<close> 
          by (simp add: Groups.mult_ac(2) divide_less_eq)
      qed
      from b2 have b4: "\<lceil>real (length sorted) * level - 5 / 10\<rceil> \<le> int (length sorted)" by simp
      have "Max {x' \<in> dom (equidistant_points_on_unit_interval_of sorted). x' < level} = lower"
        using \<open>lower = _\<close> \<open>i = _\<close> \<open>size = _\<close> \<open>length values = _\<close>
        apply (subst Max_equidistant_points_on_unit_interval_of_bounded)
           prefer 4
           apply simp
        using \<open>sorted \<noteq> []\<close> apply blast
        using assms(3) apply auto[1]
        using assms(4) by auto     
      moreover have "Min {x' \<in> dom (equidistant_points_on_unit_interval_of sorted). level \<le> x'} = upper"
        using \<open>upper = _\<close> \<open>i = _\<close> \<open>size = _\<close> \<open>length values = _\<close>
        apply (subst Min_equidistant_points_on_unit_interval_of_bounded)
         prefer 4
         apply simp
        using \<open>sorted \<noteq> []\<close> apply blast
        using assms(3) apply auto[1]
        using assms(4) by auto
      moreover have "the (equidistant_points_on_unit_interval_of sorted lower) = lower_value"
        using \<open>i = _\<close>  \<open>size = _\<close> \<open>lower_value = _\<close> \<open>lower = _\<close> \<open>length values = _\<close>
        apply (simp only:)
        apply (subst equidistant_points_on_unit_interval_of_eq_nth1)
        apply (rule b3)
        apply (rule b4)
        apply simp
        done
      moreover have "the (equidistant_points_on_unit_interval_of sorted upper) = upper_value"
        using \<open>i = _\<close>  \<open>size = _\<close> \<open>upper_value = _\<close> \<open>upper = _\<close> \<open>length values = _\<close>
        apply (simp only:)
        apply (subst equidistant_points_on_unit_interval_of_eq_nth2)
        apply (rule b1)
        apply (rule b2)
        apply simp done
      ultimately show ?thesis
        using \<open>sorted = _\<close> by simp
    qed
    finally have "lower_value + (level - lower) * (upper_value - lower_value) / (upper - lower) =
       ?def" by simp (* intermediate proof step not needed? change proof structure? *)
  }
  from this \<open>level \<noteq> _\<close> show ?thesis using percentile_inner_alternative_pseudo_def percentile_impl_inner_def
       Percentile_inner_equ
    by (simp add: percentile_inner_alternative_pseudo_def percentile_impl_inner_def)
qed

theorem percentile_java_equiv_left:
  assumes "length values > 1"
  assumes "sorted values"
  assumes "1 / real (2 * length values) = level"
  shows "Percentile.percentile values level = percentile_impl values level"
proof -
  have "(length values) * level = 1/2" using assms by auto
  then have ceil: "ceiling ((length values) * level - 0.5) = 0" using ceiling_def
    by (simp add: \<open>real (length values) * level = 1 / 2\<close>)
  have "(sort values)!0 = (sort values)!(nat (0-1))"  by simp 
  have "2 * length values \<ge> 4"
    using assms(1) by linarith
  then have "1/(2 * length values) \<le> 1/4"
    using inverse_of_nat_le by fastforce
  then have "1/(2*length values) < 1 - 1/(2 *length values)"
    by linarith
  then have "percentile_impl values level = percentile_impl_inner values level" using assms percentile_impl_def 
    by (simp add: sorted_sort_id)
  then have "percentile_impl values level = (sort values)!0"
    using ceil percentile_impl_inner_def by auto
  then have "percentile_impl_inner values level = (sort values)!0" using ceil
    by (simp add: percentile_impl_inner_def)
  have "length values = length (sort values)" by simp
  have left_most: "(\<lambda>x. (1 / length values) * (x + 0.5)) 0 = level"
    using \<open>real (length values) * level = 1 / 2\<close> add_divide_distrib eq_divide_eq_1 mult_cancel_right1 
          nonzero_mult_div_cancel_left times_divide_eq_left assms by auto
  have "level = ((map (\<lambda>x. (1 /length values) * (x + 0.5)) [0..<length values]))!0"
    using assms left_most
    by (smt add.left_neutral diff_zero gr0I not_less_zero nth_map_upt of_nat_0)
  then have "level \<in> set (map (\<lambda>x. (1 /length values) * (x + 0.5)) [0..<length values])"
    using assms(1)
    by (metis gr_implies_not0 length_map length_upt neq0_conv nth_mem zero_less_diff)
  then have "level \<in> set (map (\<lambda>x. (1 /length values) * (x + 0.5)) [0..<length values])"
       using left_most by blast
  then have "level \<in> dom (equidistant_points_on_unit_interval_of (sort values))" 
    using equidistant_points_on_unit_interval_of_def
    by simp
  then have "neighbors (equidistant_points_on_unit_interval_of (sort values)) level = (level, level)"
    using defined_point_neighbors_eq finite_equidistant_points_on_unit_interval_of by blast
  then have val_0: "linear_approximation (equidistant_points_on_unit_interval_of (sort values)) level = (sort values)!0"
    using one_point_interpolation \<open>length values = length (sort values)\<close> 
         \<open>level \<in> dom (equidistant_points_on_unit_interval_of (sort values))\<close> assms(1) 
         equidistant_points_on_unit_interval_of_eq_nth2 finite_equidistant_points_on_unit_interval_of 
         left_most length_greater_0_conv mult_cancel_right1 nat_zero_as_int of_nat_eq_0_iff 
         real_of_int times_divide_eq_left
  proof -
    have f1: "(0::int) \<le> 0"
      by auto
  have f3: "length values \<noteq> 0 \<longrightarrow> (5 / 10 + real_of_int 0) / (of_nat_1 (length (sort values))) = 1 * (5 / 10) / (if length values = 0 then 0 else of_nat_1 (length values))"
    by auto
  have f4: "1 / (if length values = 0 then 0 else (length values)) * (5 / 10) = level"
    using left_most by auto
  have "\<forall>x1. real_of_int x1 + 5 / 10 = 5 / 10 + real_of_int x1"
    by auto
  then have "length values \<noteq> 0 \<longrightarrow> linear_approximation (equidistant_points_on_unit_interval_of (sort values)) level = sort values ! 0"
    using f4 f3 f1 \<open>\<And>c b a. b / c * a = b * a / c\<close> \<open>length values = length (sort values)\<close> 
         \<open>level \<in> dom (equidistant_points_on_unit_interval_of (sort values))\<close> assms 
         equidistant_points_on_unit_interval_of_eq_nth2 finite_equidistant_points_on_unit_interval_of 
         length_greater_0_conv nat_zero_as_int one_point_interpolation 
         divide_inverse_commute divide_numeral_1 inverse_divide of_int_0
    by (smt length_0_conv)
  then show ?thesis using assms(1) by linarith
qed
  then have "Percentile.percentile values level = Percentile.percentile_inner values level" 
    using percentile_alt1[of "values" "level"]  assms
    by (smt Max_equidistant_points_on_unit_interval_of Max_ge 
       \<open>level \<in> dom (equidistant_points_on_unit_interval_of (sort values))\<close> 
       finite_equidistant_points_on_unit_interval_of le_less_trans le_numeral_extra(1) 
        length_greater_0_conv sorted_sort_id)
  then have "Percentile.percentile values level = (sort values)!0" using linear_approximation_def
    using one_point_interpolation percentile_alt1 using val_0
    by (simp add: percentile_inner_def)
  then show ?thesis
    by (simp add: \<open>percentile_impl values level = percentile_impl_inner values level\<close> 
       \<open>percentile_impl_inner values level = sort values ! 0\<close>)
   
qed


theorem percentile_java_equiv:
  assumes "sorted values" 
  assumes "length values > 1"
  assumes "0 \<le> level \<and> level \<le> 1"
  shows "Percentile.percentile values level = percentile_impl values level"
proof -
  have l1: "0 \<le> level \<and> level < 1/(2* (length values)) \<longrightarrow> 
       Percentile.percentile values level =  
         (linear (0, extrapolation_0 values) (1/(2* (length values)), values!0)) level"
       using assms(1) assms(2) percentile_alt2 by blast
  have "0 \<le> level \<and> level < 1/(2* (length values)) \<longrightarrow> 
       percentile_impl values level = 
      (linear (0, (extrapolation_0 values)) (1/(2* (length values)), values!0)) level"
    using percentile_impl_def by (simp add: assms(1) sorted_sort_id)
  then have low: "0 \<le> level \<and> level < 1/(2* (length values)) \<longrightarrow> ?thesis" using l1 by auto

  have w: "1/(2* length values) < level \<and> level \<le> 1 - 1/(2* length values) \<longrightarrow>
           1/(2* length values) \<le> level \<and> level \<le> 1 - 1/(2* length values)" by auto
  have l2: "1/(2* length values) < level \<and> level \<le> 1 - 1/(2* length values) \<longrightarrow> 
            Percentile.percentile values level = percentile_impl_inner values level"
    using percentile_inner_java_equiv[of "values" "level"] using assms(1) assms(2)
    by blast
  have  "1/(2* length values) < level \<and> level \<le> 1 - 1/(2* length values) \<longrightarrow> 
      percentile_impl values level = percentile_impl_inner values level" 
    using assms percentile_impl_def by (simp add: sorted_sort_id)
    then have mid: "1/(2* length values) < level \<and> level \<le> 1 - 1/(2* length values) \<longrightarrow> ?thesis"
      using l2 percentile_inner_java_equiv by simp

  have l3: "1 - 1/(2 * (length values)) < level \<and> level \<le> 1 \<longrightarrow> 
       Percentile.percentile values level =  
         (linear (1-1/(2* (length values)), values!(length values -1)) (1, extrapolation_1 values)) level"
    using assms(1) assms(2) percentile_alt3 by blast
  have "2 \<le> length values" using assms(2) by linarith
  then have quarter: "1/(2*(length values)) \<le> 1/4"
    using inverse_of_nat_le by fastforce
  then have "3/4 \<le> 1 - 1/(2*(length values))"
    using inverse_of_nat_le by fastforce
  then have "1/(2 * (length values)) < 1 - 1/(2 * (length values))" by linarith

  then have "1 - 1/(2 * (length values)) < level \<and> level \<le> 1 \<longrightarrow> \<not> ( level \<le> 1/(2 * (length values)))"
    by linarith

  then have "1 - 1/(2 * (length values)) < level \<and> level \<le> 1 \<longrightarrow> 
       percentile_impl values level = 
      (linear (1-1/(2* (length values)), values!(length values -1)) (1, extrapolation_1 values)) level"
    using percentile_impl_def
    by (smt assms(1) sorted_sort_id)
  then have up: "1 - 1/(2* (length values)) < level \<and> level \<le> 1 \<longrightarrow> ?thesis"
    using l3 by linarith  
  have border_left: "1/(2* (length values)) = level \<longrightarrow> ?thesis"
    using assms(1) assms(2) percentile_java_equiv_left by blast
  then show ?thesis using low mid up assms by linarith
qed

export_code percentile_impl in Scala
end
