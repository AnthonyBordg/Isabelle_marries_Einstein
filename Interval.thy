(* 
Author: Anthony Bordg 
Affiliation: University of Cambridge 
email: apdb3@cam.ac.uk
Date: October 2018 
*)

theory Interval
imports
  Main
  "HOL-Analysis.Analysis"
begin

section \<open>The Invariance of the Interval\<close>

text 
\<open>
We work in units where the value of the speed of light is 1.
We define the interval between any two events 
(not necessarily two events that belong to the world line of a beam of light). 
\<close>

definition interval :: "[real^4, real^4] \<Rightarrow> real" where
"interval u w \<equiv> -(w $ 4 - u $ 4)\<^sup>2 + (w $ 1 - u $ 1)\<^sup>2 + (w $ 2 - u $ 2)\<^sup>2 + (w $ 3 - u $ 3)\<^sup>2"

text \<open>We define a boost of velocity v in the u$1 direction.\<close>

definition boost_1 :: "[real^4, real] \<Rightarrow> real^4" where
"boost_1 u v \<equiv> 
vector
[
u $ 1 / sqrt(1 - v\<^sup>2) - (v * u $ 4) / sqrt(1 - v\<^sup>2), 
u $ 2, 
u $ 3, 
u $ 4 / sqrt(1 - v\<^sup>2) - (v * u $ 1) / sqrt(1 - v\<^sup>2)
]
"
text \<open>We define a boost of velocity v in the u$2 direction.\<close>

definition boost_2 :: "[real^4, real] \<Rightarrow> real^4" where
"boost_2 u v \<equiv> 
vector
[
u $ 1, 
u $ 2 / sqrt(1 - v\<^sup>2) - (v * u $ 4) / sqrt(1 - v\<^sup>2), 
u $ 3, 
u $ 4 / sqrt(1 - v\<^sup>2) - (v * u $ 2) / sqrt(1 - v\<^sup>2)
]
"
text \<open>We define a boost of velocity v in the u$3 direction.\<close>

definition boost_3 :: "[real^4, real] \<Rightarrow> real^4" where
"boost_3 u v \<equiv> 
vector
[
u $ 1, 
u $ 2, 
u $ 3 / sqrt(1 - v\<^sup>2) - (v * u $ 4) / sqrt(1 - v\<^sup>2), 
u $ 4 / sqrt(1 - v\<^sup>2) - (v * u $ 3) / sqrt(1 - v\<^sup>2)
]
"

text \<open>We prove the invariance of the interval with respect to a boost.\<close>

lemma vector_4 [simp]:
 "(vector [x1, x2, x3, x4] ::('a::zero)^4) $ 1 = x1"
 "(vector [x1, x2, x3, x4] ::('a)^4) $ 2 = x2"
 "(vector [x1, x2, x3, x4] ::('a)^4) $ 3 = x3"
 "(vector [x1, x2, x3, x4] ::('a)^4) $ 4 = x4"
  unfolding vector_def 
  by auto

lemma invar_1:
  fixes v:: "real" and u w::"real^4"
  assumes "v\<^sup>2 < 1"
  shows "interval u w = interval (boost_1 u v) (boost_1 w v)"
proof-
  have "interval (boost_1 u v) (boost_1 w v) = 
-((w $ 4 / sqrt(1 - v\<^sup>2) - (v * w $ 1) / sqrt(1 - v\<^sup>2)) - u $ 4 / sqrt(1 - v\<^sup>2) + (v * u $ 1) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ ((w $ 1 / sqrt(1 - v\<^sup>2) - (v * w $ 4) / sqrt(1 - v\<^sup>2)) - u $ 1 / sqrt(1 - v\<^sup>2) + (v * u $ 4) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ (w $ 2 - u $ 2)\<^sup>2 
+ (w $ 3 - u $ 3)\<^sup>2"
    by (simp add: interval_def boost_1_def diff_add_eq diff_diff_eq2)
  then have f1:"interval (boost_1 u v) (boost_1 w v) =
-((w $ 4 - v * w $ 1 - u $ 4 + v * u $ 1) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ ((w $ 1 - v * w $ 4 - u $ 1 + v * u $ 4) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ (w $ 2 - u $ 2)\<^sup>2 
+ (w $ 3 - u $ 3)\<^sup>2"
    by (simp add: add_divide_distrib diff_divide_distrib)
  have f2:"1 - v\<^sup>2 \<ge> 0"
    using assms 
    by simp 
  from f1 f2 have "interval (boost_1 u v) (boost_1 w v) =
1/(1 - v\<^sup>2) * ((w $ 1 - v * w $ 4 - u $ 1 + v * u $ 4)\<^sup>2 -(w $ 4 - v * w $ 1 - u $ 4 + v * u $ 1)\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    by (simp add: diff_divide_distrib power_divide)
  then have "interval (boost_1 u v) (boost_1 w v) =
1/(1 - v\<^sup>2) * ((w $ 1 - u $ 1 - v * (w $ 4 - u $ 4))\<^sup>2 - (w $ 4 - u $ 4 - v * (w $ 1 - u $ 1))\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    apply (simp add: right_diff_distrib')
    by smt
  then have "interval (boost_1 u v) (boost_1 w v) =
1/(1 - v\<^sup>2) * ((w $ 1 - u $ 1)\<^sup>2 - 2 * v * (w $ 1 - u $ 1) * (w $ 4 - u $ 4) + v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2
             - (w $ 4 - u $ 4)\<^sup>2 + 2 * v * (w $ 4 - u $ 4) * (w $ 1 - u $ 1) - v\<^sup>2 * (w $ 1 - u $ 1)\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    apply (simp add: power2_diff power_mult_distrib)
    by (metis (no_types, hide_lams) mult.assoc mult.commute mult.left_commute right_diff_distrib_numeral)
  then have f2:"interval (boost_1 u v) (boost_1 w v) = 
1/(1 - v\<^sup>2) * ((w $ 1 - u $ 1)\<^sup>2 + v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2 - (w $ 4 - u $ 4)\<^sup>2 - v\<^sup>2 * (w $ 1 - u $ 1)\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    by simp
  have f3:"(w $ 1 - u $ 1)\<^sup>2 - v\<^sup>2 * (w $ 1 - u $ 1)\<^sup>2 = (w $ 1 - u $ 1)\<^sup>2 * (1 - v\<^sup>2)"
    by (simp add: right_diff_distrib)
  have f4:"v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2 - (w $ 4 - u $ 4)\<^sup>2 = -(w $ 4 - u $ 4)\<^sup>2 * (1 - v\<^sup>2)"
    by (simp add: right_diff_distrib)
  from f2 f3 f4 have "interval (boost_1 u v) (boost_1 w v) = 
1/(1 - v\<^sup>2) * (- (w $ 4 - u $ 4)\<^sup>2 * (1 - v\<^sup>2) + (w $ 1 - u $ 1)\<^sup>2 * (1 - v\<^sup>2))
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    by simp
  then have "interval (boost_1 u v) (boost_1 w v) = 
1/(1 - v\<^sup>2) * (1 - v\<^sup>2) * (- (w $ 4 - u $ 4)\<^sup>2 + (w $ 1 - u $ 1)\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    using ring_distribs(2) Groups.mult_ac
    by (metis (no_types, hide_lams))
  thus ?thesis
    using assms interval_def[of u w] 
    by simp
qed

lemma invar_2:
  fixes v:: "real" and u w::"real^4"
  assumes "v\<^sup>2 < 1"
  shows "interval u w = interval (boost_2 u v) (boost_2 w v)"
proof-
have "interval (boost_2 u v) (boost_2 w v) = 
-((w $ 4 / sqrt(1 - v\<^sup>2) - (v * w $ 2) / sqrt(1 - v\<^sup>2)) - u $ 4 / sqrt(1 - v\<^sup>2) + (v * u $ 2) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ (w $ 1 - u $ 1)\<^sup>2 
+ ((w $ 2 / sqrt(1 - v\<^sup>2) - (v * w $ 4) / sqrt(1 - v\<^sup>2)) - u $ 2 / sqrt(1 - v\<^sup>2) + (v * u $ 4) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ (w $ 3 - u $ 3)\<^sup>2"
    by (simp add: interval_def boost_2_def diff_add_eq diff_diff_eq2)
  then have f1:"interval (boost_2 u v) (boost_2 w v) =
-((w $ 4 - v * w $ 2 - u $ 4 + v * u $ 2) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ (w $ 1 - u $ 1)\<^sup>2 
+ ((w $ 2 - v * w $ 4 - u $ 2 + v * u $ 4) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ (w $ 3 - u $ 3)\<^sup>2"
    by (simp add: add_divide_distrib diff_divide_distrib)
  have f2:"1 - v\<^sup>2 \<ge> 0"
    using assms 
    by simp 
  from f1 f2 have "interval (boost_2 u v) (boost_2 w v) =
1/(1 - v\<^sup>2) * ((w $ 2 - v * w $ 4 - u $ 2 + v * u $ 4)\<^sup>2 -(w $ 4 - v * w $ 2 - u $ 4 + v * u $ 2)\<^sup>2)
+ (w $ 1 - u $ 1)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    by (simp add: diff_divide_distrib power_divide)
  then have "interval (boost_2 u v) (boost_2 w v) =
1/(1 - v\<^sup>2) * ((w $ 2 - u $ 2 - v * (w $ 4 - u $ 4))\<^sup>2 - (w $ 4 - u $ 4 - v * (w $ 2 - u $ 2))\<^sup>2)
+ (w $ 1 - u $ 1)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    apply (simp add: right_diff_distrib')
    by smt
  then have "interval (boost_2 u v) (boost_2 w v) =
1/(1 - v\<^sup>2) * ((w $ 2 - u $ 2)\<^sup>2 - 2 * v * (w $ 2 - u $ 2) * (w $ 4 - u $ 4) + v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2
             - (w $ 4 - u $ 4)\<^sup>2 + 2 * v * (w $ 4 - u $ 4) * (w $ 2 - u $ 2) - v\<^sup>2 * (w $ 2 - u $ 2)\<^sup>2)
+ (w $ 1 - u $ 1)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    apply (simp add: power2_diff power_mult_distrib)
    by (metis (no_types, hide_lams) mult.commute mult.left_commute right_diff_distrib_numeral)
  then have f2:"interval (boost_2 u v) (boost_2 w v) = 
1/(1 - v\<^sup>2) * ((w $ 2 - u $ 2)\<^sup>2 + v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2 - (w $ 4 - u $ 4)\<^sup>2 - v\<^sup>2 * (w $ 2 - u $ 2)\<^sup>2)
+ (w $ 1 - u $ 1)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    by simp
  have f3:"(w $ 2 - u $ 2)\<^sup>2 - v\<^sup>2 * (w $ 2 - u $ 2)\<^sup>2 = (w $ 2 - u $ 2)\<^sup>2 * (1 - v\<^sup>2)"
    by (simp add: right_diff_distrib)
  have f4:"v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2 - (w $ 4 - u $ 4)\<^sup>2 = -(w $ 4 - u $ 4)\<^sup>2 * (1 - v\<^sup>2)"
    by (simp add: right_diff_distrib)
  from f2 f3 f4 have "interval (boost_2 u v) (boost_2 w v) = 
1/(1 - v\<^sup>2) * (- (w $ 4 - u $ 4)\<^sup>2 * (1 - v\<^sup>2) + (w $ 2 - u $ 2)\<^sup>2 * (1 - v\<^sup>2))
+ (w $ 1 - u $ 1)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    by simp
  then have "interval (boost_2 u v) (boost_2 w v) = 
1/(1 - v\<^sup>2) * (1 - v\<^sup>2) * (- (w $ 4 - u $ 4)\<^sup>2 + (w $ 2 - u $ 2)\<^sup>2)
+ (w $ 1 - u $ 1)\<^sup>2
+ (w $ 3 - u $ 3)\<^sup>2"
    using ring_distribs(2) Groups.mult_ac
    by (metis (no_types, hide_lams))
  thus ?thesis
    using assms interval_def[of u w] 
    by simp
qed

lemma invar_3:
  fixes v:: "real" and u w::"real^4"
  assumes "v\<^sup>2 < 1"
  shows "interval u w = interval (boost_3 u v) (boost_3 w v)"
proof-
 have "interval (boost_3 u v) (boost_3 w v) = 
-((w $ 4 / sqrt(1 - v\<^sup>2) - (v * w $ 3) / sqrt(1 - v\<^sup>2)) - u $ 4 / sqrt(1 - v\<^sup>2) + (v * u $ 3) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ (w $ 1 - u $ 1)\<^sup>2 
+ (w $ 2 - u $ 2)\<^sup>2 
+ ((w $ 3 / sqrt(1 - v\<^sup>2) - (v * w $ 4) / sqrt(1 - v\<^sup>2)) - u $ 3 / sqrt(1 - v\<^sup>2) + (v * u $ 4) / sqrt(1 - v\<^sup>2))\<^sup>2"
    by (simp add: interval_def boost_3_def diff_add_eq diff_diff_eq2)
  then have f1:"interval (boost_3 u v) (boost_3 w v) =
-((w $ 4 - v * w $ 3 - u $ 4 + v * u $ 3) / sqrt(1 - v\<^sup>2))\<^sup>2 
+ (w $ 1 - u $ 1)\<^sup>2 
+ (w $ 2 - u $ 2)\<^sup>2 
+ ((w $ 3 - v * w $ 4 - u $ 3 + v * u $ 4) / sqrt(1 - v\<^sup>2))\<^sup>2"
    by (simp add: add_divide_distrib diff_divide_distrib)
  have f2:"1 - v\<^sup>2 \<ge> 0"
    using assms 
    by simp 
  from f1 f2 have "interval (boost_3 u v) (boost_3 w v) =
1/(1 - v\<^sup>2) * ((w $ 3 - v * w $ 4 - u $ 3 + v * u $ 4)\<^sup>2 -(w $ 4 - v * w $ 3 - u $ 4 + v * u $ 3)\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 1 - u $ 1)\<^sup>2"
    by (simp add: diff_divide_distrib power_divide)
  then have "interval (boost_3 u v) (boost_3 w v) =
1/(1 - v\<^sup>2) * ((w $ 3 - u $ 3 - v * (w $ 4 - u $ 4))\<^sup>2 - (w $ 4 - u $ 4 - v * (w $ 3 - u $ 3))\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 1 - u $ 1)\<^sup>2"
    apply (simp add: right_diff_distrib')
    by smt
  then have "interval (boost_3 u v) (boost_3 w v) =
1/(1 - v\<^sup>2) * ((w $ 3 - u $ 3)\<^sup>2 - 2 * v * (w $ 3 - u $ 3) * (w $ 4 - u $ 4) + v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2
             - (w $ 4 - u $ 4)\<^sup>2 + 2 * v * (w $ 4 - u $ 4) * (w $ 3 - u $ 3) - v\<^sup>2 * (w $ 3 - u $ 3)\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 1 - u $ 1)\<^sup>2"
    apply (simp add: power2_diff power_mult_distrib)
    by (metis (no_types, hide_lams) mult.commute mult.left_commute right_diff_distrib_numeral)
  then have f2:"interval (boost_3 u v) (boost_3 w v) = 
1/(1 - v\<^sup>2) * ((w $ 3 - u $ 3)\<^sup>2 + v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2 - (w $ 4 - u $ 4)\<^sup>2 - v\<^sup>2 * (w $ 3 - u $ 3)\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 1 - u $ 1)\<^sup>2"
    by simp
  have f3:"(w $ 3 - u $ 3)\<^sup>2 - v\<^sup>2 * (w $ 3 - u $ 3)\<^sup>2 = (w $ 3 - u $ 3)\<^sup>2 * (1 - v\<^sup>2)"
    by (simp add: right_diff_distrib)
  have f4:"v\<^sup>2 * (w $ 4 - u $ 4)\<^sup>2 - (w $ 4 - u $ 4)\<^sup>2 = -(w $ 4 - u $ 4)\<^sup>2 * (1 - v\<^sup>2)"
    by (simp add: right_diff_distrib)
  from f2 f3 f4 have "interval (boost_3 u v) (boost_3 w v) = 
1/(1 - v\<^sup>2) * (- (w $ 4 - u $ 4)\<^sup>2 * (1 - v\<^sup>2) + (w $ 3 - u $ 3)\<^sup>2 * (1 - v\<^sup>2))
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 1 - u $ 1)\<^sup>2"
    by simp
  then have "interval (boost_3 u v) (boost_3 w v) = 
1/(1 - v\<^sup>2) * (1 - v\<^sup>2) * (- (w $ 4 - u $ 4)\<^sup>2 + (w $ 3 - u $ 3)\<^sup>2)
+ (w $ 2 - u $ 2)\<^sup>2
+ (w $ 1 - u $ 1)\<^sup>2"
    using ring_distribs(2) Groups.mult_ac
    by (metis (no_types, hide_lams))
  thus ?thesis
    using assms interval_def[of u w] 
    by simp
qed
    








end