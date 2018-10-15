(* 
Author: Anthony Bordg 
Affiliation: University of Cambridge 
email: apdb3@cam.ac.uk 
*)

theory Special_Relativity
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
"interval u w \<equiv> -(w$3 - u$3)\<^sup>2 + (w$0 - u$0)\<^sup>2 + (w$1 - u$1)\<^sup>2 + (w$2 - u$2)\<^sup>2"

text \<open>We define a boost of velocity v in the u$0 direction.\<close>

definition boost_0 :: "[real^4, real] \<Rightarrow> real^4" where
"boost_0 u v \<equiv> 
vector
[
(u$0/sqrt(1 - v\<^sup>2)) - (v * u$3)/sqrt(1 - v\<^sup>2), 
u$1, 
u$2, 
(u$3/sqrt(1 - v\<^sup>2)) - (v * u$0)/sqrt(1 - v\<^sup>2)
]
"
text \<open>We define a boost of velocity v in the u$1 direction.\<close>

definition boost_1 :: "[real^4, real] \<Rightarrow> real^4" where
"boost_1 u v \<equiv> 
vector
[
u$0, 
u$1/sqrt(1 - v\<^sup>2) - (v * u$3)/sqrt(1 - v\<^sup>2), 
u$2, 
(u$3/sqrt(1 - v\<^sup>2)) - (v * u$1)/sqrt(1 - v\<^sup>2)
]
"
text \<open>We define a boost of velocity v in the u$2 direction.\<close>

definition boost_2 :: "[real^4, real] \<Rightarrow> real^4" where
"boost_2 u v \<equiv> 
vector
[
u$0, 
u$1, 
u$2/sqrt(1 - v\<^sup>2) - (v * u$3)/sqrt(1 - v\<^sup>2), 
(u$3/sqrt(1 - v\<^sup>2)) - (v * u$2)/sqrt(1 - v\<^sup>2)
]
"

text \<open>We prove the invariance of the interval with respect to a boost.\<close>

lemma invar_0:
  fixes v:: "real" and u w::"real^4"
  assumes "v\<^sup>2 < 1"
  shows "interval u w = interval (boost_0 u v) (boost_0 w v)"
proof-
  fix v::"real" and u w::"real^4"
  have "interval (boost_0 u v) (boost_0 w v) = 
-((w$3/sqrt(1 - v\<^sup>2) - (v * w$0)/sqrt(1 - v\<^sup>2)) - u$3/sqrt(1 - v\<^sup>2) + (v * u$0)/sqrt(1 - v\<^sup>2))\<^sup>2 + 
((w$0/sqrt(1 - v\<^sup>2) - (v * w$3)/sqrt(1 - v\<^sup>2)) - u$0/sqrt(1 - v\<^sup>2) + (v * u$3)/sqrt(1 - v\<^sup>2))\<^sup>2 + 
(w$1 - u$1)\<^sup>2 + 
(w$2 - u$2)\<^sup>2"
    apply (auto intro: field_simps simp add: interval_def boost_0_def)
    








end