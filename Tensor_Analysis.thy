(* 
Author: Anthony Bordg 
Affiliation: University of Cambridge 
email: apdb3@cam.ac.uk
Date: November 2018 
*)

theory Tensor_Analysis
imports
  Main
  HOL.Real_Vector_Spaces
  "HOL-Analysis.Analysis"
begin

text \<open>The (0,1) tensors: one-forms\<close>

text 
\<open>
A one-form is a linear function of one vector into the real numbers.
We focus on the case where vectors are real four-dimensional vectors.
\<close>

typedef one_form = "{f| f:: real^4 \<Rightarrow> real. linear f}"
  using linear_zero
  by auto

text
\<open>
The set of one-forms has the structure of a vector space. It is often called the "dual vector space"
in order to distinguish it from the corresponding vector space of vectors.
\<close>

definition one_form_to_fun :: "one_form \<Rightarrow> real^4 \<Rightarrow> real" where
"one_form_to_fun f \<equiv> Rep_one_form f"

text\<open>We introduce a coercion from one_forms to functions.\<close>

declare [[coercion one_form_to_fun]]

instantiation one_form :: real_vector
begin

lemma islinear_uminus_one_form:
  fixes f::"one_form"
  shows "linear (\<lambda>v. - f(v))"
proof
  show "\<And>u v. - f (u + v) = - f u + - f v"
    using Rep_one_form
    by (simp add: linear_add one_form_to_fun_def)
  show "\<And>r b. - f (r *\<^sub>R b) = r *\<^sub>R - f b"
    using Rep_one_form
    by (simp add: linear_scale one_form_to_fun_def)
qed

definition uminus_one_form :: "one_form \<Rightarrow> one_form" where
"uminus_one_form f \<equiv> Abs_one_form (\<lambda>v. - f(v))"

lemma islinear_zero_one_form:
  shows "linear (\<lambda>v. 0)"
  using linear_zero
  by simp

definition zero_one_form :: "one_form" where
"zero_one_form \<equiv> Abs_one_form (\<lambda>v. 0)"

lemma islinear_minus_one_form:
  fixes f::"one_form" and g::"one_form"
  shows "linear (\<lambda>v. (f(v) - g(v)))" 
proof
  show "\<And>u v. f (u + v) -  g (u + v) = f (u) - g (u) + (f (v) - g (v))"
    using Rep_one_form
    by (simp add: linear_add one_form_to_fun_def)
  show "\<And>r v. f (r *\<^sub>R v) - g (r *\<^sub>R v) = r *\<^sub>R (f v - g v)"
  proof-
    fix r::"real" and v::"real^4"
    have "f (r *\<^sub>R v) - g (r *\<^sub>R v) = r *\<^sub>R f(v) -  r *\<^sub>R g(v)"
      using Rep_one_form
      by (simp add: linear_scale one_form_to_fun_def)
    thus "f (r *\<^sub>R v) - g (r *\<^sub>R v) = r *\<^sub>R (f v - g v)"
      by (metis scale_right_diff_distrib)
  qed
qed

definition minus_one_form :: "one_form \<Rightarrow> one_form \<Rightarrow> one_form" where
"minus_one_form f g \<equiv> Abs_one_form (\<lambda>v. f(v) - g(v))"

lemma islinear_plus_one_form:
  fixes f::"one_form" and g::"one_form"
  shows "linear (\<lambda>v. (f(v) + g(v)))" 
proof
  show "\<And>u v. f (u + v) +  g (u + v) = f u +  g u + (f v + g v)"
    using Rep_one_form
    by (simp add: linear_add one_form_to_fun_def)
  show "\<And>r v. f (r *\<^sub>R v) + g (r *\<^sub>R v) = r *\<^sub>R (f v + g v)"
  proof-
    fix r::"real" and v::"real^4"
    have "f (r *\<^sub>R v) + g (r *\<^sub>R v) = r *\<^sub>R f(v) +  r *\<^sub>R g(v)"
      using Rep_one_form
      by (simp add: linear_scale one_form_to_fun_def)
    thus "f (r *\<^sub>R v) + g (r *\<^sub>R v) = r *\<^sub>R (f v + g v)"
      using scaleR_add_right 
      by metis
  qed
qed

definition plus_one_form :: "one_form \<Rightarrow> one_form \<Rightarrow> one_form" where
"plus_one_form f g \<equiv> Abs_one_form (\<lambda>v. f(v) + g(v))"

lemma islinear_scaleR_one_form:
  fixes f::"one_form"
  shows "linear (\<lambda>v. r * f(v))"
proof
  show "\<And>u v. r * f (u + v) = r * f u + r * f v"
    using Rep_one_form
    by (simp add: linear_add one_form_to_fun_def ring_class.ring_distribs(1))
  show "\<And>s v. r * f (s *\<^sub>R v) = s *\<^sub>R (r * f v)"
    using Rep_one_form
    by (simp add: linear_scale one_form_to_fun_def)
qed

definition scaleR_one_form :: "real \<Rightarrow> one_form \<Rightarrow> one_form" where
"scaleR_one_form r f \<equiv> Abs_one_form (\<lambda>v. r * f(v))"

instance
proof
  show "\<And>a b c. a + b + c = a + (b + c)"
        

end


end
