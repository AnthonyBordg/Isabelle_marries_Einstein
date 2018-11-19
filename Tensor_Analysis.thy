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

lemma one_form_eq_prelim:
  fixes f::"one_form" and g::"one_form"
  assumes "one_form_to_fun f = one_form_to_fun g"
  shows "f = g"
  using assms one_form_to_fun_def
  by (simp add: Rep_one_form_inject)

lemma one_form_to_fun_eq:
  fixes f::"one_form" and g::"one_form"
  assumes "\<forall>x::real^4. one_form_to_fun f x = one_form_to_fun g x"
  shows "one_form_to_fun f = one_form_to_fun g"
  using assms
  by (simp add: ext)

lemma one_form_eq:
  fixes f::"one_form" and g::"one_form"
  assumes "\<forall>x::real^4. one_form_to_fun f x = one_form_to_fun g x"
  shows "f = g"
  using assms one_form_eq_prelim one_form_to_fun_eq 
  by simp

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

(*declare [[show_sorts,show_types,show_consts]]*)

instance
proof 
  show "\<And>f g h::one_form. f + g + h = f + (g + h)"
  proof-
    fix f g h::"one_form"
    have "(f + g + h) x = (f + (g + h)) x" for x::"real^4"
      using plus_one_form_def Rep_one_form one_form_to_fun_def semiring_normalization_rules(25)
      by (metis (mono_tags, lifting) Abs_one_form_inverse islinear_plus_one_form mem_Collect_eq)
    thus "f + g + h = f + (g + h)"
      using one_form_eq 
      by simp
  qed
  show "\<And>f g::one_form. f + g = g + f"
  proof-
    fix f g::"one_form"
    have "(f + g) x = (g + f) x" for x::"real^4"
      using plus_one_form_def Rep_one_form
      by (simp add: linordered_field_class.sign_simps(27))
    thus "f + g = g + f"
      using one_form_eq 
      by simp
  qed
  show "\<And>f::one_form. 0 + f = f"
  proof-
    fix f::"one_form"
    have "(0 + f) x = f x" for x::"real^4"
      using plus_one_form_def Rep_one_form
      by (simp add: zero_one_form_def Abs_one_form_inverse module_hom_zero one_form_to_fun_def)
    thus "0 + f = f"
      using one_form_eq 
      by simp
  qed
  show "\<And>f::one_form. - f + f = (0::one_form)"
  proof-
    fix f::"one_form"
    have "(- f + f) x = (0::one_form) x" for x::"real^4"
      using plus_one_form_def uminus_one_form_def Rep_one_form zero_one_form_def Abs_one_form_inverse 
        islinear_uminus_one_form one_form_to_fun_def 
      by simp
    thus "- f + f = (0::one_form)"
      using one_form_eq 
      by simp
  qed
  show "\<And>(f::one_form) g::one_form. f - g = f + - g"
  proof-
    fix f::"one_form" and g::"one_form"
    have "(f - g) x = (f + - g) x" for x::"real^4"
      using minus_one_form_def uminus_one_form_def plus_one_form_def Abs_one_form_inverse 
        islinear_uminus_one_form one_form_to_fun_def 
      by simp
    thus "f - g = f + - g"
      using one_form_eq 
      by simp
  qed
  show "\<And>(r::real) f g::one_form. r *\<^sub>R (f + g) = r *\<^sub>R f + r *\<^sub>R g"
  proof-
    fix r::real and f g::one_form
    have "(r *\<^sub>R (f + g)) x = (r *\<^sub>R f + r *\<^sub>R g) x" for x::"real^4"
      using plus_one_form_def scaleR_one_form_def ring_class.ring_distribs(1)
      by (metis (mono_tags, lifting) Abs_one_form_inverse islinear_plus_one_form 
          islinear_scaleR_one_form mem_Collect_eq one_form_to_fun_def)
    thus "r *\<^sub>R (f + g) = r *\<^sub>R f + r *\<^sub>R g"
      using one_form_eq 
      by simp
  qed
  show "\<And>r (s::real) f::one_form. (r + s) *\<^sub>R f = r *\<^sub>R f + s *\<^sub>R f"
  proof-
    fix r s::real and f::one_form
    have f1:"((r + s) *\<^sub>R f) x = (r + s) * f(x)" for x::"real^4"
      using scaleR_one_form_def Abs_one_form_inverse islinear_scaleR_one_form one_form_to_fun_def 
      by simp
    have f2:"(r *\<^sub>R f + s *\<^sub>R f) x = r * f(x) + s * f(x)" for x::"real^4"
      using scaleR_one_form_def plus_one_form_def
      by (metis (no_types, lifting) Abs_one_form_inverse islinear_plus_one_form islinear_scaleR_one_form 
          mem_Collect_eq one_form_to_fun_def)
    from f1 and f2 have "((r + s) *\<^sub>R f) x = (r *\<^sub>R f + s *\<^sub>R f) x" for x::"real^4"
      using scaleR_one_form_def plus_one_form_def
      by (simp add: distrib_right)
    thus "(r + s) *\<^sub>R f = r *\<^sub>R f + s *\<^sub>R f"
      using one_form_eq 
      by simp
  qed
  show "\<And>r (s::real) f::one_form. r *\<^sub>R s *\<^sub>R f = (r * s) *\<^sub>R f"
  proof-
    fix r s::real and f::one_form
    have "(r *\<^sub>R s *\<^sub>R f) x = ((r * s) *\<^sub>R f) x" for x::"real^4"
      using scaleR_one_form_def
      by (metis Abs_one_form_inverse islinear_scaleR_one_form linordered_field_class.sign_simps(23) 
          mem_Collect_eq one_form_to_fun_def)
    thus "r *\<^sub>R s *\<^sub>R f = (r * s) *\<^sub>R f"
      using one_form_eq 
      by simp
  qed
  show "\<And>f::one_form. 1 *\<^sub>R f = f"
  proof-
    fix f::one_form
    have "(1 *\<^sub>R f) x = f x" for x::"real^4"
      using scaleR_one_form_def
      by (simp add: Rep_one_form_inverse one_form_to_fun_def)
    thus "1 *\<^sub>R f = f"
      using one_form_eq 
      by simp
  qed
qed
      
end


end
