(* 
Author: Anthony Bordg 
Affiliation: University of Cambridge 
email: apdb3@cam.ac.uk
Date: November 2018 
*)

theory Tensor_Analysis
imports
  "HOL-Analysis.Analysis"
  VectorSpace.VectorSpace
begin

section \<open>The (0,1) Tensors: One-Forms\<close>

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

section \<open>Components of a One-Form on a Basis\<close>

text 
\<open>
We prove that real^4 is a (real) vector space using the notion of vector space in the theory
VectorSpace of Holden Lee. That way one can use notions like span, linear independence and basis
introduced in that theory.  
\<close>

definition real4_add :: "[real^4, real^4] \<Rightarrow> real^4" where
"real4_add x y \<equiv> vector [x $ 1 + y $ 1, x $ 2 + y $ 2, x $ 3 + y $ 3, x $ 4 + y $ 4]"

definition real4_zero :: "real^4" where
"real4_zero \<equiv> vector [0, 0, 0, 0]"

definition real4_monoid :: "(_, _) ring_scheme" where
"real4_monoid \<equiv> \<lparr>carrier = UNIV::(real^4) set, mult = real4_add, one = real4_zero, 
  zero = undefined, add = undefined\<rparr>"

interpretation isabelian_monoid_real4 : abelian_monoid "real4_monoid" sorry

interpretation isabelian_group_real4 : abelian_group "real4_monoid" sorry

definition real_ring :: "(_, _) ring_scheme" where
"real_ring \<equiv> \<lparr>carrier = UNIV::real set, mult = ( * ), one = 1, zero = 0, add = (+)\<rparr>"

interpretation iscring_real_ring : cring "real_ring" sorry

definition real4_smult :: "[real, real^4] \<Rightarrow> real^4" where
"real4_smult r x \<equiv> vector [r * x $ 1, r * x $ 2, r * x $ 3, r * x $ 4]"

definition real4_module :: "(_, _, _) module_scheme" where
"real4_module \<equiv> \<lparr>carrier = UNIV::(real^4) set, mult = real4_add, one = real4_zero, 
  zero = undefined, add = undefined, smult = real4_smult\<rparr>"

interpretation ismodule_real4 : module "real_ring" "real4_module" sorry

interpretation isdomain : domain "real_ring" sorry

interpretation isfield : field "real_ring" sorry

interpretation isvecspace_real4 : vectorspace "real_ring" "real4_module" sorry

text 
\<open>
Since for the components of a vector, vector [], one starts counting from 1, we adopt the same
convention for counting the vectors of a given basis. But it is odd from the mathematician point 
of view (usually a mathematician starts counting from 0). 
\<close>

definition vec_basis1 :: "real^4" ("e\<^sub>1") where
"vec_basis1 \<equiv> vector [1, 0, 0, 0]"

definition vec_basis2 :: "real^4" ("e\<^sub>2") where
"vec_basis2 \<equiv> vector [0, 1, 0, 0]"

definition vec_basis3 :: "real^4" ("e\<^sub>3") where
"vec_basis3 \<equiv> vector [0, 0, 1, 0]"

definition vec_basis4 :: "real^4" ("e\<^sub>4") where
"vec_basis4 \<equiv> vector [0, 0, 0, 1]"

definition basis1 :: "(real^4) set" ("\<O>") where
"basis1 \<equiv> {e\<^sub>1, e\<^sub>2, e\<^sub>3, e\<^sub>4}"

lemma isbasis_basis1 :
  shows "isvecspace_real4.basis \<O>" sorry

text
\<open>
Now, one considers the situation where a second frame of reference \<O>' moves with 
velocity v \<le> 1 (c = 1) in the x direction relative to the first frame \<O>. Then, one applies the Lorentz 
transformation to get a second basis.
\<close>

definition lorentz_factor :: "real \<Rightarrow> real" ("\<gamma>(_)") where
"lorentz_factor v \<equiv> 1/sqrt(1 - v\<^sup>2)"

definition vec_basis1' :: "real \<Rightarrow> real^4" ("e\<^sub>1'") where
"vec_basis1' v \<equiv> vector [\<gamma>(v), v * \<gamma>(v), 0 ,0]"

definition vec_basis2' :: "real \<Rightarrow> real^4" ("e\<^sub>2' (_)") where
"vec_basis2' v \<equiv> vector [v * \<gamma>(v), \<gamma>(v) , 0, 0]"

definition vec_basis3' :: "real \<Rightarrow> real^4" ("e\<^sub>3' (_)") where
"vec_basis3' v \<equiv> vector [0, 0, 1, 0]"

definition vec_basis4' :: "real \<Rightarrow> real^4" ("e\<^sub>4' (_)") where
"vec_basis4' v \<equiv> vector [0, 0, 0, 1]"

definition basis1' :: "real \<Rightarrow> (real^4) set" ("\<O>' (_)") where
"basis1' v \<equiv> {e\<^sub>1'(v), e\<^sub>2'(v), e\<^sub>3'(v), e\<^sub>4'(v)}"

lemma isbasis_basis1' :
  fixes v :: real
  shows "isvecspace_real4.basis \<O>'(v)" sorry

text 
\<open>
We define the components of a one_form on a given basis as the real numbers obtained from
the application of the one_form to the basis vectors.
\<close>

definition comp1_one_form :: "one_form \<Rightarrow> real" ("_\<^sub>1") where
"comp1_one_form f \<equiv> f(e\<^sub>1)"

definition comp1'_one_form :: "real \<Rightarrow> one_form \<Rightarrow> real" ("_\<^sub>1'") where
"comp1'_one_form v f \<equiv> f(e\<^sub>1'(v))"

definition comp2_one_form :: "one_form \<Rightarrow> real" ("_\<^sub>2") where
"comp2_one_form f \<equiv> f(e\<^sub>2)"

definition comp2'_one_form :: "real \<Rightarrow> one_form \<Rightarrow> real" ("_\<^sub>2'") where
"comp2'_one_form v f \<equiv> f(e\<^sub>2'(v))"

definition comp3_one_form :: "one_form \<Rightarrow> real" ("_\<^sub>3") where
"comp3_one_form f \<equiv> f(e\<^sub>3)"

definition comp3'_one_form :: "real \<Rightarrow> one_form \<Rightarrow> real" ("_\<^sub>3'") where
"comp3'_one_form v f \<equiv> f(e\<^sub>3'(v))"

definition comp4_one_form :: "one_form \<Rightarrow> real" ("_\<^sub>4") where
"comp4_one_form f \<equiv> f(e\<^sub>4)"

definition comp4'_one_form :: "real \<Rightarrow> one_form \<Rightarrow> real" ("_\<^sub>4'") where
"comp4'_one_form v f \<equiv> f(e\<^sub>4'(v))"

text \<open>The components of one_forms transform in the same manner as those of basis vectors.\<close>

lemma comp_one_form_transform :
  fixes v::"real" and f::"one_form"
  shows "f\<^sub>1' = (\<gamma>(v)) * f\<^sub>1 + (v * \<gamma>(v)) * f\<^sub>2" and "f\<^sub>2' = (v * \<gamma>(v)) * f\<^sub>1 + (\<gamma>(v)) * f\<^sub>2" and
    "f\<^sub>3' = f\<^sub>3" and "f\<^sub>4' = f\<^sub>4" sorry

text \<open>The components of vectors transform in the opposite manner to those of one_forms.\<close>

definition comp1'_vec :: "real \<Rightarrow> real^4 \<Rightarrow> real" ("_\<^sub>1'") where
"comp1'_vec v x \<equiv> (\<gamma>(v)) * (x $ 1) + (- v * \<gamma>(v)) * (x $ 2)"

definition comp2'_vec :: "real \<Rightarrow> real^4 \<Rightarrow> real" ("_\<^sub>2'") where
"comp2'_vec v x \<equiv> (- v * \<gamma>(v)) * (x $ 1) + (\<gamma>(v)) * (x $ 2)"

definition comp3'_vec :: "real \<Rightarrow> real^4 \<Rightarrow> real" ("_\<^sub>3'") where
"comp3'_vec v x \<equiv> x $ 3"

definition comp4'_vec :: "real \<Rightarrow> real^4 \<Rightarrow> real" ("_\<^sub>4'") where
"comp4'_vec v x \<equiv> x $ 4"

text 
\<open>
In the same way a vector is kept frame independent (but not its components which depend on the 
chosen basis), one has the following frame independent quantity.
\<close>


end
