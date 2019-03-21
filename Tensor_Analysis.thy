(* 
Author: Anthony Bordg 
Affiliation: University of Cambridge 
email: apdb3@cam.ac.uk
Date: November 2018 

Biblio:

- A First Course in General Relativity, Bernard Schutz, Cambridge University Press, second edition,
chapter 3.
*)

text \<open>Abstract: \<close>

(*
Since we follow a physics textbook, we do not strive for the most general results or the most
general mathematical formulations.
*)

theory Tensor_Analysis
imports
  "HOL-Analysis.Analysis"
  VectorSpace.VectorSpace
  "HOL-Analysis.Finite_Cartesian_Product"
  "HOL-Algebra.Ring"
  VectorSpace.MonoidSums
  HOL.Groups_Big
begin

text
\<open>
Following the textbook mentioned above we take a pedagogical approach. Indeed, we start with 
(0,1)-tensors and (0,2)-tensors before introducing the general case: (m,n)-tensors.
\<close>

section \<open>The (0,1)-Tensors: One-Forms\<close>

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

lemma linear_uminus_one_form:
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

lemma linear_zero_one_form:
  shows "linear (\<lambda>v. 0)"
  using linear_zero
  by simp

definition zero_one_form :: "one_form" where
"zero_one_form \<equiv> Abs_one_form (\<lambda>v. 0)"

lemma linear_minus_one_form:
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

lemma linear_plus_one_form:
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

lemma linear_scaleR_one_form:
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
      by (metis (mono_tags, lifting) Abs_one_form_inverse linear_plus_one_form mem_Collect_eq)
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
        linear_uminus_one_form one_form_to_fun_def 
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
        linear_uminus_one_form one_form_to_fun_def 
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
      by (metis (mono_tags, lifting) Abs_one_form_inverse linear_plus_one_form 
          linear_scaleR_one_form mem_Collect_eq one_form_to_fun_def)
    thus "r *\<^sub>R (f + g) = r *\<^sub>R f + r *\<^sub>R g"
      using one_form_eq 
      by simp
  qed
  show "\<And>r (s::real) f::one_form. (r + s) *\<^sub>R f = r *\<^sub>R f + s *\<^sub>R f"
  proof-
    fix r s::real and f::one_form
    have f1:"((r + s) *\<^sub>R f) x = (r + s) * f(x)" for x::"real^4"
      using scaleR_one_form_def Abs_one_form_inverse linear_scaleR_one_form one_form_to_fun_def 
      by simp
    have f2:"(r *\<^sub>R f + s *\<^sub>R f) x = r * f(x) + s * f(x)" for x::"real^4"
      using scaleR_one_form_def plus_one_form_def
      by (metis (no_types, lifting) Abs_one_form_inverse linear_plus_one_form linear_scaleR_one_form 
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
      by (metis Abs_one_form_inverse linear_scaleR_one_form linordered_field_class.sign_simps(23) 
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
"real4_add x y \<equiv> \<chi> i. x $ i + y $ i"

definition real4_zero :: "real^4" where
"real4_zero \<equiv> \<chi> i. 0"

lemma real4_add_zero_left:
  shows "real4_add real4_zero x = x"
  using real4_add_def
  by (simp add: real4_zero_def)

lemma real4_add_zero_right:
  shows "real4_add x real4_zero = x"
  using real4_add_def
  by (simp add: real4_zero_def)

definition real4_monoid :: "(_, _) monoid_scheme" where
"real4_monoid \<equiv> \<lparr>carrier = UNIV::(real^4) set, mult = ( * ), one = 1, 
  zero = real4_zero, add = real4_add\<rparr>"
   
interpretation monoid_real4 : monoid "real4_monoid"
  apply unfold_locales
  apply (auto simp: real4_monoid_def).

interpretation abelian_monoid_real4 : abelian_monoid "real4_monoid"
  apply unfold_locales
  apply (auto simp: real4_monoid_def real4_add_def real4_zero_def).

definition real4_minus :: "real^4 \<Rightarrow> real^4" where
"real4_minus x \<equiv> \<chi> i. uminus x $ i"

lemma real4_add_right_inv:
  fixes x::"real^4"
  shows "real4_add x (real4_minus x) = real4_zero"
  apply (auto simp: real4_minus_def real4_add_def real4_zero_def).

lemma real4_add_left_inv:
  fixes x::"real^4"
  shows "real4_add (real4_minus x) x = real4_zero"
  apply (auto simp: real4_minus_def real4_add_def real4_zero_def).

interpretation abelian_group_real4 : abelian_group "real4_monoid"
  apply unfold_locales
  apply (auto simp: real4_monoid_def Units_def)
  using real4_add_left_inv real4_add_right_inv
  by blast 

definition real_ring :: "(_, _) ring_scheme" where
"real_ring \<equiv> \<lparr>carrier = UNIV::real set, mult = ( * ), one = 1, zero = 0, add = (+)\<rparr>"

interpretation cring_real_ring : cring "real_ring"
  apply unfold_locales
  apply (auto simp: real_ring_def Units_def)
  apply (metis diff_eq_eq linordered_field_class.sign_simps(27))
  apply (simp add: ring_class.ring_distribs(2))
  by (simp add: ring_class.ring_distribs(1))

definition real4_smult :: "[real, real^4] \<Rightarrow> real^4" where
"real4_smult r x \<equiv> \<chi> i. r * x $ i"

definition real4_mult :: "real^4 \<Rightarrow> real^4 \<Rightarrow> real^4" where
"real4_mult x y \<equiv> \<chi> i. x $ i * y $ i"

definition real4_one :: "real^4" where
"real4_one \<equiv> \<chi> i. 1"

definition real4_module :: "(_, _, _) module_scheme" where
"real4_module \<equiv> \<lparr>carrier = UNIV::(real^4) set, mult = real4_mult, one = real4_one, 
  zero = real4_zero, add = real4_add, smult = real4_smult\<rparr>"

interpretation module_real4 : module "real_ring" "real4_module"
  apply unfold_locales
  apply (auto simp: real4_module_def Units_def real_ring_def real4_smult_def real4_add_def real4_zero_def)
  apply (metis (no_types, hide_lams) add.commute add.right_inverse vector_add_component zero_index)
  apply (auto simp: ring_class.ring_distribs(2) ring_class.ring_distribs(1) mult.assoc).
  
interpretation domain_real : domain "real_ring"
  apply unfold_locales
  apply (auto simp: real_ring_def).

interpretation field_real : field "real_ring"
  apply unfold_locales
  apply (auto simp: real_ring_def Units_def)
  by (metis divide_self_if mult.commute real_divide_square_eq times_divide_eq_right)

interpretation vecspace_real4 : vectorspace "real_ring" "real4_module"
  apply unfold_locales.

lemma real4_smult_smult:
  fixes x::"real^4" and k l::"real"
  shows "k \<odot>\<^bsub>real4_module\<^esub> (l \<odot>\<^bsub>real4_module\<^esub> x) = (k * l) \<odot>\<^bsub>real4_module\<^esub> x"
  apply (auto simp: vec_eq_iff real4_smult_def real4_module_def).

lemma real4_smult_left_factor:
  fixes x::"real^4" and k l::"real"
  shows "k \<odot>\<^bsub>real4_module\<^esub> x + l \<odot>\<^bsub>real4_module\<^esub> x = (k + l) \<odot>\<^bsub>real4_module\<^esub> x"
  apply (auto simp: real4_module_def real4_smult_def real4_add_def vec_eq_iff)
  by (simp add: ring_class.ring_distribs(2))

lemma real4_smult_left_distr:
  fixes x y::"real^4" and k l m::"real"
  shows "k \<odot>\<^bsub>real4_module\<^esub> (l \<odot>\<^bsub>real4_module\<^esub> x + m \<odot>\<^bsub>real4_module\<^esub> y) = 
    k * l \<odot>\<^bsub>real4_module\<^esub> x + k * m \<odot>\<^bsub>real4_module\<^esub> y"
  apply (auto simp: real4_module_def real4_smult_def real4_add_def vec_eq_iff)
  by (simp add: ring_class.ring_distribs(1))

lemma real4_smult_left_distr_bis:
  fixes x y::"real^4" and k l m k' l' m'::"real"
  shows "k \<odot>\<^bsub>real4_module\<^esub> (l \<odot>\<^bsub>real4_module\<^esub> x + m \<odot>\<^bsub>real4_module\<^esub> y) + 
  k' \<odot>\<^bsub>real4_module\<^esub> (l' \<odot>\<^bsub>real4_module\<^esub> x + m' \<odot>\<^bsub>real4_module\<^esub> y) = 
((k * l) + k' * l') \<odot>\<^bsub>real4_module\<^esub> x + ((k * m) + k' * m') \<odot>\<^bsub>real4_module\<^esub> y"
proof-
  have "k \<odot>\<^bsub>real4_module\<^esub> (l \<odot>\<^bsub>real4_module\<^esub> x + m \<odot>\<^bsub>real4_module\<^esub> y) +
    k' \<odot>\<^bsub>real4_module\<^esub> (l' \<odot>\<^bsub>real4_module\<^esub> x + m' \<odot>\<^bsub>real4_module\<^esub> y) = 
 k * l \<odot>\<^bsub>real4_module\<^esub> x + k * m \<odot>\<^bsub>real4_module\<^esub> y + 
 k' * l' \<odot>\<^bsub>real4_module\<^esub> x + k' * m' \<odot>\<^bsub>real4_module\<^esub> y"
    using real4_smult_left_distr
    by simp
  then have "k \<odot>\<^bsub>real4_module\<^esub> (l \<odot>\<^bsub>real4_module\<^esub> x + m \<odot>\<^bsub>real4_module\<^esub> y) +
    k' \<odot>\<^bsub>real4_module\<^esub> (l' \<odot>\<^bsub>real4_module\<^esub> x + m' \<odot>\<^bsub>real4_module\<^esub> y) = 
k * l \<odot>\<^bsub>real4_module\<^esub> x + k' * l' \<odot>\<^bsub>real4_module\<^esub> x + k * m \<odot>\<^bsub>real4_module\<^esub> y + k' * m' \<odot>\<^bsub>real4_module\<^esub> y"
    by simp
  thus ?thesis
    using real4_smult_left_factor[of "k * l" "x" "k' * l'"] real4_smult_left_factor[of "k * m" "y" "k' * m'"]
    by simp
qed

lemma real4_smult_left_distr_ter:
  fixes x y::"real^4" and k1 k2 k3 k4 l m l' m'::"real"
  shows "m \<odot>\<^bsub>real4_module\<^esub> (l \<odot>\<^bsub>real4_module\<^esub> (k1 \<odot>\<^bsub>real4_module\<^esub> x + k2 \<odot>\<^bsub>real4_module\<^esub> y)) +
m' \<odot>\<^bsub>real4_module\<^esub> (l' \<odot>\<^bsub>real4_module\<^esub> (k3 \<odot>\<^bsub>real4_module\<^esub> x + k4 \<odot>\<^bsub>real4_module\<^esub> y)) = 
 ((m * l * k1) + m' * l' * k3) \<odot>\<^bsub>real4_module\<^esub> x + ((m * l * k2) + m' * l' * k4) \<odot>\<^bsub>real4_module\<^esub> y"
  by (simp add: add.commute add.left_commute mult.commute mult.left_commute real4_smult_left_distr 
real4_smult_left_factor)

lemma real4_smult_one:
  fixes x::"real^4"
  shows "1 \<odot>\<^bsub>real4_module\<^esub> x = x"
  using vec_eq_iff real4_smult_def
  by (simp add: real4_module_def)

lemma real4_smult_minus:
  fixes x::"real^4" and k::"real"
  shows "k \<odot>\<^bsub>real4_module\<^esub> -x = -k \<odot>\<^bsub>real4_module\<^esub> x"
  apply (auto simp: vec_eq_iff real4_smult_def real4_module_def).

lemma real4_smult_minus_bis:
  fixes x::"real^4"
  shows "-x = -1 \<odot>\<^bsub>real4_module\<^esub> x"
  using real4_smult_one real4_smult_minus 
  by metis

lemma real4_minus_smult:
  fixes x y::"real^4" and k l::"real"
  shows "k \<odot>\<^bsub>real4_module\<^esub> x + -l \<odot>\<^bsub>real4_module\<^esub> y = k \<odot>\<^bsub>real4_module\<^esub> x - l \<odot>\<^bsub>real4_module\<^esub> y"
  by (simp add: real4_smult_minus_bis real4_smult_smult)

lemma real4_smult_left_distr_bis_minus:
  fixes x y::"real^4" and k l m k' l' m'::"real"
  shows "k \<odot>\<^bsub>real4_module\<^esub> (l \<odot>\<^bsub>real4_module\<^esub> x - m \<odot>\<^bsub>real4_module\<^esub> y) + 
  k' \<odot>\<^bsub>real4_module\<^esub> (l' \<odot>\<^bsub>real4_module\<^esub> x - m' \<odot>\<^bsub>real4_module\<^esub> y) = 
((k * l) + k' * l') \<odot>\<^bsub>real4_module\<^esub> x - (k * m + k' * m') \<odot>\<^bsub>real4_module\<^esub> y"
proof-
  have "k * -m + k' * -m' = - (k * m + k' * m')"
    apply (auto simp: Rings.ring_class.minus_mult_commute Num.neg_numeral_class.is_num_normalize(8)).
  then have "(k * -m + k' * -m') \<odot>\<^bsub>real4_module\<^esub> y = - (k * m + k' * m') \<odot>\<^bsub>real4_module\<^esub> y"
    by simp
  thus ?thesis
    using real4_smult_left_distr_bis[of "k" "l" "x" "-m" "y" "k'" "l'" "-m'"]
    by (metis real4_minus_smult)
qed

lemma real4_smult_left_distr_ter_minus:
  fixes x y::"real^4" and k1 k2 k3 k4 l m l' m'::"real"
  shows "m \<odot>\<^bsub>real4_module\<^esub> (l \<odot>\<^bsub>real4_module\<^esub> (k1 \<odot>\<^bsub>real4_module\<^esub> x - k2 \<odot>\<^bsub>real4_module\<^esub> y)) +
m' \<odot>\<^bsub>real4_module\<^esub> (l' \<odot>\<^bsub>real4_module\<^esub> (k3 \<odot>\<^bsub>real4_module\<^esub> x - k4 \<odot>\<^bsub>real4_module\<^esub> y)) = 
 ((m * l * k1) + m' * l' * k3) \<odot>\<^bsub>real4_module\<^esub> x - ((m * l * k2) + m' * l' * k4) \<odot>\<^bsub>real4_module\<^esub> y"
  using real4_smult_left_distr_ter
  by (simp add: real4_smult_left_distr_bis_minus real4_smult_smult)

lemma real4_minus:
  fixes x::"real^4" and k::"real"
  shows "- (k \<odot>\<^bsub>real4_module\<^esub> x) = -k \<odot>\<^bsub>real4_module\<^esub> x"
  using real4_minus_smult 
  by simp

text 
\<open>
Since for the components of a vector, vector [], one starts counting from 1, we adopt the same
convention for counting the vectors of a given basis. But it is odd from the mathematician point 
of view (usually a mathematician starts counting from 0). 
\<close>

definition vec_basis ::"nat \<Rightarrow> real^4" ("e \<^sub>_") where
"vec_basis i \<equiv> 
if i = 1 then vector [1, 0, 0, 0] else 
  if i = 2 then vector [0, 1, 0, 0] else
    if i = 3 then vector [0, 0, 1, 0] else 
      if i = 4 then vector [0, 0, 0, 1] else undefined"

definition vec_basis_set ::"(real^4) set" ("\<O>") where
"vec_basis_set \<equiv> {e \<^sub>1, e \<^sub>2, e \<^sub>3, e \<^sub>4}"

lemma sum_insert:
  assumes "x \<notin> F" and "finite F"
  shows "(\<Sum>y\<in>insert x F. P y) = (\<Sum>y\<in>F. P y) + P x"
  using assms insert_def
  by (simp add: add.commute)  

lemma finsum_to_sum:
  fixes F::"(real^4) set"
  assumes "finite F" and "P \<in> (F \<rightarrow> carrier real4_module)"
  shows "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>F. P v) = (\<Sum>v\<in>F. P v)"
  using assms
proof induct
  case empty
  then show "P \<in> {} \<rightarrow> carrier real4_module \<Longrightarrow> finsum real4_module P {} = sum P {}"
    by (metis module_real4.add.finprod_empty real4_module_def real4_zero_def ring_record_simps(11) 
        sum.empty zero_vec_def)
next
  case (insert x F)
  then show "\<And>x F. finite F \<Longrightarrow>
              x \<notin> F \<Longrightarrow>
                (P \<in> F \<rightarrow> carrier real4_module \<Longrightarrow> finsum real4_module P F = sum P F) \<Longrightarrow>
                  P \<in> insert x F \<rightarrow> carrier real4_module \<Longrightarrow>
                    finsum real4_module P (insert x F) = sum P (insert x F)"
  proof-
    fix x::"real^4" and F::"(real^4) set"
    assume a1:"finite F" and a2:"x \<notin> F" and rec:"P \<in> F \<rightarrow> carrier real4_module \<Longrightarrow> finsum real4_module P F = sum P F"
      and a3:"P \<in> insert x F \<rightarrow> carrier real4_module"
    then have "sum P (insert x F) = P x + sum P F"
      using Groups_Big.sum_Un insert_def
      by simp
    then have f1:"sum P (insert x F) = P x + finsum real4_module P F"
      using rec a3 
      by simp
    have "finsum real4_module P (insert x F) = P x + finsum real4_module P F"
    proof-
      have "finsum real4_module P (insert x F) = P x \<oplus>\<^bsub>real4_module\<^esub> finsum real4_module P F"
        using module_real4.finsum_insert[of "F" "x" "P"] a1 a2 a3 insert_def
        by simp
      thus ?thesis
        using real4_module_def real4_add_def
        by (smt plus_vec_def ring_record_simps(12))
    qed
   thus "finsum real4_module P (insert x F) = sum P (insert x F)"
     using f1 
     by simp
 qed
qed


lemma finsum_insert:
  assumes "x \<notin> F" and "finite F"
  shows "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>insert x F. P v) =  P x + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>F. P v)"
proof-
  have "(\<Sum>y\<in>({x} \<inter> F). P y) = real4_zero"
    using abelian_monoid.finsum_empty assms(1)
    by (simp add: real4_zero_def zero_vec_def)
  then have f1:"(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>({x}\<inter>F). P v) = real4_zero"
    using finsum_to_sum assms(1) 
    by force
  then have "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>insert x F. P v) = 
    P x + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>F. P v) - (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>({x}\<inter>F). P v)"
    using Groups_Big.sum_Un finsum_to_sum
    by (smt Pi_I UNIV_I add.right_neutral add_diff_cancel_left' assms(1) assms(2) empty_iff 
        finite.intros(1) module_real4.finsum_insert partial_object.select_convs(1) plus_vec_def 
        real4_add_def real4_module_def real4_zero_def ring_record_simps(12) sum.insert_if sum_clauses(1) 
        sum_insert zero_vec_def)
  thus ?thesis
    using f1
    by (simp add: real4_zero_def zero_vec_def)
qed

lemma lincomb_comp :
  assumes "finite A" and "a \<in> (A \<rightarrow> carrier real_ring)"
  shows "\<forall>i. (module_real4.lincomb a A) $ i = (\<Sum>x\<in>{v. v\<in>A}. a x * (x $ i))"
  apply (auto simp: module_real4.lincomb_def)
  using assms(1)
proof induct
  case empty
  then show "\<And>i. (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>{}. a v \<odot>\<^bsub>real4_module\<^esub> v) $ i = (\<Sum>x\<in>{}. a x * x $ i)"
    apply (auto simp: Ring.abelian_monoid.finsum_empty)
    by (simp add: real4_module_def real4_zero_def)
next
  case (insert x A)
  then show "\<And>x F i.
       finite F \<Longrightarrow>
       x \<notin> F \<Longrightarrow>
       (\<And>i. (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>F. a v \<odot>\<^bsub>real4_module\<^esub> v) $ i = (\<Sum>x\<in>F. a x * x $ i)) \<Longrightarrow>
       (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>insert x F. a v \<odot>\<^bsub>real4_module\<^esub> v) $ i = (\<Sum>x\<in>insert x F. a x * x $ i)"
  proof-
    fix x F i
    assume a1:"finite F" and a2:"x \<notin> F" and rec:"(\<And>i. (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>F. a v \<odot>\<^bsub>real4_module\<^esub> v) $ i = (\<Sum>x\<in>F. a x * x $ i))"
    have f1:"(\<Sum>x\<in>insert x F. a x * x $ i) = (\<Sum>x\<in>F. a x * x $ i) + a x * x $ i"
      using a1 a2
      by (simp add: sum_insert)
    have f2:"(a x \<odot>\<^bsub>real4_module\<^esub> x) $ i = a x * x $ i"
      using real4_smult_def
      by (simp add: real4_module_def)
    have "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>insert x F. a v \<odot>\<^bsub>real4_module\<^esub> v) = 
      (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>F. a v \<odot>\<^bsub>real4_module\<^esub> v) + (a x \<odot>\<^bsub>real4_module\<^esub> x)"
      using a1 a2
      by (simp add: finsum_insert)
    then have "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>insert x F. a v \<odot>\<^bsub>real4_module\<^esub> v) $ i = 
      (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>F. a v \<odot>\<^bsub>real4_module\<^esub> v) $ i + (a x \<odot>\<^bsub>real4_module\<^esub> x) $ i"
      using vec_eq_iff real4_add_def
      by simp
    then show "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>insert x F. a v \<odot>\<^bsub>real4_module\<^esub> v) $ i = (\<Sum>x\<in>insert x F. a x * x $ i)"
      using f1 f2 rec 
      by simp
  qed
qed

lemma vector_comp:
  shows "(vector [x1, x2, x3, x4]::('a::zero)^4) $ (1::4) = x1"
    and "(vector [x1, x2, x3, x4]::('a::zero)^4) $ 2 = x2"
    and "(vector [x1, x2, x3, x4]::('a::zero)^4) $ 3 = x3"
    and "(vector [x1, x2, x3, x4]::('a::zero)^4) $ 4 = x4"
  unfolding vector_def
  by auto

lemma vec_basis_noteq_1:
  shows "e \<^sub>1 \<noteq> e \<^sub>2" and "e \<^sub>1 \<noteq> e \<^sub>3" and "e \<^sub>1 \<noteq> e \<^sub>4"
  using vec_basis_def
  apply (metis One_nat_def Suc_1 old.nat.inject vector_comp(1) zero_neq_one)
  apply (metis numeral_eq_one_iff semiring_norm(84) vec_basis_def vector_comp(1) zero_neq_one)
  by (metis numeral_eq_one_iff semiring_norm(83) vec_basis_def vector_comp(1) zero_neq_one)

lemma vec_basis_noteq_2:
  shows "e \<^sub>2 \<noteq> e \<^sub>1" and "e \<^sub>2 \<noteq> e \<^sub>3" and "e \<^sub>2 \<noteq> e \<^sub>4"
  using vec_basis_def
  apply (metis One_nat_def Suc_1 old.nat.inject vector_comp(2) zero_neq_one)
  apply (metis numeral_eq_iff semiring_norm(88) vec_basis_def vec_basis_noteq_1(1) vector_comp(2))
  by (metis (no_types, lifting) numeral_eq_iff semiring_norm(85) semiring_norm(87) vec_basis_def 
      vec_basis_noteq_1(3) vector_comp(2))

lemma vec_basis_noteq_3:
  shows "e \<^sub>3 \<noteq> e \<^sub>1" and "e \<^sub>3 \<noteq> e \<^sub>2" and "e \<^sub>3 \<noteq> e \<^sub>4"
  using vec_basis_def vec_basis_noteq_1(2) apply auto[1]
  apply (metis numeral_eq_iff semiring_norm(88) vec_basis_def vec_basis_noteq_1(1) vector_comp(2))
  by (metis numeral_eq_iff semiring_norm(89) vec_basis_def vec_basis_noteq_1(3) vec_basis_noteq_2(3) 
      vector_comp(4))

lemma vec_basis_noteq_4:
  shows "e \<^sub>4 \<noteq> e \<^sub>1" and "e \<^sub>4 \<noteq> e \<^sub>2" and "e \<^sub>4 \<noteq> e \<^sub>3"
  using vec_basis_def vec_basis_noteq_1(3) apply auto[1]
  using vec_basis_noteq_2(3) apply auto[1]
  using vec_basis_noteq_3(3) 
  by auto

lemma lincomb_vec_basis:
  assumes "finite A" and "A \<subseteq> \<O>" and "a \<in> (A \<rightarrow> carrier real_ring)" and "v \<in> A" and "a v \<noteq> 0"
  shows "module_real4.lincomb a A \<noteq> real4_zero"
  apply (auto simp: module_real4.lincomb_def real4_zero_def)
proof-
  have f1:"\<forall>i. (\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ i = (\<Sum>x\<in>{u. u\<in>A}. a x * (x $ i))"
    using assms(1) assms(3) lincomb_comp module_real4.lincomb_def 
    by simp
(* One needs to distinguish 4 symmetric cases depending on the value of v *)
  have R1:"v = e \<^sub>1 \<or> v = e \<^sub>2 \<or> v = e \<^sub>3 \<or> v = e \<^sub>4"
    using assms(4) assms(2) vec_basis_set_def 
    by auto
(* case 1 : v = e1 *)
  have R2:"v = e \<^sub>1 \<longrightarrow> module_real4.lincomb a A \<noteq> real4_zero"
  proof
    assume a1:"v = e \<^sub>1"
    have f2:"(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 1 = (\<Sum>x\<in>{u. u\<in>A}. a x * (x $ 1))"
      using f1 
      by simp
    have f3:"a e \<^sub>1 * (e \<^sub>1 $ 1) = a e \<^sub>1"
      by (simp add: vec_basis_def vector_def)
    have "\<forall>i. i = 2 \<or> i = 3 \<or> i = 4 \<longrightarrow> a (e \<^sub>i) * ((e \<^sub>i) $ 1) = 0"
      using vec_basis_def
      by (simp add: vector_comp(1))
    then have f4:"(\<Sum>x\<in>A-{e \<^sub>2,e \<^sub>3,e \<^sub>4}. a x * (x $ 1)) = (\<Sum>x\<in>A. a x * (x $ 1))"
      using a1 assms(1)
      by (smt Diff_iff Diff_subset empty_iff insertE sum.mono_neutral_right)
    have "A-{e \<^sub>2,e \<^sub>3,e \<^sub>4} = {e \<^sub>1}"
      using a1 assms(4) assms(2) vec_basis_set_def vec_basis_noteq_1
      by fastforce
    then have "(\<Sum>x\<in>A-{e \<^sub>2,e \<^sub>3,e \<^sub>4}. a x * (x $ 1)) = a v"
      using a1 f3 
      by simp 
    then have "(\<Sum>x\<in>A. a x * (x $ 1)) = a v"
      using a1 f4 
      by simp
    then have "(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 1 \<noteq> 0"
      using a1 f2 assms(5) 
      by simp
    thus "module_real4.lincomb a A \<noteq> real4_zero"
      using a1 real4_zero_def
      by (metis module_real4.lincomb_def zero_index zero_vec_def)
  qed
(* case 2 : v = e2 *)
have R3:"v = e \<^sub>2 \<longrightarrow> module_real4.lincomb a A \<noteq> real4_zero"
  proof
    assume a2:"v = e \<^sub>2"
    have f5:"(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 2 = (\<Sum>x\<in>{u. u\<in>A}. a x * (x $ 2))"
      using f1 
      by simp
    have f6:"a e \<^sub>2 * (e \<^sub>2 $ 2) = a e \<^sub>2"
      by (simp add: vec_basis_def vector_def)
    have f7:"\<forall>i. i = 1 \<or> i = 3 \<or> i = 4 \<longrightarrow> a (e \<^sub>i) * ((e \<^sub>i) $ 2) = 0"
      using vec_basis_def
      by (simp add: vector_comp(2))
    then have f8:"(\<Sum>x\<in>A-{e \<^sub>1,e \<^sub>3,e \<^sub>4}. a x * (x $ 2)) = (\<Sum>x\<in>A. a x * (x $ 2))"
      using a2 assms(1)
      by (smt Diff_iff Diff_subset empty_iff insertE sum.mono_neutral_right)
    have "A-{e \<^sub>1,e \<^sub>3,e \<^sub>4} = {e \<^sub>2}"
      using a2 assms(4) assms(2) vec_basis_set_def vec_basis_noteq_2
      by fastforce
    then have "(\<Sum>x\<in>A-{e \<^sub>1,e \<^sub>3,e \<^sub>4}. a x * (x $ 2)) = a v"
      using a2 f6 
      by simp 
    then have "(\<Sum>x\<in>A. a x * (x $ 2)) = a v"
      using a2 f8 
      by simp
    then have "(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 2 \<noteq> 0"
      using a2 f5 assms(5) 
      by simp
    thus "module_real4.lincomb a A \<noteq> real4_zero"
      using a2 real4_zero_def
      by (metis module_real4.lincomb_def zero_index zero_vec_def)
  qed
(* case 3 : v = e3 *)
have R4:"v = e \<^sub>3 \<longrightarrow> module_real4.lincomb a A \<noteq> real4_zero"
  proof
    assume a3:"v = e \<^sub>3"
    have f9:"(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 3 = (\<Sum>x\<in>{u. u\<in>A}. a x * (x $ 3))"
      using f1 
      by simp
    have f10:"a e \<^sub>3 * (e \<^sub>3 $ 3) = a e \<^sub>3"
      by (simp add: vec_basis_def vector_def)
    have f11:"\<forall>i. i = 1 \<or> i = 2 \<or> i = 4 \<longrightarrow> a (e \<^sub>i) * ((e \<^sub>i) $ 3) = 0"
      using vec_basis_def
      by (simp add: vector_comp(3))
    then have f12:"(\<Sum>x\<in>A-{e \<^sub>1,e \<^sub>2,e \<^sub>4}. a x * (x $ 3)) = (\<Sum>x\<in>A. a x * (x $ 3))"
      using a3 assms(1)
      by (smt Diff_iff Diff_subset empty_iff insertE sum.mono_neutral_right)
    have "A-{e \<^sub>1,e \<^sub>2,e \<^sub>4} = {e \<^sub>3}"
      using a3 assms(4) assms(2) vec_basis_set_def vec_basis_noteq_3
      by fastforce
    then have "(\<Sum>x\<in>A-{e \<^sub>1,e \<^sub>2,e \<^sub>4}. a x * (x $ 3)) = a v"
      using a3 f10 
      by simp 
    then have "(\<Sum>x\<in>A. a x * (x $ 3)) = a v"
      using a3 f12 
      by simp
    then have "(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 3 \<noteq> 0"
      using a3 f9 assms(5) 
      by simp
    thus "module_real4.lincomb a A \<noteq> real4_zero"
      using a3 real4_zero_def
      by (metis module_real4.lincomb_def zero_index zero_vec_def)
  qed
(* case 4 : v = e4 *)
have R5:"v = e \<^sub>4 \<longrightarrow> module_real4.lincomb a A \<noteq> real4_zero"
  proof
    assume a4:"v = e \<^sub>4"
    have f13:"(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 4 = (\<Sum>x\<in>{u. u\<in>A}. a x * (x $ 4))"
      using f1 
      by simp
    have f14:"a e \<^sub>4 * (e \<^sub>4 $ 4) = a e \<^sub>4"
      by (simp add: vec_basis_def vector_def)
    have f15:"\<forall>i. i = 1 \<or> i = 2 \<or> i = 3 \<longrightarrow> a (e \<^sub>i) * ((e \<^sub>i) $ 4) = 0"
      using vec_basis_def
      by (simp add: vector_comp(4))
    then have f16:"(\<Sum>x\<in>A-{e \<^sub>1,e \<^sub>2,e \<^sub>3}. a x * (x $ 4)) = (\<Sum>x\<in>A. a x * (x $ 4))"
      using a4 assms(1)
      by (smt Diff_iff Diff_subset empty_iff insertE sum.mono_neutral_right)
    have "A-{e \<^sub>1,e \<^sub>2,e \<^sub>3} = {e \<^sub>4}"
      using a4 assms(4) assms(2) vec_basis_set_def vec_basis_noteq_4
      by fastforce
    then have "(\<Sum>x\<in>A-{e \<^sub>1,e \<^sub>2,e \<^sub>3}. a x * (x $ 4)) = a v"
      using a4 f14 
      by simp 
    then have "(\<Sum>x\<in>A. a x * (x $ 4)) = a v"
      using a4 f16 
      by simp
    then have "(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 4 \<noteq> 0"
      using a4 f13 assms(5) 
      by simp
    thus "module_real4.lincomb a A \<noteq> real4_zero"
      using a4 real4_zero_def
      by (metis module_real4.lincomb_def zero_index zero_vec_def)
  qed
  thus "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A. a v \<odot>\<^bsub>real4_module\<^esub> v) = (\<chi> i. 0) \<Longrightarrow> False"
    using R1 R2 R3 R4 R5
    by (simp add: module_real4.lincomb_def real4_zero_def)
qed

lemma lin_indpt_vec_basis :
  shows "module_real4.lin_indpt \<O>"
proof
  assume "module_real4.lin_dep \<O>"
  then obtain A a v where a1:"finite A" and a2:"A \<subseteq> \<O>" and a3:"a \<in> (A \<rightarrow> carrier real_ring)" and 
    a4:"module_real4.lincomb a A = real4_zero" and a5:"v \<in> A" and a6:"a v \<noteq> 0"
    using module_real4.lin_dep_def real4_module_def
    by (metis partial_object.select_convs(1) real_ring_def ring_record_simps(11))
  thus "False"
    using lincomb_vec_basis a1 a2 a3 a5 a6 a4
    by blast
qed

lemma vector_eta:
  fixes x::"real^4"
  shows "(\<chi> i. if i = 1 then x $ 1 else 
    if i = 2 then x $ 2 else 
      if i = 3 then x $ 3 else 
        if i = 4 then x $ 4 else 0) = 
  vector [x $ 1, x $ 2, x $ 3, x $ 4]"
  apply (auto simp: vec_eq_iff vector_def).

lemma exhaust_4:
  fixes x :: 4
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 4" 
    by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3" 
    by arith
  then show ?case 
    by auto
qed

lemma forall_4: 
  shows "(\<forall>i::4. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3 \<and> P 4"
  by (metis exhaust_4)

lemma UNIV_4: 
  shows "UNIV = {1::4, 2::4, 3::4, 4::4}"
  using exhaust_4 
  by auto

lemma sum_4: 
  shows "sum f (UNIV::4 set) = f 1 + f 2 + f 3 + f 4"
  unfolding UNIV_4 
  by (simp add: ac_simps)

lemma vector_eta_bis:
  fixes x::"real^4"
  shows "vector [x $ 1, x $ 2, x $ 3, x $ 4] = x"
  apply (auto simp: vec_eq_iff vector_def)
  using exhaust_4 
  by auto

lemma vector_add:
  shows "(vector [x1, x2, x3, x4]::(real, _) vec) + vector [y1, y2, y3, y4] = 
    vector [x1 + y1, x2 + y2, x3 + y3, x4 + y4]"
  apply (auto simp: vec_eq_iff)
  by (simp add: vector_comp(1) vec_lambda_inverse vector_def)

lemma vec_to_comp_basis:
  fixes x::"real^4"
  assumes "a \<in> (\<O> \<rightarrow> carrier real_ring)" and "a (e \<^sub>1) = x $ 1" and "a (e \<^sub>2) = x $ 2" and "a (e \<^sub>3) = x $ 3" 
    and "a (e \<^sub>4) = x $ 4"
  shows "a (e \<^sub>1) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) = vector [x $ 1, 0, 0, 0]" and 
    "a (e \<^sub>2) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) = vector [0, x $ 2, 0, 0]" and 
    "a (e \<^sub>3) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>3) = vector [0, 0, x $ 3, 0]" and
    "a (e \<^sub>4) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>4) = vector [0, 0, 0, x $ 4]"
proof-
  have "a (e \<^sub>1) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) = vector [x $ 1 * 1, x $ 1 * 0, x $ 1 * 0, x $ 1 * 0]"
    using assms(2) vec_basis_def real4_module_def real4_smult_def vector_eta
    by (smt UNIV_I module.select_convs(1) mult_cancel_left1 mult_cancel_right1 vec_lambda_inverse 
vector_comp(1) vector_comp(2) vector_comp(3) vector_comp(4) vector_eta_bis)
  then show "a (e \<^sub>1) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) = vector [x $ 1, 0, 0, 0]" 
    by simp
  have "a (e \<^sub>2) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) = vector [x $ 2 * 0, x $ 2 * 1, x $ 2 * 0, x $ 2 * 0]"
    using assms(3) vec_basis_def real4_module_def real4_smult_def vector_eta
    by (smt UNIV_I module.select_convs(1) mult_cancel_left1 mult_cancel_right1 numeral_eq_one_iff 
vec_lambda_inverse vector_comp(1) vector_comp(2) vector_comp(3) vector_comp(4) vector_eta_bis)
  then show "a (e \<^sub>2) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) = vector [0, x $ 2, 0, 0]" 
    by simp
  have "a (e \<^sub>3) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>3) = vector [x $ 3 * 0, x $ 3 * 0, x $ 3 * 1, x $ 3 * 0]"
    using assms(4) vec_basis_def real4_module_def real4_smult_def vector_eta
    by (smt UNIV_I module.select_convs(1) mult_cancel_left1 mult_cancel_right1 numeral_eq_one_iff 
rel_simps(72) semiring_norm(86) vec_lambda_inverse vector_comp(1) vector_comp(2) vector_comp(3) 
vector_comp(4) vector_eta_bis)
  then show "a (e \<^sub>3) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>3) = vector [0, 0, x $ 3, 0]" 
    by simp
  have "a (e \<^sub>4) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>4) = vector [x $ 4 * 0, x $ 4 * 0, x $ 4 * 0, x $ 4 * 1]"
    using assms(5) vec_basis_def real4_module_def real4_smult_def vector_eta
    by (smt UNIV_I module.select_convs(1) mult_cancel_left1 mult_cancel_right1 numeral_eq_one_iff 
rel_simps(72) semiring_norm(83) vec_lambda_inverse vector_comp(1) vector_comp(2) vector_comp(3) 
vector_comp(4) vector_eta_bis)
  then show "a (e \<^sub>4) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>4) = vector [0, 0, 0, x $ 4]" 
    by simp
qed

lemma vec_to_sum_comp_basis:
  fixes x::"real^4"
  assumes "a \<in> (\<O> \<rightarrow> carrier real_ring)" and "a (e \<^sub>1) = x $ 1" and "a (e \<^sub>2) = x $ 2" and "a (e \<^sub>3) = x $ 3" 
    and "a (e \<^sub>4) = x $ 4"
  shows "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>\<O>. a v \<odot>\<^bsub>real4_module\<^esub> v) = x"
proof-
  have f1:"(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>\<O>. a v \<odot>\<^bsub>real4_module\<^esub> v) = a (e \<^sub>1) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + 
a (e \<^sub>2) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) + a (e \<^sub>3) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>3) + a (e \<^sub>4) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>4)"
    using finsum_def vec_basis_set_def real4_module_def
    by (smt Pi_I' add.right_neutral empty_iff finite.emptyI finite.insertI finsum_insert finsum_to_sum 
        insertE is_num_normalize(1) sum.empty vec_basis_noteq_1(1) vec_basis_noteq_1(2) 
        vec_basis_noteq_1(3) vec_basis_noteq_2(2) vec_basis_noteq_2(3) vec_basis_noteq_3(3))
  have "a (e \<^sub>1) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + a (e \<^sub>2) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) + a (e \<^sub>3) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>3) 
+ a (e \<^sub>4) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>4) = vector [x $ 1, 0, 0, 0] + vector [0, x $ 2, 0, 0]
+ vector [0, 0, x $ 3, 0] + vector [0, 0, 0, x $ 4]"
    by (smt One_nat_def UNIV_I assms vec_eq_iff vec_lambda_inverse vec_to_comp_basis)
  then have f2:"(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>\<O>. a v \<odot>\<^bsub>real4_module\<^esub> v) = vector [x $ 1, 0, 0, 0] + vector [0, x $ 2, 0, 0]
+ vector [0, 0, x $ 3, 0] + vector [0, 0, 0, x $ 4]"
    using f1 
    by simp
  have " vector [x $ 1, 0, 0, 0] + vector [0, x $ 2, 0, 0] + vector [0, 0, x $ 3, 0] + vector [0, 0, 0, x $ 4] 
= vector [x $ 1, x $ 2, x $ 3, x $ 4]"
    by (simp add: vector_add)
  then have f3:"(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>\<O>. a v \<odot>\<^bsub>real4_module\<^esub> v) =  vector [x $ 1, x $ 2, x $ 3, x $ 4]"
    using f2 
    by simp 
  thus "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>\<O>. a v \<odot>\<^bsub>real4_module\<^esub> v) = x"
    using vector_eta_bis
    by simp
qed

lemma gen_set_vec_basis :
  shows "module_real4.gen_set \<O>"
  apply (auto simp: module_real4.span_def real4_module_def)
proof-
  fix x::"real^4"
  define a where d1:"a \<equiv> \<lambda>v\<in>\<O>. if v = vec_basis (1::nat) then (x $ 1) else
  if v = e \<^sub>2 then x $ 2 else
    if v = e \<^sub>3 then x $ 3 else
      if v = e \<^sub>4 then x $ 4 else
        undefined"
  then have f1:"a \<in> (\<O> \<rightarrow> carrier real_ring)"
    by (simp add: real_ring_def)
  then have "x = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>\<O>. a v \<odot>\<^bsub>real4_module\<^esub> v)"
  proof-
    have f2:"a (e \<^sub>1) = x $ 1"
      using d1
      by (simp add: vec_basis_set_def)
    have f3:"a (e \<^sub>2) = x $ 2"
      using d1 vec_basis_noteq_1(1) vec_basis_set_def 
      by auto
    have f4:"a (e \<^sub>3) = x $ 3"
      using d1 vec_basis_noteq_2(2) vec_basis_noteq_3(1) vec_basis_set_def 
      by auto
    have f5:"a (e \<^sub>4) = x $ 4"
      using d1 vec_basis_noteq_4(1) vec_basis_noteq_4(2) vec_basis_noteq_4(3) vec_basis_set_def 
      by auto
    thus ?thesis
      using f1 f2 f3 f4 vec_to_sum_comp_basis 
      by auto
  qed
  then have "x \<in> {module_real4.lincomb a \<O>}"
    using module.lincomb_def[of "real_ring" "real4_module" "a" "\<O>"]
    by (simp add: module_real4.module_axioms) 
  thus "x \<in> LinearCombinations.module.span real_ring
              \<lparr>carrier = UNIV, monoid.mult = real4_mult, one = real4_one, zero = real4_zero,
                 add = real4_add, smult = real4_smult\<rparr>
              \<O>"
    using LinearCombinations.module.span_def[of "real_ring" "real4_module" "\<O>"] f1
    by (metis (mono_tags, lifting) finite.emptyI finite.insertI mem_Collect_eq module_real4.module_axioms 
        real4_module_def singletonD subset_refl vec_basis_set_def)
qed
    
lemma vec_basis_in_univ :
  shows "\<O> \<subseteq> carrier real4_module"
  using vec_basis_def
  by (simp add: real4_module_def)

lemma basis_vec_basis :
  shows "vecspace_real4.basis \<O>"
  using  lin_indpt_vec_basis gen_set_vec_basis vec_basis_in_univ
  by (simp add: vecspace_real4.basis_def)

text
\<open>
Now, one considers the situation where a second frame of reference \<O>' moves with 
velocity v < 1 (with c = 1) in the x direction relative to the first frame \<O>. 
Then, one applies the Lorentz transformation to get a second basis.
\<close>

definition lorentz_factor :: "real \<Rightarrow> real" ("\<gamma> _") where
"lorentz_factor v \<equiv> 1/sqrt(1 - v\<^sup>2)"

lemma Lorentz_factor_not_zero:
  fixes v::"real" 
  assumes "v \<noteq> 1" and "v \<noteq> -1"
  shows "\<gamma> (v) \<noteq> 0"
  using lorentz_factor_def assms
  by (simp add: power2_eq_1_iff)

text \<open>The transform for components of vectors.\<close>

definition vec_nth' :: "real^4 \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" ("_ $ _ _") where
"vec_nth' x v n \<equiv> if n=1 then (\<gamma> v) * (x $ 1) + (- v * \<gamma> v) * (x $ 2) else
  if n=2 then (- v * \<gamma> v) * (x $ 1) + (\<gamma> v) * (x $ 2) else
  if n=3 then x $ 3 else
  if n= 4 then x $ 4 else undefined"

definition vec_basis1' :: "real \<Rightarrow> real^4" ("e\<^sub>1'") where
"vec_basis1' v \<equiv> vector [\<gamma> v, v * \<gamma> v, 0 ,0]"

definition vec_basis2' :: "real \<Rightarrow> real^4" ("e\<^sub>2' (_)") where
"vec_basis2' v \<equiv> vector [v * \<gamma> v, \<gamma> v , 0, 0]"

definition vec_basis3' :: "real \<Rightarrow> real^4" ("e\<^sub>3' (_)") where
"vec_basis3' v \<equiv> vector [0, 0, 1, 0]"

definition vec_basis4' :: "real \<Rightarrow> real^4" ("e\<^sub>4' (_)") where
"vec_basis4' v \<equiv> vector [0, 0, 0, 1]"

definition vec_basis' :: "real \<Rightarrow> (real^4) set" ("\<O>' (_)") where
"vec_basis' v \<equiv> {e\<^sub>1'(v), e\<^sub>2'(v), e\<^sub>3'(v), e\<^sub>4'(v)}"

lemma vec_basis1'_to_vec_basis:
  fixes v::"real"
  shows "e\<^sub>1'(v) = \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + v * \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2)"
  using vec_basis1'_def vec_basis_def real4_module_def real4_smult_def
  by (smt UNIV_I module.select_convs(1) mult_cancel_left1 mult_cancel_right1 numeral_eq_one_iff 
vec_lambda_inverse vector_add vector_comp vector_eta_bis)

lemma vec_basis2'_to_vec_basis:
  fixes v::"real"
  shows "e\<^sub>2'(v) = v * \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2)"
  using vec_basis2'_def vec_basis_def real4_module_def real4_smult_def
  by (smt UNIV_I module.select_convs(1) mult_cancel_left1 mult_cancel_right1 numeral_eq_one_iff 
vec_lambda_inverse vector_add vector_comp vector_eta_bis)

lemma vec_basis3'_to_vec_basis:
  fixes v::"real"
  shows "e\<^sub>3'(v) = e \<^sub>3"
  using vec_basis3'_def vec_basis_def
  by simp

lemma vec_basis4'_to_vec_basis:
  fixes v::"real"
  shows "e\<^sub>4'(v) = e \<^sub>4"
  using vec_basis4'_def vec_basis_def 
  by simp

lemma vec_basis1'_neq_vec_basis34:
  fixes v::"real"
  shows "e\<^sub>1'(v) \<noteq> e \<^sub>3" and "e\<^sub>1'(v) \<noteq> e \<^sub>4"
  using vec_basis1'_def vec_basis_def
  apply (metis vec_basis3'_def vec_basis3'_to_vec_basis vector_comp(3) zero_neq_one)
  by (metis (no_types, lifting) num.inject(1) numeral_eq_iff numeral_eq_one_iff semiring_norm(85) 
vec_basis1'_def vec_basis_def vec_basis_noteq_4(3) vector_comp(4))

lemma vec_basis2'_neq_vec_basis34:
  fixes v::"real"
  shows "e\<^sub>2'(v) \<noteq> e \<^sub>3" and "e\<^sub>2'(v) \<noteq> e \<^sub>4"
  using vec_basis2'_def vec_basis_def
  apply (metis vec_basis3'_def vec_basis3'_to_vec_basis vector_comp(3) zero_neq_one)
  by (metis (no_types, lifting) num.inject(1) numeral_eq_iff numeral_eq_one_iff semiring_norm(85) 
vec_basis2'_def vec_basis_def vec_basis_noteq_4(3) vector_comp(4))

lemma vec_basis2'_neq_vec_basis1':
  fixes v::"real"
  assumes "v \<noteq> 1" and "v \<noteq> -1"
  shows "e\<^sub>2'(v) \<noteq> e\<^sub>1'(v)"
proof
  assume "e\<^sub>2'(v) = e\<^sub>1'(v)"
  then have "v * \<gamma> v = \<gamma> v"
    by (metis vec_basis1'_def vec_basis2'_def vector_comp(2))
  then have "v = 1"
    using assms Lorentz_factor_not_zero 
    by simp
  thus False
    using assms(1) 
    by simp
qed

lemma lincomb_vec_basis'_to_lin_dep_vec_basis_1:
  fixes v::"real"
  assumes "finite A" and "A \<subseteq> \<O>' (v)" and "a \<in> (A \<rightarrow> carrier real_ring)" and 
"module_real4.lincomb a A = real4_zero" and "u \<in> A" and "a u \<noteq> 0" and "e\<^sub>1'(v) \<notin> A \<and> e\<^sub>2'(v) \<notin> A"
  shows "module_real4.lin_dep \<O>"
proof-
  have "A \<subseteq> \<O>"
    using assms(7) assms(2) vec_basis'_def vec_basis_set_def vec_basis3'_to_vec_basis 
      vec_basis4'_to_vec_basis
    by auto
  thus ?thesis
      using assms module.lin_dep_def[of "real_ring" "real4_module" "\<O>"]
      by (metis module_real4.module_axioms partial_object.select_convs(1) real4_module_def 
          real_ring_def ring_record_simps(11))
qed

lemma lincomb_vec_basis'_to_lin_dep_vec_basis_2:
  fixes v::"real"
  assumes "finite A" and "A \<subseteq> \<O>' (v)" and "a \<in> (A \<rightarrow> carrier real_ring)" and 
"module_real4.lincomb a A = real4_zero" and "u \<in> A" and "a u \<noteq> 0" and "e\<^sub>1'(v) \<in> A \<or> e\<^sub>2'(v) \<in> A"
and "v \<noteq> 1" and "v \<noteq> -1" and "v \<noteq> 0"
  shows "module_real4.lin_dep \<O>"
proof-
  define B where d1:"B \<equiv> (A - {e\<^sub>1'(v), e\<^sub>2'(v)}) \<union> {e \<^sub>1, e \<^sub>2}"
  then have "B \<subseteq> \<O>"
    using assms(2) vec_basis'_def vec_basis_set_def vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis
    by (smt Diff_insert2 Diff_subset_conv Un_commute Un_empty_right Un_mono insert_def subset_refl)
  have f0:"finite B"
    using d1 assms(1)
    by simp
  have f1:"module_real4.lin_dep \<O>" if h1:"e\<^sub>1'(v) \<in> A \<and> e\<^sub>2'(v) \<notin> A"
  proof-
    define b where d2:"b \<equiv> \<lambda>w. if w = e \<^sub>1 then a (vec_basis1' v) * \<gamma> (v) else 
  if w = e \<^sub>2 then a (vec_basis1' v) * v * \<gamma> (v) else
    if w = e \<^sub>3 then a e\<^sub>3'(v) else
      if w = e \<^sub>4 then  a e\<^sub>4'(v) else undefined"
    then have "b \<in> (B \<rightarrow> carrier real_ring)"
      by (simp add: real_ring_def)
    have "module_real4.lincomb a A = module_real4.lincomb b B"
    proof-
      have "module_real4.lincomb a A = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using module_real4.lincomb_def 
        by auto
      then have "module_real4.lincomb a A = 
        a (e\<^sub>1'(v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>1'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using h1
        by (metis (no_types, lifting) Diff_insert_absorb assms(1) finite_Diff finsum_insert mk_disjoint_insert)
      then have "module_real4.lincomb a A = a (e\<^sub>1'(v)) \<odot>\<^bsub>real4_module\<^esub> (\<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) 
+ v * \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2)) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>1'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using vec_basis1'_to_vec_basis 
        by simp
      then have "module_real4.lincomb a A = (a (e\<^sub>1'(v)) * \<gamma> v) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + 
(a (e\<^sub>1'(v)) * v * \<gamma> v) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>1'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using real4_smult_left_distr
        by (simp add: semiring_normalization_rules(18))
      then have f11:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>1'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using d2 vec_basis_noteq_2(1) 
        by auto
      have "A - {e\<^sub>1'(v)} = A - {e\<^sub>1'(v), e\<^sub>2'(v)}"
        using h1
        by blast
      then have f12:"A - {e\<^sub>1'(v)} = B - {e \<^sub>1, e \<^sub>2}"
        using d1 Diff_insert2 assms(2) vec_basis'_def vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis 
vec_basis_noteq_1(2) vec_basis_noteq_1(3) vec_basis_noteq_2(2) vec_basis_noteq_2(3) 
        by auto
      then have f13:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using f11
        by simp
      have "\<forall>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v = b v"
        using h1 d2 vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis f12 assms(2) vec_basis'_def
        by (smt DiffD2 insertE insertI1 insertI2 insert_Diff insert_subset)
      then have "\<forall>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v = b v \<odot>\<^bsub>real4_module\<^esub> v"
        by simp
      then have "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v) = 
(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using Tensor_Analysis.module_real4.finsum_cong'[of "B-{e \<^sub>1, e \<^sub>2}" "B-{e \<^sub>1, e \<^sub>2}" "\<lambda>v. b v \<odot>\<^bsub>real4_module\<^esub> v"] 
real4_module_def
        by (metis (no_types, lifting) Pi_I' UNIV_I partial_object.select_convs(1))
      then have f14:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using f13 
        by simp
      have "insert e \<^sub>2 (insert e \<^sub>1 (B-{e \<^sub>1, e \<^sub>2})) = B"
        using d1 vec_basis_noteq_1(1)
        by blast
      then have "module_real4.lincomb a A = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using finsum_insert f0 f14
        by (smt Diff_iff finite_insert insert_commute insert_iff is_num_normalize(1) vec_basis_noteq_2(1))
      thus "module_real4.lincomb a A = module_real4.lincomb b B"
        by (simp add: module_real4.lincomb_def)
    qed
    thus "module_real4.lin_dep \<O>"
    proof-
      have "module_real4.lin_dep \<O>" if h11:"u = e\<^sub>3'(v) \<or> u = e\<^sub>4'(v)"
      proof-
        have f15:"u = e \<^sub>3 \<or> u = e \<^sub>4"
          using h11 vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis
          by simp
        then have f16:"u \<in> B"
          using h1 d1 assms(5) \<open>B \<subseteq> \<O>\<close> vec_basis_set_def assms(2) vec_basis'_def
          by (smt Diff_insert2 Diff_insert_absorb UnCI assms(1) assms(3) assms(4) assms(6) 
insert_Diff insert_absorb2 insert_iff lincomb_vec_basis subsetCE subsetI vec_basis3'_to_vec_basis 
vec_basis4'_to_vec_basis)
        moreover have "b u = a u"
          using d2 f15 vec_basis3'_def vec_basis4'_to_vec_basis vec_basis_def vec_basis_noteq_1(2) 
vec_basis_noteq_1(3) vec_basis_noteq_2(2) vec_basis_noteq_2(3) 
          by auto
        thus ?thesis
          using module_real4.lin_dep_def f0 \<open>B \<subseteq> \<O>\<close> \<open>b \<in> (B \<rightarrow> carrier real_ring)\<close> f16
          by (smt \<open>module_real4.lincomb a A = module_real4.lincomb b B\<close> assms(4) assms(6) lincomb_vec_basis)
      qed
      have "module_real4.lin_dep \<O>" if h12:"u = e\<^sub>1'(v)"
      proof-
        have "a (e\<^sub>1'(v)) * \<gamma> (v) \<noteq> 0"
          using assms(8) assms(9) Lorentz_factor_not_zero h12 assms(6)
          by simp
        hence "b e \<^sub>1 \<noteq> 0"
          using d2
          by simp
        thus ?thesis
          using module_real4.lin_dep_def f0 \<open>B \<subseteq> \<O>\<close> \<open>b \<in> (B \<rightarrow> carrier real_ring)\<close>
          by (smt Un_insert_right \<open>module_real4.lincomb a A = module_real4.lincomb b B\<close> assms(4) d1 
insertCI lincomb_vec_basis)
      qed
      thus ?thesis
        using assms(5) h1 assms(2) vec_basis'_def \<open>u = e\<^sub>3' v \<or> u = e\<^sub>4' v \<Longrightarrow> module_real4.lin_dep \<O>\<close> 
        by blast
    qed
  qed
  have f2:"module_real4.lin_dep \<O>" if h2:"e\<^sub>1'(v) \<notin> A \<and> e\<^sub>2'(v) \<in> A"
  proof-
    define b where d2:"b \<equiv> \<lambda>w. if w = e \<^sub>2 then a (vec_basis2' v) * \<gamma> (v) else 
  if w = e \<^sub>1 then a (vec_basis2' v) * v * \<gamma> (v) else
    if w = e \<^sub>3 then a e\<^sub>3'(v) else
      if w = e \<^sub>4 then  a e\<^sub>4'(v) else undefined"
    then have "b \<in> (B \<rightarrow> carrier real_ring)"
      by (simp add: real_ring_def)
    have "module_real4.lincomb a A = module_real4.lincomb b B"
    proof-
      have "module_real4.lincomb a A = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using module_real4.lincomb_def 
        by auto
      then have "module_real4.lincomb a A = 
        a (e\<^sub>2'(v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>2'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using h2
        by (metis (no_types, lifting) Diff_insert_absorb assms(1) finite_Diff finsum_insert mk_disjoint_insert)
      then have "module_real4.lincomb a A = a (e\<^sub>2'(v)) \<odot>\<^bsub>real4_module\<^esub> (v * \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) 
+ \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2)) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>2'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using vec_basis2'_to_vec_basis 
        by simp
      then have "module_real4.lincomb a A = (a (e\<^sub>2'(v)) * v * \<gamma> v) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + 
(a (e\<^sub>2'(v)) * \<gamma> v) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>2'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using real4_smult_left_distr
        by (simp add: semiring_normalization_rules(18))
      then have f21:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>2'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using d2 vec_basis_noteq_2(1)
        by auto
      have "A - {e\<^sub>2'(v)} = A - {e\<^sub>1'(v), e\<^sub>2'(v)}"
        using h2
        by blast
      then have f22:"A - {e\<^sub>2'(v)} = B - {e \<^sub>1, e \<^sub>2}"
        using d1 Diff_insert2 assms(2) vec_basis'_def vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis 
vec_basis_noteq_1(2) vec_basis_noteq_1(3) vec_basis_noteq_2(2) vec_basis_noteq_2(3) 
        by auto
      then have f23:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using f21
        by simp
      have "\<forall>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v = b v"
        using h2 d2 vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis f22 assms(2) vec_basis'_def
        by (smt DiffD2 insertE insertI1 insertI2 insert_Diff insert_subset)
      then have "\<forall>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v = b v \<odot>\<^bsub>real4_module\<^esub> v"
        by simp
      then have "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v) = 
(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using Tensor_Analysis.module_real4.finsum_cong'[of "B-{e \<^sub>1, e \<^sub>2}" "B-{e \<^sub>1, e \<^sub>2}" "\<lambda>v. b v \<odot>\<^bsub>real4_module\<^esub> v"] 
real4_module_def
        by (metis (no_types, lifting) Pi_I' UNIV_I partial_object.select_convs(1))
      then have f24:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using f23 
        by simp
      have "insert e \<^sub>1 (insert e \<^sub>2 (B-{e \<^sub>1, e \<^sub>2})) = B"
        using d1 vec_basis_noteq_1(1)
        by blast
      then have "module_real4.lincomb a A = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using finsum_insert f0 f24
        by (smt Diff_iff finite_insert insert_commute insert_iff is_num_normalize(1) vec_basis_noteq_2(1))
      thus "module_real4.lincomb a A = module_real4.lincomb b B"
        by (simp add: module_real4.lincomb_def)
    qed
    thus "module_real4.lin_dep \<O>"
    proof-
      have "module_real4.lin_dep \<O>" if h21:"u = e\<^sub>3'(v) \<or> u = e\<^sub>4'(v)"
      proof-
        have f25:"u = e \<^sub>3 \<or> u = e \<^sub>4"
          using h21 vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis
          by simp
        then have f26:"u \<in> B"
          using h2 d1 assms(5) \<open>B \<subseteq> \<O>\<close> vec_basis_set_def assms(2) vec_basis'_def
          by (smt Diff_insert2 Diff_insert_absorb UnCI assms(1) assms(3) assms(4) assms(6) 
insert_Diff insert_absorb2 insert_iff lincomb_vec_basis subsetCE subsetI vec_basis3'_to_vec_basis 
vec_basis4'_to_vec_basis)
        moreover have "b u = a u"
          using d2 f25 vec_basis3'_def vec_basis4'_to_vec_basis vec_basis_def vec_basis_noteq_1(2) 
vec_basis_noteq_1(3) vec_basis_noteq_2(2) vec_basis_noteq_2(3) 
          by auto
        thus ?thesis
          using module_real4.lin_dep_def f0 \<open>B \<subseteq> \<O>\<close> \<open>b \<in> (B \<rightarrow> carrier real_ring)\<close> f26
          by (smt \<open>module_real4.lincomb a A = module_real4.lincomb b B\<close> assms(4) assms(6) lincomb_vec_basis)
      qed
      have "module_real4.lin_dep \<O>" if h22:"u = e\<^sub>2'(v)"
      proof-
        have "a (e\<^sub>2'(v)) * \<gamma> (v) \<noteq> 0"
          using assms(8) assms(9) Lorentz_factor_not_zero h22 assms(6)
          by simp
        hence "b e \<^sub>2 \<noteq> 0"
          using d2
          by simp
        thus ?thesis
          using module_real4.lin_dep_def f0 \<open>B \<subseteq> \<O>\<close> \<open>b \<in> (B \<rightarrow> carrier real_ring)\<close>
          by (smt Un_insert_right \<open>module_real4.lincomb a A = module_real4.lincomb b B\<close> assms(4) d1 
insertCI lincomb_vec_basis)
      qed
      thus ?thesis
        using assms(5) h2 assms(2) vec_basis'_def \<open>u = e\<^sub>3' v \<or> u = e\<^sub>4' v \<Longrightarrow> module_real4.lin_dep \<O>\<close>
        by auto 
    qed
  qed
  have "module_real4.lin_dep \<O>" if h3:"e\<^sub>1'(v) \<in> A \<and> e\<^sub>2'(v) \<in> A"
  proof-
    define b where d2:"b \<equiv> \<lambda>w. if w = e \<^sub>1 then (a (vec_basis1' v) * \<gamma> (v)) + a (e\<^sub>2'(v)) * v * \<gamma> (v) else 
  if w = e \<^sub>2 then (a (e\<^sub>1' v) * v * \<gamma> v) + (a e\<^sub>2'(v)) * \<gamma> (v) else
    if w = e \<^sub>3 then a e\<^sub>3'(v) else
      if w = e \<^sub>4 then  a e\<^sub>4'(v) else undefined"
    then have "b \<in> (B \<rightarrow> carrier real_ring)"
      by (simp add: real_ring_def)
    have "module_real4.lincomb a A = module_real4.lincomb b B"
    proof-
      have "module_real4.lincomb a A = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using module_real4.lincomb_def 
        by auto
      then have "module_real4.lincomb a A = 
        a (e\<^sub>1'(v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) + a (e\<^sub>2'(v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>1'(v), e\<^sub>2'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using h3
        by (smt Diff_insert Diff_subset Lorentz_factor_not_zero assms(1) assms(8) assms(9) finite_Diff 
finsum_insert insert_Diff insert_Diff_if is_num_normalize(1) mult_cancel_right1 singletonD 
subset_Diff_insert vec_basis1'_def vec_basis2'_def vector_comp(1))
      then have "module_real4.lincomb a A = a (e\<^sub>1'(v)) \<odot>\<^bsub>real4_module\<^esub> (\<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) 
+ v * \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2)) + a (e\<^sub>2'(v)) \<odot>\<^bsub>real4_module\<^esub> (v * \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) 
+ \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2)) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>1'(v), e\<^sub>2'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using vec_basis1'_to_vec_basis vec_basis2'_to_vec_basis 
        by simp
      then have "module_real4.lincomb a A = ((a (e\<^sub>1'(v)) * \<gamma> v) + a (e\<^sub>2'(v)) * v * \<gamma> v) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + 
((a (e\<^sub>1'(v)) * v * \<gamma> v) + a (e\<^sub>2'(v)) * \<gamma> v) \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>1'(v), e\<^sub>2'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using real4_smult_left_distr_bis
        by (simp add: semiring_normalization_rules(18))
      then have f31:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e\<^sub>1'(v), e\<^sub>2'(v)}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using d2 vec_basis_noteq_2(1)
        by auto
      have f32:"A - {e\<^sub>1'(v), e\<^sub>2'(v)} = B - {e \<^sub>1, e \<^sub>2}"
        using d1 Diff_insert2 assms(2) vec_basis'_def vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis 
vec_basis_noteq_1(2) vec_basis_noteq_1(3) vec_basis_noteq_2(2) vec_basis_noteq_2(3) 
        by auto
      then have f33:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using f31
        by simp
      have "\<forall>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v = b v"
        using h3 d2 vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis f32 assms(2) vec_basis'_def
        by (smt DiffD1 DiffD2 insertE insertI1 insert_commute subsetCE)
      then have "\<forall>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v = b v \<odot>\<^bsub>real4_module\<^esub> v"
        by simp
      then have "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v) = 
(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using Tensor_Analysis.module_real4.finsum_cong'[of "B-{e \<^sub>1, e \<^sub>2}" "B-{e \<^sub>1, e \<^sub>2}" "\<lambda>v. b v \<odot>\<^bsub>real4_module\<^esub> v"] 
real4_module_def
        by (metis (no_types, lifting) Pi_I' UNIV_I partial_object.select_convs(1))
      then have f34:"module_real4.lincomb a A = b e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>1) + b e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (e \<^sub>2) 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B-{e \<^sub>1, e \<^sub>2}. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using f33 
        by simp
      have "insert e \<^sub>1 (insert e \<^sub>2 (B-{e \<^sub>1, e \<^sub>2})) = B"
        using d1 vec_basis_noteq_1(1)
        by blast
      then have "module_real4.lincomb a A = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>B. b v \<odot>\<^bsub>real4_module\<^esub> v)"
        using finsum_insert f0 f34
        by (smt Diff_iff finite_insert insert_commute insert_iff is_num_normalize(1) vec_basis_noteq_2(1))
      thus "module_real4.lincomb a A = module_real4.lincomb b B"
        by (simp add: module_real4.lincomb_def)
    qed
    thus "module_real4.lin_dep \<O>"
    proof-
      have "module_real4.lin_dep \<O>" if h31:"u = e\<^sub>3'(v) \<or> u = e\<^sub>4'(v)"
      proof-
        have f35:"u = e \<^sub>3 \<or> u = e \<^sub>4"
          using h31 vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis
          by simp
        then have f36:"u \<in> B"
          using h3 d1 assms(5) \<open>B \<subseteq> \<O>\<close> vec_basis_set_def assms(2) vec_basis'_def vec_basis1'_neq_vec_basis34
vec_basis2'_neq_vec_basis34
          by fastforce
        moreover have "b u = a u"
          using d2 f35 vec_basis3'_def vec_basis4'_to_vec_basis vec_basis_def vec_basis_noteq_1(2) 
vec_basis_noteq_1(3) vec_basis_noteq_2(2) vec_basis_noteq_2(3) 
          by auto
        thus ?thesis
          using module_real4.lin_dep_def f0 \<open>B \<subseteq> \<O>\<close> \<open>b \<in> (B \<rightarrow> carrier real_ring)\<close> f36
          by (smt \<open>module_real4.lincomb a A = module_real4.lincomb b B\<close> assms(4) assms(6) lincomb_vec_basis)
      qed
      have "module_real4.lin_dep \<O>" if h32:"u = e\<^sub>2'(v) \<or> u = e\<^sub>1'(v)"
      proof-
        have f38:"b e \<^sub>1 \<noteq> 0" if "a (e\<^sub>1'(v)) * \<gamma> v \<noteq> - a (e\<^sub>2'(v)) * v * \<gamma> v"
          using that d2
          by simp
        then have "module_real4.lin_dep \<O>" if "a (e\<^sub>1'(v)) * \<gamma> v \<noteq> - a (e\<^sub>2'(v)) * v * \<gamma> v"
          using that module_real4.lin_dep_def[of "\<O>"] f0 d1 \<open>B \<subseteq> \<O>\<close> \<open>b \<in> (B \<rightarrow> carrier real_ring)\<close> 
f38 \<open>module_real4.lincomb a A = module_real4.lincomb b B\<close> assms(4)
          by (smt Un_insert_right insertCI lincomb_vec_basis)
        have "module_real4.lin_dep \<O>" if "a (e\<^sub>1'(v)) * \<gamma> v = - a (e\<^sub>2'(v)) * v * \<gamma> v"
        proof-
          have "(a (e\<^sub>1' v) * v * \<gamma> v)= - a (e\<^sub>2' v) * v\<^sup>2 * \<gamma> v"
            using that
            by (metis mult.commute power2_eq_square semiring_normalization_rules(18))
          then have "b e \<^sub>2 = (- a (e\<^sub>2' v) * v\<^sup>2 * \<gamma> v) + (a e\<^sub>2'(v)) * \<gamma> (v)"
            using d2 vec_basis_noteq_1(1) 
            by metis
          then have "b e \<^sub>2 = (a (e\<^sub>2' v) * \<gamma> v) * (-v\<^sup>2) + (a e\<^sub>2'(v)) * \<gamma> (v)"
            using mult_minus_right 
            by (metis mult.commute mult.left_commute)
          then have "b e \<^sub>2 = a (e\<^sub>2'(v)) * (\<gamma> v) * (1 - v\<^sup>2)"
            by (simp add: vector_space_over_itself.scale_right_diff_distrib)
          then have "b e \<^sub>2 \<noteq> 0"
            using assms(6) h32 assms(8) assms(9) assms(10) Lorentz_factor_not_zero mult_eq_0_iff
            by (metis add.inverse_neutral divide_eq_0_iff lorentz_factor_def minus_mult_commute 
mult_minus_right mult_zero_left real_sqrt_eq_zero_cancel_iff that) 
          thus ?thesis
            using that module_real4.lin_dep_def[of "\<O>"] f0 d1 \<open>B \<subseteq> \<O>\<close> \<open>b \<in> (B \<rightarrow> carrier real_ring)\<close> 
\<open>module_real4.lincomb a A = module_real4.lincomb b B\<close> assms(4)
            by (smt Un_commute Un_insert_left insertI1 lincomb_vec_basis)
        qed
        thus ?thesis
          using \<open>a (e\<^sub>1'(v)) * \<gamma> v \<noteq> - a (e\<^sub>2'(v)) * v * \<gamma> v \<Longrightarrow> module_real4.lin_dep \<O>\<close> 
          by auto
      qed
      thus ?thesis
        using assms(5) h3 assms(2) vec_basis'_def \<open>u = e\<^sub>3' v \<or> u = e\<^sub>4' v \<Longrightarrow> module_real4.lin_dep \<O>\<close>
\<open>u = e\<^sub>2'(v) \<or> u = e\<^sub>1'(v) \<Longrightarrow> module_real4.lin_dep \<O>\<close>
        by auto 
    qed
  qed
  thus ?thesis
    using f1 f2 assms(7)
    by blast
qed

lemma lincomb_vec_basis'_to_lin_dep_vec_basis:
  fixes v::"real"
  assumes "finite A" and "A \<subseteq> \<O>' (v)" and "a \<in> (A \<rightarrow> carrier real_ring)" and 
"module_real4.lincomb a A = real4_zero" and "u \<in> A" and "a u \<noteq> 0" and "v \<noteq> 1" and "v \<noteq> -1" and "v \<noteq> 0"
  shows "module_real4.lin_dep \<O>"
    using assms lincomb_vec_basis'_to_lin_dep_vec_basis_1 lincomb_vec_basis'_to_lin_dep_vec_basis_2
    by metis

lemma lin_indpt_vec_basis' :
  fixes v::"real"
  assumes "v \<noteq> 1" and "v \<noteq> -1" and "v \<noteq> 0"
  shows "module_real4.lin_indpt \<O>' (v)"
proof
  assume h1:"module_real4.lin_dep \<O>' (v)"
  then obtain A a u where a1:"finite A" and a2:"A \<subseteq> \<O>' (v)" and a3:"a \<in> (A \<rightarrow> carrier real_ring)" and 
    a4:"module_real4.lincomb a A = real4_zero" and a5:"u \<in> A" and a6:"a u \<noteq> 0"
    using module_real4.lin_dep_def real4_module_def
    by (metis partial_object.select_convs(1) real_ring_def ring_record_simps(11))
  then have "module_real4.lin_dep \<O>"
    using assms a1 a2 a3 a4 a5 a6 lincomb_vec_basis'_to_lin_dep_vec_basis 
    by simp
  thus "False"
    using lin_indpt_vec_basis 
    by blast
qed

lemma vec_basis'_in_univ :
  fixes v::"real"
  shows "\<O>' v \<subseteq> carrier real4_module"
  using vec_basis'_def
  by (simp add: real4_module_def)

lemma vec_basis1_to_vec_basis':
  fixes v::"real"
  shows "e \<^sub>1 = sqrt(1 - v/ 1 + v) \<odot>\<^bsub>real4_module\<^esub> (e\<^sub>1'(v) - v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v))" sorry
  (*apply (auto simp: vec_eq_iff)*)

lemma vec_basis2_to_vec_basis':
  fixes v::"real"
  shows "e \<^sub>2 = \<gamma> v \<odot>\<^bsub>real4_module\<^esub> (v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) - e\<^sub>2'(v))" sorry

lemma span_vec_basis_subset_span_vec_basis':
  fixes v::"real"
  assumes "v \<noteq> -1" and "v \<noteq>1"
  shows "module_real4.span \<O> \<subseteq> module_real4.span \<O>'(v)"
  apply (auto simp: module_real4.span_def real4_module_def)
proof-
  fix x::"real^4"
  assume "x \<in> module_real4.span \<O>"
  then have "\<exists>a A. (A \<subseteq> \<O> \<and> (a \<in> A\<rightarrow>carrier real_ring) \<and> (module_real4.lincomb a A = x))"
    using module_real4.in_span[of "\<O>" "real4_module" "x"]
    by (simp add: real_ring_def vec_basis_in_univ)
  then obtain A a where a1:"A \<subseteq> \<O>" and a2:"a \<in> A\<rightarrow>carrier real_ring" and a3:"module_real4.lincomb a A = x"
    by auto
  then have f1:"finite A"
    using a1
    by (simp add: vec_basis_set_def finite_subset)
  define B where d1:"B \<equiv> (A - {e \<^sub>1, e \<^sub>2}) \<union> {e\<^sub>1'(v), e\<^sub>2'(v)}"
  then have "B \<subseteq> \<O>'(v)"
    using a1 vec_basis_set_def vec_basis'_def vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis 
    by fastforce
  then have "x \<in> module_real4.span \<O>'(v)" if h1:"e \<^sub>1 \<in> A \<and> e \<^sub>2 \<in> A"
  proof-
    define b where d21:"b \<equiv> \<lambda>u. if u = e\<^sub>3'(v) then a (e \<^sub>3) else 
  if u = e\<^sub>4'(v) then a (e \<^sub>4) else
    if u = e\<^sub>1'(v) then (a (e \<^sub>1) * sqrt(1 - v/ 1 + v)) + a (e \<^sub>2) * (\<gamma> v) * v else
      if  u = e\<^sub>2'(v) then (a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * (-v)) + a (e \<^sub>2) * (-\<gamma> v) else undefined"
    then have "b \<in> B \<rightarrow> carrier real_ring"
      using d1 a2
      by (simp add: real_ring_def)
    then have "module_real4.lincomb b B = x"
    proof-
      have "module_real4.lincomb a A = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using module_real4.lincomb_def
        by simp
      then have "module_real4.lincomb a A =  a e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> e \<^sub>1 + a e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> e \<^sub>2 
+ (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using h1 finsum_def real4_module_def finsum_insert f1
        by (smt Diff_insert2 Diff_insert_absorb finite_Diff insertE is_num_normalize(1) 
mk_disjoint_insert vec_basis_noteq_2(1))
      then have f11:"module_real4.lincomb a A = 
a e \<^sub>1 \<odot>\<^bsub>real4_module\<^esub> (sqrt(1 - v/ 1 + v) \<odot>\<^bsub>real4_module\<^esub> (e\<^sub>1'(v) - v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v))) +
a e \<^sub>2 \<odot>\<^bsub>real4_module\<^esub> (\<gamma> v \<odot>\<^bsub>real4_module\<^esub> ((v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v)) - e\<^sub>2'(v))) + 
(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using vec_basis1_to_vec_basis' vec_basis2_to_vec_basis' 
        by simp
      have f12:"(a e \<^sub>1) \<odot>\<^bsub>real4_module\<^esub> (sqrt(1 - v/ 1 + v) \<odot>\<^bsub>real4_module\<^esub> (e\<^sub>1'(v) - v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v))) +
(a e \<^sub>2) \<odot>\<^bsub>real4_module\<^esub> (\<gamma> v \<odot>\<^bsub>real4_module\<^esub> ((v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v)) - e\<^sub>2'(v))) = 
(a e \<^sub>1) \<odot>\<^bsub>real4_module\<^esub> (sqrt(1 - v/ 1 + v) \<odot>\<^bsub>real4_module\<^esub> (1 \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) - v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v))) +
(a e \<^sub>2) \<odot>\<^bsub>real4_module\<^esub> (\<gamma> v \<odot>\<^bsub>real4_module\<^esub> ((v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v)) + -1 \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v)))"
        using real4_smult_one real4_smult_minus_bis
        by (metis add.inverse_inverse diff_minus_eq_add)
      have "(a e \<^sub>1) \<odot>\<^bsub>real4_module\<^esub> (sqrt(1 - v/ 1 + v) \<odot>\<^bsub>real4_module\<^esub> (1 \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) - v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v))) +
(a e \<^sub>2) \<odot>\<^bsub>real4_module\<^esub> ((\<gamma> v) \<odot>\<^bsub>real4_module\<^esub> ((v \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v)) + -1 \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v))) = 
(a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * 1 + a (e \<^sub>2) * (\<gamma> v) * v) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) -  
(a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * v + a (e \<^sub>2) * (\<gamma> v) * 1) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v)"
        using real4_smult_left_distr_ter_minus
        by (metis (no_types, hide_lams) f12 mult.commute real4_smult_one real4_smult_smult)
      then have "module_real4.lincomb a A =
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * 1) + a (e \<^sub>2) * (\<gamma> v) * v) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) -  
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * v) + a (e \<^sub>2) * (\<gamma> v) * 1) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v) + 
(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
        using f11 f12 add_diff_eq diff_add_eq real4_smult_one real4_smult_smult semiring_normalization_rules(23) 
semiring_normalization_rules(25) 
        by simp
      then have f13:"module_real4.lincomb a A =
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v)) + a (e \<^sub>2) * (\<gamma> v) * v) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) -  
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * v) + a (e \<^sub>2) * (\<gamma> v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v) + 
(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)" 
        by simp
      then have f14:"module_real4.lincomb a A =
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v)) + a (e \<^sub>2) * (\<gamma> v) * v) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) +  
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * (-v)) + a (e \<^sub>2) * (-\<gamma> v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v) + 
(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
      proof-
        have "-(a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * v + a (e \<^sub>2) * (\<gamma> v)) = 
  (a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * (-v)) + a (e \<^sub>2) * (-\<gamma> v)"
          using minus_add Rings.ring_class.minus_mult_right
          by simp
        then have "((a (e \<^sub>1) * sqrt(1 - v/ 1 + v)) + a (e \<^sub>2) * (\<gamma> v) * v) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) -  
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * v) + a (e \<^sub>2) * (\<gamma> v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v) = 
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v)) + a (e \<^sub>2) * (\<gamma> v) * v) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) +  
((a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * (-v)) + a (e \<^sub>2) * (-\<gamma> v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v)"
          apply (auto simp: real4_minus_smult real4_minus).
        thus ?thesis
          using f13 
          by simp
      qed
      then have f15:"module_real4.lincomb a A = b (e\<^sub>1'(v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>1'(v) + 
b (e\<^sub>2'(v)) \<odot>\<^bsub>real4_module\<^esub> e\<^sub>2'(v) + (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>A-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v)"
      proof-
        have "b (e\<^sub>1'(v)) = (a (e \<^sub>1) * sqrt(1 - v/ 1 + v)) + a (e \<^sub>2) * (\<gamma> v) * v"
          using d21
          by (simp add: vec_basis1'_neq_vec_basis34 vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis)
        have "b (e\<^sub>2'(v)) = (a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * (-v)) + a (e \<^sub>2) * (-\<gamma> v)"
          using d21 assms vec_basis2'_neq_vec_basis1'
          by (simp add: vec_basis2'_neq_vec_basis34(1) vec_basis2'_neq_vec_basis34(2) 
vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis)
        thus ?thesis 
          using f14 \<open>b (e\<^sub>1'(v)) = (a (e \<^sub>1) * sqrt (1 - v / 1 + v) + a (e \<^sub>2) * (\<gamma> v) * v)\<close> 
          by simp
      qed
      moreover have "\<forall>v\<in>A-{e \<^sub>1, e \<^sub>2}. a v = b v"
        using d21 a1 vec_basis_set_def h1 vec_basis3'_to_vec_basis vec_basis4'_to_vec_basis
        by (smt DiffE insert_iff subsetCE)
      then have "\<forall>v\<in>A-{e \<^sub>1, e \<^sub>2}. a v \<odot>\<^bsub>real4_module\<^esub> v = b v \<odot>\<^bsub>real4_module\<^esub> v"
        by simp
      thus ?thesis
        using f15 a3
        by (metis (mono_tags, hide_lams) ab_group_add_class.ab_diff_conv_add_uminus add.left_neutral 
assms(1) diff_add_cancel div_by_1 mult.left_neutral mult_zero_left real4_smult_one real_sqrt_one 
vec_basis1'_def vec_basis1_to_vec_basis' vec_basis2'_def vec_basis_def vector_comp(1) zero_index)
    qed
then have "x \<in> module_real4.span \<O>'(v)" if "e \<^sub>1 \<in> A \<and> e \<^sub>2 \<notin> A" sorry
(*
proof-
define b where "b \<equiv> \<lambda>u. if u = e\<^sub>3'(v) then a (e \<^sub>3) else 
    if u = e\<^sub>4'(v) then a (e \<^sub>4) else
    if u = e\<^sub>1'(v) then  a (e \<^sub>1) * sqrt(1 - v/ 1 + v) else
    if  u = e\<^sub>2'(v) then a (e \<^sub>1) * sqrt(1 - v/ 1 + v) * (-v) else undefined
qed
*)
  then have "x \<in> module_real4.span \<O>'(v)" if "e \<^sub>1 \<notin> A \<and> e \<^sub>2 \<in> A" sorry
(*
proof-
  define b where "b \<equiv> \<lambda>u. if u = e\<^sub>3'(v) then a (e \<^sub>3) else 
    if u = e\<^sub>4'(v) then a (e \<^sub>4) else
    if u = e\<^sub>1'(v) then  a (e \<^sub>2) * \<gamma> v * v else
if  u = e\<^sub>2'(v) then a (e \<^sub>2) * (-\<gamma> v) else undefined
qed
*)
then have "x \<in> module_real4.span \<O>'(v)" if "e \<^sub>1 \<notin> A \<and> e \<^sub>2 \<notin> A" sorry
(*
proof-
define b where "b \<equiv> \<lambda>u. if u = e\<^sub>3'(v) then a (e \<^sub>3) else 
    if u = e\<^sub>4'(v) then a (e \<^sub>4) else
  if u = e\<^sub>1'(v) \<or> u = e\<^sub>1'(v) then 0 else undefined
qed
*)

lemma gen_set_vec_basis':
  fixes v::"real"
  shows "module_real4.gen_set \<O>' v"
  apply (auto simp: module_real4.span_def real4_module_def)
  using gen_set_vec_basis span_vec_basis_subset_span_vec_basis'
  by (simp add: real4_module_def subset_eq)

lemma basis_vec_basis' :
  fixes v :: real
  assumes "v \<noteq> 0" and "v \<noteq> 1" and "v \<noteq> -1"
  shows "vecspace_real4.basis \<O>'(v)"
  using assms gen_set_vec_basis' vec_basis'_in_univ lin_indpt_vec_basis'
  by (simp add: vecspace_real4.basis_def)

text 
\<open>
We define the components of a one_form on a given basis as the real numbers obtained from
the application of the one_form to the basis vectors.
\<close>

definition one_form_nth :: "one_form \<Rightarrow> nat \<Rightarrow> real" ("_ \<section> _") where
"one_form_nth f n \<equiv> if n=1 then f(e \<^sub>1) else
  if n=2 then f(e \<^sub>2) else
  if n=3 then f(e \<^sub>3) else
  if n=4 then f(e \<^sub>4) else undefined"

definition one_form_nth' :: "one_form \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" (" _ \<section> _ _") where
"one_form_nth' f v n \<equiv> if n=1 then f(e\<^sub>1'(v)) else
  if n=2 then f(e\<^sub>2'(v)) else
  if n=3 then f(e\<^sub>3'(v)) else
  if n=4 then f(e\<^sub>4'(v)) else undefined"

text \<open>The components of one_forms transform in the same manner as those of basis vectors and
in the opposite manner to components of vectors.\<close>

lemma comp_one_form_transform :
  fixes v::"real" and f::"one_form"
  shows "f \<section> v 1 = (\<gamma> v) * (f \<section> 1) + (v * \<gamma> v) * (f \<section> 2)" and 
    "f \<section> v 2 = (v * \<gamma> v) * (f \<section> 1) + (\<gamma> v) * (f \<section> 2)" and 
    "f \<section> v 3 = f \<section> 3" and 
    "f \<section> v 4 = f \<section> 4" sorry

text 
\<open>
In the same way a vector is kept frame independent (but not its components which depend on the 
chosen basis), one has the following frame independent quantity for any vector and any one-form.
\<close>

lemma lorentz_factor_sqrt :
  fixes v::"real"
  assumes "v\<^sup>2 < 1"
  shows "(\<gamma> v)\<^sup>2 * (1 - v\<^sup>2) = 1"
proof-
  have f1:"(\<gamma> v)\<^sup>2 * (1 - v\<^sup>2) = (1/sqrt(1 - v\<^sup>2))\<^sup>2 * (1 - v\<^sup>2)"
    using lorentz_factor_def
    by simp
  have f2:"1 - v\<^sup>2 > 0"
    using assms
    by simp
  from f1 and f2 have "(\<gamma> v)\<^sup>2 * (1 - v\<^sup>2) = 1/(1 - v\<^sup>2) * (1 - v\<^sup>2)"
    using real_sqrt_pow2
    by (simp add: power_one_over)
  thus ?thesis
    using f2
    by simp
qed

lemma frame_ind_qty1 :
  fixes v::"real" and x::"real^4" and f::"one_form"
  assumes "v\<^sup>2 < 1"
  shows "(x $ v 1) * (f \<section> v 1) + (x $ v 2) * (f \<section> v 2) + (x $ v 3) * (f \<section> v 3) + (x $ v 4) * (f \<section> v 4) 
  = (x $ 1) * (f \<section> 1) + (x $ 2) * (f \<section> 2) + (x $ 3) * (f \<section> 3) + (x $ 4) * (f \<section> 4)"
proof-
  define q where  "q \<equiv> (x $ v 1) * (f \<section> v 1) + (x $ v 2) * (f \<section> v 2) + (x $ v 3) * (f \<section> v 3) + (x $ v 4) * (f \<section> v 4)"
  have "q = ((\<gamma> v) * (x $ 1) + (- v * \<gamma> v) * (x $ 2)) * ((\<gamma> v) * (f \<section> 1) + (v * \<gamma> v) * (f \<section> 2)) + 
  ((- v * \<gamma> v) * (x $ 1) + (\<gamma> v) * (x $ 2)) * ((v * \<gamma> v) * (f \<section> 1) + (\<gamma> v) * (f \<section> 2)) + 
  (x $ 3) * (f \<section> 3) + 
  (x $ 4) * (f \<section> 4)" sorry
  then have "q = (((\<gamma> v) * (x $ 1)) * (\<gamma> v) + ((- v * \<gamma> v) * (x $ 2)) * (\<gamma> v) + ((- v * \<gamma> v) * (x $ 1)) * (v * \<gamma> v) + ((\<gamma> v) * (x $ 2)) * (v * \<gamma> v)) * (f \<section> 1) + 
  (((\<gamma> v) * (x $ 1)) * (v * \<gamma> v) + ((- v * \<gamma> v) * (x $ 2)) * (v * \<gamma> v) + ((- v * \<gamma> v) * (x $ 1)) * (\<gamma> v) + ((\<gamma> v) * (x $ 2)) * \<gamma> v) * (f \<section> 2) + 
  (x $ 3) * (f \<section> 3) + 
  (x $ 4) * (f \<section> 4)" sorry
  then have "q = (((\<gamma> v)\<^sup>2 * (x $ 1)) * (1 - v\<^sup>2)) * (f \<section> 1) + 
  (((\<gamma> v)\<^sup>2 * (x $ 2)) * (1 - v\<^sup>2)) * (f \<section> 2) + 
  (x $ 3) * (f \<section> 3) + 
  (x $ 4) * (f \<section> 4)" sorry
  then have "q = (x $ 1) * (f \<section> 1) + (x $ 2) * (f \<section> 2) + (x $ 3) * (f \<section> 3) + (x $ 4) * (f \<section> 4)" sorry
  thus ?thesis
    using q_def 
    by simp
qed

text 
\<open>
We prove that one-forms form a (real) vector space using the notion of vector space in the theory
VectorSpace of Holden Lee. That way one can use notions like span, linear independence and basis
introduced in that theory.  
\<close>

definition one_form_add :: "[one_form, one_form] \<Rightarrow> one_form" where
"one_form_add f g \<equiv> Abs_one_form (\<lambda>v. f(v) + g(v))"

definition one_form_zero :: "one_form" where
"one_form_zero \<equiv> Abs_one_form (\<lambda>v. 0)"

definition one_form_monoid :: "(_, _) ring_scheme" where
"one_form_monoid \<equiv> \<lparr>carrier = UNIV::(one_form) set, mult = one_form_add, one = one_form_zero, 
  zero = undefined, add = undefined\<rparr>"

interpretation abelian_monoid_one_form : abelian_monoid "one_form_monoid" sorry

interpretation abelian_group_one_form : abelian_group "one_form_monoid" sorry

definition one_form_smult :: "[real, one_form] \<Rightarrow> one_form" where
"one_form_smult r f \<equiv> Abs_one_form (\<lambda>v. r * f(v))"

definition one_form_module :: "(_, _, _) module_scheme" ("1-form") where
"one_form_module \<equiv> \<lparr>carrier = UNIV::(one_form) set, mult = one_form_add, one = one_form_zero, 
  zero = undefined, add = undefined, smult = one_form_smult\<rparr>"

interpretation module_one_form : module "real_ring" "one_form_module" sorry

interpretation vecspace_one_form : vectorspace "real_ring" "one_form_module" sorry

text \<open>We define a basis for the vector space of one-forms.\<close>

definition one_form_basis_nth :: "nat \<Rightarrow> one_form" ("\<omega>\<^sup>_") where
"one_form_basis_nth n \<equiv> if n = 1 then Abs_one_form (\<lambda>x::real^4. x $ 1) else
  if n = 2 then Abs_one_form (\<lambda>x. x $ 2) else 
  if n= 3 then Abs_one_form (\<lambda>x. x $ 3) else
  if n = 4 then Abs_one_form (\<lambda>x. x $ 4) else undefined"

definition one_form_basis :: "(one_form) set" where
"one_form_basis \<equiv> {\<omega>\<^sup>n| n::nat. n \<ge> 1 \<and> n \<le> 4}"

lemma basis_one_form_basis :
  shows "vecspace_one_form.basis one_form_basis" sorry

text 
\<open>
The basis1_one_form transforms under a change of basis in the same way as
components of vectors and in the opposite way to components of one-forms.
\<close>

definition one_form_basis1' :: "real \<Rightarrow> one_form" ("\<omega>\<^sup>1'") where
"one_form_basis1' v \<equiv> (\<gamma> v) \<odot>\<^bsub>1-form\<^esub> \<omega>\<^sup>1 \<oplus>\<^bsub>1-form\<^esub> (- v * \<gamma> v) \<odot>\<^bsub>1-form\<^esub> \<omega>\<^sup>2"

definition one_form_basis2' :: "real \<Rightarrow> one_form" ("\<omega>\<^sup>2'") where
"one_form_basis2' v \<equiv> (- v * \<gamma> v) \<odot>\<^bsub>1-form\<^esub> \<omega>\<^sup>1 \<oplus>\<^bsub>1-form\<^esub> (\<gamma> v) \<odot>\<^bsub>1-form\<^esub> \<omega>\<^sup>2"

definition one_form_basis3' :: "real \<Rightarrow> one_form" ("\<omega>\<^sup>3'") where
"one_form_basis3' v \<equiv> \<omega>\<^sup>3"

definition one_form_basis4' :: "real \<Rightarrow> one_form" ("\<omega>\<^sup>4'") where
"one_form_basis4' v \<equiv> \<omega>\<^sup>4"

definition one_form_basis' :: "real \<Rightarrow> (one_form) set"  where
"one_form_basis' v \<equiv> {\<omega>\<^sup>1'(v), \<omega>\<^sup>2'(v), \<omega>\<^sup>3'(v), \<omega>\<^sup>4'(v)}"

lemma basis_one_form_basis' :
  fixes v :: real
  shows "vecspace_one_form.basis (one_form_basis' v)" sorry


section \<open>The (0,2)-Tensors: Two-Forms.\<close>

subsection \<open>Two-forms\<close>

definition bilinear :: "([real^4, real^4] \<Rightarrow> real) \<Rightarrow> bool" where
"bilinear f \<equiv> (\<forall>y::real^4. linear (\<lambda>x. f x y)) \<and> (\<forall>x::real^4. linear (\<lambda>y. f x y))"

lemma bilinear_zero :
  shows "bilinear (\<lambda>x y::real^4. 0)" sorry

typedef two_form = "{f| f:: [real^4, real^4] \<Rightarrow> real. bilinear f}"
  using bilinear_zero 
  by auto

definition two_form_to_fun :: "two_form \<Rightarrow> ([real^4, real^4] \<Rightarrow> real)" where
"two_form_to_fun f \<equiv> Rep_two_form f"

declare [[coercion two_form_to_fun]]

definition outer_prod_one_form :: "[one_form, one_form] \<Rightarrow> two_form" ("_ \<otimes> _") where
"outer_prod_one_form f g \<equiv> Abs_two_form (\<lambda>x y. f x * g y)"

text 
\<open>
First, note that the outer product of two one-forms is not commutative in general.
Second, a two-form in general is not an outer product of two one-forms, but any two-form can be
written as a finite sum of such simple outer products of one-forms.
\<close>

lemma bilinear_outer_prod_one_form :
  fixes f::"one_form" and g::"one_form"
  shows "bilinear (\<lambda>x y. f x * g y)" sorry

text \<open>Two-forms form a real vector space.\<close>

definition two_form_add :: "[two_form, two_form] \<Rightarrow> two_form" where
"two_form_add f g \<equiv> Abs_two_form (\<lambda>x y::real^4. f x y + g x y)"

definition two_form_zero :: "two_form" where
"two_form_zero \<equiv> Abs_two_form (\<lambda>x y. 0)"

definition two_form_monoid :: "(_, _) ring_scheme" where
"two_form_monoid \<equiv> \<lparr>carrier = UNIV::(two_form) set, mult = two_form_add, one = two_form_zero, 
  zero = undefined, add = undefined\<rparr>"

interpretation abelian_monoid_two_form : abelian_monoid "two_form_monoid" sorry

interpretation abelian_group_two_form : abelian_group "two_form_monoid" sorry

definition two_form_smult :: "[real, two_form] \<Rightarrow> two_form" where
"two_form_smult r f \<equiv> Abs_two_form (\<lambda>x y. r * f x y)"

definition two_form_module :: "(_, _, _) module_scheme" ("2-form") where
"two_form_module \<equiv> \<lparr>carrier = UNIV::(two_form) set, mult = two_form_add, one = two_form_zero, 
  zero = undefined, add = undefined, smult = two_form_smult\<rparr>"

interpretation module_two_form : module "real_ring" "two_form_module" sorry

interpretation vecspace_two_form : vectorspace "real_ring" "two_form_module" sorry

definition two_form_basis_nth :: "nat \<Rightarrow> nat \<Rightarrow> two_form" ("\<omega>\<^sup>_\<^sup>_") where
"two_form_basis_nth m n \<equiv> if (1 \<le> m \<and> m \<ge> 4 \<and> 1 \<le> n \<and> n \<ge> 4) then \<omega>\<^sup>m \<otimes> \<omega>\<^sup>n else undefined"

definition two_form_basis :: "(two_form) set" where
"two_form_basis \<equiv> {\<omega>\<^sup>m\<^sup>n| m n::nat. 1 \<le> m \<and> m \<ge> 4 \<and> 1 \<le> n \<and> n \<ge> 4}"

lemma basis_two_form_basis :
  shows "vecspace_two_form.basis two_form_basis" sorry

subsection \<open>Symmetries\<close>

definition symmetric_two_form :: "two_form \<Rightarrow> bool" where
"symmetric_two_form f \<equiv> \<forall>x y. f x y = f y x"

definition two_form_symmetrization :: "two_form \<Rightarrow> two_form" ("s_") where
"two_form_symmetrization f \<equiv> Abs_two_form (\<lambda>x y. 1/2 * f x y + 1/2 * f y x)"

lemma symmetric_two_form_symmetrization :
  fixes f::"two_form"
  shows "symmetric_two_form (s f)" sorry

definition antisymmetric :: "two_form \<Rightarrow> bool" where
"antisymmetric f \<equiv> \<forall>x y. f x y = - f y x"

definition two_form_antisymmetrization :: "two_form \<Rightarrow> two_form" ("a_") where
"two_form_antisymmetrization f \<equiv> Abs_two_form (\<lambda>x y. 1/2 * f x y - 1/2 * f y x)"

lemma antisymmetric_two_form_antisymmetrization :
  fixes f::"two_form"
  shows "antisymmetric (a f)" sorry

lemma split_symm_antisymm :
  fixes f::"two_form"
  shows "f = (s f) \<oplus>\<^bsub>2-form\<^esub> (a f)" sorry


section \<open>The Metric Tensor\<close>

subsection \<open>The Metric Tensor\<close>

definition metric_tensor :: "[real^4, real^4] \<Rightarrow> real" ("g _ _")where
"metric_tensor x y \<equiv> - (x $ 1 * y $ 1) + x $ 2 * y $ 2 + x $ 3 * y $ 3 + x $ 4 * y $ 4"

lemma bilinear_metric_tensor :
  shows "bilinear metric_tensor" sorry

lemma symmetric_metric_tensor :
  shows "symmetric_two_form (Abs_two_form metric_tensor)" sorry

subsection \<open>Metric as a Mapping of Vectors into One-Forms\<close>

definition mapping_vec_one_form :: "real^4 \<Rightarrow> one_form"  where
"mapping_vec_one_form x \<equiv> Abs_one_form (\<lambda>y. g x y)"

lemma linear_mapping_vec_one_form :
  fixes x::"real^4"
  shows "linear (mapping_vec_one_form x)" sorry

subsection \<open>The Inverse: Going from One-Forms to Vectors\<close>

definition mapping_one_form_vec :: "one_form \<Rightarrow> real^4" where
"mapping_one_form_vec f \<equiv> vector [- (f \<section> 1), f \<section> 2, f \<section> 3, f \<section> 4]"

text \<open>The mapping above between vectors and one-forms is one-to-one.\<close>

lemma mapping_vec_one_form_vec :
  fixes x::"real^4"
  shows "mapping_one_form_vec (mapping_vec_one_form x) = x" sorry

lemma mapping_one_form_vec_one_form :
  fixes f::"one_form"
  shows "mapping_vec_one_form (mapping_one_form_vec f) = f" sorry


section \<open>The General Case: (m,n)-Tensors\<close>


definition contra_co_linear :: "([one_form list, (real^4) list] => real) \<Rightarrow> bool" where
"contra_co_linear f \<equiv> 
\<exists>m n::nat.\<forall>l1.\<forall>l2. length l1 = m \<longrightarrow> length l2 = n \<longrightarrow> 
(
(\<forall>i. i\<ge> 1 \<and> i\<le> m \<longrightarrow> (\<forall>l3 l4. length l3 = i-1 \<longrightarrow> length l4 = m-i \<longrightarrow> (linear (\<lambda>x. f (l3 @ ([x] @ l4)) l2)))) 
\<and> 
(\<forall>j. j\<ge> 1 \<and> j\<le> n \<longrightarrow> (\<forall>l5 l6. length l5 = j-1 \<longrightarrow> length l6 = n-j \<longrightarrow> (linear (\<lambda>x. f l1 (l5 @ ([x] @ l6))))))
)"

typedef tensor = "{f| f:: [one_form list, (real^4) list] \<Rightarrow> real. contra_co_linear f}"
proof-
  have f1:"\<forall>l:: _ list. length l = 0 \<longrightarrow> l = []"
    by simp
  define f where "f = (\<lambda>x::one_form list.\<lambda>y::(real^4) list. 0::real)"
  then have "(\<lambda>x. f [] ([] @ ([x] @ []))) = (\<lambda>x. 0)"
    by simp
  then have "\<forall>l l'. length l = 0 \<longrightarrow> length l' = 0 \<longrightarrow> linear (\<lambda>x. f [] (l @ ([x] @ l')))"
    using linear_zero f_def f1 
    by simp
  then have "\<forall>l1.\<forall>l2. length l1 = 0 \<longrightarrow> length l2 = 1 \<longrightarrow> 
(
(\<forall>i. i\<ge> 1 \<and> i\<le> 0 \<longrightarrow> (\<forall>l3 l4. length l3 = i-1 \<longrightarrow> length l4 = 0-i \<longrightarrow> (linear (\<lambda>x. f (l3 @ ([x] @ l4)) l2)))) 
\<and> 
(\<forall>j. j\<ge> 1 \<and> j\<le> 1 \<longrightarrow> (\<forall>l5 l6. length l5 = j-1 \<longrightarrow> length l6 = 1-j \<longrightarrow> (linear (\<lambda>x. f l1 (l5 @ ([x] @ l6))))))
)" 
    by simp
  thus "?thesis"
    using contra_co_linear_def 
    by auto
qed

end
