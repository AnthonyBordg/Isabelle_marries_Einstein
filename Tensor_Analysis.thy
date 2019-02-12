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

definition vec_basis :: "(real^4) set" ("\<O>") where
"vec_basis \<equiv> {e\<^sub>1, e\<^sub>2, e\<^sub>3, e\<^sub>4}"

lemma sum_insert:
  assumes "x \<notin> F"
  shows "(\<Sum>y\<in>insert x F. P y) = (\<Sum>y\<in>F. P y) + P x" sorry

lemma finsum_insert:
  assumes "x \<notin> F" and "finite F"
  shows "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>insert x F. P v) = (\<Oplus>\<^bsub>real4_module\<^esub>v\<in>F. P v) + P x" sorry

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
      using a2
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
  shows "(vector [x1, x2, x3, x4]::('a::zero)^4) $ 1 = x1"
    and "(vector [x1, x2, x3, x4]::('a::zero)^4) $ 2 = x2"
    and "(vector [x1, x2, x3, x4]::('a::zero)^4) $ 3 = x3"
    and "(vector [x1, x2, x3, x4]::('a::zero)^4) $ 4 = x4"
  unfolding vector_def
  by auto

lemma lincomb_vec_basis:
  assumes "finite A" and "A \<subseteq> \<O>" and "a \<in> (A \<rightarrow> carrier real_ring)" and "v \<in> A" and "a v \<noteq> 0"
  shows "module_real4.lincomb a A \<noteq> real4_zero"
  apply (auto simp: module_real4.lincomb_def real4_zero_def)
proof-
  have f1:"v = vector [1, 0, 0, 0] \<or> v = vector [0, 1, 0, 0] \<or> v = vector [0, 0, 1, 0] \<or> v = vector [0, 0, 0, 1]"
    using assms(2) assms(4) vec_basis_def vec_basis1_def vec_basis2_def vec_basis3_def vec_basis4_def sum_def
    by fastforce
  then have f2:"\<forall>i. (\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ i = (\<Sum>x\<in>{u. u\<in>A}. a x * (x $ i))"
    using assms(1) assms(3) lincomb_comp module_real4.lincomb_def 
    by simp
  then have "(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 1 = (\<Sum>x\<in>{u. u\<in>A}. a x * (x $ 1))"
    by simp
  then have "(\<Oplus>\<^bsub>real4_module\<^esub>u\<in>A. a u \<odot>\<^bsub>real4_module\<^esub> u) $ 1 = a v" if "v = vector [1, 0, 0, 0]"
    using assms(2) assms(4) vec_basis_def vec_basis1_def vec_basis2_def vec_basis3_def vec_basis4_def 
vector_comp(1)
    

(*
  show "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>{}. a v \<odot>\<^bsub>real4_module\<^esub> v) = (\<chi> i. 0) \<Longrightarrow> False"
  proof-
    have "A \<noteq> {}"
      using assms(4) 
      by auto
    thus ?thesis
    apply (auto simp: comm_monoid.finprod_empty)
  proof-
    have "(\<Oplus>\<^bsub>real4_module\<^esub>v\<in>{}. a v \<odot>\<^bsub>real4_module\<^esub> v) = real4_one"
      using real4_one_def real4_add_def comm_monoid.finprod_empty
  using assms vec_basis_def vec_basis1_def vec_basis2_def
vec_basis3_def vec_basis4_def
*)
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

lemma gen_set_vec_basis :
  shows "module_real4.gen_set \<O>" sorry

lemma vec_basis_in_univ :
  shows "\<O> \<subseteq> carrier real4_module" sorry

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

lemma basis_vec_basis' :
  fixes v :: real
  shows "vecspace_real4.basis \<O>'(v)" sorry

text 
\<open>
We define the components of a one_form on a given basis as the real numbers obtained from
the application of the one_form to the basis vectors.
\<close>

definition one_form_nth :: "one_form \<Rightarrow> nat \<Rightarrow> real" ("_ \<section> _") where
"one_form_nth f n \<equiv> if n=1 then f(e\<^sub>1) else
  if n=2 then f(e\<^sub>2) else
  if n=3 then f(e\<^sub>3) else
  if n=4 then f(e\<^sub>4) else undefined"

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
