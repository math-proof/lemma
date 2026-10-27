import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.TensorCategories.code.K0Bimodule.Part5
open Finset FusionRing FusionRing.K0Group


namespace FusionRing

/--
[k0ActLeft_eq_grMul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma k0ActLeft_eq_grMul
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {r p : ι → ℤ} :
-- imply
  R.k0ActLeft r p = R.grMul r p := by
-- proof
  funext k
  simp only [k0ActLeft, grMul]
  congr 1; ext i; congr 1; ext j; congr 1
  exact_mod_cast (R.N_star_transpose i j k).symm

end FusionRing

namespace FusionRing

/--
[k0ActRight_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma k0ActRight_one
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {p : ι → ℤ} :
-- imply
  R.k0ActRight p R.grOne = p := by
-- proof
  funext k
  simp only [k0ActRight, grOne]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true]
  rw [R.star_unit]
  simp only [R.mul_unit_int, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]

end FusionRing

namespace FusionRing

/--
[k0ActRight_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma k0ActRight_add_left
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {p₁ p₂ r : ι → ℤ} :
-- imply
  R.k0ActRight (fun k => p₁ k + p₂ k) r = fun k => R.k0ActRight p₁ r k + R.k0ActRight p₂ r k := by
-- proof
  funext k; simp only [k0ActRight]
  simp_rw [add_mul, Finset.sum_add_distrib]

end FusionRing

namespace FusionRing

/--
[k0ActRight_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma k0ActRight_add_right
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {p r₁ r₂ : ι → ℤ} :
-- imply
  R.k0ActRight p (fun k => r₁ k + r₂ k) = fun k => R.k0ActRight p r₁ k + R.k0ActRight p r₂ k := by
-- proof
  funext k; simp only [k0ActRight]
  have h : ∀ a j, p a * (r₁ j + r₂ j) * (R.N k (R.star j) a : ℤ) =
    p a * r₁ j * (R.N k (R.star j) a : ℤ) + p a * r₂ j * (R.N k (R.star j) a : ℤ) :=
    fun _ _ => by ring
  simp_rw [h, Finset.sum_add_distrib]

end FusionRing

namespace FusionRing

/--
[k0ActRight_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma k0ActRight_zero_left
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {r : ι → ℤ} :
-- imply
  R.k0ActRight (fun _ => 0) r = fun _ => 0 := by
-- proof
  funext k; simp only [k0ActRight]; simp

end FusionRing

namespace FusionRing

/--
[k0ActRight_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma k0ActRight_zero_right
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {p : ι → ℤ} :
-- imply
  R.k0ActRight p (fun _ => 0) = fun _ => 0 := by
-- proof
  funext k; simp only [k0ActRight]; simp

end FusionRing

namespace FusionRing

/--
[star_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma star_eq_iff
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b : ι} :
-- imply
  a = R.star b ↔ b = R.star a := by
-- proof
  constructor <;> (intro h; rw [h, R.star_star])

end FusionRing

namespace FusionRing

/--
[N_cyclic_star](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma N_cyclic_star
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j k : ι} :
-- imply
  R.N i j (R.star k) = R.N j k (R.star i) := by
-- proof
  have h := R.assoc i j k R.unit
  simp only [R.duality, mul_ite, mul_one, mul_zero] at h
  simp_rw [R.star_eq_iff k] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

end FusionRing

namespace FusionRing

/--
[N_star_triple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma N_star_triple
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {p j q : ι} :
-- imply
  R.N (R.star p) (R.star j) (R.star q) = R.N j p q := by
-- proof
  rw [R.N_cyclic_star (R.star p) (R.star j) q, R.star_star]
  have h := R.N_star_transpose (R.star j) q p
  rwa [R.star_star] at h

end FusionRing

namespace FusionRing

/--
[sum_star_reparametrize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma sum_star_reparametrize
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {f : ι → ℤ} :
-- imply
  (univ.sum fun m => f m) = (univ.sum fun q => f (R.star q)) := by
-- proof
  apply Finset.sum_equiv R.starEquiv
  · intro i; simp [Finset.mem_univ]
  · intro i _; simp [starEquiv, R.star_star]

end FusionRing

namespace FusionRing

/--
[inner_sum_k0ActRight_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma inner_sum_k0ActRight_assoc
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a j p l : ι} :
-- imply
  (univ.sum fun k => (R.N k (R.star j) a : ℤ) * (R.N l (R.star p) k : ℤ)) = (univ.sum fun q => (R.N j p q : ℤ) * (R.N l (R.star q) a : ℤ)) := by
-- proof
  simp_rw [mul_comm ((R.N _ (R.star j) a : ℤ)) _]
  have h_assoc : (univ.sum fun k => (R.N l (R.star p) k : ℤ) * (R.N k (R.star j) a : ℤ)) =
    (univ.sum fun m => (R.N (R.star p) (R.star j) m : ℤ) * (R.N l m a : ℤ)) := by
    exact_mod_cast R.assoc l (R.star p) (R.star j) a
  rw [h_assoc, R.sum_star_reparametrize]
  congr 1; ext q
  congr 1
  exact_mod_cast R.N_star_triple p j q

end FusionRing

namespace FusionRing

/--
[inner_sum_bimodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma inner_sum_bimodule
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a j i l : ι} :
-- imply
  (univ.sum fun k => (R.N k (R.star j) a : ℤ) * (R.N i k l : ℤ)) = (univ.sum fun b => (R.N i a b : ℤ) * (R.N l (R.star j) b : ℤ)) := by
-- proof
  have h1 : ∀ k, (R.N i k l : ℤ) = (R.N (R.star i) l k : ℤ) := by
    intro k; exact_mod_cast R.N_star_transpose i k l
  simp_rw [h1, mul_comm ((R.N _ (R.star j) a : ℤ)) _]
  have h_assoc : (univ.sum fun k => (R.N (R.star i) l k : ℤ) * (R.N k (R.star j) a : ℤ)) =
    (univ.sum fun m => (R.N l (R.star j) m : ℤ) * (R.N (R.star i) m a : ℤ)) := by
    exact_mod_cast R.assoc (R.star i) l (R.star j) a
  rw [h_assoc]
  have h2 : ∀ m, (R.N (R.star i) m a : ℤ) = (R.N i a m : ℤ) := by
    intro m
    have := R.N_star_transpose (R.star i) m a
    rw [R.star_star] at this
    exact_mod_cast this
  simp_rw [h2]
  congr 1; ext b; ring

end FusionRing

namespace FusionRing

/--
[k0ActRight_mul_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma k0ActRight_mul_assoc
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {m s r : ι → ℤ} :
-- imply
  R.k0ActRight (R.k0ActRight m s) r = R.k0ActRight m (R.grMul s r) := by
-- proof
  funext l
  simp only [k0ActRight, grMul]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  congr 1; ext a; congr 1; ext j; congr 1; ext p
  trans m a * s j * r p * ∑ x, (R.N x (R.star j) a : ℤ) * (R.N l (R.star p) x : ℤ)
  · rw [Finset.mul_sum]; congr 1; ext x; ring
  trans m a * s j * r p * ∑ x, (R.N j p x : ℤ) * (R.N l (R.star x) a : ℤ)
  · rw [R.inner_sum_k0ActRight_assoc a j p l]
  · rw [Finset.mul_sum]; congr 1; ext x; ring

end FusionRing

namespace FusionRing

/--
[k0_bimodule_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma k0_bimodule_compat
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {r : ι → ℤ}
  {m : ι → ℤ}
  {s : ι → ℤ} :
-- imply
  R.grMul r (R.k0ActRight m s) = R.k0ActRight (R.grMul r m) s := by
-- proof
  funext l
  simp only [grMul, k0ActRight]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext a; congr 1; ext j
  trans r i * m a * s j * ∑ x, (R.N x (R.star j) a : ℤ) * (R.N i x l : ℤ)
  · rw [Finset.mul_sum]; congr 1; ext x; ring
  trans r i * m a * s j * ∑ x, (R.N i a x : ℤ) * (R.N l (R.star j) x : ℤ)
  · rw [R.inner_sum_bimodule a j i l]
  · rw [Finset.mul_sum]; congr 1; ext x; ring

end FusionRing

namespace FusionRing

/--
[prop_1_47_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
lemma prop_1_47_1
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι} :
-- imply
  SMulCommClass (GrRingOf R) (GrRingOf R)ᵐᵒᵖ (K0Group R) :=
-- proof
  K0Group.instSMulCommClass

end FusionRing

/--
[coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
private lemma coeff_zero_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {k : ι} :
-- imply
  (0 : K0Group R).coeff k = 0 := by
-- proof
  apply FusionRing.K0Group.coeff_zero R k

/--
[coeff_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
private lemma coeff_add_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a b : K0Group R}
  {k : ι} :
-- imply
  (a + b).coeff k = a.coeff k + b.coeff k := by
-- proof
  apply FusionRing.K0Group.coeff_add R a b k

/--
[coeff_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
private lemma coeff_neg_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a : K0Group R}
  {k : ι} :
-- imply
  (-a).coeff k = -a.coeff k := by
-- proof
  apply FusionRing.K0Group.coeff_neg R a k

/--
[coeff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
private lemma coeff_sub_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a b : K0Group R}
  {k : ι} :
-- imply
  (a - b).coeff k = a.coeff k - b.coeff k := by
-- proof
  apply FusionRing.K0Group.coeff_sub R a b k

/--
[smul_left_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
private lemma smul_left_coeff_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {r : GrRingOf R}
  {m : K0Group R}
  {k : ι} :
-- imply
  (r • m).coeff k = R.k0ActLeft r.coeff m.coeff k := by
-- proof
  apply FusionRing.K0Group.smul_left_coeff R r m k

/--
[smul_right_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean)
-/
@[path]
private lemma smul_right_coeff_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {r : (GrRingOf R)ᵐᵒᵖ}
  {m : K0Group R}
  {k : ι} :
-- imply
  (r • m).coeff k = R.k0ActRight m.coeff r.unop.coeff k := by
-- proof
  apply FusionRing.K0Group.smul_right_coeff R r m k


-- created on 2026-10-23
