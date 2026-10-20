import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.Hensel
open Polynomial IsLocalRing Ring
open IsDiscreteValuationRing


/--
[Polynomial.exists_isRoot_sub_mem_maximalIdeal_of_isUnit_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Hensel.lean)
-/
@[path]
private lemma Polynomial_exists_isRoot_sub_mem_maximalIdeal_of_isUnit_derivative_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  {f : A[X]}
  {a₀ : A}
-- given
  (h₁ : f.eval a₀ ∈ maximalIdeal A)
  (h₂ : IsUnit (f.derivative.eval a₀)) :
-- imply
  ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal A := by
-- proof
  apply Polynomial.exists_isRoot_sub_mem_maximalIdeal_of_isUnit_derivative f a₀ h₁ h₂

/--
[Polynomial.addVal_sub_le_addVal_eval_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Hensel.lean)
-/
@[path]
private lemma Polynomial_addVal_sub_le_addVal_eval_sub_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  {p : A[X]}
  {a a₀ : A} :
-- imply
  IsDiscreteValuationRing.addVal A (a - a₀) ≤
    IsDiscreteValuationRing.addVal A (p.eval a - p.eval a₀) := by
-- proof
  apply Polynomial.addVal_sub_le_addVal_eval_sub p a a₀

/--
[Polynomial.addVal_derivative_eval_eq_of_lt_addVal_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Hensel.lean)
-/
@[path]
private lemma Polynomial_addVal_derivative_eval_eq_of_lt_addVal_sub_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  {f : A[X]}
  {a a₀ : A}
-- given
  (hva : IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) < IsDiscreteValuationRing.addVal A (a - a₀)) :
-- imply
  IsDiscreteValuationRing.addVal A (f.derivative.eval a) =
    IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) := by
-- proof
  apply Polynomial.addVal_derivative_eval_eq_of_lt_addVal_sub f a a₀ hva

/--
[Polynomial.eq_of_isRoot_of_addVal_derivative_lt_addVal_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Hensel.lean)
-/
@[path]
private lemma Polynomial_eq_of_isRoot_of_addVal_derivative_lt_addVal_sub_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  {f : A[X]}
  {a a' a₀ : A}
-- given
  (hfa : f.IsRoot a)
  (hfa' : f.IsRoot a')
  (hva : addVal A (f.derivative.eval a₀) < addVal A (a - a₀))
  (hva' : addVal A (f.derivative.eval a₀) < addVal A (a' - a₀)) :
-- imply
  a = a' := by
-- proof
  apply Polynomial.eq_of_isRoot_of_addVal_derivative_lt_addVal_sub f a a' a₀ hfa hfa' hva hva'

/--
[addVal_lt_addVal_add_of_mem_maximalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Hensel.lean)
-/
@[path]
private lemma addVal_lt_addVal_add_of_mem_maximalIdeal_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  {d q : A}
-- given
  (hd : d ≠ 0)
  (hq : q ∈ maximalIdeal A) :
-- imply
  addVal A d < addVal A d + addVal A q := by
-- proof
  apply IsDiscreteValuationRing.addVal_lt_addVal_add_of_mem_maximalIdeal hd hq

/--
[Polynomial.exists_isRoot_of_two_mul_addVal_derivative_lt_addVal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Hensel.lean)
-/
@[path]
private lemma Polynomial_exists_isRoot_of_two_mul_addVal_derivative_lt_addVal_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  {f : A[X]}
  {a₀ : A}
-- given
  (hval : 2 * addVal A (f.derivative.eval a₀) < addVal A (f.eval a₀)) :
-- imply
  ∃ a : A,
    f.IsRoot a ∧
    a - a₀ ∈ maximalIdeal A ∧
    addVal A (f.derivative.eval a₀) < addVal A (a - a₀) ∧
    addVal A (f.eval a₀) ≤
    addVal A (a - a₀) + 2 * addVal A (f.derivative.eval a₀) ∧
    (∀ a' : A, f.IsRoot a' →
    addVal A (f.derivative.eval a₀) < addVal A (a' - a₀) → a' = a) ∧
    addVal A (f.derivative.eval a) = addVal A (f.derivative.eval a₀) := by
-- proof
  apply Polynomial.exists_isRoot_of_two_mul_addVal_derivative_lt_addVal f a₀ hval


-- created on 2026-10-20
