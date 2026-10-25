/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/Hensel.lean -/


import Theorem.RingTheory.DiscreteValuationRing.Hensel
import Lemma.Int.DiscreteValuationRing.Hensel
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum


noncomputable section

open Polynomial IsLocalRing Ring

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

example (f : A[X]) (a₀ : A) (h₁ : f.eval a₀ ∈ maximalIdeal A)
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal A :=
  f.exists_isRoot_sub_mem_maximalIdeal_of_isUnit_derivative a₀ h₁ h₂

omit [IsAdicComplete (maximalIdeal A) A] in
example (p : A[X]) (a a₀ : A) :
    IsDiscreteValuationRing.addVal A (a - a₀) ≤
      IsDiscreteValuationRing.addVal A (p.eval a - p.eval a₀) :=
  p.addVal_sub_le_addVal_eval_sub a a₀

omit [IsAdicComplete (maximalIdeal A) A] in
example (f : A[X]) (a a₀ : A)
    (hva : IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) <
      IsDiscreteValuationRing.addVal A (a - a₀)) :
    IsDiscreteValuationRing.addVal A (f.derivative.eval a) =
      IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) :=
  f.addVal_derivative_eval_eq_of_lt_addVal_sub a a₀ hva

omit [IsAdicComplete (maximalIdeal A) A] in
example (f : A[X]) (a a' a₀ : A)
    (hfa : f.IsRoot a) (hfa' : f.IsRoot a')
    (hva : IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) <
      IsDiscreteValuationRing.addVal A (a - a₀))
    (hva' : IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) <
      IsDiscreteValuationRing.addVal A (a' - a₀)) :
    a = a' :=
  f.eq_of_isRoot_of_addVal_derivative_lt_addVal_sub a a' a₀ hfa hfa' hva hva'

omit [IsAdicComplete (maximalIdeal A) A] in
example {d q : A} (hd : d ≠ 0) (hq : q ∈ maximalIdeal A) :
    IsDiscreteValuationRing.addVal A d <
      IsDiscreteValuationRing.addVal A d +
        IsDiscreteValuationRing.addVal A q :=
  IsDiscreteValuationRing.addVal_lt_addVal_add_of_mem_maximalIdeal hd hq

example (f : A[X]) (a₀ : A)
    (hval : 2 * IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) <
      IsDiscreteValuationRing.addVal A (f.eval a₀)) :
    ∃ a : A,
    f.IsRoot a ∧
    a - a₀ ∈ maximalIdeal A ∧
    IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) <
      IsDiscreteValuationRing.addVal A (a - a₀) ∧
    IsDiscreteValuationRing.addVal A (f.eval a₀) ≤
      IsDiscreteValuationRing.addVal A (a - a₀) +
        2 * IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) ∧
    (∀ a' : A, f.IsRoot a' →
      IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) <
        IsDiscreteValuationRing.addVal A (a' - a₀) → a' = a) ∧
    IsDiscreteValuationRing.addVal A (f.derivative.eval a) =
      IsDiscreteValuationRing.addVal A (f.derivative.eval a₀) :=
  f.exists_isRoot_of_two_mul_addVal_derivative_lt_addVal a₀ hval

end
