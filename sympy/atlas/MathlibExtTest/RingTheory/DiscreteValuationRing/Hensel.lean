/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/Hensel.lean -/


import sympy.atlas.RingTheory.DiscreteValuationRing.Hensel
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

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example :
    let f : ℤ_[5][X] := X ^ 2 - X - C 5
    ∃ a : ℤ_[5], f.IsRoot a ∧ a ∈ maximalIdeal ℤ_[5] ∧
      (∀ a' : ℤ_[5], f.IsRoot a' →
        0 < IsDiscreteValuationRing.addVal ℤ_[5] a' → a' = a) ∧
      IsDiscreteValuationRing.addVal ℤ_[5] (f.derivative.eval a) = 0 := by
  dsimp only
  let f : ℤ_[5][X] := X ^ 2 - X - C 5
  have hval :
      2 * IsDiscreteValuationRing.addVal ℤ_[5] (f.derivative.eval 0) <
        IsDiscreteValuationRing.addVal ℤ_[5] (f.eval 0) := by
    have h5 : IsDiscreteValuationRing.addVal ℤ_[5] 5 = 1 := by
      simpa using IsDiscreteValuationRing.addVal_uniformizer
        (PadicInt.irreducible_p (p := 5))
    simp [f, h5]
  obtain ⟨a, ha, hclose, _, _, huniq, hstable⟩ :=
    f.exists_isRoot_of_two_mul_addVal_derivative_lt_addVal 0 hval
  refine ⟨a, ha, by simpa using hclose, ?_, ?_⟩
  · intro a' ha' ha'val
    apply huniq a' ha'
    simpa [f] using ha'val
  · simpa [f] using hstable
