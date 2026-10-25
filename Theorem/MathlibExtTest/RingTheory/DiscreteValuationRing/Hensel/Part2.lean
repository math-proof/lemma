/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/Hensel.lean -/


import Theorem.RingTheory.DiscreteValuationRing.Hensel
import Lemma.Int.DiscreteValuationRing.Hensel
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum
import Instance.MathlibExtTest.RingTheory.DiscreteValuationRing.Hensel


noncomputable section

open Polynomial IsLocalRing Ring

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

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

end
