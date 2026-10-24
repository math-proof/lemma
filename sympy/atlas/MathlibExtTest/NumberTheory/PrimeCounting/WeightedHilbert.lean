/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/WeightedHilbert.lean -/


import sympy.atlas.NumberTheory.PrimeCounting.WeightedHilbert
import Lemma.Nat.PrimeCounting.WeightedHilbert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.NumberTheory.PrimeCounting.WeightedHilbert

open scoped BigOperators ComplexConjugate

open MathlibExt.NumberTheory.PrimeCounting

-- Apply the weighted Hilbert inequality to two antipodal points on the unit circle.
example :
    let x : Fin 2 → ℝ := ![0, 1 / 2]
    let δ : Fin 2 → ℝ := fun _ ↦ 1 / 2
    let z : Fin 2 → ℂ := ![1, 1]
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        z r * conj (z s) / Real.sin (Real.pi * (x r - x s))‖ ≤
      3 / 2 * ∑ r, ‖z r‖ ^ 2 / δ r := by
  dsimp only
  apply weightedHilbertCosecant
  · intro r
    norm_num
  · intro r s hrs
    fin_cases r <;> fin_cases s
    · exact (hrs rfl).elim
    · norm_num [AddCircle.norm_eq]
    · norm_num [AddCircle.norm_eq]
    · exact (hrs rfl).elim

end MathlibExtTest.NumberTheory.PrimeCounting.WeightedHilbert
