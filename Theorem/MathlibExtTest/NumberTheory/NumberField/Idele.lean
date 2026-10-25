/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Idele.lean -/

/-
Author: @toskua, Avocado
-/

import Abbrev.NumberTheory.NumberField.Idele.Part2
import Lemma.Nat.NumberField.Idele


noncomputable section

open NumberField IsDedekindDomain

section TestIntRational

example : CommGroup (TopologicalIdeleGroup ℤ ℚ) := inferInstance

example : TopologicalSpace (TopologicalIdeleGroup ℤ ℚ) := inferInstance

example : IsTopologicalGroup (TopologicalIdeleGroup ℤ ℚ) := inferInstance

example : CommGroup (FiniteIdeleGroup ℤ ℚ) := inferInstance

example : TopologicalSpace (FiniteIdeleGroup ℤ ℚ) := inferInstance

example : IsTopologicalGroup (FiniteIdeleGroup ℤ ℚ) := inferInstance

example : CommGroup (InfiniteIdeleGroup ℚ) := inferInstance

example : TopologicalSpace (InfiniteIdeleGroup ℚ) := inferInstance

example : IsTopologicalGroup (InfiniteIdeleGroup ℚ) := inferInstance

example : TopologicalSpace (TopologicalIdeleClassGroup ℤ ℚ) := inferInstance

example : IsTopologicalGroup (TopologicalIdeleClassGroup ℤ ℚ) := inferInstance

example : TopologicalIdeleGroup.principalEmbedding ℤ ℚ 1 = 1 := by
  simp

example : Function.Injective (TopologicalIdeleGroup.principalEmbedding ℤ ℚ) :=
  TopologicalIdeleGroup.principalEmbedding_injective ℤ ℚ

example : (QuotientGroup.mk (s := TopologicalIdeleGroup.principalIdeles ℤ ℚ)
    (TopologicalIdeleGroup.principalEmbedding ℤ ℚ 1) :
      TopologicalIdeleClassGroup ℤ ℚ) = 1 := by
  simp

end TestIntRational
end
