/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Idele.lean -/

/-
Author: @toskua, Avocado
-/

import Abbrev.NumberTheory.NumberField.Idele.Part2
import Lemma.Nat.NumberField.Idele
import Def.MathlibExtTest.NumberTheory.NumberField.Idele


noncomputable section

open NumberField IsDedekindDomain

section TestIntRational

example (u : (AdeleRing ℤ ℚ)ˣ) :
    testIdeleToAdeleUnits (testAdeleUnitsToIdele u) = u := by
  simp [testAdeleUnitsToIdele, testIdeleToAdeleUnits]

example (x : TopologicalIdeleGroup ℤ ℚ) :
    testAdeleUnitsToIdele (testIdeleToAdeleUnits x) = x := by
  simp [testAdeleUnitsToIdele, testIdeleToAdeleUnits]

example (x : ℚˣ) (v : InfinitePlace ℚ) :
    (TopologicalIdeleGroup.principalEmbedding ℤ ℚ x).1 v =
      Units.map (algebraMap ℚ v.Completion).toMonoidHom x := by
  rw [TopologicalIdeleGroup.principalEmbedding_fst,
    TopologicalIdeleGroup.infinitePrincipalEmbedding_apply]

example (x : ℚˣ) (v : HeightOneSpectrum ℤ) :
    (TopologicalIdeleGroup.principalEmbedding ℤ ℚ x).2 v =
      Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom x := by
  rw [TopologicalIdeleGroup.principalEmbedding_snd,
    TopologicalIdeleGroup.finitePrincipalEmbedding_apply]

end TestIntRational
end
