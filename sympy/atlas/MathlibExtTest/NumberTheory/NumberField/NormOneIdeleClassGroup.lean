/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/NormOneIdeleClassGroup.lean -/

/-
Author: @toskua, Avocado
-/

import sympy.atlas.NumberTheory.NumberField.NormOneIdeleClassGroup
import Lemma.Nat.NumberField.NormOneIdeleClassGroup


noncomputable section

open NumberField

variable (K : Type*) [Field K] [NumberField K]

example : CommGroup (TopologicalIdeleGroup.NormOneIdeleClassGroup K) := inferInstance

example : IsTopologicalGroup (TopologicalIdeleGroup.NormOneIdeleClassGroup K) :=
  inferInstance

example (x : Kˣ) :
    QuotientGroup.mk (s := TopologicalIdeleGroup.normOnePrincipalIdeles K)
        ⟨TopologicalIdeleGroup.principalEmbedding (NumberField.RingOfIntegers K) K x,
          TopologicalIdeleGroup.principalIdeles_le_normOneIdeles K ⟨x, rfl⟩⟩ = 1 :=
  TopologicalIdeleGroup.normOne_mk_principalEmbedding K x

example :
    QuotientGroup.mk (s := TopologicalIdeleGroup.normOnePrincipalIdeles ℚ)
        ⟨TopologicalIdeleGroup.principalEmbedding (NumberField.RingOfIntegers ℚ) ℚ 1,
          TopologicalIdeleGroup.principalIdeles_le_normOneIdeles ℚ ⟨1, rfl⟩⟩ = 1 :=
  TopologicalIdeleGroup.normOne_mk_principalEmbedding ℚ 1
