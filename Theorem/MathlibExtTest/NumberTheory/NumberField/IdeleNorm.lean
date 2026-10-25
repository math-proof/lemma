/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/IdeleNorm.lean -/

/-
Author: @toskua, Avocado
-/

import Def.NumberTheory.NumberField.IdeleNorm
import Lemma.Nat.NumberField.IdeleNorm


noncomputable section

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]

example (aInf : InfiniteIdeleGroup K) (aFin : FiniteIdeleGroup (𝓞 K) K) :
    TopologicalIdeleGroup.adelicNorm K (aInf, aFin) =
      (∏ w : InfinitePlace K, ‖(aInf w : w.Completion)‖ ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(aFin v : v.adicCompletion K)‖ :=
  TopologicalIdeleGroup.adelicNorm_apply K (aInf, aFin)

example (a b : TopologicalIdeleGroup (𝓞 K) K) :
    TopologicalIdeleGroup.adelicNorm K (a * b) =
      TopologicalIdeleGroup.adelicNorm K a * TopologicalIdeleGroup.adelicNorm K b :=
  map_mul (TopologicalIdeleGroup.adelicNorm K) a b

example (a : TopologicalIdeleGroup (𝓞 K) K) :
    a ∈ TopologicalIdeleGroup.normOneIdeles K ↔
      TopologicalIdeleGroup.adelicNorm K a = 1 :=
  TopologicalIdeleGroup.mem_normOneIdeles K

example : IsTopologicalGroup (TopologicalIdeleGroup.normOneIdeles K) := inferInstance

example (x : Kˣ) :
    TopologicalIdeleGroup.principalEmbedding (𝓞 K) K x ∈
      TopologicalIdeleGroup.normOneIdeles K :=
  TopologicalIdeleGroup.principalIdeles_le_normOneIdeles K ⟨x, rfl⟩

example : TopologicalIdeleGroup.principalEmbedding (𝓞 ℚ) ℚ 1 ∈
    TopologicalIdeleGroup.normOneIdeles ℚ := by
  simp

end
