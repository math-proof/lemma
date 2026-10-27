import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_12
open Finset Real VarshamovGilbert


namespace VarshamovGilbert

/--
[varshamov_gilbert](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_12.lean)
-/
@[path]
lemma varshamov_gilbert
  {d : ℕ}
  {γ : ℝ}
-- given
  (hd : 0 < d)
  (hγ_pos : 0 < γ)
  (hγ_lt : γ < 1/2) :
-- imply
  ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)), (M : ℝ) ≥ Real.exp (γ ^ 2 * d / 2) ∧ ∀ j k : Fin M, j ≠ k → (hammingDist (ω j) (ω k) : ℝ) ≥ (1/2 - γ) * d := by
-- proof
  obtain ⟨M, hM, ω, hbound, hsep⟩ := InfoTheory.varshamov_gilbert d hd γ hγ_pos hγ_lt
  exact ⟨M, hM, ω, hbound, fun j k hjk => by
    have := hsep j k hjk
    simp only [InfoTheory.hammingDist, hammingDist] at this ⊢
    exact this⟩
end VarshamovGilbert



-- created on 2026-10-23
