/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.FunctionalAnalysis.RosenthalL1.Part9
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_pairsHold_initial_even {K : Type*}
    (R : K → ℕ → ℕ → Prop) (k : K) (φ : ℕ → ℕ) :
    ∀ N, rosenthalPairsHold R k (rosenthalInitialSegment φ (2 * N)) ↔
      ∀ j < N, R k (φ (2 * j)) (φ (2 * j + 1)) := by
  intro N
  induction N generalizing φ with
  | zero => simp [rosenthalInitialSegment, rosenthalPairsHold]
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        rosenthal_initialSegment_succ, rosenthal_initialSegment_succ]
      simp only [rosenthalPairsHold]
      rw [ih]
      constructor
      · rintro ⟨hzero, htail⟩ j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simpa [rosenthalTail] using hzero
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
          have hi : i < N := by omega
          change R k (φ (2 * (i + 1))) (φ (2 * (i + 1) + 1))
          simpa [rosenthalTail, mul_add, add_assoc] using htail i hi
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [rosenthalTail] using h 0 (Nat.zero_lt_succ N)
        · intro i hi
          change R k (φ (2 * i + 1 + 1)) (φ (2 * i + 1 + 1 + 1))
          simpa [rosenthalTail, mul_add, add_assoc] using h (i + 1) (by omega)

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
