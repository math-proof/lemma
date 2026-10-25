/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.FunctionalAnalysis.RosenthalL1.Part2
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_initialSegment_succ (φ : ℕ → ℕ) (n : ℕ) :
    rosenthalInitialSegment φ (n + 1) =
      φ 0 :: rosenthalInitialSegment (rosenthalTail φ) n := by
  simp [rosenthalInitialSegment, List.range_succ_eq_map, rosenthalTail,
    Function.comp_def]

theorem rosenthal_tail_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalTail φ) := by
  exact hφ.comp fun _ _ h => Nat.add_lt_add_right h 1

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
