/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part12
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_pairLift_even (η : ℕ → ℕ) (n : ℕ) :
    rosenthalPairLift η (2 * n) = 2 * η n := by
  have hdiv : 2 * n / 2 = n := by omega
  have hmod : 2 * n % 2 = 0 := by omega
  simp only [rosenthalPairLift, hdiv, hmod, add_zero]

theorem rosenthal_pairLift_odd (η : ℕ → ℕ) (n : ℕ) :
    rosenthalPairLift η (2 * n + 1) = 2 * η n + 1 := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp only [rosenthalPairLift, hdiv, hmod]

theorem rosenthal_pairLift_strictMono
    {η : ℕ → ℕ} (hη : StrictMono η) : StrictMono (rosenthalPairLift η) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [rosenthal_pairLift_even, rosenthal_pairLift_odd]
    omega
  · rw [rosenthal_pairLift_odd,
      show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
      rosenthal_pairLift_even]
    have h : η k < η (k + 1) := by simpa using hη (Nat.lt_succ_self k)
    omega

end FunctionalAnalysis.RosenthalL1Wanted
