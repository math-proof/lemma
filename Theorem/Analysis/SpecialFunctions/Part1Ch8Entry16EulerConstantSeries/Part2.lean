/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum.Parity
import Def.Analysis.SpecialFunctions.Part1Ch8Entry16EulerConstantSeries.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch8

namespace Entry16Eulerconstantseries

open scoped BigOperators Real

open Topology

noncomputable section

theorem hG (k : ℕ) : Gfun k = (Hsum (Afun (k + 1)) - Hsum (Afun k) - 1) / 2 := rfl

theorem hT : ∀ k, Tfun k = ((k + 1 : ℕ) : ℝ) * (Gfun (k + 1) - Gfun k) := by
  intro k
  have e : k + 1 + 1 = k + 2 := by omega
  rw [Tfun_eq, block_eq, hG (k + 1), hG k, e]

theorem key_identity (n : ℕ) :
    2 * ∑ k ∈ Finset.range n, Tfun k =
      ((n : ℝ)) * (Hsum (Afun (n + 1)) - Hsum (Afun n)) - Hsum (Afun n) := by
  induction n with
  | zero => simp [Hsum_zero, show Afun 0 = 0 from rfl]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, hT n, hG n, hG (n + 1)]
    push_cast
    ring

end
end Entry16Eulerconstantseries
end Ramanujan.Part1Ch8
end
