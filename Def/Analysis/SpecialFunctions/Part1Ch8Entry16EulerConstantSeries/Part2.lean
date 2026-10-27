/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum.Parity
import Theorem.Analysis.SpecialFunctions.Part1Ch8Entry16EulerConstantSeries
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

def Gfun : ℕ → ℝ := fun k => (Hsum (Afun (k + 1)) - Hsum (Afun k) - 1) / 2

end
end Entry16Eulerconstantseries
end Ramanujan.Part1Ch8
end
