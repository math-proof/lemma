/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.NormNum.Parity
public import Theorem.Analysis.SpecialFunctions.Part1Ch8Entry16EulerConstantSeries.Part2

@[expose] public section

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

def err : ℕ → ℝ := fun n => Hsum n - Real.log ((n : ℝ)) - Real.eulerMascheroniConstant

end
end Entry16Eulerconstantseries
end Ramanujan.Part1Ch8
end
