import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part5
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Box

/-- Number of subdivisions needed to get diameter below threshold r.
    Each subdivision reduces diameter by factor of √2, so after k iterations:
    diameter ≤ original\_diameter / (√2)^k
    We need (√2)^k > diameter/r, i.e., k > log(diameter/r) / log(√2) = 2·log₂(diameter/r). -/
noncomputable def iter_count {d:ℕ} (B: Box d) (r: ℝ) : ℕ :=
  if B.diameter ≤ 0 then 0
  else if B.diameter < r then 0
  else Nat.ceil (2 * Real.log (B.diameter / r) / Real.log 2) + 1

end Box
