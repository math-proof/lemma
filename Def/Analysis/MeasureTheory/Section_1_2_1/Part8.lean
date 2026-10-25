import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part8
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Remark_1_2_8

/-- The counterexample set U: union of open intervals around rationals in \[0,1\].
    U(ε) = ⋃\_\{n:ℕ\} (q\_n - ε/2^\{n+1\}, q\_n + ε/2^\{n+1\}) -/
noncomputable def U_real (ε : ℝ) : Set ℝ :=
  ⋃ n : ℕ, Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1))

/-- The set U lifted to {lean}`EuclideanSpace' 1` -/
noncomputable def U (ε : ℝ) : Set (EuclideanSpace' 1) :=
  EuclideanSpace'.equiv_Real ⁻¹' (U_real ε)

end Remark_1_2_8
