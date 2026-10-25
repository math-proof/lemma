import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part11
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


/- ========================================================================
   End of Helpers for remark 1.2.8
   ======================================================================== -/

/-- Remark 1.2.8: There exists a bounded open set that is not Jordan measurable.
    Proof sketch: Take U = ⋃\_\{n\} (q\_n - ε/2^\{n+1\}, q\_n + ε/2^\{n+1\}) where \{q\_n\} enumerates ℚ ∩ \[0,1\].
    U is open and bounded. By countable subadditivity, m\*(U) ≤ 2ε.
    By density of ℚ, closure(U) ⊇ \[0,1\], so m\*,J(U) ≥ 1.
    For ε = 1/3, we get m\*(U) ≤ 2/3 < 1 ≤ m\*,J(U), contradicting Jordan measurability. -/
def AlmostDisjoint {d:ℕ} (B B': Box d) : Prop := interior B.toSet ∩ interior B'.toSet = ∅

