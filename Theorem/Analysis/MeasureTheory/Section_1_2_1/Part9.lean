import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part8
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Remark_1_2_8

/-- U\_real is open (union of open intervals) -/
lemma U_real_isOpen (ε : ℝ) : IsOpen (U_real ε) := by
  apply isOpen_iUnion
  intro _
  exact isOpen_Ioo

/-- U is open in {lean}`EuclideanSpace' 1` -/
lemma U_isOpen (ε : ℝ) : IsOpen (U ε) := by
  apply IsOpen.preimage _ (U_real_isOpen ε)
  exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) _

end Remark_1_2_8
