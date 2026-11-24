module
public import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
public import Mathlib.Algebra.Order.Floor.Semifield
public import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part7
set_option doc.verso.suggestions false


public section

namespace Remark_1_3_10

/-- {name}`binaryToTernary` lifted to {lean}`EuclideanSpace' 1 → EReal` (called f in informal proof). -/
noncomputable def f_lifted : EuclideanSpace' 1 → EReal :=
  fun x => Real.toEReal (max 0 (binaryToTernary (EuclideanSpace'.equiv_Real x)))

end Remark_1_3_10
