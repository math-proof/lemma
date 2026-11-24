module
public import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
public import Theorem.Analysis.Misc.NatBitwise
public import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part6


public section

namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-! ## Single-family atoms (k' = 0 specialization)

When working with a single family of sets (no second family to compare against),
we specialize the atom machinery with k' = 0. -/

/-- The atom for a single family of sets, using k' = 0 in the general atom definition -/
def singleAtom {X : Type*} {k : ℕ} (E : Fin k → Set X) (n : Fin (2^k)) : Set X :=
  atom E (fun _ : Fin 0 => ∅) ⟨n.val, by simp only [add_zero]; exact n.isLt⟩

end UnsignedSimpleFunction.IntegralWellDef
