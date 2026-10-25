import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part4


namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- Helper: construct atom index from membership pattern.
    The atom index encodes x's membership in each set as bits. -/
noncomputable def atomIndexOf {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) : ℕ :=
  (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => 2^j.val) +
  (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => 2^(k + j'.val))

end UnsignedSimpleFunction.IntegralWellDef
