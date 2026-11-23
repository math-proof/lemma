/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.BellPermutationsSecondKind.Part4

@[expose] public section


namespace MetaMathlibExt

/-- RGFs on `Fin n` with exactly `K` values. -/
abbrev Asub (n K : ℕ) := {f : Fin n → Fin n // IsRGF f ∧ numVals f = K}

abbrev Psub (n K : ℕ) := {p : (Fin n → Fin n) × Fin (n+1) //
  IsRGF p.1 ∧ p.2.val ≤ numVals p.1 ∧ numVals (ext p.1 p.2) = K}

end MetaMathlibExt
