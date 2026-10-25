/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.BellPermutationsSecondKind.Part4


namespace MetaMathlibExt

/-- RGFs on `Fin n` with exactly `K` values. -/
abbrev Asub (n K : ℕ) := {f : Fin n → Fin n // IsRGF f ∧ numVals f = K}

abbrev Psub (n K : ℕ) := {p : (Fin n → Fin n) × Fin (n+1) //
  IsRGF p.1 ∧ p.2.val ≤ numVals p.1 ∧ numVals (ext p.1 p.2) = K}

end MetaMathlibExt
