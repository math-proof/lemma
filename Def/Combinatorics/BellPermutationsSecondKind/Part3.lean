/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.BellPermutationsSecondKind.Part2

@[expose] public section

namespace MetaMathlibExt

/-! ## Part C: counting RGFs by number of values -/

/-- Extend an RGF on `Fin n` by one more value. -/
def ext {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) : Fin (n+1) → Fin (n+1) :=
  Fin.snoc (fun i => (g i).castSucc) v

end MetaMathlibExt
