/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.BellPermutationsSecondKind.Part2


namespace MetaMathlibExt

/-! ## Part C: counting RGFs by number of values -/

/-- Extend an RGF on `Fin n` by one more value. -/
def ext {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) : Fin (n+1) → Fin (n+1) :=
  Fin.snoc (fun i => (g i).castSucc) v

end MetaMathlibExt
