/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fintype.Fin


section

namespace MetaMathlibExt

/-- Descent indicator at position `n`: `1` if `w n > w (n+1)`, else `0`. -/
def desInd {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) : ℕ :=
  if h : n + 1 < K then
    if w ⟨n, by omega⟩ > w ⟨n + 1, h⟩ then 1 else 0
  else 0

/-- Prefix descent count: descents of `w` strictly before position `n`. -/
def desPrefix {m K : ℕ} (w : Fin K → Fin m) : ℕ → ℕ
  | 0 => 0
  | n + 1 => desPrefix w n + desInd w n

end MetaMathlibExt
end
