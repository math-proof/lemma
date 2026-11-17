/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Fintype.Fin

@[expose] public section

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
