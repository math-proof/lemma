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
public import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

abbrev wmiWordData (m K x : ℕ) (k : Fin m → ℕ) :=
  Σ w : { w : Fin K → Fin m //
      ∀ i, Fintype.card { j : Fin K // w j = i } = k i },
    { e : Fin K → Fin x // IsMono w.1 e }

abbrev wmiPairData (m K x : ℕ) (k : Fin m → ℕ) :=
  { f : Fin K → (Fin x ×ₗ Fin m) //
    Monotone f ∧
      ∀ i, Fintype.card { j : Fin K // (ofLex (f j)).2 = i } = k i }

end MetaMathlibExt
end
