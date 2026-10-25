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
import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part6


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
