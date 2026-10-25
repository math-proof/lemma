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
import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity


section

namespace MetaMathlibExt

/-- Weakly increasing with strict increases at descents of `w`. -/
def IsMono {m K x : ℕ} (w : Fin K → Fin m)
    (e : Fin K → Fin x) : Prop :=
  Monotone e ∧
    ∀ (j : Fin K) (h : j.val + 1 < K),
      w j > w ⟨j.val + 1, h⟩ → e j < e ⟨j.val + 1, h⟩

end MetaMathlibExt
end
