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
import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part2


section

namespace MetaMathlibExt

/-- Forward shift: subtract prefix descents from a monotone map. -/
def shiftFwd {m K x : ℕ} (w : Fin K → Fin m)
    (e : Fin K → Fin x) (hmono : IsMono w e) :
    Fin K → Fin (x - desPrefix w K) :=
  fun j =>
    have h1 : desPrefix w j.val ≤ (e j).val :=
      mono_lower hmono j.val j.isLt
    have h2 : (e j).val +
        (desPrefix w K - desPrefix w j.val) < x :=
      mono_upper hmono j.val j.isLt
    have h3 : desPrefix w j.val ≤ desPrefix w K :=
      desPrefix_le_total w j.val (by omega)
    ⟨(e j).val - desPrefix w j.val, by omega⟩

/-- Backward shift: add prefix descents to a monotone map. -/
def shiftBwd {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) :
    Fin K → Fin x :=
  fun j =>
    if hle : desPrefix w K ≤ x then
      have h1 : (g j).val < x - desPrefix w K := (g j).isLt
      have h2 : desPrefix w j.val ≤ desPrefix w K :=
        desPrefix_le_total w j.val (by omega)
      ⟨(g j).val + desPrefix w j.val, by omega⟩
    else
      have hx : x ≤ desPrefix w K := by omega
      have h0 : x - desPrefix w K = 0 :=
        Nat.sub_eq_zero_of_le hx
      Fin.elim0 (h0 ▸ g j)

end MetaMathlibExt
end
