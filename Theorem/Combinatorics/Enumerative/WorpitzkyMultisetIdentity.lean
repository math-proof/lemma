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
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity


section

namespace MetaMathlibExt

theorem desPrefix_zero {m K : ℕ} (w : Fin K → Fin m) :
    desPrefix w 0 = 0 :=
  rfl

theorem desPrefix_succ {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) :
    desPrefix w (n + 1) = desPrefix w n + desInd w n :=
  rfl

theorem desPrefix_le_succ {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) :
    desPrefix w n ≤ desPrefix w (n + 1) := by
  rw [desPrefix_succ]
  exact Nat.le_add_right _ _

theorem desPrefix_mono {m K : ℕ} (w : Fin K → Fin m) :
    Monotone (desPrefix w) :=
  monotone_nat_of_le_succ (desPrefix_le_succ w)

theorem desPrefix_le_self {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) :
    desPrefix w n ≤ n := by
  induction n with
  | zero =>
    rw [desPrefix_zero]
  | succ n ih =>
    rw [desPrefix_succ]
    have h1 := desInd_le_one w n
    omega

theorem desInd_eq_zero_of_ge {m K : ℕ} (w : Fin K → Fin m)
    (n : ℕ) (h : ¬ n + 1 < K) : desInd w n = 0 := by
  unfold desInd
  simp only [h, dite_false]

theorem desPrefix_le_total {m K : ℕ} (w : Fin K → Fin m)
    (n : ℕ) (h : n ≤ K) : desPrefix w n ≤ desPrefix w K :=
  (desPrefix_mono w) h

end MetaMathlibExt
end
