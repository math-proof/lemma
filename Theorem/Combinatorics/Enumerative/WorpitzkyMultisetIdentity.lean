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
public import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity

public section

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
