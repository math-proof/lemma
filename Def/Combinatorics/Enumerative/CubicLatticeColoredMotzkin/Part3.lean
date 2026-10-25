/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
import Lemma.Finset.Enumerative.ULDMotzkinNumberOfRankR
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Theorem.Combinatorics.Enumerative.CubicLatticeColoredMotzkin.Part2


namespace MetaMathlibExt

/-- Pointwise equivalence of steps. -/
def stepEquiv (n : ℕ) : (Fin (n + 1) × Bool) ≃ Sum Bool (Fin (2 * n)) :=
  ⟨cubeToMotzkinStep n, motzkinToCubeStep n, step_left_inv n, step_right_inv n⟩

/-- Colored Motzkin steps as `(u,l,d)`-Motzkin steps of rank `1` with one up color, `2 * n`
level colors, and one down color. -/
def motzkinStepEquiv (n : ℕ) :
    Sum Bool (Fin (2 * n)) ≃ ULDMotzkin.ULDMotzkinStep 1 (fun _ => 1) (2 * n) (fun _ => 1) where
  toFun := Sum.elim (fun b => if b then Sum.inl ⟨0, 0⟩ else Sum.inr (Sum.inr ⟨0, 0⟩))
    (fun j => Sum.inr (Sum.inl j))
  invFun s := match s with
    | Sum.inl _ => Sum.inl true
    | Sum.inr (Sum.inl j) => Sum.inr j
    | Sum.inr (Sum.inr _) => Sum.inl false
  left_inv y := by
    rcases y with (_ | _) | _ <;> rfl
  right_inv s := by
    rcases s with ⟨j, c⟩ | j | ⟨j, c⟩
    · obtain rfl := Subsingleton.elim j 0
      obtain rfl := Subsingleton.elim c 0
      rfl
    · rfl
    · obtain rfl := Subsingleton.elim j 0
      obtain rfl := Subsingleton.elim c 0
      rfl

end MetaMathlibExt
