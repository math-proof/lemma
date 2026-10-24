/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/


import sympy.atlas.Order.PosetMatrix
import Lemma.Set.PosetMatrix
import Mathlib.Tactic.FinCases

namespace MetaMathlibExt

/-- The empty `0 × 0` matrix is vacuously a poset matrix. -/
private def emptyMat : Matrix (Fin 0) (Fin 0) Bool :=
  fun _ _ => false

example : IsPosetMatrix 0 emptyMat := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- The `1 × 1` matrix whose single (diagonal) entry is `true`. -/
private def oneMat : Matrix (Fin 1) (Fin 1) Bool :=
  fun _ _ => true

example : IsPosetMatrix 1 oneMat := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    intro j
    fin_cases j
    decide
  · intro i
    fin_cases i
    decide
  · intro i
    fin_cases i
    intro j
    fin_cases j
    intro k
    fin_cases k
    decide

/-- The `2 × 2` total-order matrix: entries on and above the diagonal are `true`. -/
private def twoMat : Matrix (Fin 2) (Fin 2) Bool :=
  fun i j => decide ((i : ℕ) ≤ (j : ℕ))

example : twoMat 1 0 = false :=
  IsPosetMatrix.upper twoMat_ok 1 0 (by decide)

example : twoMat 1 1 = true :=
  IsPosetMatrix.diagonal twoMat_ok 1

example : twoMat 0 1 = true :=
  IsPosetMatrix.transitive twoMat_ok 0 0 1 rfl rfl

example : IsPosetMatrix.Rel twoMat 0 0 :=
  IsPosetMatrix.rel_refl twoMat_ok 0

example : IsPosetMatrix.Rel twoMat 0 0 :=
  IsPosetMatrix.rel_trans twoMat_ok 0 0 0
    (IsPosetMatrix.rel_refl twoMat_ok 0)
    (IsPosetMatrix.rel_refl twoMat_ok 0)

/-- A `3 × 3` upper-triangular Boolean matrix with `true` diagonal that fails
transitivity at `(0, 1)`, `(1, 2)`: the `(0, 2)`-entry is `false`. -/
private def badMat : Matrix (Fin 3) (Fin 3) Bool :=
  fun i j => decide ((i : ℕ) ≤ (j : ℕ) ∧ ¬((i : ℕ) = 0 ∧ (j : ℕ) = 2))

example : ¬ IsPosetMatrix 3 badMat := by
  intro h
  have h01 : badMat 0 1 = true := rfl
  have h12 : badMat 1 2 = true := rfl
  have h02f : badMat 0 2 = false := rfl
  have h02t : badMat 0 2 = true :=
    IsPosetMatrix.transitive h 0 1 2 h01 h12
  rw [h02f] at h02t
  exact Bool.false_ne_true h02t

end MetaMathlibExt
