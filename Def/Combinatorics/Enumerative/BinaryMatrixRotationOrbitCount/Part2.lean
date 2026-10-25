/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Combinatorics.Colex
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Theorem.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount.Part2


namespace MetaMathlibExt

open scoped BigOperators

noncomputable def fixedByEquiv {m n : ℕ} [NeZero m] [NeZero n] (g : Fin m × Fin n) :
    (AddAction.fixedBy (Fin m → Fin n → Bool) g)
      ≃ {F : (Fin m × Fin n) → Bool // ∀ p, F (p + g) = F p} where
  toFun x := ⟨fun p => x.1 p.1 p.2, by
    intro p
    have hx : g +ᵥ x.1 = x.1 := x.2
    have h := congrFun (congrFun hx p.1) p.2
    rw [shift_vadd_apply] at h
    exact h⟩
  invFun F := ⟨fun r s => F.1 (r, s), by
    change g +ᵥ (fun r s => F.1 (r, s)) = (fun r s => F.1 (r, s))
    funext r s
    rw [shift_vadd_apply]
    exact F.2 (r, s)⟩
  left_inv x := by ext r s; rfl
  right_inv F := by ext p; rfl

end MetaMathlibExt
