/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions


section

namespace MetaMathlibExt

def markedEquivSigma (n : ℕ) :
    Marked n ≃
      ↥((Finset.univ.filter
        (fun a : Fin n → Fin n => Monotone a ∧ ∀ i, (a i).val ≤ i.val)).sigma
        (fun a => Finset.univ.filter (fun i : Fin n => a i = i))) where
  toFun x :=
    ⟨⟨x.1.1, x.2.1⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1.2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2.2⟩⟩⟩
  invFun y :=
    ⟨⟨y.1.1, (Finset.mem_filter.mp (Finset.mem_sigma.mp y.2).1).2⟩,
      ⟨y.1.2, (Finset.mem_filter.mp (Finset.mem_sigma.mp y.2).2).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def splitLower (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) : Fin i0.val → Fin i0.val :=
  fun j => ⟨(a ⟨j.val, by omega⟩).val, by
    have h := ha.2 ⟨j.val, by omega⟩
    simp only at h ⊢
    omega⟩

end MetaMathlibExt
end
