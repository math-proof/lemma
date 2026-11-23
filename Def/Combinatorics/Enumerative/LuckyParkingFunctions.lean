/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions

@[expose] public section

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
