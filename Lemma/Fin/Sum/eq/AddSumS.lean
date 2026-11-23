import Def.Data.Fin.Rope
import Initialize.Tactic.Attr.Basic
import Mathlib


/-- Splitting a sum over `Fin (d + d)` into its even and odd interleaved coordinates. -/
@[path]
private lemma main
  [AddCommMonoid α]
-- given
  (f : Fin (d + d) → α) :
-- imply
  ∑ i, f i = ∑ t : Fin d, f t.ropeEven + ∑ t : Fin d, f t.ropeOdd := by
-- proof
  let e : Fin d ⊕ Fin d ≃ Fin (d + d) :=
    { toFun := fun
        | Sum.inl t => t.ropeEven
        | Sum.inr t => t.ropeOdd
      invFun := fun i =>
        if (i : ℕ) % 2 = 0 then
          Sum.inl ⟨(i : ℕ) / 2, by have := i.isLt; omega⟩
        else
          Sum.inr ⟨(i : ℕ) / 2, by have := i.isLt; omega⟩
      left_inv := by
        intro s
        cases s with
        | inl t =>
          simp [Fin.ropeEven, show 2 * (t : ℕ) % 2 = 0 by omega]
        | inr t =>
          have hod : (2 * (t : ℕ) + 1) % 2 = 1 := by omega
          simp [Fin.ropeOdd, hod, show (1 : ℕ) ≠ 0 by decide]
          apply Fin.ext
          change (2 * (t : ℕ) + 1) / 2 = (t : ℕ)
          rw [Nat.mul_add_div (by decide : 0 < 2)]
          simp
      right_inv := by
        intro i
        ext
        if h : (i : ℕ) % 2 = 0 then
          simp [Fin.ropeEven, h]
          omega
        else
          simp [Fin.ropeOdd, h]
          omega }
  have hs : ∑ i, f i = ∑ s : Fin d ⊕ Fin d, f (e s) := (e.sum_comp f).symm
  rw [hs, Fintype.sum_sum_type]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e]
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e]


-- created on 2026-11-23
