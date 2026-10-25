/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
/-!
# Permutations and unsigned Stirling numbers

This file identifies unsigned Stirling numbers of the first kind with permutations having a
prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

/-- The number of cycles of a finite permutation, including fixed points as one-cycles. -/
noncomputable def cycleQuotientCount {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) : ℕ :=
  Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ))

noncomputable def cycleQuotientEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ≃
      Function.fixedPoints σ ⊕ σ.cycleFactorsFinset := by
  classical
  let toCycle : α → Function.fixedPoints σ ⊕ σ.cycleFactorsFinset := fun x =>
    if hx : σ x = x then
      Sum.inl ⟨x, hx⟩
    else
      Sum.inr ⟨σ.cycleOf x,
        Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hx)⟩
  have toCycle_eq (x y : α) (hxy : σ.SameCycle x y) : toCycle x = toCycle y := by
    by_cases hx : σ x = x
    · have hxy' : x = y := hxy.eq_of_left hx
      subst y
      rfl
    · have hy : σ y ≠ y := fun hy => hx (hxy.apply_eq_self_iff.mpr hy)
      simp only [toCycle, hx, hy, dite_false, Sum.inr.injEq, Subtype.mk.injEq]
      exact hxy.cycleOf_eq
  refine Equiv.ofBijective (Quotient.lift toCycle toCycle_eq) ?_
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro x y hxy
    change toCycle x = toCycle y at hxy
    apply Quotient.sound
    by_cases hx : σ x = x
    · by_cases hy : σ y = y
      · simp only [toCycle, hx, hy, dite_true, Sum.inl.injEq] at hxy
        exact (congrArg Subtype.val hxy).sameCycle σ
      · simp only [toCycle, hx, hy, dite_true, dite_false] at hxy
        exact (Sum.inl_ne_inr hxy).elim
    · by_cases hy : σ y = y
      · simp only [toCycle, hx, hy, dite_true, dite_false] at hxy
        exact (Sum.inr_ne_inl hxy).elim
      · simp only [toCycle, hx, hy, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at hxy
        exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
          (Equiv.Perm.mem_support.mpr hx) (Equiv.Perm.mem_support.mpr hy)).mpr hxy
  · rintro (x | c)
    · refine ⟨Quotient.mk _ x.1, ?_⟩
      change toCycle x.1 = Sum.inl x
      have hx : σ x.1 = x.1 := x.2
      simp only [toCycle, hx, dite_true]
    · obtain ⟨x, hxc⟩ :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
      have hx : σ x ≠ x := Equiv.Perm.mem_support.mp
        (Equiv.Perm.mem_cycleFactorsFinset_support_le c.property hxc)
      refine ⟨Quotient.mk _ x, ?_⟩
      change toCycle x = Sum.inr c
      simp only [toCycle, hx, dite_false, Sum.inr.injEq]
      apply Subtype.ext
      exact (Equiv.Perm.cycle_is_cycleOf hxc c.property).symm

end MetaMathlibExt
