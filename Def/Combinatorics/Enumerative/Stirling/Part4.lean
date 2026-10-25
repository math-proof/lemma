/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Theorem.Combinatorics.Enumerative.Stirling.Part3
/-!
# Permutations and unsigned Stirling numbers

This file identifies unsigned Stirling numbers of the first kind with permutations having a
prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def decomposeFinZeroQuotientEquiv {n : ℕ}
    (e : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.Perm.decomposeFin.symm (0, e))) ≃
      Option (Quotient (Equiv.Perm.SameCycle.setoid e)) := by
  let toBase : Fin (n + 1) → Option (Quotient (Equiv.Perm.SameCycle.setoid e)) :=
    Fin.cases none (fun x => some (Quotient.mk _ x))
  have toBase_eq (x y : Fin (n + 1))
      (hxy : (Equiv.Perm.decomposeFin.symm (0, e)).SameCycle x y) :
      toBase x = toBase y := by
    cases x using Fin.cases with
    | zero =>
        cases y using Fin.cases with
        | zero => rfl
        | succ b =>
            have hfix : Function.IsFixedPt
                (Equiv.Perm.decomposeFin.symm (0, e)) (0 : Fin (n + 1)) := by
              change Equiv.Perm.decomposeFin.symm (0, e) 0 = 0
              simp
            have h : (0 : Fin (n + 1)) = b.succ := hxy.eq_of_left hfix
            exact (Fin.succ_ne_zero b h.symm).elim
    | succ a =>
        cases y using Fin.cases with
        | zero =>
            have hfix : Function.IsFixedPt
                (Equiv.Perm.decomposeFin.symm (0, e)) (0 : Fin (n + 1)) := by
              change Equiv.Perm.decomposeFin.symm (0, e) 0 = 0
              simp
            have h : a.succ = (0 : Fin (n + 1)) := hxy.eq_of_right hfix
            exact (Fin.succ_ne_zero a h).elim
        | succ b =>
            apply congrArg some
            apply Quotient.sound
            exact (decomposeFin_zero_sameCycle_succ_iff e a b).mp hxy
  refine Equiv.ofBijective (Quotient.lift toBase toBase_eq) ?_
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro x y hxy
    change toBase x = toBase y at hxy
    apply Quotient.sound
    cases x using Fin.cases with
    | zero =>
        cases y using Fin.cases with
        | zero => exact Equiv.Perm.SameCycle.rfl
        | succ v => simp [toBase] at hxy
    | succ u =>
        cases y using Fin.cases with
        | zero => simp [toBase] at hxy
        | succ v =>
            apply (decomposeFin_zero_sameCycle_succ_iff e u v).mpr
            have hquot : (Quotient.mk _ u : Quotient (Equiv.Perm.SameCycle.setoid e)) =
                Quotient.mk _ v := by simpa [toBase] using hxy
            exact Quotient.exact hquot
  · rintro (_ | a)
    · exact ⟨Quotient.mk _ 0, rfl⟩
    · refine Quotient.inductionOn a ?_
      intro x
      exact ⟨Quotient.mk _ x.succ, rfl⟩

def subtypeProdEquivSigma {α β : Type*} (p : α × β → Prop) :
    {x : α × β // p x} ≃ Σ a : α, {b : β // p (a, b)} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
