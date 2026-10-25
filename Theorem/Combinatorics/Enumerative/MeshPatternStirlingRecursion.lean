/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part2


section

namespace MetaMathlibExt

/-- `Phi` sends the insertion position to `0`. -/
lemma Phi_apply_p (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m)) :
    Phi m p τ p = 0 := by
  have h1 : p.cycleRange p = 0 := Fin.cycleRange_self p
  have h2 : (Equiv.Perm.decomposeFin.symm (0, τ)) (0 : Fin (m.succ)) = 0 :=
    Equiv.Perm.decomposeFin_symm_apply_zero 0 τ
  unfold Phi
  rw [Equiv.Perm.mul_apply, h1, h2]

/-- `Phi` sends other positions to shifted values of `τ`. -/
lemma Phi_apply_succAbove (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (j : Fin m) :
    Phi m p τ (p.succAbove j) = (τ j).succ := by
  have h1 : p.cycleRange (p.succAbove j) = j.succ := Fin.cycleRange_succAbove p j
  have h2 : (Equiv.Perm.decomposeFin.symm (0, τ)) (j.succ) = ((τ j).succ) := by
    have h := Equiv.Perm.decomposeFin_symm_apply_succ τ (0 : Fin (m + 1)) j
    rw [Equiv.swap_self] at h
    exact h
  unfold Phi
  rw [Equiv.Perm.mul_apply, h1, h2]

/-- The insertion position is the unique preimage of `0` under `Phi`. -/
lemma Phi_preimage_zero (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (x : Fin (m.succ)) (hx : Phi m p τ x = 0) : x = p := by
  have hD0 : (Equiv.Perm.decomposeFin.symm (0, τ)) (0 : Fin (m.succ)) = 0 :=
    Equiv.Perm.decomposeFin_symm_apply_zero 0 τ
  have hCp : p.cycleRange p = 0 := Fin.cycleRange_self p
  unfold Phi at hx
  rw [Equiv.Perm.mul_apply] at hx
  have hCx : p.cycleRange x = 0 := by
    have h2 : (Equiv.Perm.decomposeFin.symm (0, τ)) (p.cycleRange x) =
        (Equiv.Perm.decomposeFin.symm (0, τ)) 0 := by rw [hx, hD0]
    exact (Equiv.Perm.decomposeFin.symm (0, τ)).injective h2
  exact p.cycleRange.injective (hCx.trans hCp.symm)

/-- `Phi` is injective as a map on pairs. -/
lemma Phi_injective (m : ℕ) : Function.Injective
    (fun pr : Fin (m.succ) × Equiv.Perm (Fin m) => Phi m pr.1 pr.2) := by
  rintro ⟨p, τ⟩ ⟨p', τ'⟩ h
  have h' : Phi m p τ = Phi m p' τ' := h
  have hpp : p = p' := by
    have h0 : Phi m p' τ' p = 0 := by
      have hpp0 : Phi m p τ p = 0 := Phi_apply_p m p τ
      rwa [h'] at hpp0
    exact Phi_preimage_zero m p' τ' p h0
  subst hpp
  have hτ : τ = τ' := by
    apply Equiv.ext
    intro j
    have hc := congrArg (fun σ : Equiv.Perm (Fin (m.succ)) => σ (p.succAbove j)) h'
    rw [Phi_apply_succAbove, Phi_apply_succAbove] at hc
    exact Fin.succ_injective m hc
  rw [hτ]

end MetaMathlibExt
end
