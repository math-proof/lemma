import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_exists_residueMap_of_surjective_residue_comp_algebraMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_residueMap_of_surjective_residue_comp_algebraMap.lean)
-/
@[main]
private lemma main
  [CommRing Λ] [IsLocalRing Λ] [Field k] [CommRing T] [IsLocalRing T] [Algebra Λ T]
  {res₀ : Λ →+* k}
-- given
  (hres₀ : Function.Surjective res₀)
  (hker₀ : RingHom.ker res₀ = maximalIdeal Λ)
  (hT : Function.Surjective (⇑(residue T) ∘ ⇑(algebraMap Λ T))) :
-- imply
  ∃ resT : T →+* k, Function.Surjective resT ∧ RingHom.ker resT = maximalIdeal T ∧
      ∀ w : Λ, resT (algebraMap Λ T w) = res₀ w := by
-- proof
  classical
  let g : Λ →+* ResidueField T := (residue T).comp (algebraMap Λ T)
  have hg : Function.Surjective g := hT
  have hkerg : RingHom.ker g = maximalIdeal Λ :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g hg)
  let φ : Λ ⧸ RingHom.ker g →+* k := Ideal.Quotient.lift (RingHom.ker g) res₀ (by
    intro a ha
    rw [hkerg, ← hker₀] at ha
    exact ha)
  have hφ : ∀ w, φ (Ideal.Quotient.mk _ w) = res₀ w := fun w => Ideal.Quotient.lift_mk _ _ _
  let e : Λ ⧸ RingHom.ker g ≃+* ResidueField T := RingHom.quotientKerEquivOfSurjective hg
  have he : ∀ w, e (Ideal.Quotient.mk _ w) = g w := fun w => RingHom.kerLift_mk g w
  let resT : T →+* k := (φ.comp e.symm.toRingHom).comp (residue T)
  have hcomp : ∀ w : Λ, resT (algebraMap Λ T w) = res₀ w := by
    intro w
    show φ (e.symm (residue T (algebraMap Λ T w))) = res₀ w
    have h1 : residue T (algebraMap Λ T w) = g w := rfl
    rw [h1, ← he w, e.symm_apply_apply, hφ]
  have hsurj : Function.Surjective resT := by
    intro x
    obtain ⟨w, hw⟩ := hres₀ x
    exact ⟨algebraMap Λ T w, (hcomp w).trans hw⟩
  exact ⟨resT, hsurj, IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resT hsurj), hcomp⟩


-- created on 2026-10-05
