-- Carved from Lemma/Definitions/Def_GaloisRep_InertiaRing.lean: instance decls only.
import Mathlib
import Def.GaloisRep_Flat
import Def.FLTPrelim_Ramification
import Lemma.GaloisRep.InertiaRing

set_option autoImplicit false

noncomputable section

namespace GaloisRep

namespace InertiaRing

variable (A : ValuationSubring ℚ̄)

instance instAlgebraField : Algebra (inertiaRing A) (inertiaField A) :=
  (({ toFun := fun x => ⟨(x : ℚ̄), coe_mem_inertiaField A x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl } : inertiaRing A →+* inertiaField A)).toAlgebra

instance instTowerField : IsScalarTower (inertiaRing A) (inertiaField A) ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance instIsFractionRing : IsFractionRing (inertiaRing A) (inertiaField A) where
  map_units y := by
    apply IsUnit.mk0
    intro h0
    have : ((y.1 : inertiaRing A) : ℚ̄) = 0 := by
      have := congrArg (fun z : inertiaField A => (z : ℚ̄)) h0
      exact this
    exact nonZeroDivisors.ne_zero y.2 (Subtype.ext this)
  surj k := by
    by_cases hk0 : (k : ℚ̄) = 0
    · refine ⟨(0, 1), ?_⟩
      have : k = 0 := Subtype.ext hk0
      rw [this]; simp
    rcases mem_or_inv_mem A k.2 with h | h
    · refine ⟨(⟨k, h⟩, 1), ?_⟩
      show k * algebraMap (inertiaRing A) (inertiaField A) 1 = algebraMap (inertiaRing A) (inertiaField A) ⟨k, h⟩
      rw [map_one, mul_one]
      exact Subtype.ext rfl
    · have hne : (⟨(k : ℚ̄)⁻¹, h⟩ : inertiaRing A) ∈ nonZeroDivisors (inertiaRing A) :=
        mem_nonZeroDivisors_of_ne_zero (fun h0 => hk0 (inv_eq_zero.mp (congrArg (fun z : inertiaRing A => (z : ℚ̄)) h0)))
      refine ⟨(1, ⟨⟨(k : ℚ̄)⁻¹, h⟩, hne⟩), ?_⟩
      show k * algebraMap (inertiaRing A) (inertiaField A) ⟨(k : ℚ̄)⁻¹, h⟩ = algebraMap (inertiaRing A) (inertiaField A) 1
      rw [map_one]
      apply Subtype.ext
      show (k : ℚ̄) * (k : ℚ̄)⁻¹ = 1
      exact mul_inv_cancel₀ hk0
  exists_of_eq {a b} h := ⟨1, by
    have : ((a : ℚ̄)) = b := by
      have := congrArg (fun z : inertiaField A => (z : ℚ̄)) h
      exact this
    rw [Subtype.ext this]⟩

end InertiaRing

end GaloisRep

end

