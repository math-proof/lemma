/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean -/

import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.PicardGroup
@[expose] noncomputable section

open scoped nonZeroDivisors
open Module

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-! # Duals of submodules of the fraction field -/


/-- Every dual element is multiplication by a fraction. -/
theorem Submodule.exists_mul_rep (M : Submodule A K) (hM : M ≠ ⊥)
    (f : Module.Dual A M) :
    ∃ x : K, ∀ m : M, algebraMap A K (f m) = x * m := by
  obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff M).mp hM
  let mm : M := ⟨m, hmM⟩
  refine ⟨algebraMap A K (f mm) / m, fun y ↦ ?_⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A ((y : K) / m)
  have hb0 : algebraMap A K b ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors (algebraMap A K) (IsFractionRing.injective A K) hb
  have hcross : algebraMap A K a * m = algebraMap A K b * (y : K) := by
    rw [div_eq_div_iff hb0 hm0] at hab
    simpa [mul_comm] using hab
  have hsub : b • y = a • mm := by
    apply Subtype.ext
    simpa [Algebra.smul_def, mm] using hcross.symm
  have hfrel : b * f y = a * f mm := by
    have := congrArg f hsub
    simpa only [map_smul, smul_eq_mul] using this
  have hmap : algebraMap A K b * algebraMap A K (f y) =
      algebraMap A K a * algebraMap A K (f mm) := by
    simpa only [map_mul] using congrArg (algebraMap A K) hfrel
  apply mul_left_cancel₀ hb0
  rw [hmap]
  calc algebraMap A K a * algebraMap A K (f mm) =
      algebraMap A K (f mm) / m * (algebraMap A K a * m) := by field_simp
    _ = algebraMap A K b * (algebraMap A K (f mm) / m * (y : K)) := by rw [hcross]; ring

omit [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K] in
/-- Multiplication bilinear form is nondegenerate. -/
theorem LinearMap.BilinForm.mul_nondegenerate :
    (LinearMap.mul K K : LinearMap.BilinForm K K).Nondegenerate := by
  constructor
  · intro x hx; simpa using hx 1
  · intro y hy; simpa using hy 1

omit [IsDomain A] [IsFractionRing A K] in
/-- A nonzero submodule spans the fraction field. -/
theorem Submodule.span_coe_eq_top (M : Submodule A K) (hM : M ≠ ⊥) :
    Submodule.span K (M : Set K) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff M).mp hM
  rw [← div_mul_cancel₀ x hm0, ← smul_eq_mul]
  exact Submodule.smul_mem _ (x / m) (Submodule.subset_span hmM)

/-- `dualSubmoduleToDual` for `mul` is surjective on nonzero submodules. -/
theorem Submodule.mul_dualSubmoduleToDual_surjective (M : Submodule A K) (hM : M ≠ ⊥) :
    Function.Surjective (LinearMap.BilinForm.dualSubmoduleToDual
      (LinearMap.mul K K : LinearMap.BilinForm K K) M) := by
  intro f
  obtain ⟨x, hx⟩ := Submodule.exists_mul_rep M hM f
  let xdual : LinearMap.BilinForm.dualSubmodule (LinearMap.mul K K : LinearMap.BilinForm K K) M :=
    ⟨x, fun y hy ↦ by
      change x * y ∈ (1 : Submodule A K)
      rw [← hx ⟨y, hy⟩]
      exact Submodule.mem_one.mpr ⟨f ⟨y, hy⟩, rfl⟩⟩
  refine ⟨xdual, LinearMap.ext fun y ↦ ?_⟩
  apply IsFractionRing.injective A K
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply,
    LinearMap.BilinForm.dualSubmoduleParing_spec, hx]
  rfl

