module

public import Mathlib

public section

open scoped DualNumber RightActions

universe u

namespace Representation

variable (k : Type*) {A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {G : Type*} [Monoid G]


@[simp]
public theorem adjointAux_one : adjointAux k (1 : Aˣ) = LinearMap.id := by
  ext a
  simp


public theorem adjointAux_mul (u v : Aˣ) :
    adjointAux k (u * v) = (adjointAux k u).comp (adjointAux k v) := by
  ext a
  simp only [adjointAux_apply, LinearMap.comp_apply, mul_inv_rev, Units.val_mul, mul_assoc]


@[simp]
public theorem adjoint_apply (ρ₀ : G →* Aˣ) (g : G) (a : A) :
    adjoint k ρ₀ g a = ↑(ρ₀ g) * a * ↑(ρ₀ g)⁻¹ := rfl

end Representation

namespace TrivSqZeroExt

variable {A : Type*} [Ring A]


@[simp] public theorem dualUnit_val_fst (u : Aˣ) (m : A) : (dualUnit u m : A[ε]).fst = ↑u := rfl


@[simp] public theorem dualUnit_val_snd (u : Aˣ) (m : A) : (dualUnit u m : A[ε]).snd = m * ↑u := rfl


@[simp] public theorem dualUnit_inv_val_fst (u : Aˣ) (m : A) :
    (((dualUnit u m)⁻¹ : (A[ε])ˣ) : A[ε]).fst = ↑u⁻¹ := rfl


@[simp] public theorem dualUnit_inv_val_snd (u : Aˣ) (m : A) :
    (((dualUnit u m)⁻¹ : (A[ε])ˣ) : A[ε]).snd = -(↑u⁻¹ * m) := rfl


@[simp]
public theorem dualUnit_one_zero : dualUnit (1 : Aˣ) (0 : A) = 1 := by
  apply Units.ext
  exact TrivSqZeroExt.ext (by simp) (by simp)


public theorem dualUnit_mul_dualUnit (u v : Aˣ) (m n : A) :
    dualUnit u m * dualUnit v n = dualUnit (u * v) (↑u * n * ↑u⁻¹ + m) := by
  apply Units.ext
  refine TrivSqZeroExt.ext (by simp) ?_
  show (dualUnit u m : A[ε]).fst •> (dualUnit v n : A[ε]).snd
        + (dualUnit u m : A[ε]).snd <• (dualUnit v n : A[ε]).fst
      = (↑u * n * ↑u⁻¹ + m) * ↑(u * v)
  simp only [dualUnit_val_fst, dualUnit_val_snd, smul_eq_mul, op_smul_eq_mul, Units.val_mul,
    add_mul, mul_assoc, Units.inv_mul_cancel_left]


public theorem eq_dualUnit_of_fst_eq {w : (A[ε])ˣ} {u : Aˣ} (h : (w : A[ε]).fst = ↑u) :
    w = dualUnit u ((w : A[ε]).snd * ↑u⁻¹) := by
  apply Units.ext
  exact TrivSqZeroExt.ext h (Units.inv_mul_cancel_right _ u).symm

end TrivSqZeroExt

namespace groupCohomology

open TrivSqZeroExt

variable {k A G : Type u} [CommRing k] [Ring A] [Algebra k A] [Group G]


@[simp]
public theorem adjointRep_ρ_apply (ρ₀ : G →* Aˣ) (g : G) (a : A) :
    (adjointRep k ρ₀).ρ g a = ↑(ρ₀ g) * a * ↑(ρ₀ g)⁻¹ := rfl


public theorem dualLift_ext {ρ₀ : G →* Aˣ} {ρ ρ' : G →* (A[ε])ˣ}
    (hρ : IsDualLift ρ₀ ρ) (hρ' : IsDualLift ρ₀ ρ')
    (h : dualLiftToCochain ρ₀ ρ = dualLiftToCochain ρ₀ ρ') : ρ = ρ' := by
  refine MonoidHom.ext fun g => ?_
  rw [eq_dualUnit_of_fst_eq (hρ g), eq_dualUnit_of_fst_eq (hρ' g)]
  exact congrArg _ (congrFun h g)


public theorem dualLiftToCochain_mem_cocycles₁ {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ}
    (hρ : IsDualLift ρ₀ ρ) :
    dualLiftToCochain ρ₀ ρ ∈ cocycles₁ (adjointRep k ρ₀) := by
  rw [mem_cocycles₁_iff]
  intro g h
  show dualLiftToCochain ρ₀ ρ (g * h)
      = ↑(ρ₀ g) * dualLiftToCochain ρ₀ ρ h * ↑(ρ₀ g)⁻¹ + dualLiftToCochain ρ₀ ρ g
  unfold dualLiftToCochain
  simp only [map_mul, Units.val_mul, snd_mul, mul_inv_rev, hρ g, hρ h, smul_eq_mul,
    op_smul_eq_mul, add_mul, mul_assoc, Units.mul_inv_cancel_left]


@[simp]
public theorem dualLiftToCocycle_coe {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) :
    ((dualLiftToCocycle k hρ : cocycles₁ (adjointRep k ρ₀)) : G → A)
      = dualLiftToCochain ρ₀ ρ := rfl


@[simp]
public theorem cocycleToDualLift_apply (ρ₀ : G →* Aˣ) (c : cocycles₁ (adjointRep k ρ₀)) (g : G) :
    cocycleToDualLift ρ₀ c g = dualUnit (ρ₀ g) (c g) := rfl


public theorem isDualLift_cocycleToDualLift (ρ₀ : G →* Aˣ) (c : cocycles₁ (adjointRep k ρ₀)) :
    IsDualLift ρ₀ (cocycleToDualLift ρ₀ c) := fun _ => rfl


@[simp]
public theorem dualLiftEquivCocycles₁_apply (ρ₀ : G →* Aˣ) (ρ : {ρ : G →* (A[ε])ˣ // IsDualLift ρ₀ ρ}) :
    dualLiftEquivCocycles₁ k ρ₀ ρ = dualLiftToCocycle k ρ.2 := rfl


@[simp]
public theorem dualLiftEquivCocycles₁_symm_apply (ρ₀ : G →* Aˣ) (c : cocycles₁ (adjointRep k ρ₀)) :
    ((dualLiftEquivCocycles₁ k ρ₀).symm c : G →* (A[ε])ˣ) = cocycleToDualLift ρ₀ c := rfl

end groupCohomology
