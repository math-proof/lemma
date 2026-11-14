import Mathlib

open scoped DualNumber RightActions

universe u

namespace Representation

variable (k : Type*) {A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {G : Type*} [Monoid G]

@[simps]
def adjointAux (u : Aˣ) : A →ₗ[k] A where
  toFun a := ↑u * a * ↑u⁻¹
  map_add' a b := by rw [mul_add, add_mul]
  map_smul' c a := by
    rw [RingHom.id_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

@[simp]
lemma adjointAux_one : adjointAux k (1 : Aˣ) = LinearMap.id := by
  ext a
  simp

lemma adjointAux_mul (u v : Aˣ) :
    adjointAux k (u * v) = (adjointAux k u).comp (adjointAux k v) := by
  ext a
  simp only [adjointAux_apply, LinearMap.comp_apply, mul_inv_rev, Units.val_mul, mul_assoc]

def adjoint (ρ₀ : G →* Aˣ) : Representation k G A where
  toFun g := adjointAux k (ρ₀ g)
  map_one' := by
    ext a
    simp
  map_mul' g h := by
    ext a
    simp only [map_mul, adjointAux_mul, LinearMap.comp_apply, Module.End.mul_apply]

@[simp]
lemma adjoint_apply (ρ₀ : G →* Aˣ) (g : G) (a : A) :
    adjoint k ρ₀ g a = ↑(ρ₀ g) * a * ↑(ρ₀ g)⁻¹ := rfl

end Representation

namespace TrivSqZeroExt

variable {A : Type*} [Ring A]

def dualUnit (u : Aˣ) (m : A) : (A[ε])ˣ where
  val := ⟨↑u, m * ↑u⟩
  inv := ⟨↑u⁻¹, -(↑u⁻¹ * m)⟩
  val_inv := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [fst_mul, fst_mk, fst_one, Units.mul_inv]
    · simp only [snd_mul, fst_mk, snd_mk, snd_one, smul_eq_mul, op_smul_eq_mul, mul_neg,
        Units.mul_inv_cancel_left, Units.mul_inv_cancel_right]
      exact neg_add_cancel m
  inv_val := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [fst_mul, fst_mk, fst_one, Units.inv_mul]
    · simp only [snd_mul, fst_mk, snd_mk, snd_one, smul_eq_mul, op_smul_eq_mul, neg_mul,
        ← mul_assoc]
      exact add_neg_cancel _

@[simp] lemma dualUnit_val_fst (u : Aˣ) (m : A) : (dualUnit u m : A[ε]).fst = ↑u := rfl

@[simp] lemma dualUnit_val_snd (u : Aˣ) (m : A) : (dualUnit u m : A[ε]).snd = m * ↑u := rfl

@[simp] lemma dualUnit_inv_val_fst (u : Aˣ) (m : A) :
    (((dualUnit u m)⁻¹ : (A[ε])ˣ) : A[ε]).fst = ↑u⁻¹ := rfl

@[simp] lemma dualUnit_inv_val_snd (u : Aˣ) (m : A) :
    (((dualUnit u m)⁻¹ : (A[ε])ˣ) : A[ε]).snd = -(↑u⁻¹ * m) := rfl

@[simp]
lemma dualUnit_one_zero : dualUnit (1 : Aˣ) (0 : A) = 1 := by
  apply Units.ext
  exact TrivSqZeroExt.ext (by simp) (by simp)

lemma dualUnit_mul_dualUnit (u v : Aˣ) (m n : A) :
    dualUnit u m * dualUnit v n = dualUnit (u * v) (↑u * n * ↑u⁻¹ + m) := by
  apply Units.ext
  refine TrivSqZeroExt.ext (by simp) ?_
  show (dualUnit u m : A[ε]).fst •> (dualUnit v n : A[ε]).snd
        + (dualUnit u m : A[ε]).snd <• (dualUnit v n : A[ε]).fst
      = (↑u * n * ↑u⁻¹ + m) * ↑(u * v)
  simp only [dualUnit_val_fst, dualUnit_val_snd, smul_eq_mul, op_smul_eq_mul, Units.val_mul,
    add_mul, mul_assoc, Units.inv_mul_cancel_left]

lemma eq_dualUnit_of_fst_eq {w : (A[ε])ˣ} {u : Aˣ} (h : (w : A[ε]).fst = ↑u) :
    w = dualUnit u ((w : A[ε]).snd * ↑u⁻¹) := by
  apply Units.ext
  exact TrivSqZeroExt.ext h (Units.inv_mul_cancel_right _ u).symm

end TrivSqZeroExt

namespace groupCohomology

open TrivSqZeroExt

variable {k A G : Type u} [CommRing k] [Ring A] [Algebra k A] [Group G]

noncomputable abbrev adjointRep (k : Type u) [CommRing k] [Algebra k A] (ρ₀ : G →* Aˣ) :
    Rep k G :=
  Rep.of (Representation.adjoint k ρ₀)

@[simp]
lemma adjointRep_ρ_apply (ρ₀ : G →* Aˣ) (g : G) (a : A) :
    (adjointRep k ρ₀).ρ g a = ↑(ρ₀ g) * a * ↑(ρ₀ g)⁻¹ := rfl

def IsDualLift (ρ₀ : G →* Aˣ) (ρ : G →* (A[ε])ˣ) : Prop :=
  ∀ g, ((ρ g : A[ε])).fst = ↑(ρ₀ g)

def dualLiftToCochain (ρ₀ : G →* Aˣ) (ρ : G →* (A[ε])ˣ) (g : G) : A :=
  ((ρ g : A[ε])).snd * ↑(ρ₀ g)⁻¹

lemma dualLift_ext {ρ₀ : G →* Aˣ} {ρ ρ' : G →* (A[ε])ˣ}
    (hρ : IsDualLift ρ₀ ρ) (hρ' : IsDualLift ρ₀ ρ')
    (h : dualLiftToCochain ρ₀ ρ = dualLiftToCochain ρ₀ ρ') : ρ = ρ' := by
  refine MonoidHom.ext fun g => ?_
  rw [eq_dualUnit_of_fst_eq (hρ g), eq_dualUnit_of_fst_eq (hρ' g)]
  exact congrArg _ (congrFun h g)

lemma dualLiftToCochain_mem_cocycles₁ {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ}
    (hρ : IsDualLift ρ₀ ρ) :
    dualLiftToCochain ρ₀ ρ ∈ cocycles₁ (adjointRep k ρ₀) := by
  rw [mem_cocycles₁_iff]
  intro g h
  show dualLiftToCochain ρ₀ ρ (g * h)
      = ↑(ρ₀ g) * dualLiftToCochain ρ₀ ρ h * ↑(ρ₀ g)⁻¹ + dualLiftToCochain ρ₀ ρ g
  unfold dualLiftToCochain
  simp only [map_mul, Units.val_mul, snd_mul, mul_inv_rev, hρ g, hρ h, smul_eq_mul,
    op_smul_eq_mul, add_mul, mul_assoc, Units.mul_inv_cancel_left]

noncomputable def dualLiftToCocycle (k : Type u) [CommRing k] [Algebra k A]
    {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) :
    cocycles₁ (adjointRep k ρ₀) :=
  ⟨dualLiftToCochain ρ₀ ρ, dualLiftToCochain_mem_cocycles₁ hρ⟩

@[simp]
lemma dualLiftToCocycle_coe {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) :
    ((dualLiftToCocycle k hρ : cocycles₁ (adjointRep k ρ₀)) : G → A)
      = dualLiftToCochain ρ₀ ρ := rfl

noncomputable def cocycleToDualLift (ρ₀ : G →* Aˣ) (c : cocycles₁ (adjointRep k ρ₀)) :
    G →* (A[ε])ˣ where
  toFun g := dualUnit (ρ₀ g) (c g)
  map_one' := by
    simp only [map_one, cocycles₁_map_one, dualUnit_one_zero]
  map_mul' g h := by
    dsimp only
    rw [dualUnit_mul_dualUnit, ← map_mul ρ₀]
    congr 1
    exact (mem_cocycles₁_iff (A := adjointRep k ρ₀) (c : G → A)).mp c.2 g h

@[simp]
lemma cocycleToDualLift_apply (ρ₀ : G →* Aˣ) (c : cocycles₁ (adjointRep k ρ₀)) (g : G) :
    cocycleToDualLift ρ₀ c g = dualUnit (ρ₀ g) (c g) := rfl

lemma isDualLift_cocycleToDualLift (ρ₀ : G →* Aˣ) (c : cocycles₁ (adjointRep k ρ₀)) :
    IsDualLift ρ₀ (cocycleToDualLift ρ₀ c) := fun _ => rfl

noncomputable def dualLiftEquivCocycles₁ (k : Type u) [CommRing k] [Algebra k A]
    (ρ₀ : G →* Aˣ) :
    {ρ : G →* (A[ε])ˣ // IsDualLift ρ₀ ρ} ≃ cocycles₁ (adjointRep k ρ₀) where
  toFun ρ := dualLiftToCocycle k ρ.2
  invFun c := ⟨cocycleToDualLift ρ₀ c, isDualLift_cocycleToDualLift ρ₀ c⟩
  left_inv ρ := by
    refine Subtype.ext
      (dualLift_ext (isDualLift_cocycleToDualLift ρ₀ _) ρ.2 (funext fun g => ?_))
    show (dualUnit (ρ₀ g) (dualLiftToCochain ρ₀ ρ.1 g) : A[ε]).snd * ↑(ρ₀ g)⁻¹
        = dualLiftToCochain ρ₀ ρ.1 g
    rw [dualUnit_val_snd]
    exact Units.mul_inv_cancel_right _ _
  right_inv c := by
    refine Subtype.ext (funext fun g => ?_)
    show (dualUnit (ρ₀ g) ((c : G → A) g) : A[ε]).snd * ↑(ρ₀ g)⁻¹ = (c : G → A) g
    rw [dualUnit_val_snd]
    exact Units.mul_inv_cancel_right _ _

@[simp]
lemma dualLiftEquivCocycles₁_apply (ρ₀ : G →* Aˣ) (ρ : {ρ : G →* (A[ε])ˣ // IsDualLift ρ₀ ρ}) :
    dualLiftEquivCocycles₁ k ρ₀ ρ = dualLiftToCocycle k ρ.2 := rfl

@[simp]
lemma dualLiftEquivCocycles₁_symm_apply (ρ₀ : G →* Aˣ) (c : cocycles₁ (adjointRep k ρ₀)) :
    ((dualLiftEquivCocycles₁ k ρ₀).symm c : G →* (A[ε])ˣ) = cocycleToDualLift ρ₀ c := rfl

end groupCohomology
