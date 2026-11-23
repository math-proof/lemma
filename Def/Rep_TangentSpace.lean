module

public import Mathlib

@[expose] public section

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

def adjoint (ρ₀ : G →* Aˣ) : Representation k G A where
  toFun g := adjointAux k (ρ₀ g)
  map_one' := by
    ext a
    simp
  map_mul' g h := by
    ext a
    simp only [map_mul, adjointAux_mul, LinearMap.comp_apply, Module.End.mul_apply]

end Representation

namespace TrivSqZeroExt

variable {A : Type*} [Ring A]

def dualUnit (u : Aˣ) (m : A) : (A[ε])ˣ where
  val := ⟨↑u, m * ↑u⟩
  inv := ⟨↑u⁻¹, -(↑u⁻¹ * m)⟩
  val_inv := by
    let x : A[ε] := ⟨↑u, m * ↑u⟩
    let y : A[ε] := ⟨↑u⁻¹, -(↑u⁻¹ * m)⟩
    change x * y = 1
    have h1 : fst (x * y) = 1 := by
      rw [fst_mul, show fst x = ↑u from rfl, show fst y = ↑u⁻¹ from rfl]
      apply Units.mul_inv
    have h2 : snd (x * y) = 0 := by
      rw [snd_mul, show fst x = ↑u from rfl, show snd y = -(↑u⁻¹ * m) from rfl,
        show snd x = m * ↑u from rfl, show fst y = ↑u⁻¹ from rfl,
        smul_eq_mul, op_smul_eq_mul, mul_neg, Units.mul_inv_cancel_left,
        Units.mul_inv_cancel_right]
      apply neg_add_cancel
    apply ext h1 h2
  inv_val := by
    let y : A[ε] := ⟨↑u⁻¹, -(↑u⁻¹ * m)⟩
    let x : A[ε] := ⟨↑u, m * ↑u⟩
    change y * x = 1
    have h1 : fst (y * x) = 1 := by
      rw [fst_mul, show fst y = ↑u⁻¹ from rfl, show fst x = ↑u from rfl]
      apply Units.inv_mul
    have h2 : snd (y * x) = 0 := by
      rw [snd_mul, show fst y = ↑u⁻¹ from rfl, show snd x = m * ↑u from rfl,
        show snd y = -(↑u⁻¹ * m) from rfl, show fst x = ↑u from rfl,
        smul_eq_mul, op_smul_eq_mul, neg_mul, ← mul_assoc]
      apply add_neg_cancel
    apply ext h1 h2

end TrivSqZeroExt

namespace groupCohomology

open TrivSqZeroExt

variable {k A G : Type u} [CommRing k] [Ring A] [Algebra k A] [Group G]

noncomputable abbrev adjointRep (k : Type u) [CommRing k] [Algebra k A] (ρ₀ : G →* Aˣ) :
    Rep k G :=
  Rep.of (Representation.adjoint k ρ₀)

def IsDualLift (ρ₀ : G →* Aˣ) (ρ : G →* (A[ε])ˣ) : Prop :=
  ∀ g, ((ρ g : A[ε])).fst = ↑(ρ₀ g)

def dualLiftToCochain (ρ₀ : G →* Aˣ) (ρ : G →* (A[ε])ˣ) (g : G) : A :=
  ((ρ g : A[ε])).snd * ↑(ρ₀ g)⁻¹

noncomputable def dualLiftToCocycle (k : Type u) [CommRing k] [Algebra k A]
    {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) :
    cocycles₁ (adjointRep k ρ₀) :=
  ⟨dualLiftToCochain ρ₀ ρ, dualLiftToCochain_mem_cocycles₁ hρ⟩

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

end groupCohomology

end
