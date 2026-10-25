import Instance.AlgebraicCurve_DivisorClassGroup
import Mathlib.Algebra.Ring.Action.End
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- Semilinear automorphisms of an algebraic curve function field (defs carve). -/
def SemilinearAut : Subgroup (RingAut F × RingAut K) where
  carrier := {p | ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a)}
  one_mem' _ := rfl
  mul_mem' := fun {p q} hp hq a => by
    show p.1 (q.1 (algebraMap K F a)) = algebraMap K F (p.2 (q.2 a))
    rw [hq a, hp (q.2 a)]
  inv_mem' := fun {p} hp a => by
    show p.1.symm (algebraMap K F a) = algebraMap K F (p.2.symm a)
    apply p.1.injective
    rw [RingEquiv.apply_symm_apply, hp (p.2.symm a), RingEquiv.apply_symm_apply]

namespace SemilinearAut

variable {K F}

theorem mem_iff {p : RingAut F × RingAut K} :
    p ∈ SemilinearAut K F ↔ ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a) :=
  Iff.rfl

def toRingAut (g : SemilinearAut K F) : F ≃+* F := g.val.1

def baseAut (g : SemilinearAut K F) : K ≃+* K := g.val.2

theorem commutes (g : SemilinearAut K F) (a : K) :
    toRingAut g (algebraMap K F a) = algebraMap K F (baseAut g a) :=
  g.prop a

@[simp] theorem toRingAut_one : toRingAut (1 : SemilinearAut K F) = 1 := rfl

@[simp] theorem baseAut_one : baseAut (1 : SemilinearAut K F) = 1 := rfl

@[simp] theorem toRingAut_mul (g h : SemilinearAut K F) :
    toRingAut (g * h) = toRingAut g * toRingAut h := rfl

@[simp] theorem baseAut_mul (g h : SemilinearAut K F) :
    baseAut (g * h) = baseAut g * baseAut h := rfl

@[simp] theorem toRingAut_inv (g : SemilinearAut K F) :
    toRingAut g⁻¹ = (toRingAut g).symm := rfl

@[simp] theorem baseAut_inv (g : SemilinearAut K F) :
    baseAut g⁻¹ = (baseAut g).symm := rfl

def ofAlgAut : (F ≃ₐ[K] F) →* SemilinearAut K F where
  toFun σ := ⟨((σ : F ≃+* F), 1), fun a => by simp⟩
  map_one' := Subtype.ext (by ext <;> rfl)
  map_mul' σ τ := Subtype.ext (by ext <;> rfl)

@[simp]
theorem toRingAut_ofAlgAut (σ : F ≃ₐ[K] F) : toRingAut (ofAlgAut σ) = (σ : F ≃+* F) := rfl

@[simp]
theorem baseAut_ofAlgAut (σ : F ≃ₐ[K] F) : baseAut (ofAlgAut σ) = 1 := rfl

end SemilinearAut

end AlgebraicCurve
