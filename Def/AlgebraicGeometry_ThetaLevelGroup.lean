module
public import Mathlib
public import Instance.AlgebraicGeometry_ThetaLevelGroup
public import Structure.AlgebraicGeometry_ThetaLevelGroup
public import Abbrev.AlgebraicGeometry_ThetaLevelGroup
set_option autoImplicit false


public section

noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry.ThetaLevel

section Heis

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ)

noncomputable def iota (i : Fin g) : ZMod (δ i) →+ ZMod (2 * d) :=
  if hdiv : δ i ∣ 2 * d then
    ZMod.lift (δ i)
      ⟨(AddMonoidHom.mulLeft ((2 * d / δ i : ℕ) : ZMod (2 * d))).comp (Int.castAddHom (ZMod (2 * d))), by
        change ((2 * d / δ i : ℕ) : ZMod (2 * d)) * (((δ i : ℕ) : ℤ) : ZMod (2 * d)) = 0
        rw [Int.cast_natCast, ← Nat.cast_mul, Nat.div_mul_cancel hdiv, ZMod.natCast_self]⟩
  else 0

noncomputable def pair (k h : HH δ) : ZMod (2 * d) := ∑ i, iota δ d i (k i * h i)

@[ext]

namespace Heis

variable {δ} {d}

def cen (a : ZMod (2 * d)) : Heis δ d := ⟨a, 0, 0⟩

def theta (h : HH δ) : Heis δ d := ⟨0, h, 0⟩

def eta (k : HH δ) : Heis δ d := ⟨0, 0, k⟩

variable (δ d) in

def Gam : Subgroup (MulAut (Heis δ d)) where
  carrier := {γ | ∀ a, γ (cen a) = cen a}
  mul_mem' := by
    intro γ γ' hγ hγ' a
    show γ (γ' (cen a)) = cen a
    rw [hγ', hγ]
  one_mem' := by intro a; rfl
  inv_mem' := by
    intro γ hγ a
    show γ.symm (cen a) = cen a
    rw [MulEquiv.symm_apply_eq]
    exact (hγ a).symm

end Heis

section Schrodinger

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)

def omegaPow (a : ZMod (2 * d)) : B := ω ^ a.val

omit [NeZero d] in
def thetaChar (k : HH δ) : HH δ → B := fun h => omegaPow d B ω (pair δ d k h)

def shiftOp (h : HH δ) : (HH δ → B) →ₗ[B] (HH δ → B) := LinearMap.funLeft B B (fun x => x - h)

def diagOp (c : HH δ → B) : (HH δ → B) →ₗ[B] (HH δ → B) := LinearMap.mulLeft B c

def schrod (z : Heis δ d) : (HH δ → B) →ₗ[B] (HH δ → B) :=
  omegaPow d B ω z.a • (shiftOp δ B z.h ∘ₗ diagOp δ B (thetaChar δ d B ω z.k))

omit [NeZero d] in
def schrodHom (hω : ω ^ (2 * d) = 1) : Heis δ d →* Module.End B (HH δ → B) where
  toFun := schrod δ d B ω
  map_one' := schrod_one δ d B ω
  map_mul' z z' := by rw [schrod_mul δ d B ω hω]; rfl

end Schrodinger

section Matrices

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) (B : Type) [CommRing B] (ω : B) {n : ℕ} (e : Fin n ≃ HH δ)

def schrodMat (z : Heis δ d) : Matrix (Fin n) (Fin n) B :=
  fun i j => if e i = e j + z.h then omegaPow d B ω (z.a + pair δ d z.k (e j)) else 0

def IsIntertwiner (γ : MulAut (Heis δ d)) (U : Matrix (Fin n) (Fin n) B) : Prop :=
  IsUnit U ∧ ∀ z : Heis δ d, U * schrodMat δ d B ω e z = schrodMat δ d B ω e (γ z) * U

def inter (γ : MulAut (Heis δ d)) : Matrix (Fin n) (Fin n) B := by
end Matrices

end AlgebraicGeometry.ThetaLevel

end

end
