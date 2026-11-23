import Mathlib
import Def.CuspForm_HeckeAlgebra
import Def.HeckeGalois_EichlerShimura

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularCurve

section Period

def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

def segmentPoint (τ₀ τ₁ : ℍ) (t : ℝ) : ℂ :=
  (1 - clamp01 t) • (τ₀ : ℂ) + clamp01 t • (τ₁ : ℂ)

def segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) : ℍ :=
  UpperHalfPlane.mk (segmentPoint τ₀ τ₁ t) (segmentPoint_im_pos τ₀ τ₁ t)

variable (N : ℕ)

def periodIntegrand (τ₀ τ₁ : ℍ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (t : ℝ) : ℂ :=
  f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)

def periodAlong (τ₀ τ₁ : ℍ) : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) where
  toFun f := ∫ t in (0 : ℝ)..1, periodIntegrand N τ₀ τ₁ f t
  map_add' f g := by
    rw [periodIntegrand_add]
    exact intervalIntegral.integral_add (intervalIntegrable_periodIntegrand N τ₀ τ₁ f 0 1)
      (intervalIntegrable_periodIntegrand N τ₀ τ₁ g 0 1)
  map_smul' c f := by
    rw [periodIntegrand_smul, RingHom.id_apply, smul_eq_mul]
    exact intervalIntegral.integral_const_mul c _

def period (γ : CongruenceSubgroup.Gamma0 N) :
    Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  periodAlong N UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)

def periodLattice : Submodule ℤ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
  Submodule.span ℤ (Set.range (period N))

end Period

section Hecke

variable (N : ℕ) [NeZero N]

def cuspHeckeGen (ℓ : Nat.Primes) : CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) :=
  if h : (ℓ : ℕ) ∣ N then CuspForm.heckeAlgebra.U (S := (∅ : Set ℕ)) ℓ.prop h (Set.notMem_empty _)
  else CuspForm.heckeAlgebra.T (S := (∅ : Set ℕ)) ℓ.prop h (Set.notMem_empty _)

def cuspHeckeAeval : HeckeAlg →ₐ[ℤ] CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) :=
  MvPolynomial.aeval (cuspHeckeGen N)

def cuspHeckeRep : HeckeAlg →+* Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  ((CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)).val.comp (cuspHeckeAeval N)).toRingHom

def dualHeckeRep : HeckeAlg →+* Module.End ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) where
  toFun t := (cuspHeckeRep N t).dualMap
  map_one' := by rw [map_one]; exact LinearMap.dualMap_id
  map_mul' s t := by
    rw [mul_comm s t, map_mul]
    exact (LinearMap.dualMap_comp_dualMap (cuspHeckeRep N s) (cuspHeckeRep N t)).symm
  map_zero' := by
    rw [map_zero]; exact map_zero (Module.Dual.transpose (R := ℂ))
  map_add' s t := by
    rw [map_add]; exact map_add (Module.Dual.transpose (R := ℂ)) _ _

def PeriodLatticeHeckeStable : Prop :=
  ∀ (ℓ : Nat.Primes) (x : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
    x ∈ periodLattice N → dualHeckeRep N (heckeGen ℓ) x ∈ periodLattice N

variable {N}

variable (N)

def periodLatticeRestrict (h : PeriodLatticeHeckeStable N) (t : HeckeAlg) :
    Module.End ℤ (periodLattice N) :=
  ((dualHeckeRep N t).toAddMonoidHom.toIntLinearMap).restrict
    (fun x hx => periodLattice_stable_of h t x hx)

def periodLatticeRestrictHom (h : PeriodLatticeHeckeStable N) :
    HeckeAlg →+* Module.End ℤ (periodLattice N) where
  toFun := periodLatticeRestrict N h
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' s t := LinearMap.ext fun x => Subtype.ext (by simp)
  map_zero' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_add' s t := LinearMap.ext fun x => Subtype.ext (by simp)

open Classical in

def periodLatticeHeckeEnd : HeckeAlg →+* Module.End ℤ (periodLattice N) :=
  if h : PeriodLatticeHeckeStable N then periodLatticeRestrictHom N h
  else (Int.castRingHom (Module.End ℤ (periodLattice N))).comp
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))

variable {N}

variable (N)

@[implicit_reducible]
def periodLatticeModule : Module HeckeAlg (periodLattice N) :=
  Module.compHom (periodLattice N) (periodLatticeHeckeEnd N)

end Hecke

end ModularCurve

end
