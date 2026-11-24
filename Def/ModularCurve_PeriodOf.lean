module
public import Mathlib
public import Def.ModularCurve_PeriodLattice
public import Def.ModularCurve_PeriodMap
public import Theorem.UpperHalfPlane.PeriodMapBundled
public import Theorem.CuspForm.Petersson
set_option autoImplicit false


public section

noncomputable section

open UpperHalfPlane Filter Topology

open scoped MatrixGroups ModularForm

namespace ModularCurve

section Period

variable (Γ : Subgroup SL(2, ℤ))

def periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) (t : ℝ) : ℂ :=
  f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)

def periodAlongOf (τ₀ τ₁ : ℍ) : Module.Dual ℂ (CuspForm Γ 2) where
  toFun f := ∫ t in (0 : ℝ)..1, periodIntegrandOf Γ τ₀ τ₁ f t
  map_add' f g := by
    rw [periodIntegrandOf_add]
    exact intervalIntegral.integral_add (intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ f 0 1)
      (intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ g 0 1)
  map_smul' c f := by
    rw [periodIntegrandOf_smul, RingHom.id_apply, smul_eq_mul]
    exact intervalIntegral.integral_const_mul c _

def periodOf (γ : Γ) : Module.Dual ℂ (CuspForm Γ 2) :=
  periodAlongOf Γ UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)

def periodLatticeOf : Submodule ℤ (Module.Dual ℂ (CuspForm Γ 2)) :=
  Submodule.span ℤ (Set.range (periodOf Γ))

def HasEquivariantPrimitiveOf (f : CuspForm Γ 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    Period.IsEquivariantPrimitive Γ F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in

def periodMapOf (f : CuspForm Γ 2) : Additive Γ →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitiveOf Γ f F then h.choose_spec.2.2.1.periodHom else 0

end Period

end ModularCurve

namespace CuspForm

variable (Γ : Subgroup SL(2, ℤ)) {k : ℤ}

def peterssonIntegrandOf (f g : CuspForm Γ k) (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (⇑f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (⇑g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

def peterssonOf (f g : CuspForm Γ k) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd) (peterssonIntegrandOf Γ f g)

end CuspForm

end
