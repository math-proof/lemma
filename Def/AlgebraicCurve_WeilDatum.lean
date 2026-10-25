import Mathlib
import Def.AlgebraicCurve_PlaceEvaluation
import Structure.AlgebraicCurve_WeilDatum

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in


namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)

def pairing : K :=
  Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁

def symm : WeilDatum K F n where
  D₁ := d.D₂
  D₂ := d.D₁
  f₁ := d.f₂
  f₂ := d.f₁
  f₁_ne_zero := d.f₂_ne_zero
  f₂_ne_zero := d.f₁_ne_zero
  ord_f₁ := d.ord_f₂
  ord_f₂ := d.ord_f₁
  disjoint := fun v => (d.disjoint v).symm
  rational := fun v hv => d.rational v hv.symm

def addLeft (d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (_hf : d.f₂ = d'.f₂) :
    WeilDatum K F n where
  D₁ := d.D₁ + d'.D₁
  D₂ := d.D₂
  f₁ := d.f₁ * d'.f₁
  f₂ := d.f₂
  f₁_ne_zero := mul_ne_zero d.f₁_ne_zero d'.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ := fun v => by
    rw [v.ord_mul d.f₁_ne_zero d'.f₁_ne_zero, d.ord_f₁ v, d'.ord_f₁ v, Finsupp.add_apply,
      mul_add]
  ord_f₂ := d.ord_f₂
  disjoint := fun v => by
    rcases eq_or_ne (d.D₂ v) 0 with h2 | h2
    · exact Or.inr h2
    · refine Or.inl ?_
      rw [Finsupp.add_apply, (d.disjoint v).resolve_right h2,
        (d'.disjoint v).resolve_right (hD ▸ h2), add_zero]
  rational := fun v hv => by
    rcases hv with h1 | h2
    · rw [Finsupp.add_apply] at h1
      rcases eq_or_ne (d.D₁ v) 0 with hd | hd
      · exact d'.rational v (Or.inl fun hd' => h1 (by rw [hd, hd', add_zero]))
      · exact d.rational v (Or.inl hd)
    · exact d.rational v (Or.inr h2)

end WeilDatum

end AlgebraicCurve
