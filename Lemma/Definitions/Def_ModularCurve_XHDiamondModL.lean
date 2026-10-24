import Mathlib
import Lemma.Definitions.Def_ModularCurve_XH

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularCurve

def IsDiamondPullbackModL (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ)
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        qExpFunctionFieldC K (CohCarrier.GammaH M H))) : Prop :=
  ∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
    (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg pf₁ pg₁ : PowerSeries ℤ),
    IsIntegralQExp f pf → IsIntegralQExp g pg →
    IsIntegralQExp f₁ pf₁ → IsIntegralQExp g₁ pg₁ →
    (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    intSeriesC K pg ≠ 0 →
    ∀ x : qExpFunctionFieldC K (CohCarrier.GammaH M H),
      (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁ →
      ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
        intSeriesC K pf / intSeriesC K pg

variable {K : Type*} [Field K] {M : ℕ} {H : Subgroup (ZMod M)ˣ}
  {ρ : CongruenceSubgroup.Gamma0 M →*
    (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M H))}

theorem IsDiamondPullbackModL.coe_apply_eq (hρ : IsDiamondPullbackModL K M H ρ)
    (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
    {f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k}
    {pf pg pf₁ pg₁ : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hf₁ : IsIntegralQExp f₁ pf₁) (hg₁ : IsIntegralQExp g₁ pg₁)
    (hfs : (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hgs : (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hpg : intSeriesC K pg ≠ 0)
    {x : qExpFunctionFieldC K (CohCarrier.GammaH M H)}
    (hx : (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁) :
    ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
      intSeriesC K pf / intSeriesC K pg :=
  hρ γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg x hx

end ModularCurve

end
