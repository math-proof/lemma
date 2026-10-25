import Def.WeierstrassCurve_ModularityProps

set_option autoImplicit false

namespace WeierstrassCurve

def ThreeFiveSwitchCurveAtThreeConditioned (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible 5 →
    ∃ W' : WeierstrassCurve ℤ, W'.Δ ≠ 0 ∧ W'.IsSemistableModel ∧
      W'.ModRepIsIrreducible 3 ∧ W'.ModRepHasUnipotent 3 ∧
      ((¬ W.IsGoodPrimeFor 3 ∨ ¬ (3 : ℤ) ∣ W.apOfModel 3) →
        (¬ W'.IsGoodPrimeFor 3 ∨ ¬ (3 : ℤ) ∣ W'.apOfModel 3)) ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 →
        (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ)

end WeierstrassCurve
