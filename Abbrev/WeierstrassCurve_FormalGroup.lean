module

public import Def.WeierstrassCurve_FormalGroupLaw
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Evaluation

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

end MvPowerSeries

@[expose] public noncomputable section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
variable {σ : Type*}

abbrev GenK (σ : Type*) (R : Type*) [CommRing R] [IsDomain R] : Type _ :=
  FractionRing (MvPowerSeries σ R)

noncomputable abbrev genι : MvPowerSeries σ R →+* GenK σ R :=
  algebraMap (MvPowerSeries σ R) (FractionRing (MvPowerSeries σ R))

end WeierstrassCurve

end

set_option maxHeartbeats 1000000

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

abbrev NoVar {σ : Type*} (j : σ) (x : MvPowerSeries σ R) : Prop :=
  ∀ d : σ →₀ ℕ, d j ≠ 0 → MvPowerSeries.coeff d x = 0

end

end WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

end WeierstrassCurve
