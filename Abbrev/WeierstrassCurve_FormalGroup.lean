import Def.WeierstrassCurve_FormalGroupLaw
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Evaluation

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

end MvPowerSeries

noncomputable section

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
