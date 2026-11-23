module

public import Theorem.WeierstrassCurve.FormalGroupLaw
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Abbrev.WeierstrassCurve_FormalGroup

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false


noncomputable section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
variable {σ : Type*}

noncomputable def fgGenW (t : MvPowerSeries σ R) : MvPowerSeries σ R :=
  PowerSeries.subst t W.formalW

noncomputable def xGen (t : MvPowerSeries σ R) : GenK σ R :=
  genι t / genι (W.fgGenW t)

noncomputable def yGen (t : MvPowerSeries σ R) : GenK σ R :=
  -1 / genι (W.fgGenW t)

noncomputable def genW (σ : Type*) : WeierstrassCurve (GenK σ R) :=
  W.map (algebraMap R (GenK σ R))

noncomputable def genericPoint [W.IsElliptic] {t : MvPowerSeries σ R}
    (ht : PowerSeries.HasSubst t) (hw : genι (W.fgGenW t) ≠ 0) :
    (W.genW σ).toAffine.Point :=
  .some (W.xGen t) (W.yGen t) (W.nonsingular_genericPoint ht hw)

end WeierstrassCurve

end

set_option maxHeartbeats 1000000

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

set_option maxRecDepth 100000 in
open Classical in

open Classical in

open Classical in

open Classical in

open Classical in

open Classical in

def formalGroup [W.IsElliptic] : FormalGroup R where
  toPowerSeries := W.formalGroupLawFixed
  zero_constantCoeff := W.constantCoeff_formalGroupLawFixed
  lin_coeff_X := W.coeff_zero_formalGroupLawFixed
  lin_coeff_Y := W.coeff_one_formalGroupLawFixed
  assoc := W.formalGroupLawFixed_assoc

end

end WeierstrassCurve

end
