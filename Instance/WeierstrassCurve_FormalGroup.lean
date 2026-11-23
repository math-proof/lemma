-- Carved from Lemma/Definitions/Def_WeierstrassCurve_FormalGroup.lean: instance decls only.
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Theorem.WeierstrassCurve.FormalGroup
@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false


set_option maxHeartbeats 1000000

open PowerSeries MvPowerSeries


namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

instance instIsCommFormalGroup [W.IsElliptic] : W.formalGroup.IsComm where
  comm := by
    show W.formalGroup.toPowerSeries
      = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] W.formalGroup.toPowerSeries
    exact (W.formalGroupLawFixed_comm).symm

end WeierstrassCurve
