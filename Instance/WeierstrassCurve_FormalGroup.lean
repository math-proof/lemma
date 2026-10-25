-- Carved from Lemma/Definitions/Def_WeierstrassCurve_FormalGroup.lean: instance decls only.
import Lemma.WeierstrassCurve.FormalGroupLaw
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Lemma.WeierstrassCurve.FormalGroup

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
