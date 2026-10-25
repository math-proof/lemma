import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSquarePressureAgreement
open MeasureTheory Set StatMech StatMech.FrontierD


/--
[fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountableAtLogistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSquarePressureAgreement.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountableAtLogistic_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  square.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountableAtLogistic q hq

/--
[fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSquarePressureAgreement.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountable_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  square.FreeWiredIncreasingCylinderAgreementOffCountable q := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountable q hq


-- created on 2026-10-23
