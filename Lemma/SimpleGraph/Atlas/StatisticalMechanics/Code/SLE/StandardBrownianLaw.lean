import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.SLE.StandardBrownianLaw
open MeasureTheory ProbabilityTheory StatMech StatMech.SLE


/--
[IsStandardBrownianMotion.memLp_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma memLp_two_eq
  [MeasurableSpace Omega]
  {t : Real}
-- given
  (hB : IsStandardBrownianMotion B P) :
-- imply
  MemLp (B t) 2 P := by
-- proof
  apply StatMech.SLE.IsStandardBrownianMotion.memLp_two hB t

/--
[IsStandardBrownianMotion.integral_increment_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma integral_increment_eq_zero_eq
  [MeasurableSpace Omega]
  {s t : Real}
-- given
  (hB : IsStandardBrownianMotion B P)
  (hst : s <= t) :
-- imply
  (integral P fun omega => B t omega - B s omega) = 0 := by
-- proof
  apply StatMech.SLE.IsStandardBrownianMotion.integral_increment_eq_zero hB hst

/--
[IsStandardBrownianMotion.integral_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma integral_eq_zero_eq
  [MeasurableSpace Omega]
  {t : Real}
-- given
  (hB : IsStandardBrownianMotion B P) :
-- imply
  (integral P fun omega => B t omega) = 0 := by
-- proof
  apply StatMech.SLE.IsStandardBrownianMotion.integral_eq_zero hB t

/--
[IsStandardBrownianMotion.variance_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma variance_increment_eq
  [MeasurableSpace Omega]
  {s t : Real}
-- given
  (hB : IsStandardBrownianMotion B P)
  (hst : s <= t) :
-- imply
  Var[fun omega => B t omega - B s omega; P] = t - s := by
-- proof
  apply StatMech.SLE.IsStandardBrownianMotion.variance_increment hB hst

/--
[IsStandardBrownianMotion.variance_eq_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma variance_eq_abs_eq
  [MeasurableSpace Omega]
  {t : Real}
-- given
  (hB : IsStandardBrownianMotion B P) :
-- imply
  Var[B t; P] = := by
-- proof
  apply StatMech.SLE.IsStandardBrownianMotion.variance_eq_abs hB t

/--
[IsStandardBrownianMotion.covariance_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma covariance_eq_eq
  [MeasurableSpace Omega]
  {s t : Real}
-- given
  (hB : IsStandardBrownianMotion B P) :
-- imply
  cov[B s, B t; P] = (|s| + |t| - |t - s|) / 2 := by
-- proof
  apply StatMech.SLE.IsStandardBrownianMotion.covariance_eq hB s t

/--
[standardBrownian_restrict_law_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma standardBrownian_restrict_law_eq_eq
  [MeasurableSpace Omega]
  [MeasurableSpace Omega1]
  [MeasurableSpace Omega2]
  {B1 : Real -> Omega1 -> Real}
  {B2 : Real -> Omega2 -> Real}
  {P1 : Measure Omega1}
  {P2 : Measure Omega2}
  {I : Finset Real}
-- given
  (hB1 : IsStandardBrownianMotion B1 P1)
  (hB2 : IsStandardBrownianMotion B2 P2) :
-- imply
  P1.map (fun omega => I.restrict (B1 · omega)) = P2.map (fun omega => I.restrict (B2 · omega)) := by
-- proof
  apply StatMech.SLE.standardBrownian_restrict_law_eq hB1 hB2 I

/--
[standardBrownian_restrict_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma standardBrownian_restrict_law_eq
  [MeasurableSpace Omega]
  {I : Finset Real}
-- given
  (hB : IsStandardBrownianMotion B P) :
-- imply
  HasLaw (fun omega => I.restrict (B · omega)) (brownianFiniteDimensionalPiLaw I) P := by
-- proof
  apply StatMech.SLE.standardBrownian_restrict_law hB I

/--
[standardBrownian_processLaw_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma standardBrownian_processLaw_eq_eq
  [MeasurableSpace Omega]
  [MeasurableSpace Omega1]
  [MeasurableSpace Omega2]
  {B1 : Real -> Omega1 -> Real}
  {B2 : Real -> Omega2 -> Real}
  {P1 : Measure Omega1}
  {P2 : Measure Omega2}
-- given
  (hB1 : IsStandardBrownianMotion B1 P1)
  (hB2 : IsStandardBrownianMotion B2 P2) :
-- imply
  P1.map (fun omega t => B1 t omega) = P2.map (fun omega t => B2 t omega) := by
-- proof
  apply StatMech.SLE.standardBrownian_processLaw_eq hB1 hB2

/--
[measurable_sleDrivingPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma measurable_sleDrivingPath_eq
  [MeasurableSpace Omega]
  {kappa : Real} :
-- imply
  Measurable (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) := by
-- proof
  apply StatMech.SLE.measurable_sleDrivingPath kappa

/--
[standardBrownian_sleDriving_processLaw_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/StandardBrownianLaw.lean)
-/
@[path]
private lemma standardBrownian_sleDriving_processLaw_eq_eq
  [MeasurableSpace Omega]
  [MeasurableSpace Omega1]
  [MeasurableSpace Omega2]
  {B1 : Real -> Omega1 -> Real}
  {B2 : Real -> Omega2 -> Real}
  {P1 : Measure Omega1}
  {P2 : Measure Omega2}
  {kappa : Real}
-- given
  (hB1 : IsStandardBrownianMotion B1 P1)
  (hB2 : IsStandardBrownianMotion B2 P2) :
-- imply
  P1.map (fun omega => sleDriving kappa B1 omega) = P2.map (fun omega => sleDriving kappa B2 omega) := by
-- proof
  apply StatMech.SLE.standardBrownian_sleDriving_processLaw_eq hB1 hB2 kappa


-- created on 2026-10-23
