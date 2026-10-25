import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen.Part2
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[measurableSet_isingMomentumCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma measurableSet_isingMomentumCube_eq
  {d : Nat} :
-- imply
  MeasurableSet (isingMomentumCube d) := by
-- proof
  apply StatMech.FrontierA.measurableSet_isingMomentumCube d

/--
[isingMomentumCube_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma isingMomentumCube_zero_eq
  {d : Nat} :
-- imply
  (0 : IsingMomentumSpace d) ∈ isingMomentumCube d := by
-- proof
  apply StatMech.FrontierA.isingMomentumCube_zero d

/--
[continuous_isingContinuumDispersion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma continuous_isingContinuumDispersion_eq
  {d : Nat} :
-- imply
  Continuous (isingContinuumDispersion : IsingMomentumSpace d → Real) := by
-- proof
  apply StatMech.FrontierA.continuous_isingContinuumDispersion d

/--
[isingContinuumDispersion_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma isingContinuumDispersion_nonneg_eq
  {d : Nat}
  {p : IsingMomentumSpace d} :
-- imply
  0 ≤ isingContinuumDispersion p := by
-- proof
  apply StatMech.FrontierA.isingContinuumDispersion_nonneg p

/--
[isingContinuumDispersion_quadratic_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma isingContinuumDispersion_quadratic_lower_eq
  {d : Nat}
  {p : IsingMomentumSpace d}
-- given
  (hp : p ∈ isingMomentumCube d) :
-- imply
  (4 / Real.pi ^ 2) * ‖p‖ ^ 2 ≤ isingContinuumDispersion p := by
-- proof
  apply StatMech.FrontierA.isingContinuumDispersion_quadratic_lower hp

/--
[isingContinuumDispersion_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma isingContinuumDispersion_pos_eq
  {d : Nat}
  {p : IsingMomentumSpace d}
-- given
  (hp : p ∈ isingMomentumCube d)
  (hp0 : p ≠ 0) :
-- imply
  0 < isingContinuumDispersion p := by
-- proof
  apply StatMech.FrontierA.isingContinuumDispersion_pos hp hp0

/--
[measurable_isingContinuumInverseDispersion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma measurable_isingContinuumInverseDispersion_eq
  {d : Nat} :
-- imply
  Measurable (isingContinuumInverseDispersion : IsingMomentumSpace d → Real) := by
-- proof
  apply StatMech.FrontierA.measurable_isingContinuumInverseDispersion d

/--
[measurable_isingContinuumGreenDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma measurable_isingContinuumGreenDensity_eq
  {d : Nat} :
-- imply
  Measurable (isingContinuumGreenDensity d) := by
-- proof
  apply StatMech.FrontierA.measurable_isingContinuumGreenDensity d

/--
[norm_isingContinuumGreenDensity_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma norm_isingContinuumGreenDensity_le_eq
  {d : Nat}
  {p : IsingMomentumSpace d} :
-- imply
  ‖isingContinuumGreenDensity d p‖ ≤ (Real.pi ^ 2 / 4) * ‖p‖ ^ (-2 : Real) := by
-- proof
  apply StatMech.FrontierA.norm_isingContinuumGreenDensity_le p

/--
[isBounded_isingMomentumCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma isBounded_isingMomentumCube_eq
  {d : Nat} :
-- imply
  Bornology.IsBounded (isingMomentumCube d) := by
-- proof
  apply StatMech.FrontierA.isBounded_isingMomentumCube d

/--
[integrable_isingContinuumGreenDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma integrable_isingContinuumGreenDensity_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Integrable (isingContinuumGreenDensity d) := by
-- proof
  apply StatMech.FrontierA.integrable_isingContinuumGreenDensity hd

/--
[isingContinuumGreen_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredContinuumGreen.lean)
-/
@[path]
private lemma isingContinuumGreen_tendsto_zero_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Filter.Tendsto (isingContinuumGreen d) (Filter.cocompact (IsingMomentumSpace d)) (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingContinuumGreen_tendsto_zero hd


-- created on 2026-10-23
