import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingInfraredBlockAverage
open Finset StatMech StatMech.FrontierA


/--
[finiteTorusBlockCharacterWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredBlockAverage.lean)
-/
@[path]
private lemma finiteTorusBlockCharacterWeight_nonneg_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {B : Finset Gamma}
  {chi : AddChar Gamma Complex} :
-- imply
  0 ≤ finiteTorusBlockCharacterWeight B chi := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockCharacterWeight_nonneg B chi

/--
[finiteTorusBlockDifferenceAverage_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredBlockAverage.lean)
-/
@[path]
private lemma finiteTorusBlockDifferenceAverage_fourier_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {B : Finset Gamma} :
-- imply
  finiteTorusBlockDifferenceAverage G B = (1 / Fintype.card Gamma : Real) * ∑ chi : AddChar Gamma Complex, (finiteTorusFourierCoeff G chi).re * finiteTorusBlockCharacterWeight B chi := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockDifferenceAverage_fourier G B

/--
[finiteTorusBlockCharacterWeight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredBlockAverage.lean)
-/
@[path]
private lemma finiteTorusBlockCharacterWeight_zero_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {B : Finset Gamma} :
-- imply
  finiteTorusBlockCharacterWeight B (0 : AddChar Gamma Complex) = if B.card = 0 then 0 else 1 := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockCharacterWeight_zero B

/--
[finiteTorusBlockDifferenceAverage_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredBlockAverage.lean)
-/
@[path]
private lemma finiteTorusBlockDifferenceAverage_le_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {B : Finset Gamma}
  {C : Real}
  {dispersion : AddChar Gamma Complex → Real}
-- given
  (hB : B.Nonempty)
  (hreal : ∀ chi, (finiteTorusFourierCoeff G chi).im = 0)
  (hbound : ∀ chi, chi ≠ 0 → 0 ≤ (finiteTorusFourierCoeff G chi).re ∧ (finiteTorusFourierCoeff G chi).re ≤ C / dispersion chi) :
-- imply
  finiteTorusBlockDifferenceAverage G B ≤ (finiteTorusFourierCoeff G 0).re / Fintype.card Gamma + (1 / Fintype.card Gamma : Real) * ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex), (C / dispersion chi) * finiteTorusBlockCharacterWeight B chi := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockDifferenceAverage_le G B C dispersion hB hreal hbound


-- created on 2026-10-23
