import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingTorusBlockQuantitative
open Finset Set StatMech StatMech.FrontierA


/--
[finiteTorusBlockCharacterWeight_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusBlockQuantitative.lean)
-/
@[path]
private lemma finiteTorusBlockCharacterWeight_le_one_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {B : Finset Gamma}
  {chi : AddChar Gamma Complex} :
-- imply
  finiteTorusBlockCharacterWeight B chi <= 1 := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockCharacterWeight_le_one B chi

/--
[sum_finiteTorusBlockCharacterWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusBlockQuantitative.lean)
-/
@[path]
private lemma sum_finiteTorusBlockCharacterWeight_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {B : Finset Gamma}
-- given
  (hB : B.Nonempty) :
-- imply
  ∑ chi : AddChar Gamma Complex, finiteTorusBlockCharacterWeight B chi = Fintype.card Gamma / (B.card : Real) := by
-- proof
  apply StatMech.FrontierA.sum_finiteTorusBlockCharacterWeight B hB

/--
[isingTorusCharacterDispersion_inverse_le_of_not_lowMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusBlockQuantitative.lean)
-/
@[path]
private lemma isingTorusCharacterDispersion_inverse_le_of_not_lowMomentum_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {d k M : Nat}
  {p : IsingDyadicTorus d k}
-- given
  (hp0 : p ≠ 0)
  (hpHigh : p ∉ isingTorusLowMomentum d k M) :
-- imply
  (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ <= (isingDyadicSide k : Real) ^ 2 / (16 * ((M + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.isingTorusCharacterDispersion_inverse_le_of_not_lowMomentum p hp0 hpHigh

/--
[finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusBlockQuantitative.lean)
-/
@[path]
private lemma finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {d k M : Nat}
  {B : Finset (IsingDyadicTorus d k)}
  {M : Nat}
  {C : Real}
-- given
  (hd : 2 < d)
  (hB : B.Nonempty)
  (hM : 1 <= M)
  (hMhalf : M <= isingDyadicSide k / 2)
  (hLow : (1 / (isingDyadicSide k : Real) ^ d) * ∑ p ∈ isingTorusLowMomentum d k M, (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ <= C * ((M : Real) / isingDyadicSide k) ^ (d - 2)) :
-- imply
  finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) B <= C * ((M : Real) / isingDyadicSide k) ^ (d - 2) + (isingDyadicSide k : Real) ^ 2 / (16 * ((M + 1 : Nat) : Real) ^ 2 * B.card) := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power hd B hB M hM hMhalf C hLow

/--
[exists_finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusBlockQuantitative.lean)
-/
@[path]
private lemma exists_finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {d k M : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ (k : Nat) (B : Finset (IsingDyadicTorus d k)), B.Nonempty -> ∀ M : Nat, 1 <= M -> M <= isingDyadicSide k / 2 -> finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) B <= C * ((M : Real) / isingDyadicSide k) ^ (d - 2) + (isingDyadicSide k : Real) ^ 2 / (16 * ((M + 1 : Nat) : Real) ^ 2 * B.card) := by
-- proof
  apply StatMech.FrontierA.exists_finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power hd

/--
[isingTorusTwoPoint_blockDifferenceAverage_le_green](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusBlockQuantitative.lean)
-/
@[path]
private lemma isingTorusTwoPoint_blockDifferenceAverage_le_green_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {d k M : Nat}
  {beta : Real}
  {B : Finset (IsingDyadicTorus d k)}
-- given
  (hbeta : 0 < beta)
  (hB : B.Nonempty) :
-- imply
  finiteTorusBlockDifferenceAverage (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) B <= (finiteTorusFourierCoeff (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re / Fintype.card (IsingDyadicTorus d k) + (1 / beta) * finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) B := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_blockDifferenceAverage_le_green beta hbeta B hB


-- created on 2026-10-23
