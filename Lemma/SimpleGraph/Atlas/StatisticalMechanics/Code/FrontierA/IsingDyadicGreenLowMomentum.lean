import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
open Finset Set StatMech StatMech.FrontierA


/--
[isingTorusLowMomentum_centeredInt_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenLowMomentum.lean)
-/
@[path]
private lemma isingTorusLowMomentum_centeredInt_mem_box_eq
  {d k M : Nat}
  {p : IsingDyadicTorus d k}
-- given
  (hp : p ∈ isingTorusLowMomentum d k M) :
-- imply
  isingTorusCenteredIntMomentum p ∈ integerMomentumBoxWithoutZero d M := by
-- proof
  apply StatMech.FrontierA.isingTorusLowMomentum_centeredInt_mem_box hp

/--
[isingTorusCharacterDispersion_centered_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenLowMomentum.lean)
-/
@[path]
private lemma isingTorusCharacterDispersion_centered_lower_eq
  {d k M : Nat}
  {p : IsingDyadicTorus d k}
-- given
  (hp : p ∈ isingTorusLowMomentum d k M)
  (hM : M ≤ isingDyadicSide k / 2) :
-- imply
  (16 / (isingDyadicSide k : Real) ^ 2) * integerMomentumNormSq (isingTorusCenteredIntMomentum p) ≤ isingTorusCharacterDispersion (isingTorusMomentumChar p) := by
-- proof
  apply StatMech.FrontierA.isingTorusCharacterDispersion_centered_lower hp hM

/--
[isingTorusLowMomentum_inverseDispersion_term_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenLowMomentum.lean)
-/
@[path]
private lemma isingTorusLowMomentum_inverseDispersion_term_le_eq
  {d k M : Nat}
  {p : IsingDyadicTorus d k}
-- given
  (hp : p ∈ isingTorusLowMomentum d k M)
  (hM : M ≤ isingDyadicSide k / 2) :
-- imply
  (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ ≤ ((isingDyadicSide k : Real) ^ 2 / 16) * (integerMomentumNormSq (isingTorusCenteredIntMomentum p))⁻¹ := by
-- proof
  apply StatMech.FrontierA.isingTorusLowMomentum_inverseDispersion_term_le hp hM

/--
[sum_inv_integerMomentumNormSq_lowMomentum_le_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenLowMomentum.lean)
-/
@[path]
private lemma sum_inv_integerMomentumNormSq_lowMomentum_le_box_eq
  {d k M : Nat}
  {d k M : Nat} :
-- imply
  ∑ p ∈ isingTorusLowMomentum d k M, (integerMomentumNormSq (isingTorusCenteredIntMomentum p))⁻¹ ≤ ∑ m ∈ integerMomentumBoxWithoutZero d M, (integerMomentumNormSq m)⁻¹ := by
-- proof
  apply StatMech.FrontierA.sum_inv_integerMomentumNormSq_lowMomentum_le_box d k M

/--
[isingTorusLowMomentum_inverseDispersion_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenLowMomentum.lean)
-/
@[path]
private lemma isingTorusLowMomentum_inverseDispersion_le_eq
  {d k M : Nat}
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ k M, 1 ≤ M → M ≤ isingDyadicSide k / 2 → (1 / (isingDyadicSide k : Real) ^ d) * ∑ p ∈ isingTorusLowMomentum d k M, (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ ≤ C * ((M : Real) / isingDyadicSide k) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.isingTorusLowMomentum_inverseDispersion_le hd


-- created on 2026-10-23
