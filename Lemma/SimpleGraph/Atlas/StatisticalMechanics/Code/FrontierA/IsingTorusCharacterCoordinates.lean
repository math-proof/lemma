import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingTorusCharacterCoordinates
open Finset StatMech StatMech.FrontierA


/--
[isingTorusMomentumChar_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean)
-/
@[path]
private lemma isingTorusMomentumChar_apply_eq
  {d k : Nat}
  {p x : IsingDyadicTorus d k} :
-- imply
  isingTorusMomentumChar p x = ∏ i : Fin d, ZMod.stdAddChar (p i * x i) := by
-- proof
  apply StatMech.FrontierA.isingTorusMomentumChar_apply p x

/--
[isingTorusMomentumChar_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean)
-/
@[path]
private lemma isingTorusMomentumChar_single_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k}
  {i : Fin d}
  {a : ZMod (2 ^ (k + 2))} :
-- imply
  isingTorusMomentumChar p (Pi.single i a) = ZMod.stdAddChar (p i * a) := by
-- proof
  apply StatMech.FrontierA.isingTorusMomentumChar_single p i a

/--
[isingTorusMomentumChar_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean)
-/
@[path]
private lemma isingTorusMomentumChar_injective_eq
  {d k : Nat} :
-- imply
  Function.Injective (isingTorusMomentumChar : IsingDyadicTorus d k → AddChar (IsingDyadicTorus d k) Complex) := by
-- proof
  apply StatMech.FrontierA.isingTorusMomentumChar_injective

/--
[isingTorusMomentumEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean)
-/
@[path]
private lemma isingTorusMomentumEquiv_apply_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusMomentumEquiv p = isingTorusMomentumChar p := by
-- proof
  apply StatMech.FrontierA.isingTorusMomentumEquiv_apply p

/--
[isingTorusCharacterDispersion_momentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean)
-/
@[path]
private lemma isingTorusCharacterDispersion_momentum_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusCharacterDispersion (isingTorusMomentumChar p) = ∑ i : Fin d, Complex.normSq (1 - ZMod.stdAddChar (p i)) := by
-- proof
  apply StatMech.FrontierA.isingTorusCharacterDispersion_momentum p

/--
[normSq_one_sub_stdAddChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean)
-/
@[path]
private lemma normSq_one_sub_stdAddChar_eq
  {d k : Nat}
  {a : ZMod (2 ^ (k + 2))} :
-- imply
  Complex.normSq (1 - ZMod.stdAddChar a) = 2 - 2 * Real.cos (2 * Real.pi * (a.val : Real) / (2 ^ (k + 2) : Nat)) := by
-- proof
  apply StatMech.FrontierA.normSq_one_sub_stdAddChar a

/--
[isingTorusCharacterDispersion_momentum_cos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean)
-/
@[path]
private lemma isingTorusCharacterDispersion_momentum_cos_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusCharacterDispersion (isingTorusMomentumChar p) = ∑ i : Fin d, (2 - 2 * Real.cos (2 * Real.pi * ((p i).val : Real) / (2 ^ (k + 2) : Nat))) := by
-- proof
  apply StatMech.FrontierA.isingTorusCharacterDispersion_momentum_cos p

/--
[isingTorusMomentumChar_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean)
-/
@[path]
private lemma isingTorusMomentumChar_eq_zero_iff_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusMomentumChar p = 0 ↔ p = 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusMomentumChar_eq_zero_iff p


-- created on 2026-10-23
