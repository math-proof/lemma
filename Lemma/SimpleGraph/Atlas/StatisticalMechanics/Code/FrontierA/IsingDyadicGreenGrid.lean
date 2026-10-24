import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenGrid
open Finset Set StatMech StatMech.FrontierA


/--
[isingTorusCenteredMomentum_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusCenteredMomentum_apply_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k}
  {i : Fin d} :
-- imply
  isingTorusCenteredMomentum p i = ((p i).valMinAbs : Real) / isingDyadicSide k := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredMomentum_apply p i

/--
[isingTorusCenteredMomentumFun_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusCenteredMomentumFun_apply_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k}
  {i : Fin d} :
-- imply
  isingTorusCenteredMomentumFun p i = ((p i).valMinAbs : Real) / isingDyadicSide k := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredMomentumFun_apply p i

/--
[isingDyadicSide_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingDyadicSide_eq_eq
  {d k : Nat}
  {k : Nat} :
-- imply
  isingDyadicSide k = 2 ^ (k + 2) := by
-- proof
  apply StatMech.FrontierA.isingDyadicSide_eq k

/--
[isingDyadicSide_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingDyadicSide_pos_eq
  {d k : Nat}
  {k : Nat} :
-- imply
  0 < isingDyadicSide k := by
-- proof
  apply StatMech.FrontierA.isingDyadicSide_pos k

/--
[isingTorusCenteredMomentum_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusCenteredMomentum_mem_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusCenteredMomentum p ∈ isingNormalizedMomentumCube d := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredMomentum_mem p

/--
[isingTorusCenteredIntMomentum_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusCenteredIntMomentum_injective_eq
  {d k : Nat} :
-- imply
  Function.Injective (isingTorusCenteredIntMomentum : IsingDyadicTorus d k → Fin d → Int) := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredIntMomentum_injective

/--
[isingTorusCenteredMomentum_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusCenteredMomentum_injective_eq
  {d k : Nat} :
-- imply
  Function.Injective (isingTorusCenteredMomentum : IsingDyadicTorus d k → IsingMomentumSpace d) := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredMomentum_injective

/--
[isingTorusCenteredMomentumFun_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusCenteredMomentumFun_injective_eq
  {d k : Nat} :
-- imply
  Function.Injective (isingTorusCenteredMomentumFun : IsingDyadicTorus d k → Fin d → Real) := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredMomentumFun_injective

/--
[isingTorusCenteredMomentum_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusCenteredMomentum_eq_zero_iff_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusCenteredMomentum p = 0 ↔ p = 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredMomentum_eq_zero_iff p

/--
[isingTorusLowMomentum_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusLowMomentum_mem_iff_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  p ∈ isingTorusLowMomentum d k M ↔ p ≠ 0 ∧ ∀ i : Fin d, (p i).valMinAbs.natAbs ≤ M := by
-- proof
  apply StatMech.FrontierA.isingTorusLowMomentum_mem_iff p

/--
[isingTorusCharacterDispersion_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean)
-/
@[path]
private lemma isingTorusCharacterDispersion_centered_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusCharacterDispersion (isingTorusMomentumChar p) = ∑ i : Fin d, (2 - 2 * Real.cos (2 * Real.pi * isingTorusCenteredMomentum p i)) := by
-- proof
  apply StatMech.FrontierA.isingTorusCharacterDispersion_centered p


-- created on 2026-10-23
