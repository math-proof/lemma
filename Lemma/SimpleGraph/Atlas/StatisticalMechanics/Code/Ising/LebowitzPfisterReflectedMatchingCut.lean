import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
open Finset StatMech StatMech.Ising


/--
[lpReflectSource_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectSource_symmDiff_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1}
  {A B : Finset W} :
-- imply
  lpReflectSource R (A ∆ B) = lpReflectSource R A ∆ lpReflectSource R B := by
-- proof
  apply StatMech.Ising.lpReflectSource_symmDiff R A B

/--
[lpReflectSource_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectSource_empty_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1} :
-- imply
  lpReflectSource R ∅ = ∅ := by
-- proof
  apply StatMech.Ising.lpReflectSource_empty R

/--
[lpReflectSource_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectSource_seam_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1}
  {i : I} :
-- imply
  lpReflectSource R (lpMatchingSeamSource left right i) = lpMatchingSeamSource left right i := by
-- proof
  apply StatMech.Ising.lpReflectSource_seam R i

/--
[lpReflectSource_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectSource_ghost_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1} :
-- imply
  lpReflectSource R (lpMatchingGhostSource g0 g1) = lpMatchingGhostSource g0 g1 := by
-- proof
  apply StatMech.Ising.lpReflectSource_ghost R

/--
[lpReflectSource_matchingCommonSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectSource_matchingCommonSource_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1}
  {i j : I} :
-- imply
  lpReflectSource R (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1) = lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1 := by
-- proof
  apply StatMech.Ising.lpReflectSource_matchingCommonSource R i j

/--
[lpReflectedMatchingCut_bondEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectedMatchingCut_bondEnergy_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1}
  {sigma : ConfigSpace W} :
-- imply
  (∑ e ∈ G.edgeFinset, J e * bond (isingCfgEquiv R.reflect sigma) e) = ∑ e ∈ G.edgeFinset, J e * bond sigma e := by
-- proof
  apply StatMech.Ising.lpReflectedMatchingCut_bondEnergy R sigma

/--
[lpReflectedMatchingCut_boltzmannJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectedMatchingCut_boltzmannJ_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1}
  {beta : Real}
  {sigma : ConfigSpace W} :
-- imply
  boltzmannJ G beta J (isingCfgEquiv R.reflect sigma) = boltzmannJ G beta J sigma := by
-- proof
  apply StatMech.Ising.lpReflectedMatchingCut_boltzmannJ R beta sigma

/--
[lpReflectedMatchingCut_expectationJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectedMatchingCut_expectationJ_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1}
  {beta : Real}
  {S : Finset W} :
-- imply
  expectationJ G beta J (lpReflectSource R S) = expectationJ G beta J S := by
-- proof
  apply StatMech.Ising.lpReflectedMatchingCut_expectationJ R beta S

/--
[lpReflectedMatchingCut_currentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean)
-/
@[path]
private lemma lpReflectedMatchingCut_currentSum_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {J : Sym2 W -> Real}
  {left right : I -> W}
  {g0 g1 : W}
  {R : LPReflectedMatchingCut G J left right g0 g1}
  {beta : Real}
  {S : Finset W} :
-- imply
  currentSum G beta J (lpReflectSource R S) = currentSum G beta J S := by
-- proof
  apply StatMech.Ising.lpReflectedMatchingCut_currentSum R beta S


-- created on 2026-10-23
