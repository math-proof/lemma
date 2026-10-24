import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeRankSimplex
open StatMech StatMech.Ising


/--
[fourBridge_rankMass_recover_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRankSimplex.lean)
-/
@[path]
private lemma fourBridge_rankMass_recover_one_eq
  [Fintype V]
  [DecidableEq V]
  {a b c d : Real} :
-- imply
  a = 4 * (fourBridgeRankMass a b c d 4 - fourBridgeRankMass a b c d 0) + 2 * (fourBridgeRankMass a b c d 3 - fourBridgeRankMass a b c d 1) := by
-- proof
  apply StatMech.Ising.fourBridge_rankMass_recover_one a b c d

/--
[fourBridge_rankMass_recover_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRankSimplex.lean)
-/
@[path]
private lemma fourBridge_rankMass_recover_two_eq
  [Fintype V]
  [DecidableEq V]
  {a b c d : Real} :
-- imply
  b = 6 * (fourBridgeRankMass a b c d 0 + fourBridgeRankMass a b c d 4) - 2 * fourBridgeRankMass a b c d 2 := by
-- proof
  apply StatMech.Ising.fourBridge_rankMass_recover_two a b c d

/--
[fourBridge_rankMass_recover_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRankSimplex.lean)
-/
@[path]
private lemma fourBridge_rankMass_recover_three_eq
  [Fintype V]
  [DecidableEq V]
  {a b c d : Real} :
-- imply
  c = 4 * (fourBridgeRankMass a b c d 4 - fourBridgeRankMass a b c d 0) + 2 * (fourBridgeRankMass a b c d 1 - fourBridgeRankMass a b c d 3) := by
-- proof
  apply StatMech.Ising.fourBridge_rankMass_recover_three a b c d

/--
[fourBridge_rankMass_recover_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRankSimplex.lean)
-/
@[path]
private lemma fourBridge_rankMass_recover_four_eq
  [Fintype V]
  [DecidableEq V]
  {a b c d : Real} :
-- imply
  d = fourBridgeRankMass a b c d 0 - fourBridgeRankMass a b c d 1 + fourBridgeRankMass a b c d 2 - fourBridgeRankMass a b c d 3 + fourBridgeRankMass a b c d 4 := by
-- proof
  apply StatMech.Ising.fourBridge_rankMass_recover_four a b c d

/--
[fourBridgeRankMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRankSimplex.lean)
-/
@[path]
private lemma fourBridgeRankMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {i : Fin 5}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 <= fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_nonneg G J hf w x y z i

/--
[fourBridgeRankMass_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRankSimplex.lean)
-/
@[path]
private lemma fourBridgeRankMass_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {i : Fin 5}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 1 := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_le_one G J hf w x y z i


-- created on 2026-10-23
