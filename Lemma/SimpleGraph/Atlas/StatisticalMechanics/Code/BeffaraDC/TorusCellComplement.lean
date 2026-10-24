import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.TorusCellComplement
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusCellDiagonalShift_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCellDiagonalShift_apply_eq
  {L : ℕ}
  {v : ZMod L × ZMod L} :
-- imply
  torusCellDiagonalShift L v = (v.1 + 1, v.2 + 1) := by
-- proof
  apply StatMech.BeffaraDC.torusCellDiagonalShift_apply L v

/--
[torusCellDiagonalShift_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCellDiagonalShift_adj_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ZMod L × ZMod L} :
-- imply
  (onsTorusGraph L).Adj (torusCellDiagonalShift L u) (torusCellDiagonalShift L v) ↔ (onsTorusGraph L).Adj u v := by
-- proof
  apply StatMech.BeffaraDC.torusCellDiagonalShift_adj_iff L u v

/--
[torusCellCrossing_symm_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCellCrossing_symm_sq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : TorusAmbientEdge L} :
-- imply
  (((torusCellCrossing L).symm ((torusCellCrossing L).symm e) : TorusAmbientEdge L) : Sym2 (ZMod L × ZMod L)) = Sym2.map (torusCellDiagonalShift L) (e : Sym2 (ZMod L × ZMod L)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_symm_sq L e

/--
[torusCellPrimalOfDualEdge_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_sq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (ZMod L × ZMod L)}
-- given
  (he : e ∈ (onsTorusGraph L).edgeFinset) :
-- imply
  torusCellPrimalOfDualEdge L (torusCellPrimalOfDualEdge L e) = Sym2.map (torusCellDiagonalShift L) e := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_sq L he

/--
[torusCellDualConfig_dualConfig_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCellDualConfig_dualConfig_of_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (ZMod L × ZMod L))}
  {e : Sym2 (ZMod L × ZMod L)}
-- given
  (he : e ∈ (onsTorusGraph L).edgeFinset) :
-- imply
  torusCellDualConfig L (torusCellDualConfig L omega) e = FK.reCfg (torusCellDiagonalShift L) omega e := by
-- proof
  apply StatMech.BeffaraDC.torusCellDualConfig_dualConfig_of_mem L omega he

/--
[torusCell_openSub_dualConfig_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCell_openSub_dualConfig_dualConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.openSub (onsTorusGraph L) (torusCellDualConfig L (torusCellDualConfig L omega)) = FK.openSub (onsTorusGraph L) (FK.reCfg (torusCellDiagonalShift L) omega) := by
-- proof
  apply StatMech.BeffaraDC.torusCell_openSub_dualConfig_dualConfig L omega

/--
[torusCell_numClusters_dualConfig_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCell_numClusters_dualConfig_dualConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.numClusters (onsTorusGraph L) (torusCellDualConfig L (torusCellDualConfig L omega)) = FK.numClusters (onsTorusGraph L) omega := by
-- proof
  apply StatMech.BeffaraDC.torusCell_numClusters_dualConfig_dualConfig L omega

/--
[torusCellDefect_add_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCellDefect_add_dualConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  torusCellDefect L (FK.openSub (onsTorusGraph L) omega) + torusCellDefect L (FK.openSub (onsTorusGraph L) (torusCellDualConfig L omega)) = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_add_dualConfig L omega

/--
[torusCellDefect_add_dualCutGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean)
-/
@[path]
private lemma torusCellDefect_add_dualCutGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hK : K ≤ onsTorusGraph L) :
-- imply
  torusCellDefect L K + torusCellDefect L (torusCellDualCutGraph L K) = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_add_dualCutGraph L K hK


-- created on 2026-10-23
