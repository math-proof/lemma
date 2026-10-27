import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusHalfTurn_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torusHalfTurn_apply_eq
  {L : ℕ}
  {v : ZMod L × ZMod L} :
-- imply
  torusHalfTurn L v = (-v.1, -v.2) := by
-- proof
  apply StatMech.BeffaraDC.torusHalfTurn_apply L v

/--
[torusHalfTurn_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torusHalfTurn_adj_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ZMod L × ZMod L} :
-- imply
  (onsTorusGraph L).Adj (torusHalfTurn L u) (torusHalfTurn L v) ↔ (onsTorusGraph L).Adj u v := by
-- proof
  apply StatMech.BeffaraDC.torusHalfTurn_adj_iff L u v

/--
[torusDualConfig_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torusDualConfig_dualConfig_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  torusDualConfig L (torusDualConfig L ω) = FK.reCfg (torusHalfTurn L) ω := by
-- proof
  apply StatMech.BeffaraDC.torusDualConfig_dualConfig L ω

/--
[torus_numClusters_dualConfig_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torus_numClusters_dualConfig_dualConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.numClusters (onsTorusGraph L) (torusDualConfig L (torusDualConfig L ω)) = FK.numClusters (onsTorusGraph L) ω := by
-- proof
  apply StatMech.BeffaraDC.torus_numClusters_dualConfig_dualConfig L ω

/--
[torusGeometricDefect_add_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torusGeometricDefect_add_dual_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  torusGeometricDefect L (FK.openSub (onsTorusGraph L) ω) + torusGeometricDefect L (FK.openSub (onsTorusGraph L) (torusDualConfig L ω)) = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusGeometricDefect_add_dual L ω

/--
[torusGeometricDefect_le_two_of_dual_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torusGeometricDefect_le_two_of_dual_nonneg_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))}
-- given
  (hdual : 0 ≤ torusGeometricDefect L (FK.openSub (onsTorusGraph L) (torusDualConfig L ω))) :
-- imply
  torusGeometricDefect L (FK.openSub (onsTorusGraph L) ω) ≤ 2 := by
-- proof
  apply StatMech.BeffaraDC.torusGeometricDefect_le_two_of_dual_nonneg L ω hdual

/--
[torus_openSub_configOfGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torus_openSub_configOfGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hK : K ≤ onsTorusGraph L) :
-- imply
  FK.openSub (onsTorusGraph L) (torusConfigOfGraph L K) = K := by
-- proof
  apply StatMech.BeffaraDC.torus_openSub_configOfGraph L K hK

/--
[torusGeometricDefect_add_dualCutGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torusGeometricDefect_add_dualCutGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hK : K ≤ onsTorusGraph L) :
-- imply
  torusGeometricDefect L K + torusGeometricDefect L (torusDualCutGraph L K) = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusGeometricDefect_add_dualCutGraph L K hK

/--
[torusDefectClassified_of_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean)
-/
@[path]
private lemma torusDefectClassified_of_nonnegative_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hnonneg : ∀ K : SimpleGraph (ZMod L × ZMod L), K ≤ onsTorusGraph L → 0 ≤ torusGeometricDefect L K) :
-- imply
  TorusDefectClassified L := by
-- proof
  apply StatMech.BeffaraDC.torusDefectClassified_of_nonnegative L hnonneg


-- created on 2026-10-23
