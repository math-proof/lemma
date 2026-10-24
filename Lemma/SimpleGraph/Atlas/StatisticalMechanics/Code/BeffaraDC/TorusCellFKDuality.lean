import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.TorusCellFKDuality
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusCell_primalWeight_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellFKDuality.lean)
-/
@[path]
private lemma torusCell_primalWeight_openSub_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  torusCellPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) = FK.fkWeight (onsTorusGraph L) p q ω := by
-- proof
  apply StatMech.BeffaraDC.torusCell_primalWeight_openSub L p q ω

/--
[torusCell_dualWeight_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellFKDuality.lean)
-/
@[path]
private lemma torusCell_dualWeight_openSub_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  torusCellDualWeight L p q (FK.openSub (onsTorusGraph L) ω) = FK.fkWeight (onsTorusGraph L) p q (torusCellDualConfig L ω) := by
-- proof
  apply StatMech.BeffaraDC.torusCell_dualWeight_openSub L p q ω

/--
[torusCell_subgraph_edgeCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellFKDuality.lean)
-/
@[path]
private lemma torusCell_subgraph_edgeCount_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hK : K ≤ onsTorusGraph L) :
-- imply
  K.edgeSet.ncard ≤ (onsTorusGraph L).edgeFinset.card := by
-- proof
  apply StatMech.BeffaraDC.torusCell_subgraph_edgeCount_le L K hK

/--
[torusCell_clusterEuler_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellFKDuality.lean)
-/
@[path]
private lemma torusCell_clusterEuler_signed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)} :
-- imply
  ((K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 : ℕ) : ℤ) = ((Nat.card (ZMod L × ZMod L) + torusCellFaceCount L K : ℕ) : ℤ) + torusCellDefect L K := by
-- proof
  apply StatMech.BeffaraDC.torusCell_clusterEuler_signed L K

/--
[torusCell_weight_duality_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellFKDuality.lean)
-/
@[path]
private lemma torusCell_weight_duality_signed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
  {p q : ℝ}
-- given
  (hK : K ≤ onsTorusGraph L)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusCellPrimalWeight L p q K * q ^ ((onsTorusGraph L).edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) * torusCellDualWeight L (dualParam p q) q K * q ^ torusCellDefect L K := by
-- proof
  apply StatMech.BeffaraDC.torusCell_weight_duality_signed L K hK hp hp1 hq

/--
[torusCell_fkWeight_duality_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellFKDuality.lean)
-/
@[path]
private lemma torusCell_fkWeight_duality_signed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkWeight (onsTorusGraph L) p q ω * q ^ ((onsTorusGraph L).edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) * FK.fkWeight (onsTorusGraph L) (dualParam p q) q (torusCellDualConfig L ω) * q ^ torusCellDefect L (FK.openSub (onsTorusGraph L) ω) := by
-- proof
  apply StatMech.BeffaraDC.torusCell_fkWeight_duality_signed L ω hp hp1 hq


-- created on 2026-10-23
