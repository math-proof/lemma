import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.SelfDualPointMassScore
open StatMech StatMech.FK


/--
[selfDualPoint_odds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SelfDualPointMassScore.lean)
-/
@[path]
private lemma selfDualPoint_odds_eq
  [Fintype V]
  [DecidableEq V]
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  BeffaraDC.selfDualPoint q / (1 - BeffaraDC.selfDualPoint q) = Real.sqrt q := by
-- proof
  apply StatMech.FK.selfDualPoint_odds hq

/--
[edgeProduct_selfDualPoint_eq_common_mul_sqrt_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SelfDualPointMassScore.lean)
-/
@[path]
private lemma edgeProduct_selfDualPoint_eq_common_mul_sqrt_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hq : 0 < q) :
-- imply
  edgeProduct G (BeffaraDC.selfDualPoint q) omega = (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card * (Real.sqrt q) ^ openCount G omega := by
-- proof
  apply StatMech.FK.edgeProduct_selfDualPoint_eq_common_mul_sqrt_pow G hq omega

/--
[bcWeight_selfDualPoint_eq_common_mul_sqrt_pow_score](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SelfDualPointMassScore.lean)
-/
@[path]
private lemma bcWeight_selfDualPoint_eq_common_mul_sqrt_pow_score_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {q : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hq : 0 < q) :
-- imply
  bcWeight G C (BeffaraDC.selfDualPoint q) q omega = (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card * (Real.sqrt q) ^ (openCount G omega + 2 * numClustersBC G C omega) := by
-- proof
  apply StatMech.FK.bcWeight_selfDualPoint_eq_common_mul_sqrt_pow_score G C hq omega

/--
[bcWeight_selfDualPoint_le_sqrt_pow_of_score_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SelfDualPointMassScore.lean)
-/
@[path]
private lemma bcWeight_selfDualPoint_le_sqrt_pow_of_score_le_eq
  [Fintype V]
  [DecidableEq V]
  {G C D : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  [DecidableRel D.Adj]
  {q : Real}
  {N : Nat}
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (hq : 1 <= q)
  (hscore : openCount G omega + 2 * numClustersBC G C omega <= openCount G eta + 2 * numClustersBC G D eta + N) :
-- imply
  bcWeight G C (BeffaraDC.selfDualPoint q) q omega <= (Real.sqrt q) ^ N * bcWeight G D (BeffaraDC.selfDualPoint q) q eta := by
-- proof
  apply StatMech.FK.bcWeight_selfDualPoint_le_sqrt_pow_of_score_le G C D hq N omega eta hscore

/--
[bcWeight_selfDualPoint_le_qpow_of_score_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SelfDualPointMassScore.lean)
-/
@[path]
private lemma bcWeight_selfDualPoint_le_qpow_of_score_le_eq
  [Fintype V]
  [DecidableEq V]
  {G C D : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  [DecidableRel D.Adj]
  {q : Real}
  {N : Nat}
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (hq : 1 <= q)
  (hscore : openCount G omega + 2 * numClustersBC G C omega <= openCount G eta + 2 * numClustersBC G D eta + N) :
-- imply
  bcWeight G C (BeffaraDC.selfDualPoint q) q omega <= q ^ N * bcWeight G D (BeffaraDC.selfDualPoint q) q eta := by
-- proof
  apply StatMech.FK.bcWeight_selfDualPoint_le_qpow_of_score_le G C D hq N omega eta hscore

/--
[bcProb_selfDualPoint_le_qpow_of_score_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SelfDualPointMassScore.lean)
-/
@[path]
private lemma bcProb_selfDualPoint_le_qpow_of_score_le_eq
  [Fintype V]
  [DecidableEq V]
  {G C D : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  [DecidableRel D.Adj]
  {q : Real}
  {N : Nat}
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (hCD : C <= D)
  (hq : 1 <= q)
  (hscore : openCount G omega + 2 * numClustersBC G C omega <= openCount G eta + 2 * numClustersBC G D eta + N) :
-- imply
  bcProb G C (BeffaraDC.selfDualPoint q) q omega <= q ^ N * bcProb G D (BeffaraDC.selfDualPoint q) q eta := by
-- proof
  apply StatMech.FK.bcProb_selfDualPoint_le_qpow_of_score_le G C D hCD hq N omega eta hscore

/--
[bcProb_selfDualPoint_le_sqrt_pow_of_score_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SelfDualPointMassScore.lean)
-/
@[path]
private lemma bcProb_selfDualPoint_le_sqrt_pow_of_score_le_eq
  [Fintype V]
  [DecidableEq V]
  {G C D : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  [DecidableRel D.Adj]
  {q : Real}
  {N : Nat}
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (hCD : C <= D)
  (hq : 1 <= q)
  (hscore : openCount G omega + 2 * numClustersBC G C omega <= openCount G eta + 2 * numClustersBC G D eta + N) :
-- imply
  bcProb G C (BeffaraDC.selfDualPoint q) q omega <= (Real.sqrt q) ^ N * bcProb G D (BeffaraDC.selfDualPoint q) q eta := by
-- proof
  apply StatMech.FK.bcProb_selfDualPoint_le_sqrt_pow_of_score_le G C D hCD hq N omega eta hscore


-- created on 2026-10-23
