import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusQuarterTurn_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusQuarterTurn_apply_eq
  {L : ℕ}
  {v : ZMod L × ZMod L} :
-- imply
  torusQuarterTurn L v = (v.2, -v.1) := by
-- proof
  apply StatMech.BeffaraDC.torusQuarterTurn_apply L v

/--
[torusQuarterTurn_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusQuarterTurn_adj_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ZMod L × ZMod L} :
-- imply
  (onsTorusGraph L).Adj (torusQuarterTurn L u) (torusQuarterTurn L v) ↔ (onsTorusGraph L).Adj u v := by
-- proof
  apply StatMech.BeffaraDC.torusQuarterTurn_adj_iff L u v

/--
[torusDualCutGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusDualCutGraph_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {f g : ZMod L × ZMod L} :
-- imply
  (torusDualCutGraph L G).Adj f g ↔ (onsTorusGraph L).Adj f g ∧ ¬ G.Adj (torusQuarterTurn L f) (torusQuarterTurn L g) := by
-- proof
  apply StatMech.BeffaraDC.torusDualCutGraph_adj L G f g

/--
[geometric_euler_torus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma geometric_euler_torus_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)} :
-- imply
  (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard + torusGeometricFaceCount L G = Nat.card G.ConnectedComponent + 1 - torusGeometricDefect L G := by
-- proof
  apply StatMech.BeffaraDC.geometric_euler_torus L G

/--
[geometric_euler_torus_of_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma geometric_euler_torus_of_defect_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {δ : ℕ}
-- given
  (hδ : torusGeometricDefect L G = δ) :
-- imply
  (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard + torusGeometricFaceCount L G = Nat.card G.ConnectedComponent + 1 - δ := by
-- proof
  apply StatMech.BeffaraDC.geometric_euler_torus_of_defect L G δ hδ

/--
[torusDualCutGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusDualCutGraph_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)} :
-- imply
  torusDualCutGraph L G ≤ onsTorusGraph L := by
-- proof
  apply StatMech.BeffaraDC.torusDualCutGraph_le L G

/--
[torusDualCutGraph_anti](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusDualCutGraph_anti_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G H : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hGH : G ≤ H) :
-- imply
  torusDualCutGraph L H ≤ torusDualCutGraph L G := by
-- proof
  apply StatMech.BeffaraDC.torusDualCutGraph_anti L hGH

/--
[torusGeometricFaceCount_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusGeometricFaceCount_mono_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G H : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hGH : G ≤ H) :
-- imply
  torusGeometricFaceCount L G ≤ torusGeometricFaceCount L H := by
-- proof
  apply StatMech.BeffaraDC.torusGeometricFaceCount_mono L hGH

/--
[torusDualCutGraph_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusDualCutGraph_bot_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  torusDualCutGraph L (⊥ : SimpleGraph (ZMod L × ZMod L)) = onsTorusGraph L := by
-- proof
  apply StatMech.BeffaraDC.torusDualCutGraph_bot L

/--
[torusDualCutGraph_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusDualCutGraph_full_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  torusDualCutGraph L (onsTorusGraph L) = ⊥ := by
-- proof
  apply StatMech.BeffaraDC.torusDualCutGraph_full L

/--
[torusGeometricFaceCount_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusGeometricFaceCount_full_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  torusGeometricFaceCount L (onsTorusGraph L) = L ^ 2 := by
-- proof
  apply StatMech.BeffaraDC.torusGeometricFaceCount_full L

/--
[torusGeometricFaceCount_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusGeometricFaceCount_bot_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hconn : (onsTorusGraph L).Connected) :
-- imply
  torusGeometricFaceCount L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 1 := by
-- proof
  apply StatMech.BeffaraDC.torusGeometricFaceCount_bot L hconn

/--
[torusGeometricDefect_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusGeometricDefect_bot_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hconn : (onsTorusGraph L).Connected) :
-- imply
  torusGeometricDefect L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 0 := by
-- proof
  apply StatMech.BeffaraDC.torusGeometricDefect_bot L hconn

/--
[torusGeometricDefect_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean)
-/
@[path]
private lemma torusGeometricDefect_full_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hconn : (onsTorusGraph L).Connected) :
-- imply
  torusGeometricDefect L (onsTorusGraph L) = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusGeometricDefect_full L hconn


-- created on 2026-10-23
