import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.EulerTorus
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[bet_torus_defect_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/EulerTorus.lean)
-/
@[path]
private lemma bet_torus_defect_le_two_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : ℕ}
-- given
  (h : IsTorusDefect G δ) :
-- imply
  δ ≤ 2 := by
-- proof
  apply StatMech.BeffaraDC.bet_torus_defect_le_two h

/--
[bet_torusFaceCount_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/EulerTorus.lean)
-/
@[path]
private lemma bet_torusFaceCount_pos_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : ℕ}
-- given
  (h : IsTorusDefect G δ) :
-- imply
  1 ≤ torusFaceCount G δ := by
-- proof
  apply StatMech.BeffaraDC.bet_torusFaceCount_pos h

/--
[bet_torusFaceCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/EulerTorus.lean)
-/
@[path]
private lemma bet_torusFaceCount_eq_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : ℕ}
-- given
  (h : IsTorusDefect G δ) :
-- imply
  torusFaceCount G δ = (nullity G - δ) + 1 := by
-- proof
  apply StatMech.BeffaraDC.bet_torusFaceCount_eq h

/--
[bet_euler_torus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/EulerTorus.lean)
-/
@[path]
private lemma bet_euler_torus_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : ℕ}
-- given
  (h : IsTorusDefect G δ) :
-- imply
  (Nat.card V : ℤ) - G.edgeSet.ncard + torusFaceCount G δ = Nat.card G.ConnectedComponent + 1 - δ := by
-- proof
  apply StatMech.BeffaraDC.bet_euler_torus h

/--
[bet_euler_torus_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/EulerTorus.lean)
-/
@[path]
private lemma bet_euler_torus_nat_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : ℕ}
-- given
  (h : IsTorusDefect G δ) :
-- imply
  Nat.card V + torusFaceCount G δ + δ = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
-- proof
  apply StatMech.BeffaraDC.bet_euler_torus_nat h

/--
[bet_euler_torus_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/EulerTorus.lean)
-/
@[path]
private lemma bet_euler_torus_planar_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  torusFaceCount G 0 = faceCount G ∧ (Nat.card V : ℤ) - G.edgeSet.ncard + torusFaceCount G 0 = Nat.card G.ConnectedComponent + 1 := by
-- proof
  apply StatMech.BeffaraDC.bet_euler_torus_planar G


-- created on 2026-10-23
