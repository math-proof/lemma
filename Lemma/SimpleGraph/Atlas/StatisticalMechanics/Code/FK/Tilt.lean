import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
open StatMech StatMech.FK


/--
[openCount_add_closedCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma openCount_add_closedCount_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  openCount G ω + closedCount G ω = G.edgeFinset.card := by
-- proof
  apply StatMech.FK.openCount_add_closedCount G ω

/--
[edgeProduct_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma edgeProduct_eq_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  edgeProduct G p ω = p ^ openCount G ω * (1 - p) ^ closedCount G ω := by
-- proof
  apply StatMech.FK.edgeProduct_eq_pow G p ω

/--
[tiltFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma tiltFactor_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 : ℝ}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1) :
-- imply
  0 < tiltFactor p1 p2 := by
-- proof
  apply StatMech.FK.tiltFactor_pos G hp1 hp1' hp2 hp2'

/--
[tiltFactor_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma tiltFactor_lt_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 : ℝ}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hlt : p2 < p1) :
-- imply
  tiltFactor p1 p2 < 1 := by
-- proof
  apply StatMech.FK.tiltFactor_lt_one G hp1 hp1' hlt

/--
[pow_tilt_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma pow_tilt_aux_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 : ℝ}
  {o c : ℕ}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1) :
-- imply
  p2 ^ o * (1 - p2) ^ c = ((1 - p2) / (1 - p1)) ^ (o + c) * tiltFactor p1 p2 ^ o * (p1 ^ o * (1 - p1) ^ c) := by
-- proof
  apply StatMech.FK.pow_tilt_aux G hp1 hp1' hp2 hp2' o c

/--
[fkWeight_tilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma fkWeight_tilt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1) :
-- imply
  fkWeight G p2 q ω = ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card * tiltFactor p1 p2 ^ openCount G ω * fkWeight G p1 q ω := by
-- proof
  apply StatMech.FK.fkWeight_tilt G hp1 hp1' hp2 hp2' ω

/--
[fkExpect_tiltPow_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma fkExpect_tiltPow_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 q : ℝ}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hq : 0 < q) :
-- imply
  0 < fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
-- proof
  apply StatMech.FK.fkExpect_tiltPow_pos G hp1 hp1' hp2 hp2' hq

/--
[fkZ_tilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma fkZ_tilt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 q : ℝ}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1) :
-- imply
  fkZ G p2 q = ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card * ∑ ω : ConfigSpace (Sym2 V), tiltFactor p1 p2 ^ openCount G ω * fkWeight G p1 q ω := by
-- proof
  apply StatMech.FK.fkZ_tilt G hp1 hp1' hp2 hp2'

/--
[fkProb_tilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma fkProb_tilt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hq : 0 < q) :
-- imply
  fkProb G p2 q ω = tiltFactor p1 p2 ^ openCount G ω * fkProb G p1 q ω / fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
-- proof
  apply StatMech.FK.fkProb_tilt G hp1 hp1' hp2 hp2' hq ω

/--
[fkExpect_tilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean)
-/
@[path]
private lemma fkExpect_tilt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 q : ℝ}
  {X : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hq : 0 < q) :
-- imply
  fkExpect G p2 q X = fkExpect G p1 q (fun ω => X ω * tiltFactor p1 p2 ^ openCount G ω) / fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
-- proof
  apply StatMech.FK.fkExpect_tilt G hp1 hp1' hp2 hp2' hq X


-- created on 2026-10-23
