import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TwoPoint
open SimpleGraph StatMech StatMech.FK


/--
[openSub_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma openSub_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hab : a ≤ b) :
-- imply
  openSub G a ≤ openSub G b := by
-- proof
  apply StatMech.FK.openSub_mono G hab

/--
[mem_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma mem_connEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  ω ∈ connEvent G x y ↔ (openSub G ω).Reachable x y := by
-- proof
  apply StatMech.FK.mem_connEvent G

/--
[connEvent_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma connEvent_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V} :
-- imply
  connEvent G x x = Set.univ := by
-- proof
  apply StatMech.FK.connEvent_self G x

/--
[connEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma connEvent_isIncreasing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V} :
-- imply
  IsIncreasing (connEvent G x y) := by
-- proof
  apply StatMech.FK.connEvent_isIncreasing G x y

/--
[allOpen_mem_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma allOpen_mem_connEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (h : G.Reachable x y) :
-- imply
  (fun _ => true) ∈ connEvent G x y := by
-- proof
  apply StatMech.FK.allOpen_mem_connEvent G h

/--
[twoPointFun_eq_sum_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma twoPointFun_eq_sum_filter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V} :
-- imply
  twoPointFun G p q x y = ∑ ω ∈ Finset.univ.filter (· ∈ connEvent G x y), fkProb G p q ω := by
-- proof
  apply StatMech.FK.twoPointFun_eq_sum_filter G p q x y

/--
[twoPointFun_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma twoPointFun_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ twoPointFun G p q x y := by
-- proof
  apply StatMech.FK.twoPointFun_nonneg G hp hp1 hq x y

/--
[twoPointFun_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma twoPointFun_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  twoPointFun G p q x y ≤ 1 := by
-- proof
  apply StatMech.FK.twoPointFun_le_one G hp hp1 hq x y

/--
[twoPointFun_pos_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma twoPointFun_pos_of_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (h : G.Reachable x y) :
-- imply
  0 < twoPointFun G p q x y := by
-- proof
  apply StatMech.FK.twoPointFun_pos_of_reachable G hp hp1 hq h

/--
[twoPointFun_self_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma twoPointFun_self_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < twoPointFun G p q x x := by
-- proof
  apply StatMech.FK.twoPointFun_self_pos G hp hp1 hq x

/--
[twoPointFun_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean)
-/
@[path]
private lemma twoPointFun_fkg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y u v : V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  twoPointFun G p q x y * twoPointFun G p q u v ≤ ∑ ω, fkProb G p q ω * (connEvent G x y ∩ connEvent G u v).indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.FK.twoPointFun_fkg G hp hp1 hq x y u v


-- created on 2026-10-23
