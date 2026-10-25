import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingAsymmRefute
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[bcar_site_eq_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_site_eq_x0_eq
  {a : Site 2}
-- given
  (ha0 : a 0 = 0) :
-- imply
  a = ![0, a 1] := by
-- proof
  apply StatMech.Universality.bcar_site_eq_x0 ha0

/--
[bcar_open_no_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_open_no_x0_eq
  {a b : Site 2}
-- given
  (hopen : bcar_cfg s(a, b) = true) :
-- imply
  a 0 ≠ 0 ∧ b 0 ≠ 0 := by
-- proof
  apply StatMech.Universality.bcar_open_no_x0 hopen

/--
[bcar_open_keeps_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_open_keeps_x0_eq
  {a b : Site 2}
-- given
  (hopen : bcar_cfg s(a, b) = true) :
-- imply
  (a 0 = 0 ↔ b 0 = 0) := by
-- proof
  apply StatMech.Universality.bcar_open_keeps_x0 hopen

/--
[bcar_walk_keeps_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_walk_keeps_x0_eq
  {x y : (rect 0 2 0 1 : Set (Site 2))}
  {w : (openSubgraphInduce 2 bcar_cfg (rect 0 2 0 1)).Walk x y} :
-- imply
  ((x : Site 2) 0 = 0 ↔ (y : Site 2) 0 = 0) := by
-- proof
  apply StatMech.Universality.bcar_walk_keeps_x0 w

/--
[bcar_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_noH_eq :
-- imply
  ¬ HorizontalCrossing bcar_cfg 0 2 0 1 := by
-- proof
  apply StatMech.Universality.bcar_noH

/--
[bcar_crossEdge_symm_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_crossEdge_symm_mk_eq
  {x y : Site 2} :
-- imply
  crossEdge.symm s(x, y) = s(rot90Inv x, rot90Inv y) := by
-- proof
  apply StatMech.Universality.bcar_crossEdge_symm_mk x y

/--
[bcar_topRung_dualClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_topRung_dualClosed_eq
  {p q : Site 2}
-- given
  (hp1 : p 1 = 1)
  (hq1 : q 1 = 2)
  (hpq0 : p 0 = q 0)
  (hx : p 0 = -1 ∨ p 0 = 0) :
-- imply
  dualConfig bcar_cfg s(p, q) = false := by
-- proof
  apply StatMech.Universality.bcar_topRung_dualClosed hp1 hq1 hpq0 hx

/--
[bcar_dualOpen_keeps_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_dualOpen_keeps_snd_le_eq
  {p q : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj p q)
  (hp : p ∈ rect (-1) 0 0 2)
  (hq : q ∈ rect (-1) 0 0 2)
  (hopen : dualConfig bcar_cfg s(p, q) = true)
  (hple : p 1 ≤ 1) :
-- imply
  q 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.bcar_dualOpen_keeps_snd_le hadj hp hq hopen hple

/--
[bcar_dualVwalk_keeps_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_dualVwalk_keeps_snd_eq
  {x y : (rect (-1) 0 0 2 : Set (Site 2))}
  {w : (openSubgraphInduce 2 (dualConfig bcar_cfg) (rect (-1) 0 0 2)).Walk x y}
-- given
  (hx : (x : Site 2) 1 ≤ 1) :
-- imply
  (y : Site 2) 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.bcar_dualVwalk_keeps_snd w hx

/--
[bcar_noV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_noV_eq :
-- imply
  ¬ DualVerticalCrossing bcar_cfg (-1) 0 0 2 := by
-- proof
  apply StatMech.Universality.bcar_noV

/--
[bcar_noH_noV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_noH_noV_eq :
-- imply
  ¬ HorizontalCrossing bcar_cfg 0 2 0 1 ∧ ¬ DualVerticalCrossing bcar_cfg (-1) 0 0 2 := by
-- proof
  apply StatMech.Universality.bcar_noH_noV

/--
[bcar_asymm_dichotomy_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingAsymmRefute.lean)
-/
@[path]
private lemma bcar_asymm_dichotomy_false_eq :
-- imply
  ¬ ((horizontalCrossingEvent 0 2 0 1)ᶜ ⊆ dualVerticalCrossingEvent (-1) 0 0 2) := by
-- proof
  apply StatMech.Universality.bcar_asymm_dichotomy_false


-- created on 2026-10-23
