import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[bcc_site_eq_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_site_eq_x0_eq
  {a : Site 2}
-- given
  (ha0 : a 0 = 0) :
-- imply
  a = ![0, a 1] := by
-- proof
  apply StatMech.Universality.bcc_site_eq_x0 ha0

/--
[bcc_site_eq_x1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_site_eq_x1_eq
  {b : Site 2}
  {c : ℤ}
-- given
  (hb0 : b 0 = 1)
  (h0 : b 1 = c) :
-- imply
  b = ![1, c] := by
-- proof
  apply StatMech.Universality.bcc_site_eq_x1 hb0 h0

/--
[bcc_is_wall_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_is_wall_edge_eq
  {a b : Site 2}
-- given
  (ha0 : a 0 = 0)
  (hb0 : b 0 = 1)
  (h0 : a 1 = b 1)
  (hc : a 1 = 0 ∨ a 1 = 1 ∨ a 1 = 2) :
-- imply
  s(a, b) = s(![0,0],![1,0]) ∨ s(a, b) = s(![0,1],![1,1]) ∨ s(a, b) = s(![0,2],![1,2]) := by
-- proof
  apply StatMech.Universality.bcc_is_wall_edge ha0 hb0 h0 hc

/--
[bcc_wall_open_keeps_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_wall_open_keeps_x0_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b)
  (ha : a ∈ rect 0 2 0 2)
  (hb : b ∈ rect 0 2 0 2)
  (hopen : bcc_wallCfg s(a, b) = true) :
-- imply
  (a 0 = 0 ↔ b 0 = 0) := by
-- proof
  apply StatMech.Universality.bcc_wall_open_keeps_x0 hab ha hb hopen

/--
[bcc_wall_walk_keeps_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_wall_walk_keeps_x0_eq
  {x y : (rect 0 2 0 2 : Set (Site 2))}
  {w : (openSubgraphInduce 2 bcc_wallCfg (rect 0 2 0 2)).Walk x y} :
-- imply
  ((x : Site 2) 0 = 0 ↔ (y : Site 2) 0 = 0) := by
-- proof
  apply StatMech.Universality.bcc_wall_walk_keeps_x0 w

/--
[bcc_noH_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_noH_wall_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.bcc_noH_wall

/--
[bcc_wallCfg_false_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_wallCfg_false_iff_eq
  {e : Sym2 (Site 2)} :
-- imply
  bcc_wallCfg e = false ↔ (e = s(![0,0],![1,0]) ∨ e = s(![0,1],![1,1]) ∨ e = s(![0,2],![1,2])) := by
-- proof
  apply StatMech.Universality.bcc_wallCfg_false_iff e

/--
[bcc_crossEdge_symm_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_crossEdge_symm_mk_eq
  {x y : Site 2} :
-- imply
  crossEdge.symm s(x, y) = s(rot90Inv x, rot90Inv y) := by
-- proof
  apply StatMech.Universality.bcc_crossEdge_symm_mk x y

/--
[bcc_dualOpen_char](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualOpen_char_eq
  {p q : Site 2}
-- given
  (h : dualConfig bcc_wallCfg s(p, q) = true) :
-- imply
  s(rot90Inv p, rot90Inv q) = s(![0,0],![1,0]) ∨ s(rot90Inv p, rot90Inv q) = s(![0,1],![1,1]) ∨ s(rot90Inv p, rot90Inv q) = s(![0,2],![1,2]) := by
-- proof
  apply StatMech.Universality.bcc_dualOpen_char h

/--
[bcc_rot90Inv_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_rot90Inv_fst_eq
  {p : Site 2} :
-- imply
  (rot90Inv p) 0 = p 1 := by
-- proof
  apply StatMech.Universality.bcc_rot90Inv_fst p

/--
[bcc_dualOpen_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualOpen_snd_le_eq
  {p q : Site 2}
-- given
  (h : dualConfig bcc_wallCfg s(p, q) = true) :
-- imply
  p 1 ≤ 1 ∧ q 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.bcc_dualOpen_snd_le h

/--
[bcc_dualVwalk_keeps_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualVwalk_keeps_snd_eq
  {x y : (rect 0 2 0 2 : Set (Site 2))}
  {w : (openSubgraphInduce 2 (dualConfig bcc_wallCfg) (rect 0 2 0 2)).Walk x y}
-- given
  (hx : (x : Site 2) 1 ≤ 1) :
-- imply
  (y : Site 2) 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.bcc_dualVwalk_keeps_snd w hx

/--
[bcc_noV_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_noV_wall_eq :
-- imply
  ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.bcc_noV_wall

/--
[bcc_wall_noH_noV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_wall_noH_noV_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.bcc_wall_noH_noV

/--
[bcc_dichotomy_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dichotomy_false_eq :
-- imply
  ¬ ((horizontalCrossingEvent 0 2 0 2)ᶜ ⊆ dualVerticalCrossingEvent 0 2 0 2) := by
-- proof
  apply StatMech.Universality.bcc_dichotomy_false

/--
[bcc_connWithin_bot_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_connWithin_bot_eq_eq
  {S : Set (Site 2)}
  {x y : S}
-- given
  (h : ConnectedWithin 2 bcc_botCfg S x y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Universality.bcc_connWithin_bot_eq h

/--
[bcc_leftReach_bot_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_leftReach_bot_eq_eq
  {n : ℤ} :
-- imply
  bcd_leftReach bcc_botCfg n = leftSide 0 n 0 n := by
-- proof
  apply StatMech.Universality.bcc_leftReach_bot_eq n

/--
[bcc_barrier_bot_char](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_barrier_bot_char_eq
  {v w : Site 2}
-- given
  (h : dcw_isBarrierEdge bcc_botCfg 2 v w) :
-- imply
  v 0 = 0 ∧ v 1 = w 1 ∧ w 0 = 1 := by
-- proof
  apply StatMech.Universality.bcc_barrier_bot_char h

/--
[bcc_dualBarrier_bot_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualBarrier_bot_snd_le_eq
  {p q : Site 2}
-- given
  (h : (dcw_dualBarrierGraph bcc_botCfg 2).Adj p q) :
-- imply
  p 1 ≤ 1 ∧ q 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.bcc_dualBarrier_bot_snd_le h

/--
[bcc_barrier_walk_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_barrier_walk_snd_le_eq
  {p q : Site 2}
  {c : (dcw_dualBarrierGraph bcc_botCfg 2).Walk p q}
-- given
  (hp : p 1 ≤ 1) :
-- imply
  ∀ z ∈ c.support, z 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.bcc_barrier_walk_snd_le c hp

/--
[bcc_barrierRoute_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_barrierRoute_false_eq :
-- imply
  ¬ dcw_BarrierRoute bcc_botCfg 2 := by
-- proof
  apply StatMech.Universality.bcc_barrierRoute_false

/--
[bcc_dualConfig_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualConfig_bot_eq
  {e : Sym2 (Site 2)} :
-- imply
  dualConfig bcc_botCfg e = true := by
-- proof
  apply StatMech.Universality.bcc_dualConfig_bot e

/--
[bcc_dualVert_botCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualVert_botCfg_eq :
-- imply
  DualVerticalCrossing bcc_botCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.bcc_dualVert_botCfg

/--
[bcc_dualVert_iff_reach_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualVert_iff_reach_top_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  DualVerticalCrossing ω 0 n 0 n ↔ ∃ y : Site 2, y ∈ topSide 0 n 0 n ∧ y ∈ bcc_dualBottomReach ω n := by
-- proof
  apply StatMech.Universality.bcc_dualVert_iff_reach_top ω n

/--
[bcc_bottomSide_in_dualReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_bottomSide_in_dualReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x : Site 2}
-- given
  (hx : x ∈ bottomSide 0 n 0 n) :
-- imply
  x ∈ bcc_dualBottomReach ω n := by
-- proof
  apply StatMech.Universality.bcc_bottomSide_in_dualReach ω n hx

/--
[bcc_dualReach_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualReach_extend_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcc_dualBottomReach ω n)
  (hwbox : w ∈ rect 0 n 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : dualConfig ω s(v, w) = true) :
-- imply
  w ∈ bcc_dualBottomReach ω n := by
-- proof
  apply StatMech.Universality.bcc_dualReach_extend ω n hv hwbox hadj hopen

/--
[bcc_dualReach_boundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualReach_boundary_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcc_dualBottomReach ω n)
  (hwbox : w ∈ rect 0 n 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ bcc_dualBottomReach ω n) :
-- imply
  dualConfig ω s(v, w) = false := by
-- proof
  apply StatMech.Universality.bcc_dualReach_boundary_closed ω n hv hwbox hadj hw

/--
[bcc_dualReach_boundary_primal_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualReach_boundary_primal_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcc_dualBottomReach ω n)
  (hwbox : w ∈ rect 0 n 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ bcc_dualBottomReach ω n) :
-- imply
  ω (crossEdge.symm s(v, w)) = true := by
-- proof
  apply StatMech.Universality.bcc_dualReach_boundary_primal_open ω n hv hwbox hadj hw

/--
[bcc_topSide_notin_dualReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_topSide_notin_dualReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {y : Site 2}
-- given
  (hno : ¬ DualVerticalCrossing ω 0 n 0 n)
  (hy : y ∈ topSide 0 n 0 n) :
-- imply
  y ∉ bcc_dualBottomReach ω n := by
-- proof
  apply StatMech.Universality.bcc_topSide_notin_dualReach ω n hno hy

/--
[bcc_dualReach_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean)
-/
@[path]
private lemma bcc_dualReach_separates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
-- given
  (hno : ¬ DualVerticalCrossing ω 0 n 0 n)
  (hx : x ∈ bottomSide 0 n 0 n)
  (hy : y ∈ topSide 0 n 0 n) :
-- imply
  ¬ (latticeMinusBarrier (bcc_dualBottomReach ω n)).Reachable x y := by
-- proof
  apply StatMech.Universality.bcc_dualReach_separates ω n hno hx hy


-- created on 2026-10-23
