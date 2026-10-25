import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossing.Part4
open StatMech StatMech.Onsager StatMech.Onsager.WalkCrossing


/--
[snd_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma snd_step_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (pos d (k + 1)).2 = (pos d k).2 + (stepOf (d k)).2 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.snd_step d hclosed k

/--
[fst_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma fst_step_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (pos d (k + 1)).1 = (pos d k).1 + (stepOf (d k)).1 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.fst_step d hclosed k

/--
[vert_x_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma vert_x_const_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : isVertEdge (d k)) :
-- imply
  (pos d (k + 1)).1 = (pos d k).1 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.vert_x_const d hclosed k hk

/--
[vert_y_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma vert_y_step_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : isVertEdge (d k)) :
-- imply
  (pos d (k + 1)).2 = (pos d k).2 + 1 ∨ (pos d (k + 1)).2 = (pos d k).2 - 1 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.vert_y_step d hclosed k hk

/--
[horiz_y_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma horiz_y_const_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : isHorizEdge (d k)) :
-- imply
  (pos d (k + 1)).2 = (pos d k).2 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.horiz_y_const d hclosed k hk

/--
[horiz_x_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma horiz_x_step_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : isHorizEdge (d k)) :
-- imply
  (pos d (k + 1)).1 = (pos d k).1 + 1 ∨ (pos d (k + 1)).1 = (pos d k).1 - 1 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.horiz_x_step d hclosed k hk

/--
[stepOf_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma stepOf_snd_eq
  {n : ℕ}
  [NeZero n]
  {w : Fin 4} :
-- imply
  (stepOf w).2 = 0 ∨ (stepOf w).2 = 1 ∨ (stepOf w).2 = -1 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.stepOf_snd w

/--
[stepOf_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma stepOf_fst_eq
  {n : ℕ}
  [NeZero n]
  {w : Fin 4} :
-- imply
  (stepOf w).1 = 0 ∨ (stepOf w).1 = 1 ∨ (stepOf w).1 = -1 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.stepOf_fst w

/--
[snd_step_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma snd_step_bound_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (pos d (k + 1)).2 = (pos d k).2 ∨ (pos d (k + 1)).2 = (pos d k).2 + 1 ∨ (pos d (k + 1)).2 = (pos d k).2 - 1 := by
-- proof
  apply StatMech.Onsager.WalkCrossing.snd_step_bound d hclosed k

/--
[upDown_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma upDown_card_eq_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m : ℤ}
-- given
  (_hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (Finset.univ.filter (fun k : Fin n => (pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2)).card = (Finset.univ.filter (fun k : Fin n => m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m)).card := by
-- proof
  apply StatMech.Onsager.WalkCrossing.upDown_card_eq d _hclosed m

/--
[fullLineCross_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma fullLineCross_even_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  Even (fullLineCross d m) := by
-- proof
  apply StatMech.Onsager.WalkCrossing.fullLineCross_even d hclosed m

/--
[onEdge_horiz_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma onEdge_horiz_endpoint_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
  {p : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : isHorizEdge (d k))
  (hp : onEdge d k p) :
-- imply
  p = pos d k ∨ p = pos d (k + 1) := by
-- proof
  apply StatMech.Onsager.WalkCrossing.onEdge_horiz_endpoint d hclosed k hk p hp

/--
[onEdge_vert_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma onEdge_vert_endpoint_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
  {p : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : isVertEdge (d k))
  (hp : onEdge d k p) :
-- imply
  p = pos d k ∨ p = pos d (k + 1) := by
-- proof
  apply StatMech.Onsager.WalkCrossing.onEdge_vert_endpoint d hclosed k hk p hp

/--
[horiz_vert_cross_shared_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma horiz_vert_cross_shared_vertex_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k j : Fin n}
  {p : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : isHorizEdge (d k))
  (hj : isVertEdge (d j))
  (hpk : onEdge d k p)
  (hpj : onEdge d j p) :
-- imply
  (p = pos d k ∨ p = pos d (k + 1)) ∧ (p = pos d j ∨ p = pos d (j + 1)) := by
-- proof
  apply StatMech.Onsager.WalkCrossing.horiz_vert_cross_shared_vertex d hclosed k j hk hj p hpk hpj

/--
[edges_cross_not_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma edges_cross_not_injective_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k j : Fin n}
  {p : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : isHorizEdge (d k))
  (hj : isVertEdge (d j))
  (hne1 : k ≠ j)
  (hne2 : k + 1 ≠ j)
  (hne3 : k ≠ j + 1)
  (hne4 : k + 1 ≠ j + 1)
  (hpk : onEdge d k p)
  (hpj : onEdge d j p) :
-- imply
  ¬ Function.Injective (pos d) := by
-- proof
  apply StatMech.Onsager.WalkCrossing.edges_cross_not_injective d hclosed k j hk hj hne1 hne2 hne3 hne4 p hpk hpj

/--
[rayCross_le_fullLineCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean)
-/
@[path]
private lemma rayCross_le_fullLineCross_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m qx : ℤ} :
-- imply
  rayCross d m qx ≤ fullLineCross d m := by
-- proof
  apply StatMech.Onsager.WalkCrossing.rayCross_le_fullLineCross d m qx


-- created on 2026-10-23
