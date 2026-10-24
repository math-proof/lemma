import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.BoundaryDecay
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[fbd_free_le_wired_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_free_le_wired_edgeMarg_eq
  {d : ℕ}
  {m : ℕ}
  {e : Sym2 (boxVerts d m)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  edgeMargProb (fkProb (boxGraph d m) p 2) e ≤ edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e := by
-- proof
  apply StatMech.FK.fbd_free_le_wired_edgeMarg m e hp hp1

/--
[fbd_wired_free_gap_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_wired_free_gap_tendsto_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p - freeEdgeDensity d 2 (edgeIncl d N eb) p)) := by
-- proof
  apply StatMech.FK.fbd_wired_free_gap_tendsto N eb hp hp1

/--
[fbd_wired_free_gap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_wired_free_gap_nonneg_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p ≤ wiredEdgeDensity d 2 (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.fbd_wired_free_gap_nonneg N eb hp hp1

/--
[fbd_box_wired_edgeMarg_innerEdgeLE_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_box_wired_edgeMarg_innerEdgeLE_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNm : N ≤ m) :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (innerEdgeLE d hNm eb) = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (innerEdgeLE d hNm (Sym2.map (S.lift N) eb)) := by
-- proof
  apply StatMech.FK.fbd_box_wired_edgeMarg_innerEdgeLE_boxSym S N m hNm eb

/--
[fbd_box_free_edgeMarg_innerEdgeLE_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_box_free_edgeMarg_innerEdgeLE_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNm : N ≤ m) :
-- imply
  edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm eb) = edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm (Sym2.map (S.lift N) eb)) := by
-- proof
  apply StatMech.FK.fbd_box_free_edgeMarg_innerEdgeLE_boxSym S N m hNm eb

/--
[fbd_boundary_decay_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_boundary_decay_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ} :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_boundary_decay_boxSym S N eb

/--
[fbd_boundary_decay_boxSym_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_boundary_decay_boxSym_free_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ} :
-- imply
  Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_boundary_decay_boxSym_free S N eb

/--
[fbd_wired_density_eq_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_wired_density_eq_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
-- proof
  apply StatMech.FK.fbd_wired_density_eq_boxSym S N eb hp hp1

/--
[fbd_free_density_eq_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_free_density_eq_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
-- proof
  apply StatMech.FK.fbd_free_density_eq_boxSym S N eb hp hp1

/--
[fbd_wired_density_eq_boxSym_innerEdgeLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryDecay.lean)
-/
@[path]
private lemma fbd_wired_density_eq_boxSym_innerEdgeLE_eq
  {d : ℕ}
  {S : BoxSym d}
  {N N' : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNN' : N ≤ N')
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N' (innerEdgeLE d hNN' eb)) p = wiredEdgeDensity d 2 (edgeIncl d N' (innerEdgeLE d hNN' (Sym2.map (S.lift N) eb))) p := by
-- proof
  apply StatMech.FK.fbd_wired_density_eq_boxSym_innerEdgeLE S N N' hNN' eb hp hp1


-- created on 2026-10-23
