import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccrayPt
open StatMech.Lattice StatMech.Percolation StatMech StatMech.Walls


/--
[bkm_dccrayPt_adj_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccrayPt.lean)
-/
@[path]
private lemma bkm_dccrayPt_adj_origin_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  (hypercubicLattice d).Adj (0 : Site d) (hrHD_rayPt j 1) := by
-- proof
  apply StatMech.Walls.bkm_dccrayPt_adj_origin j

/--
[bkm_dccrayPt_eq_iff_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccrayPt.lean)
-/
@[path]
private lemma bkm_dccrayPt_eq_iff_of_ne_eq
  {d : ℕ}
  {i j : Fin d}
  {s t : ℤ}
-- given
  (h : i ≠ j) :
-- imply
  (hrHD_rayPt i s : Site d) = hrHD_rayPt j t ↔ (s = 0 ∧ t = 0) := by
-- proof
  apply StatMech.Walls.bkm_dccrayPt_eq_iff_of_ne h s t

/--
[bkm_dccrayPt_ne_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccrayPt.lean)
-/
@[path]
private lemma bkm_dccrayPt_ne_of_ne_eq
  {d : ℕ}
  {i j : Fin d}
  {s t : ℤ}
-- given
  (h : i ≠ j)
  (hs : s ≠ 0) :
-- imply
  (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t := by
-- proof
  apply StatMech.Walls.bkm_dccrayPt_ne_of_ne h hs

/--
[bkm_dccrayPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccrayPt.lean)
-/
@[path]
private lemma bkm_dccrayPt_eq
  {d : ℕ} :
-- imply
  (∀ j : Fin d, (hypercubicLattice d).Adj (0 : Site d) (hrHD_rayPt j 1)) ∧ (∀ {i j : Fin d}, i ≠ j → ∀ s t : ℤ, ((hrHD_rayPt i s : Site d) = hrHD_rayPt j t ↔ (s = 0 ∧ t = 0))) := by
-- proof
  apply StatMech.Walls.bkm_dccrayPt


-- created on 2026-10-23
