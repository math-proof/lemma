import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc7rayPtoffboxneighbor
open Set StatMech.Lattice StatMech.Percolation StatMech StatMech.Walls


/--
[bc7_adj_exists_unique_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7rayPtoffboxneighbor.lean)
-/
@[path]
private lemma bc7_adj_exists_unique_diff_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  ∃ k : Fin d, (x k - y k).natAbs = 1 ∧ ∀ i, i ≠ k → x i = y i := by
-- proof
  apply StatMech.Walls.bc7_adj_exists_unique_diff hadj

/--
[bc7_rayPt_offBox_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7rayPtoffboxneighbor.lean)
-/
@[path]
private lemma bc7_rayPt_offBox_neighbor_eq
  {d : ℕ}
  {a : Fin d}
  {N s : ℕ}
  {v : Site d}
-- given
  (hs1 : 1 ≤ s)
  (hsN : s ≤ N)
  (hadj : (hypercubicLattice d).Adj (hrHD_rayPt a (s : ℤ)) v)
  (hvbox : v ∉ box d N) :
-- imply
  s = N ∧ v = hrHD_rayPt a ((s : ℤ) + 1) := by
-- proof
  apply StatMech.Walls.bc7_rayPt_offBox_neighbor hs1 hsN hadj hvbox

/--
[bc7_offBox_neighbor_eq_succ_rayPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7rayPtoffboxneighbor.lean)
-/
@[path]
private lemma bc7_offBox_neighbor_eq_succ_rayPt_eq
  {d : ℕ}
  {a : Fin d}
  {N s : ℕ}
  {v : Site d}
-- given
  (hs1 : 1 ≤ s)
  (hsN : s ≤ N)
  (hadj : (hypercubicLattice d).Adj (hrHD_rayPt a (s : ℤ)) v)
  (hvbox : v ∉ box d N) :
-- imply
  v = hrHD_rayPt a ((s : ℤ) + 1) := by
-- proof
  apply StatMech.Walls.bc7_offBox_neighbor_eq_succ_rayPt hs1 hsN hadj hvbox

/--
[bc7_offBox_neighbor_forces_farEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7rayPtoffboxneighbor.lean)
-/
@[path]
private lemma bc7_offBox_neighbor_forces_farEnd_eq
  {d : ℕ}
  {a : Fin d}
  {N s : ℕ}
  {v : Site d}
-- given
  (hs1 : 1 ≤ s)
  (hsN : s ≤ N)
  (hadj : (hypercubicLattice d).Adj (hrHD_rayPt a (s : ℤ)) v)
  (hvbox : v ∉ box d N) :
-- imply
  s = N := by
-- proof
  apply StatMech.Walls.bc7_offBox_neighbor_forces_farEnd hs1 hsN hadj hvbox


-- created on 2026-10-23
