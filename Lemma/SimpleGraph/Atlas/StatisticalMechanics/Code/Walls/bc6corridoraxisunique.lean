import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc6corridoraxisunique
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc6_corridorEdge_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6corridoraxisunique.lean)
-/
@[path]
private lemma bc6_corridorEdge_endpoints_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {u v : Site d}
-- given
  (hmem : s(u, v) ∈ hrHD_corridorEdges j L)
  (hno0 : (0 : Site d) ∉ s(u, v)) :
-- imply
  ∃ p : ℕ, 1 ≤ p ∧ p < L ∧ ((u = hrHD_rayPt j (p : ℤ) ∧ v = hrHD_rayPt j ((p : ℤ) + 1)) ∨ (u = hrHD_rayPt j ((p : ℤ) + 1) ∧ v = hrHD_rayPt j (p : ℤ))) := by
-- proof
  apply StatMech.Walls.bc6_corridorEdge_endpoints hmem hno0

/--
[bc6_endpoint_is_rayPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6corridoraxisunique.lean)
-/
@[path]
private lemma bc6_endpoint_is_rayPt_eq
  {d : ℕ}
  {k : Fin d}
  {L : ℕ}
  {u v : Site d}
  {w : Site d}
-- given
  (hmem : s(u, v) ∈ hrHD_corridorEdges k L)
  (hno0 : (0 : Site d) ∉ s(u, v))
  (hw : w ∈ s(u, v)) :
-- imply
  ∃ p : ℕ, 1 ≤ p ∧ p ≤ L ∧ w = hrHD_rayPt k (p : ℤ) := by
-- proof
  apply StatMech.Walls.bc6_endpoint_is_rayPt hmem hno0 hw

/--
[bc6_endpoint_axis_value_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6corridoraxisunique.lean)
-/
@[path]
private lemma bc6_endpoint_axis_value_ne_zero_eq
  {d : ℕ}
  {k : Fin d}
  {L : ℕ}
  {u v : Site d}
  {w : Site d}
-- given
  (hmem : s(u, v) ∈ hrHD_corridorEdges k L)
  (hno0 : (0 : Site d) ∉ s(u, v))
  (hw : w ∈ s(u, v)) :
-- imply
  w k ≠ 0 ∧ ∀ i : Fin d, i ≠ k → w i = 0 := by
-- proof
  apply StatMech.Walls.bc6_endpoint_axis_value_ne_zero hmem hno0 hw

/--
[bc6_rayPt_notMem_crossCorridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6corridoraxisunique.lean)
-/
@[path]
private lemma bc6_rayPt_notMem_crossCorridor_eq
  {d : ℕ}
  {k m : Fin d}
  {L : ℕ}
  {q : ℤ}
  {u v : Site d}
-- given
  (hkm : k ≠ m)
  (hq : q ≠ 0)
  (hmem : s(u, v) ∈ hrHD_corridorEdges k L) :
-- imply
  (hrHD_rayPt m q : Site d) ∉ s(u, v) := by
-- proof
  apply StatMech.Walls.bc6_rayPt_notMem_crossCorridor hkm hq hmem

/--
[bc6_endpoint_not_crossRayPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6corridoraxisunique.lean)
-/
@[path]
private lemma bc6_endpoint_not_crossRayPt_eq
  {d : ℕ}
  {k m : Fin d}
  {L : ℕ}
  {u v : Site d}
  {w : Site d}
  {q : ℤ}
-- given
  (hkm : k ≠ m)
  (hmem : s(u, v) ∈ hrHD_corridorEdges k L)
  (hno0 : (0 : Site d) ∉ s(u, v))
  (hw : w ∈ s(u, v)) :
-- imply
  w ≠ hrHD_rayPt m q := by
-- proof
  apply StatMech.Walls.bc6_endpoint_not_crossRayPt hkm hmem hno0 hw q

/--
[bc6_corridorEdges_endpoints_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6corridoraxisunique.lean)
-/
@[path]
private lemma bc6_corridorEdges_endpoints_disjoint_eq
  {d : ℕ}
  {k m : Fin d}
  {L₁ L₂ : ℕ}
  {u v u' v' : Site d}
  {w : Site d}
-- given
  (hkm : k ≠ m)
  (hmem₁ : s(u, v) ∈ hrHD_corridorEdges k L₁)
  (hmem₂ : s(u', v') ∈ hrHD_corridorEdges m L₂)
  (hno0₂ : (0 : Site d) ∉ s(u', v'))
  (hw₁ : w ∈ s(u, v))
  (hw₂ : w ∈ s(u', v')) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc6_corridorEdges_endpoints_disjoint hkm hmem₁ hmem₂ hno0₂ hw₁ hw₂


-- created on 2026-10-23
