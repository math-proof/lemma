import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc7crossaxisunique
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc7_crossAxisUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7crossaxisunique.lean)
-/
@[path]
private lemma bc7_crossAxisUnique_eq
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
  apply StatMech.Walls.bc7_crossAxisUnique hkm hq hmem

/--
[bc7_crossAxisUnique_of_corridorAxisUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7crossaxisunique.lean)
-/
@[path]
private lemma bc7_crossAxisUnique_of_corridorAxisUnique_eq
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
  apply StatMech.Walls.bc7_crossAxisUnique_of_corridorAxisUnique hkm hq hmem

/--
[bc7_crossAxisUnique_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7crossaxisunique.lean)
-/
@[path]
private lemma bc7_crossAxisUnique_nat_eq
  {d : ℕ}
  {k m : Fin d}
  {L p : ℕ}
  {u v : Site d}
-- given
  (hkm : k ≠ m)
  (hp : 1 ≤ p)
  (hmem : s(u, v) ∈ hrHD_corridorEdges k L) :
-- imply
  (hrHD_rayPt m (p : ℤ) : Site d) ∉ s(u, v) := by
-- proof
  apply StatMech.Walls.bc7_crossAxisUnique_nat hkm hp hmem

/--
[bc7_endpoint_ne_crossRayPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7crossaxisunique.lean)
-/
@[path]
private lemma bc7_endpoint_ne_crossRayPt_eq
  {d : ℕ}
  {k m : Fin d}
  {L : ℕ}
  {q : ℤ}
  {u v : Site d}
  {w : Site d}
-- given
  (hkm : k ≠ m)
  (hq : q ≠ 0)
  (hmem : s(u, v) ∈ hrHD_corridorEdges k L)
  (hw : w ∈ s(u, v)) :
-- imply
  w ≠ hrHD_rayPt m q := by
-- proof
  apply StatMech.Walls.bc7_endpoint_ne_crossRayPt hkm hq hmem hw

/--
[bc7_crossCorridor_endpoints_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7crossaxisunique.lean)
-/
@[path]
private lemma bc7_crossCorridor_endpoints_disjoint_eq
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
  apply StatMech.Walls.bc7_crossCorridor_endpoints_disjoint hkm hmem₁ hmem₂ hno0₂ hw₁ hw₂

/--
[bc7_crossRayPt_notMem_rayInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7crossaxisunique.lean)
-/
@[path]
private lemma bc7_crossRayPt_notMem_rayInterior_eq
  {d : ℕ}
  {k m : Fin d}
  {L : ℕ}
  {q : ℤ}
-- given
  (hkm : k ≠ m) :
-- imply
  (hrHD_rayPt m q : Site d) ∉ bc6_rayInterior k L := by
-- proof
  apply StatMech.Walls.bc7_crossRayPt_notMem_rayInterior hkm q

/--
[bc7_rayInteriors_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7crossaxisunique.lean)
-/
@[path]
private lemma bc7_rayInteriors_disjoint_eq
  {d : ℕ}
  {k m : Fin d}
  {L₁ L₂ : ℕ}
-- given
  (hkm : k ≠ m) :
-- imply
  Disjoint (bc6_rayInterior k L₁) (bc6_rayInterior m L₂) := by
-- proof
  apply StatMech.Walls.bc7_rayInteriors_disjoint hkm


-- created on 2026-10-23
