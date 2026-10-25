import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBoxClusterUnion
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[mem_squareBoxClusterUnion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBoxClusterUnion.lean)
-/
@[path]
private lemma mem_squareBoxClusterUnion_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
  {y : Site 2} :
-- imply
  y ∈ squareBoxClusterUnion omega n ↔ ∃ x ∈ box 2 n, y ∈ cluster 2 omega x := by
-- proof
  apply StatMech.FrontierD.mem_squareBoxClusterUnion_iff omega n y

/--
[box_subset_squareBoxClusterUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBoxClusterUnion.lean)
-/
@[path]
private lemma box_subset_squareBoxClusterUnion_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat} :
-- imply
  box 2 n ⊆ squareBoxClusterUnion omega n := by
-- proof
  apply StatMech.FrontierD.box_subset_squareBoxClusterUnion omega n

/--
[squareBoxClusterUnion_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBoxClusterUnion.lean)
-/
@[path]
private lemma squareBoxClusterUnion_finite_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
-- given
  (hfinite : ∀ x ∈ box 2 n, (cluster 2 omega x).Finite) :
-- imply
  (squareBoxClusterUnion omega n).Finite := by
-- proof
  apply StatMech.FrontierD.squareBoxClusterUnion_finite omega n hfinite

/--
[squareBoxClusterUnion_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBoxClusterUnion.lean)
-/
@[path]
private lemma squareBoxClusterUnion_connected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat} :
-- imply
  ∀ a b : squareBoxClusterUnion omega n, ((hypercubicLattice 2).induce (squareBoxClusterUnion omega n)).Reachable a b := by
-- proof
  apply StatMech.FrontierD.squareBoxClusterUnion_connected omega n

/--
[squareBoxClusterUnion_fill_boundary_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBoxClusterUnion.lean)
-/
@[path]
private lemma squareBoxClusterUnion_fill_boundary_connected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
-- given
  (hfinite : ∀ x ∈ box 2 n, (cluster 2 omega x).Finite) :
-- imply
  FaceBoundaryConnected (squareHoleFill (squareBoxClusterUnion omega n) (squareBoxClusterUnion_finite omega n hfinite)) (phb_boundarySupport (squareHoleFill (squareBoxClusterUnion omega n) (squareBoxClusterUnion_finite omega n hfinite)) (squareHoleFill_finite (squareBoxClusterUnion omega n) (squareBoxClusterUnion_finite omega n hfinite))) := by
-- proof
  apply StatMech.FrontierD.squareBoxClusterUnion_fill_boundary_connected omega n hfinite


-- created on 2026-10-23
