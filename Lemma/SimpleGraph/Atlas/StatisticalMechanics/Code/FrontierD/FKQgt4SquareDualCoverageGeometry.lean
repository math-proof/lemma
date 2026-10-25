import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoverageGeometry
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[box_subset_squareDualClusterCoverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoverageGeometry.lean)
-/
@[path]
private lemma box_subset_squareDualClusterCoverage_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat} :
-- imply
  box 2 n ⊆ squareDualClusterCoverage omega n := by
-- proof
  apply StatMech.FrontierD.box_subset_squareDualClusterCoverage omega n

/--
[squareDualClusterCoverage_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoverageGeometry.lean)
-/
@[path]
private lemma squareDualClusterCoverage_finite_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
-- given
  (hfinite : ∀ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Finite) :
-- imply
  (squareDualClusterCoverage omega n).Finite := by
-- proof
  apply StatMech.FrontierD.squareDualClusterCoverage_finite omega n hfinite

/--
[squareDualClusterCoverage_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoverageGeometry.lean)
-/
@[path]
private lemma squareDualClusterCoverage_closed_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
  {x y : Site 2}
-- given
  (hx : x ∈ squareDualClusterCoverage omega n)
  (hxy : (fci_faceOpenDual omega).Adj x y) :
-- imply
  y ∈ squareDualClusterCoverage omega n := by
-- proof
  apply StatMech.FrontierD.squareDualClusterCoverage_closed omega n hx hxy

/--
[squareDualClusterCoverage_inside_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoverageGeometry.lean)
-/
@[path]
private lemma squareDualClusterCoverage_inside_connected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat} :
-- imply
  ∀ a b : Site 2, a ∈ squareDualClusterCoverage omega n → b ∈ squareDualClusterCoverage omega n → (latticeMinusBarrier (squareDualClusterCoverage omega n)).Reachable a b := by
-- proof
  apply StatMech.FrontierD.squareDualClusterCoverage_inside_connected omega n

/--
[squareHoleFill_closed_of_faceDual_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoverageGeometry.lean)
-/
@[path]
private lemma squareHoleFill_closed_of_faceDual_closed_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hS : S.Finite)
  (hclosed : ∀ {x y}, x ∈ S → (fci_faceOpenDual omega).Adj x y → y ∈ S)
  (hx : x ∈ squareHoleFill S hS)
  (hxy : (fci_faceOpenDual omega).Adj x y) :
-- imply
  y ∈ squareHoleFill S hS := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_closed_of_faceDual_closed omega S hS hclosed hx hxy

/--
[squareDualClusterCoverage_fill_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoverageGeometry.lean)
-/
@[path]
private lemma squareDualClusterCoverage_fill_connected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
-- given
  (hfinite : ∀ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Finite) :
-- imply
  let S := squareDualClusterCoverage omega n let hS := squareDualClusterCoverage_finite omega n hfinite ∀ a b : squareHoleFill S hS, ((hypercubicLattice 2).induce (squareHoleFill S hS)).Reachable a b := by
-- proof
  apply StatMech.FrontierD.squareDualClusterCoverage_fill_connected omega n hfinite

/--
[squareDualClusterCoverage_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoverageGeometry.lean)
-/
@[path]
private lemma squareDualClusterCoverage_faceBoundaryConnected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
-- given
  (hfinite : ∀ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Finite) :
-- imply
  let S := squareDualClusterCoverage omega n let hS := squareDualClusterCoverage_finite omega n hfinite FaceBoundaryConnected (squareHoleFill S hS) (phb_boundarySupport (squareHoleFill S hS) (squareHoleFill_finite S hS)) := by
-- proof
  apply StatMech.FrontierD.squareDualClusterCoverage_faceBoundaryConnected omega n hfinite


-- created on 2026-10-23
