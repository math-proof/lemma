import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualOpenBoundary
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[squareDualBoundaryShift_flankFaces_eq_sharedPrimalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualOpenBoundary.lean)
-/
@[path]
private lemma squareDualBoundaryShift_flankFaces_eq_sharedPrimalEdge_eq
  {p q : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  Sym2.map (square.shift squareDualBoundaryShift) (flankFaces p q) = sharedPrimalEdge p q := by
-- proof
  apply StatMech.FrontierD.squareDualBoundaryShift_flankFaces_eq_sharedPrimalEdge hpq

/--
[sharedPrimalEdge_open_of_faceDual_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualOpenBoundary.lean)
-/
@[path]
private lemma sharedPrimalEdge_open_of_faceDual_closed_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {x y : Site 2}
-- given
  (hclosed : ∀ {x y}, x ∈ K → (fci_faceOpenDual omega).Adj x y → y ∈ K)
  (hxy : (hypercubicLattice 2).Adj x y)
  (hboundary : s(x, y) ∈ boundaryEdgeSet K) :
-- imply
  omega (sharedPrimalEdge x y) = true := by
-- proof
  apply StatMech.FrontierD.sharedPrimalEdge_open_of_faceDual_closed omega K hclosed hxy hboundary

/--
[squareDualClusterCoverage_fill_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualOpenBoundary.lean)
-/
@[path]
private lemma squareDualClusterCoverage_fill_closed_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
-- given
  (hfinite : ∀ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Finite) :
-- imply
  let S := squareDualClusterCoverage omega n let hS := squareDualClusterCoverage_finite omega n hfinite ∀ {x y}, x ∈ squareHoleFill S hS → (fci_faceOpenDual omega).Adj x y → y ∈ squareHoleFill S hS := by
-- proof
  apply StatMech.FrontierD.squareDualClusterCoverage_fill_closed omega n hfinite


-- created on 2026-10-23
