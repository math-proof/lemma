/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualOpenBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoverageGeometry
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBoxClusterUnion
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualOpenBoundary
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

theorem squareDualBoundaryShift_flankFaces_eq_sharedPrimalEdge
    {p q : Site 2} (hpq : (hypercubicLattice 2).Adj p q) :
    Sym2.map (square.shift squareDualBoundaryShift) (flankFaces p q) =
      sharedPrimalEdge p q := by
  rcases adj_cases hpq with ⟨h0, hpq1 | hqp1⟩ | ⟨h1, hpq0 | hqp0⟩
  · have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> simp
    have hq : q = ![p 0, p 1 - 1] := by
      ext i
      fin_cases i
      · simpa [h0]
      · simp; omega
    rw [hp, hq]
    simp [flankFaces, sharedPrimalEdge, squareDualBoundaryShift,
      square, siteTranslate, Sym2.map_mk]
  · have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> simp
    have hq : q = ![p 0, p 1 + 1] := by
      ext i
      fin_cases i
      · simpa [h0]
      · simp; omega
    rw [hp, hq]
    simp [flankFaces, sharedPrimalEdge, squareDualBoundaryShift,
      square, siteTranslate, Sym2.map_mk]
  · have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> simp
    have hq : q = ![p 0 - 1, p 1] := by
      ext i
      fin_cases i
      · simp; omega
      · simpa [h1]
    rw [hp, hq]
    simp [flankFaces, sharedPrimalEdge, squareDualBoundaryShift,
      square, siteTranslate, Sym2.map_mk,
      show p 0 ≠ p 0 - 1 by omega]
  · have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> simp
    have hq : q = ![p 0 + 1, p 1] := by
      ext i
      fin_cases i
      · simp; omega
      · simpa [h1]
    rw [hp, hq]
    simp [flankFaces, sharedPrimalEdge, squareDualBoundaryShift,
      square, siteTranslate, Sym2.map_mk]


theorem sharedPrimalEdge_open_of_faceDual_closed
    (omega : ConfigSpace (Sym2 (Site 2)))
    (K : Set (Site 2))
    (hclosed : ∀ {x y}, x ∈ K → (fci_faceOpenDual omega).Adj x y → y ∈ K)
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y)
    (hboundary : s(x, y) ∈ boundaryEdgeSet K) :
    omega (sharedPrimalEdge x y) = true := by
  have hstraddle : edgeStraddles K s(x, y) :=
    (edgeStraddles_iff_mem_boundaryEdgeSet K hxy).mpr hboundary
  rw [edgeStraddles_mk] at hstraddle
  cases hopen : omega (sharedPrimalEdge x y) with
  | false =>
      exfalso
      have hdual : (fci_faceOpenDual omega).Adj x y := ⟨hxy, hopen⟩
      by_cases hx : x ∈ K
      · exact (hstraddle.mp hx) (hclosed hx hdual)
      · have hy : y ∈ K := by
          by_contra hy
          exact hx (hstraddle.mpr hy)
        exact hx (hclosed hy hdual.symm)
  | true => rfl


theorem squareDualClusterCoverage_fill_closed
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite) :
    let S := squareDualClusterCoverage omega n
    let hS := squareDualClusterCoverage_finite omega n hfinite
    ∀ {x y}, x ∈ squareHoleFill S hS →
      (fci_faceOpenDual omega).Adj x y → y ∈ squareHoleFill S hS := by
  dsimp only
  exact squareHoleFill_closed_of_faceDual_closed omega _ _
    (squareDualClusterCoverage_closed omega n)


end
end StatMech.FrontierD
