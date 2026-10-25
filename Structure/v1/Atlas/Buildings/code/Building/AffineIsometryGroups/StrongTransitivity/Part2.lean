/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometryGroups/StrongTransitivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Lemma.Fin.SquareDetV'.eq.One.of.All_Eq.Nondegenerate
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.BilinearForms
import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups.Part3
import Def.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part5
import Def.v1.Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- The affine alternating-form building: a simplicial complex of
$\mathfrak{o}$-lattices in $k^n$ whose vertices satisfy
`IsAffineAlternatingVertex`, whose simplices are pairwise incident, and
whose face set is downward closed under nonempty subsets. -/
structure AffineAlternatingComplex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k) where
  simplices : Set (Finset (OLattice C))
  vertex_condition : ∀ σ ∈ simplices, ∀ Λ ∈ σ, IsAffineAlternatingVertex C B Λ
  pairwise_incident : ∀ σ ∈ simplices, ∀ Λ₁ ∈ σ, ∀ Λ₂ ∈ σ,
    AffineAlternatingIncidence C B Λ₁ Λ₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (OLattice C),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices

/-- A symplectic frame for an alternating form $B$: $m$ pairs of isotropic
lines indexed by $\mathrm{Fin}\,m \times \mathrm{Bool}$ such that within
each pair $(i, \mathrm{true}), (i, \mathrm{false})$ the pairing
$B(\ell_{i,\mathrm{true}}, \ell_{i,\mathrm{false}})$ is a unit, and lines
with different indices are orthogonal. -/
structure FrameAlternating (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (m : ℕ) where
  lines : Fin m × Bool → Fin C.n → C.k
  lines_isotropic : ∀ ib, B (lines ib) (lines ib) = 0
  lines_pairing : ∀ i : Fin m, C.isUnitInO (B (lines (i, true)) (lines (i, false)))
  lines_orthogonal : ∀ i j : Fin m, i ≠ j → ∀ s t : Bool,
    B (lines (i, s)) (lines (j, t)) = 0

end AffineIsometryBuilding
