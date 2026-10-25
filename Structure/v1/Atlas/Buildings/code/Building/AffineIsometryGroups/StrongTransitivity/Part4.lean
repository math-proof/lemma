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
import Def.v1.Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity.Part3
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- The single oriflamme building of $B$ (type $\tilde B_n$): a
simplicial complex of lattices whose vertices are
`IsSingleOriflammeVertex`, simplices are pairwise single-oriflamme
incident, and faces are downward closed under nonempty subsets. -/
structure SingleOriflammeComplex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k) where
  simplices : Set (Finset (OLattice C))
  vertex_condition : ∀ σ ∈ simplices, ∀ Λ ∈ σ,
    IsSingleOriflammeVertex C B Λ
  pairwise_incident : ∀ σ ∈ simplices, ∀ Λ₁ ∈ σ, ∀ Λ₂ ∈ σ,
    SingleOriflammeIncidence C B Λ₁ Λ₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (OLattice C),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


end AffineIsometryBuilding
