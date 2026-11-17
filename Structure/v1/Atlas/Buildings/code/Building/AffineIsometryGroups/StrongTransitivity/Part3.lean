/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometryGroups/StrongTransitivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
public import Theorem.Nat.IsInO
public import Lemma.Fin.SquareDetV'.eq.One.of.All_Eq.Nondegenerate
public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.BilinearForms
public import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups.Part3
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part5
public import Def.v1.Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity.Part2
public section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- The double oriflamme building of $B$ (type $\tilde D_n$): a
simplicial complex of $\mathfrak{o}$-lattices whose vertices are
`IsDoubleOriflammeVertex`, simplices are pairwise oriflamme-incident,
and faces are closed under nonempty subsets. -/
structure DoubleOriflammeComplex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (halfDim : ℕ) where
  simplices : Set (Finset (OLattice C))
  vertex_condition : ∀ σ ∈ simplices, ∀ Λ ∈ σ,
    IsDoubleOriflammeVertex C B Λ halfDim
  pairwise_incident : ∀ σ ∈ simplices, ∀ Λ₁ ∈ σ, ∀ Λ₂ ∈ σ,
    DoubleOriflammeIncidence C B Λ₁ Λ₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (OLattice C),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


end AffineIsometryBuilding
