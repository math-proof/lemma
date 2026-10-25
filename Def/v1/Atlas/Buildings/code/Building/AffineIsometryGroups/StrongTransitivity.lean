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
import Structure.v1.Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- The dual of an $\mathfrak{o}$-lattice $\Lambda$ with respect to $B$:
$\Lambda^\# = \{v : B(v, w) \in \mathfrak{m} \text{ for all } w \in \Lambda\}$. -/
def dualLattice (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) : Set (Fin C.n → C.k) :=
  { v | ∀ w ∈ Λ.carrier, C.isInMaxIdeal (B v w) }

/-- $\Lambda_1 \subseteq \Lambda_2$ as sets of vectors in $k^n$. -/
def latticeContained (Λ₁ Λ₂ : OLattice C) : Prop :=
  ∀ v ∈ Λ₁.carrier, v ∈ Λ₂.carrier

/-- The bilinear form $B$ takes values in the maximal ideal on $\Lambda$:
$B(v, w) \in \mathfrak{m}$ for all $v, w \in \Lambda$. -/
def formValuesInMaxIdeal (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) : Prop :=
  ∀ v ∈ Λ.carrier, ∀ w ∈ Λ.carrier, C.isInMaxIdeal (B v w)

/-- A lattice $\Lambda$ is a vertex of the affine alternating-form
building if there exists a sublattice $\Lambda_0 \subseteq \Lambda$ such
that $B$ is integral on $\Lambda_0$, takes values in $\mathfrak{m}$ on
$\Lambda$, and the uniformizer multiplied by any element of $\Lambda$
lands in $\Lambda_0$ (so $\Lambda / \Lambda_0$ has bounded denominator). -/
def IsAffineAlternatingVertex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) : Prop :=
  ∃ (Λ₀ : OLattice C),

    latticeContained C Λ₀ Λ ∧

    formValuesInMaxIdeal C B Λ ∧


    (∀ v ∈ Λ₀.carrier, ∀ w ∈ Λ₀.carrier, C.isInO (B v w)) ∧


    (∀ v ∈ Λ.carrier, C.oscal C.uniformizer v ∈ Λ₀.carrier)

/-- Incidence relation for the affine alternating-form building: two
lattices $\Lambda_1, \Lambda_2$ are incident if there is a common
$\Lambda_0$ on which $B$ is integral, the uniformizer maps either
$\Lambda_i$ into $\Lambda_0$, and one of $\Lambda_1, \Lambda_2$ is
contained in the other. -/
def AffineAlternatingIncidence (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ₁ Λ₂ : OLattice C) : Prop :=
  ∃ (Λ₀ : OLattice C),

    (∀ v ∈ Λ₀.carrier, ∀ w ∈ Λ₀.carrier, C.isInO (B v w)) ∧

    latticeContained C Λ₀ Λ₁ ∧
    (∀ v ∈ Λ₁.carrier, C.oscal C.uniformizer v ∈ Λ₀.carrier) ∧

    latticeContained C Λ₀ Λ₂ ∧
    (∀ v ∈ Λ₂.carrier, C.oscal C.uniformizer v ∈ Λ₀.carrier) ∧

    (latticeContained C Λ₁ Λ₂ ∨ latticeContained C Λ₂ Λ₁)

end AffineIsometryBuilding
