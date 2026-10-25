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
import Structure.v1.Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity.Part3
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- A lattice $\Lambda$ is a vertex of the single oriflamme building
(type $\tilde B_n$) of $B$ if there is a superlattice $\Lambda_0 \supseteq
\Lambda$ such that the uniformizer maps $\Lambda_0$ into $\Lambda$, $B$
is integral on $\Lambda_0$, every non-divisible element of $\Lambda_0$
has a unit pairing with some other element, and $B$ takes values in
$\mathfrak{m}$ on $\Lambda$. -/
def IsSingleOriflammeVertex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) : Prop :=
  ∃ (Λ₀ : OLattice C),

    latticeContained C Λ Λ₀ ∧

    (∀ v ∈ Λ₀.carrier, C.oscal C.uniformizer v ∈ Λ.carrier) ∧

    (∀ v ∈ Λ₀.carrier, ∀ w ∈ Λ₀.carrier, C.isInO (B v w)) ∧

    (∀ v ∈ Λ₀.carrier,
      (¬ ∃ w ∈ Λ₀.carrier, v = C.oscal C.uniformizer w) →
      ∃ w ∈ Λ₀.carrier, C.isUnitInO (B v w)) ∧

    formValuesInMaxIdeal C B Λ

/-- Incidence in the single oriflamme building: either the alternating
incidence relation, or both lattices are integral for $B$ and differ by
exactly one direction $d \in \Lambda_1 \setminus \Lambda_2$. -/
def SingleOriflammeIncidence (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ₁ Λ₂ : OLattice C) : Prop :=

  AffineAlternatingIncidence C B Λ₁ Λ₂ ∨

  (
   (∀ v ∈ Λ₁.carrier, ∀ w ∈ Λ₁.carrier, C.isInO (B v w)) ∧
   (∀ v ∈ Λ₂.carrier, ∀ w ∈ Λ₂.carrier, C.isInO (B v w)) ∧

   Λ₁.carrier ≠ Λ₂.carrier ∧
   ∃ d : Fin C.n → C.k,
     d ∈ Λ₁.carrier ∧ d ∉ Λ₂.carrier ∧
     (∀ v ∈ Λ₁.carrier, ∃ w ∈ Λ₂.carrier, ∃ r : C.𝔬,
       v = fun i => w i + C.embed r * d i))

end AffineIsometryBuilding
