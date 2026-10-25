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
import Structure.v1.Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity.Part2
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- A lattice $\Lambda$ lies in the apartment of a symplectic frame $F$
if it admits a description as $\mathfrak{o}$-span of the frame lines
scaled by nonzero scalars (one per frame line). -/
def IsInAlternatingApartment (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (m : ℕ) (F : FrameAlternating C B m) (Λ : OLattice C) : Prop :=
  ∃ (scalars : Fin m × Bool → C.𝔬),

    (∀ ib, scalars ib ≠ 0) ∧

    Λ.carrier = { v | ∃ c : Fin m × Bool → C.𝔬,
      v = fun idx => ∑ ib : Fin m × Bool,
        C.embed (c ib * scalars ib) * F.lines ib idx }


/-- A lattice $\Lambda$ is a vertex of the double oriflamme building (type
$\tilde D_n$) of $B$ if it admits a sublattice $\Lambda_0$ satisfying the
same containment / integrality / uniformizer conditions as in the
alternating case, plus a "doubling" condition certifying that $\Lambda$
is one of the two lattices arising in an oriflamme split. -/
def IsDoubleOriflammeVertex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) (_halfDim : ℕ) : Prop :=
  ∃ (Λ₀ : OLattice C),

    latticeContained C Λ₀ Λ ∧

    formValuesInMaxIdeal C B Λ ∧

    (∀ v ∈ Λ₀.carrier, ∀ w ∈ Λ₀.carrier, C.isInO (B v w)) ∧

    (∀ v ∈ Λ.carrier, C.oscal C.uniformizer v ∈ Λ₀.carrier) ∧

    (¬ (∀ v ∈ Λ.carrier, v ∈ Λ₀.carrier) ∨
      ∃ v ∈ Λ.carrier, ∃ w ∈ Λ.carrier,
        ¬ ∃ (r : C.𝔬) (u : Fin C.n → C.k),
          u ∈ Λ₀.carrier ∧ (fun i => v i - C.embed r * w i) = u)

/-- Incidence relation for the double oriflamme building: either the
underlying alternating-form incidence, or an oriflamme incidence where
$\Lambda_1, \Lambda_2$ share a common $\Lambda_0$ and differ by a single
direction $d \in \Lambda_1 \setminus \Lambda_2$. -/
def DoubleOriflammeIncidence (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ₁ Λ₂ : OLattice C) : Prop :=

  AffineAlternatingIncidence C B Λ₁ Λ₂ ∨


  (∃ (Λ₀ : OLattice C),
    latticeContained C Λ₀ Λ₁ ∧
    latticeContained C Λ₀ Λ₂ ∧


    Λ₁.carrier ≠ Λ₂.carrier ∧


    ∃ d : Fin C.n → C.k,
      d ∈ Λ₁.carrier ∧ d ∉ Λ₂.carrier ∧
      (∀ v ∈ Λ₁.carrier, ∃ w ∈ Λ₂.carrier, ∃ r : C.𝔬,
        v = fun i => w i + C.embed r * d i))

end AffineIsometryBuilding
