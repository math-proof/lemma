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
import Structure.v1.Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity.Part4
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- The alternating-form simplicial complex is a thick building: any two
simplices lie in a common apartment described by some symplectic frame,
and every panel is contained in at least three distinct chambers. -/
def AlternatingIsThickBuilding
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (X : AffineAlternatingComplex C B) : Prop :=

  (∀ σ₁ ∈ X.simplices, ∀ σ₂ ∈ X.simplices,
    ∃ (m : ℕ) (F : FrameAlternating C B m),
      (∀ Λ ∈ σ₁, IsInAlternatingApartment C B m F Λ) ∧
      (∀ Λ ∈ σ₂, IsInAlternatingApartment C B m F Λ)) ∧

  (∀ panel ∈ X.simplices,
    ∃ C₁ C₂ C₃ : Finset (OLattice C),
      C₁ ∈ X.simplices ∧ C₂ ∈ X.simplices ∧ C₃ ∈ X.simplices ∧
      panel ⊆ C₁ ∧ panel ⊆ C₂ ∧ panel ⊆ C₃ ∧
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃)

/-- Thickness for the double oriflamme building: every panel is contained
in at least three pairwise-distinct chambers. -/
def DoubleOriflammeIsThickBuilding
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (halfDim : ℕ) (X : DoubleOriflammeComplex C B halfDim) : Prop :=

  ∀ panel ∈ X.simplices,
    ∃ C₁ C₂ C₃ : Finset (OLattice C),
      C₁ ∈ X.simplices ∧ C₂ ∈ X.simplices ∧ C₃ ∈ X.simplices ∧
      panel ⊆ C₁ ∧ panel ⊆ C₂ ∧ panel ⊆ C₃ ∧
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃

/-- Thickness for the single oriflamme building: every panel is contained
in at least three pairwise-distinct chambers. -/
def SingleOriflammeIsThickBuilding
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (X : SingleOriflammeComplex C B) : Prop :=

  ∀ panel ∈ X.simplices,
    ∃ C₁ C₂ C₃ : Finset (OLattice C),
      C₁ ∈ X.simplices ∧ C₂ ∈ X.simplices ∧ C₃ ∈ X.simplices ∧
      panel ⊆ C₁ ∧ panel ⊆ C₂ ∧ panel ⊆ C₃ ∧
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃


/-- An element $g \in GL_n(k)$ is an isometry of the bilinear form $B$ if
$B(gv, gw) = B(v, w)$ for all $v, w \in k^n$. -/
def IsIsometry (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (g : GL (Fin C.n) C.k) : Prop :=
  ∀ v w : Fin C.n → C.k, B (fun i => ∑ j, g.val i j * v j) (fun i => ∑ j, g.val i j * w j) = B v w

/-- The isometry group of $B$ as a subset of $GL_n(k)$. -/
def IsometryGroupSet (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k) : Set C.GL_n_k :=
  { g | IsIsometry C B g }

/-- The image $g \cdot \Lambda$ of a lattice $\Lambda$ under
$g \in GL_n(k)$, as a set of vectors. -/
def GLImageLatticeCarrier (g : C.GL_n_k) (Λ : OLattice C) :
    Set (Fin C.n → C.k) :=
  { w | ∃ v ∈ Λ.carrier, w = fun i => ∑ j, g.val i j * v j }

/-- $g \in GL_n(k)$ maps simplex $\sigma_1$ to simplex $\sigma_2$ if for
every lattice $\Lambda \in \sigma_1$ there is some $\Lambda' \in \sigma_2$
with $g \cdot \Lambda = \Lambda'$ as sets. -/
def GLMapsSimplex (g : C.GL_n_k)
    (σ₁ σ₂ : Finset (OLattice C)) : Prop :=
  ∀ Λ ∈ σ₁, ∃ Λ' ∈ σ₂, GLImageLatticeCarrier C g Λ = Λ'.carrier

/-- $g \in GL_n(k)$ maps the apartment of frame $F_1$ to that of $F_2$ if
every lattice in the $F_1$-apartment has its $g$-image in the
$F_2$-apartment. -/
def GLMapsAlternatingApartment
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (m : ℕ) (g : C.GL_n_k)
    (F₁ F₂ : FrameAlternating C B m) : Prop :=
  ∀ Λ : OLattice C,
    IsInAlternatingApartment C B m F₁ Λ →
    ∃ Λ' : OLattice C,
      GLImageLatticeCarrier C g Λ = Λ'.carrier ∧
      IsInAlternatingApartment C B m F₂ Λ'

/-- Strong transitivity for the alternating-form building: the isometry
group acts transitively on pairs (apartment, simplex inside that
apartment). -/
def StrongTransitivityAlternating
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (X : AffineAlternatingComplex C B)
    (m : ℕ) : Prop :=
  ∀ (F₁ F₂ : FrameAlternating C B m)
    (σ₁ : Finset (OLattice C)), σ₁ ∈ X.simplices →
    ∀ (σ₂ : Finset (OLattice C)), σ₂ ∈ X.simplices →
    (∀ Λ ∈ σ₁, IsInAlternatingApartment C B m F₁ Λ) →
    (∀ Λ ∈ σ₂, IsInAlternatingApartment C B m F₂ Λ) →
    ∃ g ∈ IsometryGroupSet C B,

      GLMapsAlternatingApartment C B m g F₁ F₂

/-- Strong transitivity for the double oriflamme building: the isometry
group acts transitively on simplices of the complex. -/
def StrongTransitivityDoubleOriflamme
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (halfDim : ℕ) (X : DoubleOriflammeComplex C B halfDim) : Prop :=
  ∀ (σ₁ : Finset (OLattice C)), σ₁ ∈ X.simplices →
    ∀ (σ₂ : Finset (OLattice C)), σ₂ ∈ X.simplices →
    ∃ g ∈ IsometryGroupSet C B, GLMapsSimplex C g σ₁ σ₂

/-- Strong transitivity for the single oriflamme building: the isometry
group acts transitively on simplices of the complex. -/
def StrongTransitivitySingleOriflamme
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (X : SingleOriflammeComplex C B) : Prop :=
  ∀ (σ₁ : Finset (OLattice C)), σ₁ ∈ X.simplices →
    ∀ (σ₂ : Finset (OLattice C)), σ₂ ∈ X.simplices →
    ∃ g ∈ IsometryGroupSet C B, GLMapsSimplex C g σ₁ σ₂

end AffineIsometryBuilding
