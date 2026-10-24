/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/StrongIsometryExt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.Eq.of.Eq.Any_And_Any_All_Eq_Mul.IsMaximal.In_Faces.IsMaximal.In_Faces.IsMaximal.In_Apartments
import Mathlib.GroupTheory.Coxeter.Length

set_option maxHeartbeats 800000

variable {V : Type*} [DecidableEq V]

/-- The *$W$-valued distance* on a building: a function
$\delta : \mathrm{Cham}(X)^2 \to W$ taking values in a Coxeter group $W$, with
$\delta(C, C) = 1$, satisfying $\ell(\delta(C, D)) = d(C, D)$, and compatible
with the natural Coxeter labeling of each apartment via an isomorphism. -/
structure Building.WValuedDist (b : Building V) where
  S_idx : Type*
  [S_idx_dec : DecidableEq S_idx]
  [S_idx_fin : Fintype S_idx]
  coxeterMatrix : CoxeterMatrix S_idx
  delta : Finset V → Finset V → coxeterMatrix.Group
  delta_self : ∀ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C →
    delta C C = 1
  galleryDist_eq_length : ∀ (C D : Finset V),
    galleryDist b.toChamberComplex.toSimplicialComplex C D =
    coxeterMatrix.toCoxeterSystem.length (delta C D)

  delta_apt_compat : ∀ A ∈ b.apartmentSystem.apartments,
    ∀ (B_idx : Type) (M : CoxeterMatrix B_idx) (φ : Finset V → M.Group),
    (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) →
    (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) →
    ∃ (iso : coxeterMatrix.Group ≃* M.Group),
      ∀ C D, C ∈ A.faces → A.IsMaximal C → D ∈ A.faces → A.IsMaximal D →
        iso (delta C D) = (φ C)⁻¹ * (φ D)

/-- A *strong isometry* $f : Y \to f(Y)$ between sets of chambers is a
bijection that preserves the $W$-valued distance $\delta$. -/
def IsStrongIsometry {b : Building V} (δW : Building.WValuedDist b)
    (Y Z : Set (Finset V))
    (φ : Finset V → Finset V) : Prop :=
  (∀ C ∈ Y, φ C ∈ Z) ∧
  (∀ C ∈ Z, ∃ D ∈ Y, φ D = C) ∧
  (∀ C ∈ Y, ∀ D ∈ Y,
    δW.delta (φ C) (φ D) = δW.delta C D)
