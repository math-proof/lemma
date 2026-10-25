/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part7
import Lemma.Rat.EqProjectToH.of.Given
import Lemma.Ideal.IsHomogeneousAugmentationIdealGraded
import Instance.v1.Atlas.LieGroups.code.SyzygiesKoszul.Part2
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Invariant.Basic


noncomputable section

universe u

def qIntegerCST (d : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range d, PowerSeries.X ^ i

def quotientGradedComponent (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (N : ℕ) :
    Submodule ℂ (MvPolynomial (Fin n) ℂ ⧸ I) :=
  Submodule.map (I.mkQ.restrictScalars ℂ)
    (MvPolynomial.homogeneousSubmodule (Fin n) ℂ N)

def polyRepresentation {n : ℕ} {G : Type*} [Group G]
    (algAct : G →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)) :
    Representation ℂ G (MvPolynomial (Fin n) ℂ) where
  toFun g := (algAct g).toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [map_mul]

end
