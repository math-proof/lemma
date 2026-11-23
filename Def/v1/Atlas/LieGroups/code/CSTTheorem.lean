/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part7
public import Theorem.Rat.EqProjectToH.of.Given
public import Theorem.Ideal.IsHomogeneous_AugmentationIdealGraded
public import Instance.v1.Atlas.LieGroups.code.SyzygiesKoszul.Part2
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Equiv
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Invariant.Basic

@[expose] public section

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
