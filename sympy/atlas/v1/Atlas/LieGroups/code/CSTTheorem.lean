/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.ChevalleyRestriction
import Lemma.Rat.EqProjectToH.of.Given
import Lemma.Ideal.IsHomogeneousAugmentationIdealGraded
import sympy.atlas.v1.Atlas.LieGroups.code.SyzygiesKoszul
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

structure CSTPartIIData where
  n : ℕ
  G : Type*
  [instGroup : Group G]
  [instFintype : Fintype G]
  [instDecEq : DecidableEq G]
  linearAction : G →* ((Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
  is_reflection_group : IsComplexReflectionGroup G linearAction
  algAct : G →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)
  invariantSubalgebra : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)
  mem_invariant_iff : ∀ p : MvPolynomial (Fin n) ℂ,
    p ∈ invariantSubalgebra ↔ ∀ g : G, algAct g p = p
  basicInvariants : Fin n → ↥invariantSubalgebra
  alg_independent : AlgebraicIndependent ℂ basicInvariants
  generators_generate : Algebra.adjoin ℂ (Set.range basicInvariants) = ⊤
  degrees : Fin n → ℕ
  basicInvariants_homogeneous : ∀ i,
    (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ).IsHomogeneous (degrees i)
  basicInvariants_vanish : ∀ (v : Fin n → ℂ),
    (∀ i, MvPolynomial.eval v (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ) = 0) → v = 0
  R₀ : Type*
  [instR₀AddCommGroup : AddCommGroup R₀]
  [instR₀Module : Module ℂ R₀]
  [instR₀FiniteDimensional : FiniteDimensional ℂ R₀]
  R₀Action : Representation ℂ G R₀
  R₀_quotient_iso : R₀ ≃ₗ[ℂ]
    (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun i => (basicInvariants i : MvPolynomial (Fin n) ℂ))))
  hilbertR₀ : PowerSeries ℤ
  hilbertR₀_coeff_eq : ∀ N : ℕ,
    (PowerSeries.coeff N) hilbertR₀ =
      ↑(Module.finrank ℂ
        (quotientGradedComponent n
          (Ideal.span (Set.range (fun i => (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ))))
          N))

attribute [instance] CSTPartIIData.instGroup CSTPartIIData.instFintype
attribute [instance] CSTPartIIData.instDecEq
attribute [instance] CSTPartIIData.instR₀AddCommGroup CSTPartIIData.instR₀Module
attribute [instance] CSTPartIIData.instR₀FiniteDimensional

def CSTPartIIData.polyRep (cst : CSTPartIIData) :
    Representation ℂ cst.G (MvPolynomial (Fin cst.n) ℂ) :=
  polyRepresentation cst.algAct

variable (cst : CSTPartIIData)

def qIntPoly (d : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range d, Polynomial.X ^ i
