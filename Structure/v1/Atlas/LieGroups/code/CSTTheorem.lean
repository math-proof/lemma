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
public import Def.v1.Atlas.LieGroups.code.CSTTheorem


public noncomputable section

universe u

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

end
