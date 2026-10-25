/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Structure.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part2


noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

def polynomialInvariantSubalgebra (k : Type*) [CommSemiring k]
    (G : Type*) [Group G] (ι : Type*)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)) :
    Subalgebra k (MvPolynomial ι k) :=
  Subalgebra.invariants G algAct

def IsInducedPolynomialAction {k : Type*} [CommRing k]
    {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V)
    (G : Type*) [Group G]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)) : Prop :=
  ∀ (g : G) (i : ι),
    algAct g (MvPolynomial.X i) =
    Finset.univ.sum fun j =>
      MvPolynomial.C (b.repr (ρ g (b i)) j) * MvPolynomial.X j

def IsPolynomialAlgebra {R : Type*} [CommSemiring R]
    (A : Type*) [Semiring A] [Algebra R A] : Prop :=
  ∃ (n : ℕ), Nonempty (MvPolynomial (Fin n) R ≃ₐ[R] A)

noncomputable def orbitPoly {k : Type*} [Field k]
    {G : Type*} [Group G] [Fintype G] {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) : Polynomial (MvPolynomial ι k) :=
  Finset.univ.prod (fun g => Polynomial.X - Polynomial.C ((algAct g) p))

end
