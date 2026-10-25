/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.SimpleModule.Basic
import Def.v1.Atlas.LieGroups.code.KostantTheorem


noncomputable section

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

variable {P' : Type*} [DecidableEq P'] [AddCommGroup P']

structure KostantSetupData
    [LieAlgebra.IsSemisimple R 𝔤] where
  cartanSubalgebra : LieSubalgebra R 𝔤
  [instCartan : cartanSubalgebra.IsCartanSubalgebra]
  [instLieRingModuleSg : LieRingModule 𝔤 (SymmetricAlgebra R 𝔤)]
  [instLieModuleSg : LieModule R 𝔤 (SymmetricAlgebra R 𝔤)]
  invariantSubalgebra : Subalgebra R (SymmetricAlgebra R 𝔤)
  invariantSubalgebra_eq :
    ∀ x : SymmetricAlgebra R 𝔤,
      x ∈ invariantSubalgebra ↔ x ∈ LieModule.maxTrivSubmodule R 𝔤 (SymmetricAlgebra R 𝔤)
  harmonicSubspace : Submodule R (SymmetricAlgebra R 𝔤)
  [instFreeHarmonic : Module.Free R harmonicSubspace]
  harmonicSubspaceUEA : Submodule R (UniversalEnvelopingAlgebra R 𝔤)
  pbwHarmonicEquiv : harmonicSubspace ≃ₗ[R] harmonicSubspaceUEA
  pbwSymmEquiv : SymmetricAlgebra R 𝔤 ≃ₗ[R] UniversalEnvelopingAlgebra R 𝔤
  pbwInvariantToCenter : invariantSubalgebra ≃ₐ[R]
    Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)
  pbwSymmCompat : ∀ (a : ↥invariantSubalgebra) (h : ↥harmonicSubspace),
    pbwSymmEquiv (a.val * h.val) =
    (pbwInvariantToCenter a).val * (pbwHarmonicEquiv h).val
  W : Type*
  [instGroup : Group W]
  [instFintype : Fintype W]
  rank : ℕ
  degrees : Fin rank → ℕ
  P : Type*
  [instAddCommGroup_P : AddCommGroup P]
  [instDecEq_P : DecidableEq P]
  roots : Finset P
  posRoots : Finset P
  posRoots_sub_roots : posRoots ⊆ roots
  dominantWeights : Set P
  simpleCoroots : Fin rank → P
  pairingCoroot : P → Fin rank → ℤ
  dominantWeights_spec : dominantWeights = {μ : P | ∀ i : Fin rank, 0 ≤ pairingCoroot μ i}
  pairingCoroot_zero : ∀ i : Fin rank, pairingCoroot 0 i = 0
  rho : P
  signRep : W → ℤ
  actionW : W → P → P
  weylCharacter : P → AddMonoidAlgebra ℤ P

  gradedHomDim : P → ℕ → ℕ

  equation12_geom_form_field :
    ∀ (wt : P) (_ : wt ∈ dominantWeights),
      (Fintype.card W : ℤ) • gradedHilbertSeries (gradedHomDim wt) =
      (∏ i : Fin rank, qInteger (degrees i)) *
      powerSeriesCT (geomProductPS roots *
        PowerSeries.C (numeratorProd roots * weylCharacter wt))

  cst_equiv : TensorProduct R invariantSubalgebra harmonicSubspace ≃ₗ[R] SymmetricAlgebra R 𝔤
  cst_equiv_apply_tmul :
    ∀ (a : invariantSubalgebra) (h : harmonicSubspace),
      cst_equiv (a ⊗ₜ[R] h) = a.val * h.val
  invariantPolynomial : invariantSubalgebra ≃ₐ[R] MvPolynomial (Fin rank) R

end
