/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductTransport
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


section FiniteProductFamily

variable [∀ e, Fintype (S e)]

structure BernoulliBlockData {T : Type*} [Fintype T] (w : T → ℝ) where
  n : ℕ
  phi : Fin n → Bool → ℝ
  decode : (Fin n → Bool) → T
  phi_nonneg : ∀ i b, 0 ≤ phi i b
  phi_sum_one : ∀ i, phi i false + phi i true = 1
  decode_surjective : Function.Surjective decode
  expectation : ∀ h : T → ℝ,
    productExpectation phi (h ∘ decode) = ∑ t, w t * h t

noncomputable irreducible_def bernoulliBlockDataOfWeights {T : Type*} [Fintype T]
    (w : T → ℝ) (hw0 : ∀ t, 0 ≤ w t) (hw1 : (∑ t, w t) = 1) :
    BernoulliBlockData w :=
  Classical.choice <| by
    rcases exists_bernoulliBlockRepresentation w hw0 hw1 with
      ⟨n, phi, decode, hphi0, hphi1, hdecode, hexpect⟩
    exact ⟨
      { n := n
        phi := phi
        decode := decode
        phi_nonneg := hphi0
        phi_sum_one := hphi1
        decode_surjective := hdecode
        expectation := hexpect }⟩

end FiniteProductFamily
end StatMech.FrontierA
