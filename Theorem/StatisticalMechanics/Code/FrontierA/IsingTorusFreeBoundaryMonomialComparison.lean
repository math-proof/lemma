/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusPlusBoundaryField.Part2
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryMonomial
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryMonomialComparison
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteCutConditionalSpinProd_le_plus
    (beta : Real) (hbeta : 0 ≤ beta) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (A : Finset {v : V // v ∈ S}) :
    finiteCutConditionalSpinProd G beta S outside A ≤
      finiteCutPlusSpinProd G beta S A := by
  unfold finiteCutConditionalSpinProd finiteCutPlusSpinProd
  have hmono := ginibre_boundary_monomial_product_mono
    (finiteCutGraph G S).edgeFinset (fun _ ↦ beta)
    (fun z ↦ beta * finiteCutPlusBoundaryField G S z)
    (fun z ↦ beta * finiteCutBoundaryField G S outside z)
    (fun _ _ ↦ hbeta)
    (fun z ↦ by
      rw [abs_mul, abs_of_nonneg hbeta]
      exact mul_le_mul_of_nonneg_left
        (abs_finiteCutBoundaryField_le_plus G S outside z) hbeta)
    (spinProd A) (fun _ ↦ 1)
    (isSpinMonomial_spinProd A) IsSpinMonomial.const_one
  simpa only [mul_one] using hmono


end
end StatMech.FrontierA
