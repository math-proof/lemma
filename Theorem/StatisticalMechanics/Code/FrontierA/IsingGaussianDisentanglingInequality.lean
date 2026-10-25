/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedAuxiliaryAlgebra
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianDisentanglingInequality
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem summable_finiteTreePairVacuumWeight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A : Finset V) :
    Summable (finiteTreePairVacuumWeight G beta J A) := by
  have h := summable_gatedSourcePairSummand G beta J A ∅ (fun _ => True)
  apply h.congr
  rintro ⟨p, q⟩
  simp [finiteTreePairVacuumWeight]

theorem summable_finiteTreeIndependentDisjointSummand_fourCurrent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    Summable (finiteTreeIndependentDisjointSummand G beta J i j k l) := by
  have hleft := summable_finiteTreePairVacuumWeight
    G beta J ({i, j} : Finset V)
  have hright := summable_finiteTreePairVacuumWeight
    G beta J ({k, l} : Finset V)
  have hmajor : Summable (fun z : DisentangleFourProfiles G =>
      ‖finiteTreePairVacuumWeight G beta J {i, j} z.1‖ *
        ‖finiteTreePairVacuumWeight G beta J {k, l} z.2‖) :=
    hleft.norm.mul_of_nonneg hright.norm
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply Summable.of_norm
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro z
  unfold finiteTreeIndependentDisjointSummand
  by_cases h : ¬ ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
  · simp [h, norm_mul]
  · simp [h]
    positivity

end StatMech.FrontierA
