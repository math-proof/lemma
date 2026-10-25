/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


@[simp] theorem piFiberAssemble_apply_mem (K : Set E) (x : ∀ e, S e)
    (z : PiFiberFreeConfig (S := S) K) {e : E} (he : e ∈ K) :
    piFiberAssemble K x z e = x e := by
  simp [piFiberAssemble, he]

@[simp] theorem piFiberAssemble_apply_notMem (K : Set E) (x : ∀ e, S e)
    (z : PiFiberFreeConfig (S := S) K) {e : E} (he : e ∉ K) :
    piFiberAssemble K x z e = z ⟨e, he⟩ := by
  simp [piFiberAssemble, he]

theorem measurable_piFiberAssemble_right (K : Set E) (x : ∀ e, S e) :
    Measurable (piFiberAssemble K x) := by
  classical
  apply measurable_pi_lambda
  intro e
  by_cases he : e ∈ K
  · simpa [piFiberAssemble, he] using
      (measurable_const : Measurable
        (fun _ : PiFiberFreeConfig (S := S) K => x e))
  · let i : {e : E // e ∉ K} := ⟨e, he⟩
    simpa [piFiberAssemble, he, i] using
      (measurable_pi_apply i : Measurable
        (fun z : PiFiberFreeConfig (S := S) K => z i))

theorem measurable_piFiberAssemble_uncurry (K : Set E) :
    Measurable (Function.uncurry (piFiberAssemble (S := S) K)) := by
  classical
  apply measurable_pi_lambda
  intro e
  by_cases he : e ∈ K
  · simpa [Function.uncurry, piFiberAssemble, he] using
      (measurable_pi_apply e).comp measurable_fst
  · let i : {e : E // e ∉ K} := ⟨e, he⟩
    simpa [Function.uncurry, piFiberAssemble, he, i] using
      (measurable_pi_apply i).comp measurable_snd

theorem piFiberAssemble_piEquiv_symm
    (K : Set E)
    (u : ∀ i : {e : E // e ∈ K}, S i)
    (v w : PiFiberFreeConfig (S := S) K) :
    piFiberAssemble K
        ((piFiberSplit (S := S) K).symm (u, v)) w =
      (piFiberSplit (S := S) K).symm (u, w) := by
  classical
  funext e
  by_cases he : e ∈ K
  · simp [piFiberAssemble, piFiberSplit, he]
  · simp [piFiberAssemble, piFiberSplit, he]


end StatMech.FrontierA
