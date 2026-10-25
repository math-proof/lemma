/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourCurrentTree
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorEdgecopyBridge
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneResummation
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneCardBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorResummation
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteTreeFourCurrentPattern_resum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (P : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> Prop)
    (hsum : Summable (finiteTreeFourCurrentPatternSummand G beta J P))
    (hnonneg : ∀ z, 0 <= finiteTreeFourCurrentPatternSummand G beta J P z) :
    Summable (fun total : G.edgeFinset -> Nat =>
      finiteTreeFourColorCoefficient G total P *
        weight G beta J (ofEdgeFun G total)) ∧
      (∑' z, finiteTreeFourCurrentPatternSummand G beta J P z) =
        ∑' total : G.edgeFinset -> Nat,
          finiteTreeFourColorCoefficient G total P *
            weight G beta J (ofEdgeFun G total) := by
  let Q := grahamPairPairEquivSigma (E := G.edgeFinset)
  let f := finiteTreeFourCurrentPatternSummand G beta J P
  have hF : Summable (fun s => f (Q.symm s)) :=
    Q.symm.summable_iff.mpr hsum
  have hFnonneg : ∀ s, 0 <= f (Q.symm s) := fun s => hnonneg _
  have houter : Summable (fun total =>
      ∑' split : GrahamFourSplit G total, f (Q.symm ⟨total, split⟩)) :=
    (summable_sigma_of_nonneg hFnonneg).mp hF |>.2
  have hfiber (total : G.edgeFinset -> Nat) :
      (∑' split : GrahamFourSplit G total, f (Q.symm ⟨total, split⟩)) =
        finiteTreeFourColorCoefficient G total P *
          weight G beta J (ofEdgeFun G total) := by
    rw [tsum_fintype]
    unfold finiteTreeFourColorCoefficient
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro split hsplit
    change finiteTreeFourCurrentPatternSummand G beta J P
        (Q.symm ⟨total, split⟩) = _
    dsimp [finiteTreeFourCurrentPatternSummand, Q,
      grahamPairPairEquivSigma, grahamQuadEquivSigma,
      grahamFourthProfile]
    rw [show grahamFourthProfile total split.1.1 split.1.2.1
        split.1.2.2 =
        (fun e => total e - split.1.1 e - split.1.2.1 e - split.1.2.2 e) by
      rfl]
    rw [grahamWeight_split4_eq_binom G beta J total
      split.1.1 split.1.2.1 split.1.2.2 split.2]
    simp only [grahamFourSplitMultiplicity]
    ring
  have hcoeff : Summable (fun total : G.edgeFinset -> Nat =>
      finiteTreeFourColorCoefficient G total P *
        weight G beta J (ofEdgeFun G total)) :=
    houter.congr hfiber
  refine ⟨hcoeff, ?_⟩
  change (∑' z, f z) = _
  calc
    (∑' z, f z) = ∑' z, f (Q.symm (Q z)) := by
      apply tsum_congr
      intro z
      rw [Equiv.symm_apply_apply]
    _ = ∑' s, f (Q.symm s) := Q.tsum_eq (fun s => f (Q.symm s))
    _ = ∑' total, ∑' split : GrahamFourSplit G total,
        f (Q.symm ⟨total, split⟩) := by
      exact hF.tsum_sigma
    _ = _ := by
      apply tsum_congr
      exact hfiber


end StatMech.FrontierA
