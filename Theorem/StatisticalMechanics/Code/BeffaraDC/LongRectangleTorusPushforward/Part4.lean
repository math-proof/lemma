/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Instance.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part2
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


theorem torusPlanarPushforward_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (Site 2)))) :
    torusPlanarPushforward L hp hp1 hq B =
      torusAmbientMeasure L hp hp1 hq
        (torusPlanarPullback L ⁻¹' B) := by
  exact (measurableEmbedding_torusPlanarPullback L).map_apply
    (torusAmbientMeasure L hp hp1 hq) B


theorem torusPlanarPushforward_real_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (Site 2)))) :
    (torusPlanarPushforward L hp hp1 hq).real B =
      (torusAmbientMeasure L hp hp1 hq).real
        (torusPlanarPullback L ⁻¹' B) := by
  simp only [Measure.real, torusPlanarPushforward_apply]


theorem torusPlanarPushforward_image_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    torusPlanarPushforward L hp hp1 hq
        (torusPlanarPullback L '' A) =
      torusAmbientMeasure L hp hp1 hq A := by
  rw [torusPlanarPushforward_apply]
  rw [Set.preimage_image_eq A (torusPlanarPullback_injective L)]


theorem torusPlanarPushforward_real_image_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    (torusPlanarPushforward L hp hp1 hq).real
        (torusPlanarPullback L '' A) =
      (torusAmbientMeasure L hp hp1 hq).real A := by
  simp only [Measure.real, torusPlanarPushforward_image_apply]


theorem torusPlanarPushforward_planarLiftEvent_apply
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    torusPlanarPushforward L hp hp1 hq
        (bdcTorusPlanarLiftEvent L A) =
      torusAmbientMeasure L hp hp1 hq A := by
  exact torusPlanarPushforward_image_apply L hp hp1 hq A


theorem torusPlanarPushforward_real_planarLiftEvent_apply
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    (torusPlanarPushforward L hp hp1 hq).real
        (bdcTorusPlanarLiftEvent L A) =
      (torusAmbientMeasure L hp hp1 hq).real A := by
  exact torusPlanarPushforward_real_image_apply L hp hp1 hq A


theorem monotone_torusPlanarPullback (L : ℕ) [Fact (2 < L)] :
    Monotone (torusPlanarPullback L) := by
  intro omega eta homega e
  unfold torusPlanarPullback torusAmbientConfigExtend
  split_ifs with he
  · exact homega ⟨Sym2.map (torusReduceSite L) e, he⟩
  · exact le_rfl


theorem torusPlanarPullback_preimage_isIncreasing
    (L : ℕ) [Fact (2 < L)]
    {A : Set (ConfigSpace (Sym2 (Site 2)))} (hA : IsIncreasing A) :
    IsIncreasing (torusPlanarPullback L ⁻¹' A) := by
  intro omega eta homegaeta homega
  exact hA (monotone_torusPlanarPullback L homegaeta) homega


theorem torusPlanarPushforward_positivelyAssociated
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hpa : PositivelyAssociated (torusAmbientMeasure L hp hp1 hq)) :
    PositivelyAssociated (torusPlanarPushforward L hp hp1 hq) := by
  intro A B hA hB
  rw [torusPlanarPushforward_real_apply,
    torusPlanarPushforward_real_apply,
    torusPlanarPushforward_real_apply]
  rw [preimage_inter]
  exact hpa _ _
    (torusPlanarPullback_preimage_isIncreasing L hA)
    (torusPlanarPullback_preimage_isIncreasing L hB)


theorem torusPlanarPushforward_positivelyAssociated_of_one_le
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq : 1 ≤ q) :
    PositivelyAssociated (torusPlanarPushforward L hp hp1 hq0) :=
  torusPlanarPushforward_positivelyAssociated L hp hp1 hq0
    (torusAmbientMeasure_positivelyAssociated L hp hp1 hq0 hq)


end StatMech.BeffaraDC
