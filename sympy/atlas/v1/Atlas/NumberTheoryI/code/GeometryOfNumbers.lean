/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GeometryOfNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.NumberTheoryI.code.DirichletSeries
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.DirichletSeries

universe u

noncomputable section

open MeasureTheory Measure Set Submodule ZLattice Module
open scoped NumberField

namespace GeometryOfNumbers

abbrev IsCocompactAddSubgroup {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    (H : AddSubgroup G) : Prop :=
  CompactSpace (G ⧸ H)


abbrev IsFullLattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Prop :=
  IsZLattice ℝ L

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in


abbrev IsFundamentalDomain {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (L : Submodule ℤ E) (F : Set E)
    (μ : MeasureTheory.Measure E := by volume_tac) : Prop :=
  IsAddFundamentalDomain L F μ


abbrev covol {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (L : Submodule ℤ E) (μ : MeasureTheory.Measure E := by volume_tac) : ℝ :=
  covolume L μ


def IsSymmetricSet {V : Type*} [AddCommGroup V] (S : Set V) : Prop :=
  -S = S


abbrev convexBody (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    Set (NumberField.mixedEmbedding.mixedSpace K) :=
  NumberField.mixedEmbedding.convexBodySum K t

open NumberField.InfinitePlace NumberField.mixedEmbedding in
alias convex_body_volume := convexBodySum_volume

open NumberField in

def IsUnramifiedOutside (K : Type*) [Field K] [NumberField K] (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ¬((p : ℤ) ∣ discr K)
