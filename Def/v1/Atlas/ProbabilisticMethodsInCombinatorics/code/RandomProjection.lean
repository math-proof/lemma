/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.SubGaussian
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.SubGaussian
open MeasureTheory Measure Real Set
open scoped ENNReal NNReal


namespace RandomProjection

set_option maxHeartbeats 800000

/-- Norm of the projection of $z \in \mathbb{R}^m$ onto the first $d$ coordinates,
$\| (z_1, \dots, z_d) \|_2$. -/
noncomputable def normProj (m d : ℕ) (hd : d ≤ m)
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.sqrt (∑ i : Fin d, (z (Fin.castLE hd i)) ^ 2)

end RandomProjection
