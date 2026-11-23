/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/RandomProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.SubGaussian
public import Theorem.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.SubGaussian

@[expose] public section

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
