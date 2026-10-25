/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.MaxInfluenceHalf
import Theorem.StatisticalMechanics.Code.Probability.NearHalfBKKKL
import Theorem.StatisticalMechanics.Code.Probability.PBiasedKKLClose
import Theorem.StatisticalMechanics.Code.BeffaraDC.MaxInfluencePBiased
open scoped BigOperators
open Finset Real Set


namespace StatMech.BeffaraDC

open StatMech ConfigSpace Probability OSSS TwoDim

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def pBiasedCorrection (p : ℝ) : ℝ :=
  (1 - 4 * p * (1 - p)) * (Probability.ptn_sigma p) ^ 2


end StatMech.BeffaraDC
