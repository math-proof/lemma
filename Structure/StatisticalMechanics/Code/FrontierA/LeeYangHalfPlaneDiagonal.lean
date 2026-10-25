/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
open Filter Metric Set Topology
open scoped UniformConvergence


namespace StatMech.FrontierA

open StatMech.FK


structure CompactExhaustion (U : Set ℂ) where
  sets : ℕ → Set ℂ
  isCompact : ∀ n, IsCompact (sets n)
  subset : ∀ n, sets n ⊆ U
  cofinal : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ n, K ⊆ sets n


end StatMech.FrontierA
