module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph Set
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def bondEnergySusceptibility (β h : ℝ) (o : V) : ℝ :=
  ∑ e ∈ G.edgeFinset, cov3sym G β h o e


noncomputable def susceptibility (β h : ℝ) (o : V) : ℝ :=
  ∑ x, cov2 G β h o x


end Ising
end StatMech
