/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GHSUnconditional
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

open StatMech.Walls StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamGhostLeadingRHS (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (i j k : V) : ℝ :=
  -2 * onePt G beta h i * onePt G beta h j * onePt G beta h k


noncomputable def grahamImprovedGHSRHS (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (i j k : V) : ℝ :=
  -2 * cov2 G beta h i k * cov2 G beta h j k * onePt G beta h k


noncomputable def grahamGhostCorrectedRHS (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (i j k : V) : ℝ :=
  grahamGhostLeadingRHS G beta h i j k + grahamImprovedGHSRHS G beta h i j k


end StatMech.FrontierA
