module
public import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
public import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
public import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
public import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part8
open scoped BigOperators symmDiff
open Finset SimpleGraph Set
set_option maxHeartbeats 2400000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsiDirectionalCovariance (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (f : ConfigSpace V → ℝ) : ℝ :=
  expJ G.edgeFinset K hf (fun s => f s * ghsiDirSpin dir s) -
    expJ G.edgeFinset K hf f * expJ G.edgeFinset K hf (ghsiDirSpin dir)

end StatMech.Ising
