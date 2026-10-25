/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part8
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsi_hasDerivAt_directionalCovariance (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (f : ConfigSpace V → ℝ) (t : ℝ) :
    HasDerivAt
      (fun u => ghsiDirectionalCovariance G K (ghsiFieldLine hf dir u) dir f)
      (expJ G.edgeFinset K (ghsiFieldLine hf dir t)
          (fun s => f s * ghsiDirSpin dir s * ghsiDirSpin dir s) -
        expJ G.edgeFinset K (ghsiFieldLine hf dir t)
            (fun s => f s * ghsiDirSpin dir s) *
          expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) -
        (expJ G.edgeFinset K (ghsiFieldLine hf dir t)
            (fun s => f s * ghsiDirSpin dir s) -
          expJ G.edgeFinset K (ghsiFieldLine hf dir t) f *
            expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir)) *
          expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) -
        expJ G.edgeFinset K (ghsiFieldLine hf dir t) f *
          (expJ G.edgeFinset K (ghsiFieldLine hf dir t)
              (fun s => ghsiDirSpin dir s * ghsiDirSpin dir s) -
            expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) *
              expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir))) t := by
  unfold ghsiDirectionalCovariance
  have h := (ghsi_hasDerivAt_expectation_fieldLine G K hf dir
      (fun s => f s * ghsiDirSpin dir s) t).sub
    ((ghsi_hasDerivAt_expectation_fieldLine G K hf dir f t).mul
      (ghsi_hasDerivAt_expectation_fieldLine G K hf dir (ghsiDirSpin dir) t))
  convert h using 1 <;> ring


end StatMech.Ising
