/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part2
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def ghsiSubsetMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) : ℝ :=
  ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf)
      (ghsvp_fieldSet A) *
    ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf)
      (ghsvp_someSet Aᶜ)

end StatMech.Ising
