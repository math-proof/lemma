/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def ghsiTZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) : ℝ :=
  ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e)
    (fun x => if x ∈ A then 2 * hf x else 0)


noncomputable def ghsiUZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e) (fun _ => 0)


end StatMech.Ising
