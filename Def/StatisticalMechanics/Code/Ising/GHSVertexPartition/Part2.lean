module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
public import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part2
open Finset Classical
set_option maxHeartbeats 1600000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


noncomputable def ghsvp_vertexCorr (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (S P : Finset W) : Real :=
  expJ (ghsvp_vertexEdges E S) J (fun _ => 0) (spinProd P)


noncomputable def ghsvp_vertexCorrField (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (S P : Finset W) : Real :=
  expJ (ghsvp_vertexEdges E S) J hf (spinProd P)

end StatMech.Ising
