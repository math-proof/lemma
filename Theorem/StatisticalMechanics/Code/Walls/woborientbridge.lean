/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part5
import Theorem.StatisticalMechanics.Code.Walls.wosorientedsign.Part2
import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wob_rayEdge_eq_hCrossEdge (z : Site 2) (c : ℤ) :
    wcb_canonRayEdge z c = rpc_hCrossEdge (![c, z 1] : Site 2) := by
  unfold wcb_canonRayEdge rpc_hCrossEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]


theorem wob_signStep_ne_zero_col (z u v : Site 2) (h : wnd_signStep z u v ≠ 0) :
    jec_rayEdge z s(u, v) :=
  (wnd_signStep_ne_zero_iff z u v).mp h


end Lattice
end StatMech
