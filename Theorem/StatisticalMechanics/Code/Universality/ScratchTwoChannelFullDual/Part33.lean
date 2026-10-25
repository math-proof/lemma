/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part41
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullMaxInnerTraceRep_onEither {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcTwoChannelFullInnerVertex gamma gamma') :
    rlc_connectorOnEither gamma gamma'
      (rlc_twoChannelFullMaxInnerTraceRep gamma gamma' x) :=
  rlc_twoChannelFullMaxComponentTraceRep_onEither gamma gamma' _

theorem rlc_twoChannelFullMaxInnerContraction_eq_of_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Reachable
      x y) :
    rlc_twoChannelFullMaxInnerContraction gamma gamma' x =
      rlc_twoChannelFullMaxInnerContraction gamma gamma' y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => rfl
  | cons huv p ih =>
      exact (rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring
        gamma gamma' huv).trans ih

theorem rlc_twoChannelFullMaxInnerTraceRep_eq_of_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Reachable
      x y) :
    rlc_twoChannelFullMaxInnerTraceRep gamma gamma' x =
      rlc_twoChannelFullMaxInnerTraceRep gamma gamma' y :=
  congrArg (rlc_twoChannelFullMaxComponentTraceRep gamma gamma')
    (rlc_twoChannelFullMaxInnerContraction_eq_of_reachable
      gamma gamma' hxy)


end
end StatMech.Universality
