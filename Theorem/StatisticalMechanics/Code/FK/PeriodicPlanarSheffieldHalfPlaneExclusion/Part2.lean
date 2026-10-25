/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneBarrier
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

theorem not_primalBarrierReady_and_complementaryDualTransverseWalks
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V)) :
    ¬(D.primalEmbedding.primalHalfPlaneBarrierReady omega ∧
      D.HasOpenComplementaryDualTransverseWalks omega) := by
  rintro ⟨hbarrier, htransverse⟩
  obtain ⟨a, b, c, d, hab, hcd, xl, xu, xj, lower, upper,
    hlowerNil, hupperNil, hlowerOpen, hupperOpen,
    hlowerBottom, hupperTop, hlowerX, hupperX⟩ := hbarrier
  obtain ⟨yl, yr, dual, hdualNil, hdualOpen, hdualLeft,
    hdualRight, hdualY⟩ := htransverse a b c d hab hcd
  exact D.no_open_dual_transverse_walk_of_joined_primal_arms
    omega hab hcd lower upper dual hlowerNil hupperNil hdualNil
    hlowerOpen hupperOpen hdualOpen hdualLeft hdualRight
    hlowerBottom hupperTop hlowerX hupperX hdualY

end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
