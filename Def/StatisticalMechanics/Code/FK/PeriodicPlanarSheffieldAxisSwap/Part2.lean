/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def siteAxisSwapAddEquiv : Site 2 ≃+ Site 2 where
  toFun := siteAxisSwap
  invFun := siteAxisSwap
  left_inv := siteAxisSwap_swap
  right_inv := siteAxisSwap_swap
  map_add' := siteAxisSwap_add


def PeriodicGraph.axisSwap (P : PeriodicGraph V) : PeriodicGraph V where
  graph := P.graph
  shift z := P.shift (siteAxisSwap z)
  shift_zero := by simpa using P.shift_zero
  shift_add z w v := by
    simpa using P.shift_add (siteAxisSwap z) (siteAxisSwap w) v
  shift_adj z x y := P.shift_adj (siteAxisSwap z) x y
  fundamentalDomain := P.fundamentalDomain
  fundamentalDomain_nonempty := P.fundamentalDomain_nonempty
  covers v := by
    obtain ⟨z, u, hu, hzu⟩ := P.covers v
    exact ⟨siteAxisSwap z, u, hu, by simpa [siteAxisSwap_swap] using hzu⟩
  locallyFinite := P.locallyFinite


def axisSwapCoordinates :
    (Fin 2 → Real) ≃L[Real] (Fin 2 → Real) :=
  ContinuousLinearEquiv.piCongrLeft Real (fun _ : Fin 2 => Real) Fin.revPerm

end StatMech.FK.PeriodicPlanar
