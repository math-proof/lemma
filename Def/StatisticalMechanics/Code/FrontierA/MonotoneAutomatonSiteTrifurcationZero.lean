/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonTrifurcation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonBurtonKeane
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open Finset Filter Topology

open scoped ENNReal

variable {d : ℕ}

def SiteCanonicalTrifurcationEvent (x : Site d) :
    Set (ConfigSpace (Site d)) :=
  {eta | IsCanonicalTrifurcation d (siteToBond eta) x}

end StatMech.FrontierA
