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
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteTrifurcationZero
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open Finset Filter Topology

open scoped ENNReal

variable {d : ℕ}

noncomputable def siteCanonicalTrifurcationCount
    (eta : ConfigSpace (Site d)) (n : ℕ) : ℕ :=
  (canonicalTrifurcationsInBox (siteToBond eta) (n + 1)).card

end StatMech.FrontierA
