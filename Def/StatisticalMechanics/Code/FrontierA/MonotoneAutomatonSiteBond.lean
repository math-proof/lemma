/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def siteToBond (eta : ConfigSpace (Site d)) :
    ConfigSpace (Sym2 (Site d)) :=
  Sym2.lift ⟨fun x y => eta x && eta y, fun _ _ => Bool.and_comm _ _⟩

end StatMech.FrontierA
