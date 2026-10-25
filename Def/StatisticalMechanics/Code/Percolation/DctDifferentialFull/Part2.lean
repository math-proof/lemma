/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull
open MeasureTheory Function Set
open scoped NNReal ENNReal
open StatMech
open Finset


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def edgesWithinFinset (S : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  (S ×ˢ S).image (fun p => s(p.1, p.2))

end Percolation
end StatMech
