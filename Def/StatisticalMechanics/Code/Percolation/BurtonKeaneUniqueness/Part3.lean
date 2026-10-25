/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part2
open MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


noncomputable def boxFinsetBK (d n : ℕ) : Finset (Site d) := (box_finite d n).toFinset

open Classical in


noncomputable def Tcount (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : ℕ :=
  ((boxFinsetBK d n).filter (fun x => IsTrifurcation d ω x)).card


end Percolation
end StatMech
