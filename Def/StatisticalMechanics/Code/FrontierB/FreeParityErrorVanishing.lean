/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorVanishing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorVanishing
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

noncomputable def inverseAxisTranslateFinset
    (hd : 1 ≤ d) (n : Nat) (B : Finset (Site d)) : Finset (Site d) :=
  B.image fun x => (FK.freeAxisTranslationPower hd n)⁻¹ • x

end StatMech.FrontierB
