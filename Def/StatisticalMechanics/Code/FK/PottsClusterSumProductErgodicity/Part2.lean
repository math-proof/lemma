/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumErgodicFactor.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity
open Filter Function MeasureTheory MeasurableSpace Set Topology
open scoped ENNReal symmDiff


namespace StatMech.FK

open Lattice

noncomputable def pottsInverseAxisFinset {d : Nat}
    (hd : 1 <= d) (n : Nat) (B : Finset (Site d)) : Finset (Site d) :=
  B.image fun x => (freeAxisTranslationPower hd n)⁻¹ • x

end StatMech.FK
