/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def PairedEdgeTwoColorHexAlternative {V I : Type*}
    (source target : I → Sym2 V) (R L : Set V) : Prop :=
  ∀ A B : Set V,
    R ⊆ A → L ∩ A = ∅ → R ⊆ B → L ∩ B = ∅ →
      ¬∀ i : I, PairedEdgeMonochromatic A (source i) ∨
        PairedEdgeMonochromatic B (target i)

end
end StatMech.Universality
