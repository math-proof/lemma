/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part3
import Theorem.StatisticalMechanics.Code.Foundations.FiniteBidegreeHall
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexMarkedDecoratedPair_eq_pairMass
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    (Fintype.card (SixVertexMarkedDecoratedPair T left right k) : Real) =
      sixVertexMarkedSectorPairMass T left right k := by
  unfold sixVertexMarkedSectorPairMass
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro pair hpair
  exact (sixVertexMarkedPairMultiplicity_eq_natCast
    pair.1.1 pair.2.1 pair.1.2.1 pair.2.2.1 k).symm


end
end StatMech.FrontierD
