/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part4


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationUnitCyclePairedRepairs.toPairUnionCycle
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationUnitCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt where
  target source branch :=
    sixVertexUnitCyclePhysicalTarget source (repairs.repair source branch)
  related source branch :=
    (repairs.repair source branch).target_twoCycleFine
  source_recoverable := repairs.source_recoverable
  branch_distinct := repairs.branch_distinct


def SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  ∀ M n : Nat, (hn0 : 0 < n) → (hnN : n < N) →
    Nonempty
      (SixVertexConfigurationPairUnionCyclePairedRepairs
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)

def SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs : Prop :=
  ∀ r k : Nat,
    SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))


def SixVertexPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  ∀ M n : Nat, (hn0 : 0 < n) → (hnN : n < N) →
    Nonempty
      (SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)

def SixVertexCanonicalPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings :
    Prop :=
  ∀ r k : Nat,
    SixVertexPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))

end
end StatMech.FrontierD
