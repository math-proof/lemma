/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part2


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationUnitCyclePairedRepairs.toPhysicalPairedBranches
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationUnitCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt where
  branch choice :=
    { toFun := fun source =>
        sixVertexUnitCyclePhysicalTarget source (repairs.repair source choice)
      inj' := by
        intro first second heq
        exact repairs.source_recoverable first second choice heq }
  distinct := repairs.branch_distinct
  aggregateTotalC := by
    intro source
    have hfalse := (repairs.repair source false).loopGrade_eq
    have htrue := (repairs.repair source true).loopGrade_eq
    simp only [sixVertexPhysicalArrowPairGrade, Prod.mk.injEq,
      and_true] at hfalse htrue
    change
      2 * (sixVertexTorusCTypeCount source.1.1 +
          sixVertexTorusCTypeCount source.2.1) ≤
        (sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source false).first.mask source.1.1) +
          sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source false).second.mask source.2.1)) +
        (sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source true).first.mask source.1.1) +
          sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source true).second.mask source.2.1))
    rw [hfalse, htrue]
    omega

def SixVertexPositiveEvenTraceUnitCyclePairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) → (hnN : n < N) →
    Nonempty
      (SixVertexConfigurationUnitCyclePairedRepairs
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)

def SixVertexCanonicalPositiveEvenTraceUnitCyclePairedRepairs : Prop :=
  forall r k : Nat,
    SixVertexPositiveEvenTraceUnitCyclePairedRepairs
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))

end
end StatMech.FrontierD
