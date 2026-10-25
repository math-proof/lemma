/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part13
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourAuditedCoordinateTargetPair_valid
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedCoordinateTargetPairValid c := by
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hsource := sixVertexFourByFourAuditedCoordinateSourcePair_valid c
  unfold SixVertexFourByFourAuditedCoordinateSourcePairValid at hsource
  change (sixVertexFourByFourAuditedParamSourceFirst p c.firstSeam).IceRule /\
    (sixVertexFourByFourAuditedParamSourceSecond p c.secondSeam).IceRule /\ _ /\ _
    at hsource
  have hrepair := sixVertexFourByFourAuditedParamMatching_valid
    p c.firstSeam c.secondSeam hsource.1 hsource.2.1
      hsource.2.2.1 hsource.2.2.2
  unfold SixVertexFourByFourAuditedCoordinateTargetPairValid
  unfold SixVertexFourByFourValidColumnRepair at hrepair
  simpa [sixVertexFourByFourAuditedCoordinateTargetPair, p] using hrepair

theorem sixVertexFourByFourAuditedCoordinate_fineRelated
    (c : SixVertexFourByFourAuditedCoordinates) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByFourAuditedCoordinateSourcePair c)
      (sixVertexFourByFourAuditedCoordinateTargetPair c) := by
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hsource := sixVertexFourByFourAuditedCoordinateSourcePair_valid c
  unfold SixVertexFourByFourAuditedCoordinateSourcePairValid at hsource
  change (sixVertexFourByFourAuditedParamSourceFirst p c.firstSeam).IceRule /\
    (sixVertexFourByFourAuditedParamSourceSecond p c.secondSeam).IceRule /\ _ /\ _
    at hsource
  have hcolumns := sixVertexFourByFourAudited_selectedColumns_constant
    p c.firstSeam c.secondSeam hsource.1 hsource.2.1
      hsource.2.2.1 hsource.2.2.2
  simpa [sixVertexFourByFourAuditedCoordinateSourcePair,
    sixVertexFourByFourAuditedCoordinateTargetPair,
    sixVertexFourByFourAuditedParamTargetFirst,
    sixVertexFourByFourAuditedParamTargetSecond, p] using
    sixVertexFourByFourTogglePair_fineRelated
      (sixVertexFourByFourAuditedParamSourceFirst p c.firstSeam)
      (sixVertexFourByFourAuditedParamSourceSecond p c.secondSeam)
      (sixVertexFourByFourAuditedRepairColumns
        c.firstSeam c.secondSeam).1
      (sixVertexFourByFourAuditedRepairColumns
        c.firstSeam c.secondSeam).2
      hcolumns.1 hcolumns.2

theorem sixVertexFourByFourRowOfMask_injective_of_lt
    {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hrow : sixVertexFourByFourRowOfMask a =
      sixVertexFourByFourRowOfMask b) :
    a = b := by
  have hbits := congrArg Nat.ofBits hrow
  have haBits : Nat.ofBits (sixVertexFourByFourRowOfMask a) = a := by
    simpa [sixVertexFourByFourRowOfMask, Nat.mod_eq_of_lt ha] using
      (Nat.ofBits_testBit a 4)
  have hbBits : Nat.ofBits (sixVertexFourByFourRowOfMask b) = b := by
    simpa [sixVertexFourByFourRowOfMask, Nat.mod_eq_of_lt hb] using
      (Nat.ofBits_testBit b 4)
  exact haBits.symm.trans (hbits.trans hbBits)

theorem sixVertexFourByFourAuditedRowZero_lt (p : Fin 16) :
    (sixVertexFourByFourAuditedRowZero p).1 < 16 /\
      (sixVertexFourByFourAuditedRowZero p).2 < 16 := by
  fin_cases p <;> decide

theorem sixVertexFourByFourAuditedRowMiddle_lt (p : Fin 16) :
    (sixVertexFourByFourAuditedRowMiddle p).1 < 16 /\
      (sixVertexFourByFourAuditedRowMiddle p).2 < 16 := by
  fin_cases p <;> decide

theorem sixVertexFourByFourAuditedRowLast_lt (p : Fin 4) :
    (sixVertexFourByFourAuditedRowLast p).1 < 16 /\
      (sixVertexFourByFourAuditedRowLast p).2 < 16 := by
  fin_cases p <;> decide

theorem sixVertexFourByFourAuditedRowZero_injective :
    Function.Injective sixVertexFourByFourAuditedRowZero := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp_all [sixVertexFourByFourAuditedRowZero]

theorem sixVertexFourByFourAuditedRowMiddle_injective :
    Function.Injective sixVertexFourByFourAuditedRowMiddle := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp_all [sixVertexFourByFourAuditedRowMiddle]

theorem sixVertexFourByFourAuditedRowLast_injective :
    Function.Injective sixVertexFourByFourAuditedRowLast := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp_all [sixVertexFourByFourAuditedRowLast]

theorem sixVertexFourByFourAuditedCoordinateRowZero_injective :
    Function.Injective (fun s : Fin 4 × Fin 4 =>
      sixVertexFourByFourAuditedCoordinateRowZero s.1 s.2) := by
  rintro ⟨first, second⟩ ⟨first', second'⟩
  fin_cases first <;> fin_cases second <;>
    fin_cases first' <;> fin_cases second' <;>
    simp_all [sixVertexFourByFourAuditedCoordinateRowZero]

set_option maxHeartbeats 2000000 in

theorem sixVertexFourByFourAuditedMiddlePair_injective
    (firstSeam secondSeam : Fin 4) :
    Function.Injective
      (sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam) := by
  intro a b
  fin_cases firstSeam <;> fin_cases secondSeam <;>
    fin_cases a <;> fin_cases b <;>
    simp_all [sixVertexFourByFourAuditedMiddlePair,
      sixVertexFourByFourAuditedMiddleA,
      sixVertexFourByFourAuditedMiddleB,
      sixVertexFourByFourAuditedMiddleBNext,
      sixVertexFourByFourAuditedMiddleC]

end
end StatMech.FrontierD
