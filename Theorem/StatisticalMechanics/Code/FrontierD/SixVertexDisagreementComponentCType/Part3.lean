/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusSwitchFirst_fullDisagreement
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    sixVertexTorusSwitchFirst
      (sixVertexFullDisagreementMask omega eta) omega eta = eta := by
  apply SixVertexArrows.ext <;> funext v
  · by_cases h : omega.horizontal v = eta.horizontal v <;>
      simp [sixVertexTorusSwitchFirst, sixVertexFullDisagreementMask, h]
  · by_cases h : omega.vertical v = eta.vertical v <;>
      simp [sixVertexTorusSwitchFirst, sixVertexFullDisagreementMask, h]


theorem sixVertexTorusSwitchSecond_fullDisagreement
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    sixVertexTorusSwitchSecond
      (sixVertexFullDisagreementMask omega eta) omega eta = omega := by
  apply SixVertexArrows.ext <;> funext v
  · by_cases h : omega.horizontal v = eta.horizontal v <;>
      simp [sixVertexTorusSwitchSecond, sixVertexFullDisagreementMask, h]
  · by_cases h : omega.vertical v = eta.vertical v <;>
      simp [sixVertexTorusSwitchSecond, sixVertexFullDisagreementMask, h]


theorem sixVertexFullDisagreementMask_seamTransfer_eq_two
    {T : EvenTorus} (omega eta : SixVertexArrows T) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    sixVertexTorusMaskSeamTransfer
      (sixVertexFullDisagreementMask omega eta) omega eta = 2 := by
  have hcount := intCast_upCount_switchFirst_eq_add_seamTransfer
    (sixVertexFullDisagreementMask omega eta) omega eta
  rw [sixVertexTorusSwitchFirst_fullDisagreement,
    homegaSector, hetaSector] at hcount
  have hone : n - 1 + 1 = n :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')
  omega


theorem sixVertexLexDisagreementComponentSwitch_local_eq_or_swap
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (v : T.Vertex) :
    (sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchFirst
          (sixVertexLexDisagreementComponentMask T omega eta h)
          omega eta) v,
      sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchSecond
          (sixVertexLexDisagreementComponentMask T omega eta h)
          omega eta) v) =
        (sixVertexLocalIncomingPattern omega v,
          sixVertexLocalIncomingPattern eta v) \/
      (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) v,
        sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) v) =
          (sixVertexLocalIncomingPattern eta v,
            sixVertexLocalIncomingPattern omega v) := by
  rw [sixVertexTorusLocalIncomingPattern_pairSwitch]
  by_cases hactive : exists d, sixVertexTorusLocalSwitchMask
      (sixVertexLexDisagreementComponentMask T omega eta h) v d = true
  · right
    exact sixVertexLocalSwapMask_eq_pair_of_disagreementMask _ _ _
      (sixVertexLexDisagreementComponentMask_local_eq_disagreement
        T omega eta h v hactive)
  · left
    have hzero : sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) v =
          fun _ => false := by
      funext d
      cases hm : sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) v d
      · rfl
      · exact False.elim (hactive ⟨d, hm⟩)
    simp [sixVertexLocalSwapMask, hzero]


theorem sixVertexLexDisagreementComponentSwitch_localCTypeCount
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (v : T.Vertex) :
    sixVertexLocalCTypeCount
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) v)
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) v) =
      sixVertexLocalCTypeCount
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v) := by
  rcases sixVertexLexDisagreementComponentSwitch_local_eq_or_swap
    T omega eta h v with hsame | hswap
  · have hfirst : sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) v = sixVertexLocalIncomingPattern omega v := by
        simpa using congrArg Prod.fst hsame
    have hsecond : sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) v = sixVertexLocalIncomingPattern eta v := by
        simpa using congrArg Prod.snd hsame
    rw [hfirst, hsecond]
  · have hfirst : sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) v = sixVertexLocalIncomingPattern eta v := by
        simpa using congrArg Prod.fst hswap
    have hsecond : sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) v = sixVertexLocalIncomingPattern omega v := by
        simpa using congrArg Prod.snd hswap
    rw [hfirst, hsecond]
    simp only [sixVertexLocalCTypeCount, add_comm]


theorem sixVertexLexDisagreementComponentSwitch_totalCTypeCount
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    sixVertexTorusCTypeCount
          (sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) +
        sixVertexTorusCTypeCount
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) =
      sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta := by
  classical
  simp only [sixVertexTorusCTypeCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  let first := sixVertexTorusSwitchFirst
    (sixVertexLexDisagreementComponentMask T omega eta h) omega eta
  let second := sixVertexTorusSwitchSecond
    (sixVertexLexDisagreementComponentMask T omega eta h) omega eta
  have hlocal := sixVertexLexDisagreementComponentSwitch_localCTypeCount
    T omega eta h v
  unfold sixVertexLocalCTypeCount at hlocal
  have hfirst :
      (if (sixVertexLocalIncomingPattern first v).IsCType then 1 else 0) =
        if first.IsCType v then 1 else 0 :=
    if_congr (sixVertexLocalIncomingPattern_isCType_iff first v) rfl rfl
  have hsecond :
      (if (sixVertexLocalIncomingPattern second v).IsCType then 1 else 0) =
        if second.IsCType v then 1 else 0 :=
    if_congr (sixVertexLocalIncomingPattern_isCType_iff second v) rfl rfl
  have homega :
      (if (sixVertexLocalIncomingPattern omega v).IsCType then 1 else 0) =
        if omega.IsCType v then 1 else 0 :=
    if_congr (sixVertexLocalIncomingPattern_isCType_iff omega v) rfl rfl
  have heta :
      (if (sixVertexLocalIncomingPattern eta v).IsCType then 1 else 0) =
        if eta.IsCType v then 1 else 0 :=
    if_congr (sixVertexLocalIncomingPattern_isCType_iff eta v) rfl rfl
  change (if first.IsCType v then 1 else 0) +
      (if second.IsCType v then 1 else 0) =
    (if omega.IsCType v then 1 else 0) +
      (if eta.IsCType v then 1 else 0)
  rw [← hfirst, ← hsecond, ← homega, ← heta]
  exact hlocal


theorem sixVertexLexDisagreementComponentSwitch_multiplicityNat
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (k : Nat) :
    sixVertexMarkedPairMultiplicityNat
        (sixVertexTorusSwitchFirst
          (sixVertexLexDisagreementComponentMask T omega eta h)
          omega eta)
        (sixVertexTorusSwitchSecond
          (sixVertexLexDisagreementComponentMask T omega eta h)
          omega eta) k =
      sixVertexMarkedPairMultiplicityNat omega eta k := by
  unfold sixVertexMarkedPairMultiplicityNat
  rw [sixVertexLexDisagreementComponentSwitch_totalCTypeCount
    T omega eta h]


theorem sixVertexLexDisagreementComponentSwitch_markedWeight
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (homega : omega.IceRule) (heta : eta.IceRule)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    sixVertexTorusMarkedWeight
          (sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) *
        sixVertexTorusMarkedWeight
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta) =
      sixVertexTorusMarkedWeight omega *
        sixVertexTorusMarkedWeight eta := by
  obtain ⟨hfirstIce, hsecondIce⟩ :=
    sixVertexLexDisagreementComponentSwitch_ice
      T omega eta homega heta h
  rw [sixVertexTorusMarkedWeight_eq_pow _ hfirstIce,
    sixVertexTorusMarkedWeight_eq_pow _ hsecondIce,
    sixVertexTorusMarkedWeight_eq_pow _ homega,
    sixVertexTorusMarkedWeight_eq_pow _ heta,
    ← pow_add, ← pow_add,
    sixVertexLexDisagreementComponentSwitch_totalCTypeCount
      T omega eta h]


theorem sixVertexLexDisagreementComponentSwitch_to_middle_of_transfer_one
    (T : EvenTorus) (omega eta : SixVertexArrows T) (n : Nat)
    (homega : omega.IceRule) (heta : eta.IceRule)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (htransfer : sixVertexTorusMaskSeamTransfer
      (sixVertexLexDisagreementComponentMask T omega eta h)
      omega eta = 1) :
    let first := sixVertexTorusSwitchFirst
      (sixVertexLexDisagreementComponentMask T omega eta h) omega eta
    let second := sixVertexTorusSwitchSecond
      (sixVertexLexDisagreementComponentMask T omega eta h) omega eta
    first.IceRule /\ second.IceRule /\
      sixVertexUpCount
        (svTorusVerticalRows T first (svFinLast T.height_pos)) = n /\
      sixVertexUpCount
        (svTorusVerticalRows T second (svFinLast T.height_pos)) = n := by
  dsimp only
  obtain ⟨hfirstIce, hsecondIce⟩ :=
    sixVertexLexDisagreementComponentSwitch_ice
      T omega eta homega heta h
  refine ⟨hfirstIce, hsecondIce, ?_, ?_⟩
  · have hcount := intCast_upCount_switchFirst_eq_add_seamTransfer
      (sixVertexLexDisagreementComponentMask T omega eta h) omega eta
    rw [homegaSector, htransfer] at hcount
    have hnat : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')
    rw [← hnat]
    exact_mod_cast hcount
  · have hcount := intCast_upCount_switchSecond_eq_sub_seamTransfer
      (sixVertexLexDisagreementComponentMask T omega eta h) omega eta
    rw [hetaSector, htransfer] at hcount
    have hcast : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
    rw [hcast] at hcount
    exact_mod_cast hcount

end
end StatMech.FrontierD
