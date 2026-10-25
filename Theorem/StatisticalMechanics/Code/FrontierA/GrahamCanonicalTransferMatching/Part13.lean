/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part13
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem mem_canonicalTransferUnion_iff_row_componentComplements
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p)
    {e : I} (hem : e ∈ m) {u : W} (hu : u ∈ ends e) :
    e ∈ canonicalTransferUnion ends m k zero c.1.1 ↔
      ((e ∈ rowClass m c.1.1 0 ∧
          u ∉ StatMech.FrontierA.grahamComponentComplement
            ends (rowClass m c.1.1 0) zero) ∨
        (e ∉ rowClass m c.1.1 0 ∧
          u ∉ StatMech.FrontierA.grahamComponentComplement
            ends (m \ rowClass m c.1.1 0) k)) := by
  rw [mem_canonicalTransferUnion_iff_rooted_endpoints]
  constructor
  · rintro (⟨he0, hall⟩ | ⟨he1, hall⟩)
    · left
      refine ⟨he0, ?_⟩
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
      exact not_not.mpr (hall u hu)
    · right
      have he1' : e ∈ m \ rowClass m c.1.1 0 := by
        simpa only [rowClass_one_eq_sdiff] using he1
      have he1mem := Finset.mem_sdiff.mp he1'
      refine ⟨he1mem.2, ?_⟩
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
      have hconn := hall u hu
      exact not_not.mpr (by
        simpa only [rowClass_one_eq_sdiff] using hconn)
  · rintro (⟨he0, hu0⟩ | ⟨he0, hu1⟩)
    · left
      refine ⟨he0, ?_⟩
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK] at hu0
      have hzu : StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m c.1.1 0) zero u := not_not.mp hu0
      intro v hv
      by_cases huv : u = v
      · simpa [huv] using hzu
      · exact hzu.tail ⟨e, he0, hu, hv, huv⟩
    · right
      have he1 : e ∈ m \ rowClass m c.1.1 0 :=
        Finset.mem_sdiff.mpr ⟨hem, he0⟩
      refine ⟨?_, ?_⟩
      · rwa [rowClass_one_eq_sdiff]
      · rw [StatMech.FrontierA.grahamComponentComplement,
          StatMech.Sharpness.RandomCurrent.mem_notConnCompK] at hu1
        have hku : StatMech.Sharpness.RandomCurrent.connK
            ends (m \ rowClass m c.1.1 0) k u := not_not.mp hu1
        intro v hv
        rw [rowClass_one_eq_sdiff]
        by_cases huv : u = v
        · simpa [huv] using hku
        · exact hku.tail ⟨e, he1, hu, hv, huv⟩

theorem mem_iff_mem_of_noCrossingK
    {ends : I -> Sym2 W} {K : Finset I} {S : Finset W}
    (hno : StatMech.Sharpness.RandomCurrent.NoCrossingK ends K S)
    {e : I} (he : e ∈ K) {u v : W}
    (hu : u ∈ ends e) (hv : v ∈ ends e) :
    u ∈ S ↔ v ∈ S := by
  rcases hno e he with hin | hout
  · exact iff_of_true (hin u hu) (hin v hv)
  · exact iff_of_false
      (fun huS => (Finset.mem_compl.mp (hout u hu)) huS)
      (fun hvS => (Finset.mem_compl.mp (hout v hv)) hvS)

theorem noCrossingK_of_endpoint_membership_iff
    {ends : I -> Sym2 W} {K : Finset I} {S : Finset W}
    (hsame : ∀ e ∈ K, ∀ u ∈ ends e, ∀ v ∈ ends e,
      (u ∈ S ↔ v ∈ S)) :
    StatMech.Sharpness.RandomCurrent.NoCrossingK ends K S := by
  intro e he
  let u := (ends e).out.1
  have hu : u ∈ ends e := Sym2.out_fst_mem (ends e)
  by_cases huS : u ∈ S
  · left
    intro v hv
    exact (hsame e he u hu v hv).mp huS
  · right
    intro v hv
    rw [Finset.mem_compl]
    exact fun hvS => huS ((hsame e he u hu v hv).mpr hvS)

set_option maxHeartbeats 1000000 in
theorem canonicalNormalCuts_boolean
    (er ec tr tc aru arv bru brv acu acv bcu bcv : Prop)
    (hAr : er -> (aru ↔ arv)) (hBr : ¬ er -> (bru ↔ brv))
    (hAc : ec -> (acu ↔ acv)) (hBc : ¬ ec -> (bcu ↔ bcv))
    (hTru : tr ↔ (er ∧ ¬ aru) ∨ (¬ er ∧ ¬ bru))
    (hTrv : tr ↔ (er ∧ ¬ arv) ∨ (¬ er ∧ ¬ brv))
    (hTcu : tc ↔ (ec ∧ ¬ acu) ∨ (¬ ec ∧ ¬ bcu))
    (hTcv : tc ↔ (ec ∧ ¬ acv) ∨ (¬ ec ∧ ¬ bcv))
    (hnormal : ((er ∧ ¬ tr) ∨ (tr ∧ ¬ er)) ↔
      ((ec ∧ ¬ tc) ∨ (tc ∧ ¬ ec))) :
    ((((ec ∧ ¬ tr) ∨ (tr ∧ ¬ ec)) ->
        (((¬ aru ∧ bcu) ∨ (¬ acu ∧ bru)) ↔
          ((¬ arv ∧ bcv) ∨ (¬ acv ∧ brv)))) ∧
      (¬ ((ec ∧ ¬ tr) ∨ (tr ∧ ¬ ec)) ->
        (((¬ aru ∧ ¬ acu) ∨ (bru ∧ bcu)) ↔
          ((¬ arv ∧ ¬ acv) ∨ (brv ∧ bcv))))) := by
  by_cases her : er <;> by_cases hec : ec <;>
    by_cases htr : tr <;> by_cases htc : tc <;>
    simp only [her, hec, htr, htc, true_and, false_and, and_true, and_false,
      not_true_eq_false, not_false_eq_true, false_or, true_or] at * <;>
    tauto


theorem canonicalMaskNormalFiberComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I) :
    CanonicalMaskNormalFiberComplete ends m j k l zero p := by
  intro r c hnormal
  rw [canonicalTransferWorks_iff_translatedRowDisconnects
    hloop hjk hkl r c]
  let R := rowClass m r.1.1 0
  let C := rowClass m c.1.1 0
  let Tr := canonicalTransferUnion ends m k zero r.1.1
  let Tc := canonicalTransferUnion ends m k zero c.1.1
  let K := C ∆ Tr
  let Ar := StatMech.FrontierA.grahamComponentComplement ends R zero
  let Br := StatMech.FrontierA.grahamComponentComplement ends (m \ R) k
  let Ac := StatMech.FrontierA.grahamComponentComplement ends C zero
  let Bc := StatMech.FrontierA.grahamComponentComplement ends (m \ C) k
  let Srow := (Arᶜ ∩ Bc) ∪ (Acᶜ ∩ Br)
  let Scomp := (Arᶜ ∩ Acᶜ) ∪ (Br ∩ Bc)
  have hrGate : RowsDisconnect ends m r.1.1 k zero :=
    r.1.2.2.2.2.2
  have hcGate : RowsDisconnect ends m c.1.1 k zero :=
    c.1.2.2.2.2.2
  have hzeroAr : zero ∉ Ar :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends R zero
  have hkAr : k ∈ Ar := by
    dsimp only [Ar]
    rw [StatMech.FrontierA.grahamComponentComplement,
      StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
    intro h
    exact hrGate.1
      (StatMech.Sharpness.RandomCurrent.connK_symm ends R h)
  have hkBr : k ∉ Br :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends (m \ R) k
  have hzeroBr : zero ∈ Br := by
    dsimp only [Br]
    rw [StatMech.FrontierA.grahamComponentComplement,
      StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
    simpa only [R, rowClass_one_eq_sdiff] using hrGate.2
  have hzeroAc : zero ∉ Ac :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends C zero
  have hkAc : k ∈ Ac := by
    dsimp only [Ac]
    rw [StatMech.FrontierA.grahamComponentComplement,
      StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
    intro h
    exact hcGate.1
      (StatMech.Sharpness.RandomCurrent.connK_symm ends C h)
  have hkBc : k ∉ Bc :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends (m \ C) k
  have hzeroBc : zero ∈ Bc := by
    dsimp only [Bc]
    rw [StatMech.FrontierA.grahamComponentComplement,
      StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
    simpa only [C, rowClass_one_eq_sdiff] using hcGate.2
  have hzeroSrow : zero ∈ Srow := by
    simp only [Srow, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, hzeroAr, hzeroBc, not_false_eq_true,
      true_and, true_or]
  have hkSrow : k ∉ Srow := by
    simp only [Srow, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, hkAr, hkAc, hkBr, hkBc,
      not_true_eq_false, false_and, and_false, false_or, not_false_eq_true]
  have hzeroScomp : zero ∈ Scomp := by
    simp only [Scomp, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, hzeroAr, hzeroAc, not_false_eq_true,
      true_and, true_or]
  have hkScomp : k ∉ Scomp := by
    simp only [Scomp, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, hkAr, hkAc, hkBr, hkBc,
      not_true_eq_false, false_and, and_false, false_or, not_false_eq_true]
  have hKm : K ⊆ m := by
    simpa only [K, C, Tr] using
      canonicalTranslatedRow_subset_m hloop hjk hkl r c
  have hnormal' : R ∆ Tr = C ∆ Tc := by
    simpa only [R, C, Tr, Tc, canonicalNormalRow] using hnormal
  have hNoRow :
      StatMech.Sharpness.RandomCurrent.NoCrossingK ends K Srow := by
    apply noCrossingK_of_endpoint_membership_iff
    intro e heK u hu v hv
    have hem : e ∈ m := hKm heK
    have hAr : e ∈ R -> (u ∈ Ar ↔ v ∈ Ar) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends R zero) he hu hv
    have hBr : e ∉ R -> (u ∈ Br ↔ v ∈ Br) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends (m \ R) k) (Finset.mem_sdiff.mpr ⟨hem, he⟩) hu hv
    have hAc : e ∈ C -> (u ∈ Ac ↔ v ∈ Ac) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends C zero) he hu hv
    have hBc : e ∉ C -> (u ∈ Bc ↔ v ∈ Bc) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends (m \ C) k) (Finset.mem_sdiff.mpr ⟨hem, he⟩) hu hv
    have hTru :=
      mem_canonicalTransferUnion_iff_row_componentComplements r hem hu
    have hTrv :=
      mem_canonicalTransferUnion_iff_row_componentComplements r hem hv
    have hTcu :=
      mem_canonicalTransferUnion_iff_row_componentComplements c hem hu
    have hTcv :=
      mem_canonicalTransferUnion_iff_row_componentComplements c hem hv
    change e ∈ Tr ↔
      ((e ∈ R ∧ u ∉ Ar) ∨ (e ∉ R ∧ u ∉ Br)) at hTru
    change e ∈ Tr ↔
      ((e ∈ R ∧ v ∉ Ar) ∨ (e ∉ R ∧ v ∉ Br)) at hTrv
    change e ∈ Tc ↔
      ((e ∈ C ∧ u ∉ Ac) ∨ (e ∉ C ∧ u ∉ Bc)) at hTcu
    change e ∈ Tc ↔
      ((e ∈ C ∧ v ∉ Ac) ∨ (e ∉ C ∧ v ∉ Bc)) at hTcv
    have hn : e ∈ R ∆ Tr ↔ e ∈ C ∆ Tc := by rw [hnormal']
    simp only [Finset.mem_symmDiff] at hn
    change e ∈ C ∆ Tr at heK
    simp only [Finset.mem_symmDiff] at heK
    simp only [Srow, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl]
    exact (canonicalNormalCuts_boolean
      (e ∈ R) (e ∈ C) (e ∈ Tr) (e ∈ Tc)
      (u ∈ Ar) (v ∈ Ar) (u ∈ Br) (v ∈ Br)
      (u ∈ Ac) (v ∈ Ac) (u ∈ Bc) (v ∈ Bc)
      hAr hBr hAc hBc hTru hTrv hTcu hTcv hn).1 heK
  have hNoComp :
      StatMech.Sharpness.RandomCurrent.NoCrossingK ends (m \ K) Scomp := by
    apply noCrossingK_of_endpoint_membership_iff
    intro e heComp u hu v hv
    have heComp' := Finset.mem_sdiff.mp heComp
    have hem : e ∈ m := heComp'.1
    have heNotK : e ∉ K := heComp'.2
    have hAr : e ∈ R -> (u ∈ Ar ↔ v ∈ Ar) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends R zero) he hu hv
    have hBr : e ∉ R -> (u ∈ Br ↔ v ∈ Br) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends (m \ R) k) (Finset.mem_sdiff.mpr ⟨hem, he⟩) hu hv
    have hAc : e ∈ C -> (u ∈ Ac ↔ v ∈ Ac) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends C zero) he hu hv
    have hBc : e ∉ C -> (u ∈ Bc ↔ v ∈ Bc) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends (m \ C) k) (Finset.mem_sdiff.mpr ⟨hem, he⟩) hu hv
    have hTru :=
      mem_canonicalTransferUnion_iff_row_componentComplements r hem hu
    have hTrv :=
      mem_canonicalTransferUnion_iff_row_componentComplements r hem hv
    have hTcu :=
      mem_canonicalTransferUnion_iff_row_componentComplements c hem hu
    have hTcv :=
      mem_canonicalTransferUnion_iff_row_componentComplements c hem hv
    change e ∈ Tr ↔
      ((e ∈ R ∧ u ∉ Ar) ∨ (e ∉ R ∧ u ∉ Br)) at hTru
    change e ∈ Tr ↔
      ((e ∈ R ∧ v ∉ Ar) ∨ (e ∉ R ∧ v ∉ Br)) at hTrv
    change e ∈ Tc ↔
      ((e ∈ C ∧ u ∉ Ac) ∨ (e ∉ C ∧ u ∉ Bc)) at hTcu
    change e ∈ Tc ↔
      ((e ∈ C ∧ v ∉ Ac) ∨ (e ∉ C ∧ v ∉ Bc)) at hTcv
    have hn : e ∈ R ∆ Tr ↔ e ∈ C ∆ Tc := by rw [hnormal']
    simp only [Finset.mem_symmDiff] at hn
    change e ∉ C ∆ Tr at heNotK
    simp only [Finset.mem_symmDiff] at heNotK
    simp only [Scomp, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl]
    exact (canonicalNormalCuts_boolean
      (e ∈ R) (e ∈ C) (e ∈ Tr) (e ∈ Tc)
      (u ∈ Ar) (v ∈ Ar) (u ∈ Br) (v ∈ Br)
      (u ∈ Ac) (v ∈ Ac) (u ∈ Bc) (v ∈ Bc)
      hAr hBr hAc hBc hTru hTrv hTcu hTcv hn).2 heNotK
  change RowSupportDisconnects ends m K k zero
  exact ⟨fun hconn => hkSrow
      (connK_mem_of_noCrossing hNoRow hzeroSrow
        (StatMech.Sharpness.RandomCurrent.connK_symm ends K hconn)),
    fun hconn => hkScomp
      (connK_mem_of_noCrossing hNoComp hzeroScomp
        (StatMech.Sharpness.RandomCurrent.connK_symm ends (m \ K) hconn))⟩


theorem canonicalNormalRows_ne_of_not_canonicalTransferWorks
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    canonicalNormalRow ends m k zero r.1.1 ≠
      canonicalNormalRow ends m k zero c.1.1 := by
  intro hnormal
  exact hbad (canonicalMaskNormalFiberComplete
    ends m j k l zero hloop hjk hkl p r c hnormal)


theorem canonicalNormalRows_ne_of_rootComponentCut
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hcut : CanonicalTranslatedRowRootComponentCut
      ends m k zero r.1.1 c.1.1) :
    canonicalNormalRow ends m k zero r.1.1 ≠
      canonicalNormalRow ends m k zero c.1.1 := by
  apply canonicalNormalRows_ne_of_not_canonicalTransferWorks
    hloop hjk hkl r c
  intro hworks
  have hdisc := (canonicalTransferWorks_iff_translatedRowDisconnects
    hloop hjk hkl r c).mp hworks
  rcases hcut with hcut | hcut
  · exact hdisc.1 hcut.1
  · exact hdisc.2 hcut.1


theorem card_le_canonicalMaskRightNeighborhood_of_normalFiber
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (hnormal : ∀ c ∈ S,
      canonicalNormalRow ends m k zero r.1.1 =
        canonicalNormalRow ends m k zero c.1.1) :
    S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
  apply card_le_canonicalMaskRightNeighborhood_of_reference
    ends m j k l zero hloop hjk hkl p S r
  intro c hcS
  exact canonicalMaskNormalFiberComplete
    ends m j k l zero hloop hjk hkl p r c (hnormal c hcS)


end StatMech.GrahamGHS.FourColor
