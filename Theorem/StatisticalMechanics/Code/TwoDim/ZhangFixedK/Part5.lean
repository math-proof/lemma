/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part5
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_rotInv_mem_leftSquare (N : ℕ) {x : Site 2}
    (hx : x ∈ zfk_leftSquare N) : rot90Inv x ∈ zfk_leftSquare N := by
  have hxB : x ∈ box 2 N := by
    exact (zbd_mem_box_iff_rect N x).mpr (by simpa [zfk_leftSquare] using hx)
  have hrB := rot90Inv_mem_box N hxB
  simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N (rot90Inv x)).mp hrB

theorem zfk_rotFun_mem_leftSquare (N : ℕ) {x : Site 2}
    (hx : x ∈ zfk_leftSquare N) : rot90Fun x ∈ zfk_leftSquare N := by
  have hxB : x ∈ box 2 N := by
    exact (zbd_mem_box_iff_rect N x).mpr (by simpa [zfk_leftSquare] using hx)
  have hrB := rot90Fun_mem_box N hxB
  simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N (rot90Fun x)).mp hrB

theorem zfk_rotInv_leftSide_mem_topSide (N : ℕ)
    (a : StatMech.RSW.Box.leftSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Inv a ∈ StatMech.RSW.Box.topSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_topSide]
  refine ⟨zfk_rotInv_mem_leftSquare N
    (StatMech.RSW.Box.leftSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Inv, ha]

theorem zfk_rotFun_topSide_mem_leftSide (N : ℕ)
    (a : StatMech.RSW.Box.topSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Fun a ∈ StatMech.RSW.Box.leftSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_leftSide]
  refine ⟨zfk_rotFun_mem_leftSquare N
    (StatMech.RSW.Box.topSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Fun, ha]

theorem zfk_rotInv_topSide_mem_rightSide (N : ℕ)
    (a : StatMech.RSW.Box.topSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Inv a ∈ StatMech.RSW.Box.rightSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_rightSide]
  refine ⟨zfk_rotInv_mem_leftSquare N
    (StatMech.RSW.Box.topSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Inv, ha]

theorem zfk_rotFun_rightSide_mem_topSide (N : ℕ)
    (a : StatMech.RSW.Box.rightSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Fun a ∈ StatMech.RSW.Box.topSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_topSide]
  refine ⟨zfk_rotFun_mem_leftSquare N
    (StatMech.RSW.Box.rightSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Fun, ha]

theorem zfk_rotInv_rightSide_mem_bottomSide (N : ℕ)
    (a : StatMech.RSW.Box.rightSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Inv a ∈ StatMech.RSW.Box.bottomSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_bottomSide]
  refine ⟨zfk_rotInv_mem_leftSquare N
    (StatMech.RSW.Box.rightSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Inv, ha]

theorem zfk_rotFun_bottomSide_mem_rightSide (N : ℕ)
    (a : StatMech.RSW.Box.bottomSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Fun a ∈ StatMech.RSW.Box.rightSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_rightSide]
  refine ⟨zfk_rotFun_mem_leftSquare N
    (StatMech.RSW.Box.bottomSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Fun, ha]

theorem zfk_rot_connectedWithin_leftSquare_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (N : ℕ)
    {x y : Site 2} (hx : x ∈ zfk_leftSquare N) (hy : y ∈ zfk_leftSquare N) :
    ConnectedWithin 2 (kdi_rotConfig omega) (zfk_leftSquare N) ⟨x, hx⟩ ⟨y, hy⟩ ↔
      ConnectedWithin 2 omega (zfk_leftSquare N)
        ⟨rot90Inv x, zfk_rotInv_mem_leftSquare N hx⟩
        ⟨rot90Inv y, zfk_rotInv_mem_leftSquare N hy⟩ := by
  have hto : zfk_leftSquare N ⊆ box 2 N := by
    intro z hz
    exact (zbd_mem_box_iff_rect N z).mpr (by simpa [zfk_leftSquare] using hz)
  have hfrom : box 2 N ⊆ zfk_leftSquare N := by
    intro z hz
    simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N z).mp hz
  constructor
  · intro h
    have hb := StatMech.RSW.Strip.connectedWithin_mono_set
      (kdi_rotConfig omega) hto h
    have hr := (zfk_rot_connectedWithin_box_iff omega N
      ⟨x, hto hx⟩ ⟨y, hto hy⟩).mp hb
    exact StatMech.RSW.Strip.connectedWithin_mono_set omega hfrom hr
  · intro h
    have hb := StatMech.RSW.Strip.connectedWithin_mono_set omega hto h
    have hr := (zfk_rot_connectedWithin_box_iff omega N
      ⟨x, hto hx⟩ ⟨y, hto hy⟩).mpr hb
    exact StatMech.RSW.Strip.connectedWithin_mono_set
      (kdi_rotConfig omega) hfrom hr

theorem zfk_rot_leftArmEvent_eq_top (k N : ℕ) :
    zrs_rot (zfk_LeftArmEvent k N) = zfk_TopArmEvent k N := by
  ext omega
  change kdi_rotConfig omega ∈ zfk_LeftArmEvent k N ↔ _
  constructor
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Inv x
    let a' : StatMech.RSW.Box.topSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Inv a, zfk_rotInv_leftSide_mem_topSide N a⟩
    refine ⟨x', rot90Inv_mem_box k hxK,
      (zbd_rot_clusterInfinite_iff omega x).mp hxInf,
      zfk_rotInv_mem_leftSquare N hxS, a', ?_⟩
    exact (zfk_rot_connectedWithin_leftSquare_iff omega N
      (StatMech.RSW.Box.leftSide_subset a.2) hxS).mp hax
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Fun x
    let a' : StatMech.RSW.Box.leftSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Fun a, zfk_rotFun_topSide_mem_leftSide N a⟩
    refine ⟨x', rot90Fun_mem_box k hxK, ?_,
      zfk_rotFun_mem_leftSquare N hxS, a', ?_⟩
    · apply (zbd_rot_clusterInfinite_iff omega x').mpr
      have hix : rot90Inv x' = x := by
        exact Equiv.symm_apply_apply rot90Equiv x
      rwa [hix]
    · apply (zfk_rot_connectedWithin_leftSquare_iff omega N
        (StatMech.RSW.Box.leftSide_subset a'.2)
        (zfk_rotFun_mem_leftSquare N hxS)).mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      have hia : rot90Inv (a' : Site 2) = (a : Site 2) :=
        Equiv.symm_apply_apply rot90Equiv a
      convert hax using 1 <;> apply Subtype.ext
      · exact hia
      · exact hix

theorem zfk_rot_topArmEvent_eq_right (k N : ℕ) :
    zrs_rot (zfk_TopArmEvent k N) = zfk_CenteredRightArmEvent k N := by
  ext omega
  change kdi_rotConfig omega ∈ zfk_TopArmEvent k N ↔ _
  constructor
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Inv x
    let a' : StatMech.RSW.Box.rightSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Inv a, zfk_rotInv_topSide_mem_rightSide N a⟩
    refine ⟨x', rot90Inv_mem_box k hxK,
      (zbd_rot_clusterInfinite_iff omega x).mp hxInf,
      zfk_rotInv_mem_leftSquare N hxS, a', ?_⟩
    exact (zfk_rot_connectedWithin_leftSquare_iff omega N
      (StatMech.RSW.Box.topSide_subset a.2) hxS).mp hax
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Fun x
    let a' : StatMech.RSW.Box.topSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Fun a, zfk_rotFun_rightSide_mem_topSide N a⟩
    refine ⟨x', rot90Fun_mem_box k hxK, ?_,
      zfk_rotFun_mem_leftSquare N hxS, a', ?_⟩
    · apply (zbd_rot_clusterInfinite_iff omega x').mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      rwa [hix]
    · apply (zfk_rot_connectedWithin_leftSquare_iff omega N
        (StatMech.RSW.Box.topSide_subset a'.2)
        (zfk_rotFun_mem_leftSquare N hxS)).mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      have hia : rot90Inv (a' : Site 2) = (a : Site 2) :=
        Equiv.symm_apply_apply rot90Equiv a
      convert hax using 1 <;> apply Subtype.ext
      · exact hia
      · exact hix

theorem zfk_rot_rightArmEvent_eq_bottom (k N : ℕ) :
    zrs_rot (zfk_CenteredRightArmEvent k N) = zfk_BottomArmEvent k N := by
  ext omega
  change kdi_rotConfig omega ∈ zfk_CenteredRightArmEvent k N ↔ _
  constructor
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Inv x
    let a' : StatMech.RSW.Box.bottomSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Inv a, zfk_rotInv_rightSide_mem_bottomSide N a⟩
    refine ⟨x', rot90Inv_mem_box k hxK,
      (zbd_rot_clusterInfinite_iff omega x).mp hxInf,
      zfk_rotInv_mem_leftSquare N hxS, a', ?_⟩
    exact (zfk_rot_connectedWithin_leftSquare_iff omega N
      (StatMech.RSW.Box.rightSide_subset a.2) hxS).mp hax
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Fun x
    let a' : StatMech.RSW.Box.rightSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Fun a, zfk_rotFun_bottomSide_mem_rightSide N a⟩
    refine ⟨x', rot90Fun_mem_box k hxK, ?_,
      zfk_rotFun_mem_leftSquare N hxS, a', ?_⟩
    · apply (zbd_rot_clusterInfinite_iff omega x').mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      rwa [hix]
    · apply (zfk_rot_connectedWithin_leftSquare_iff omega N
        (StatMech.RSW.Box.rightSide_subset a'.2)
        (zfk_rotFun_mem_leftSquare N hxS)).mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      have hia : rot90Inv (a' : Site 2) = (a : Site 2) :=
        Equiv.symm_apply_apply rot90Equiv a
      convert hax using 1 <;> apply Subtype.ext
      · exact hia
      · exact hix


theorem zfk_boxHitsInfinite_subset_armUnion (k N : ℕ) (hkN : k ≤ N) :
    zbd_boxHitsInfinite k ⊆
      zrs_sideFamily (zfk_LeftArmEvent k N) 0 ∪
        zrs_sideFamily (zfk_LeftArmEvent k N) 1 ∪
        zrs_sideFamily (zfk_LeftArmEvent k N) 2 ∪
        zrs_sideFamily (zfk_LeftArmEvent k N) 3 := by
  intro omega
  rintro ⟨x, hxK, hxInf⟩
  obtain ⟨y, hyOutside, hxy⟩ := (cluster_infinite_iff omega x).mp hxInf N
  rcases hxy with ⟨w⟩
  classical
  let P : ℕ → Prop := fun m => w.getVert m ∉ box 2 N
  have hPend : P w.length := by simpa [P] using hyOutside
  let j := Nat.find ⟨w.length, hPend⟩
  have hjP : w.getVert j ∉ box 2 N := Nat.find_spec ⟨w.length, hPend⟩
  have hjle : j ≤ w.length := Nat.find_le hPend
  have hxN : x ∈ box 2 N := box_mono 2 hkN hxK
  have hj0 : j ≠ 0 := by
    intro hj
    rw [hj, w.getVert_zero] at hjP
    exact hjP hxN
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hmlt : m < w.length := by omega
  have hmnotP : ¬ P m := Nat.find_min ⟨w.length, hPend⟩ (by omega)
  have hmBox : w.getVert m ∈ box 2 N := by simpa [P] using hmnotP
  have hmRect : w.getVert m ∈ zfk_leftSquare N := by
    simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N (w.getVert m)).mp hmBox
  have hprefixSupp : ∀ z ∈ (w.take m).support, z ∈ box 2 N := by
    intro z hz
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
    obtain ⟨r, hrlt, hrz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hrlt
    have hrle : r ≤ m := by omega
    have hrw : z = w.getVert r := by
      have hrlen : r ≤ w.length := by omega
      rw [List.getElem_take] at hrz
      rw [← hrz, ← SimpleGraph.Walk.getVert_eq_support_getElem w hrlen]
    rw [hrw]
    by_contra hrout
    have : P r := by simpa [P] using hrout
    exact (Nat.find_min ⟨w.length, hPend⟩ (by omega)) this
  have hxm : ConnectedWithin 2 omega (box 2 N)
      ⟨x, hxN⟩ ⟨w.getVert m, hmBox⟩ :=
    ⟨(w.take m).induce (box 2 N) hprefixSupp⟩
  have hxmRect : ConnectedWithin 2 omega (zfk_leftSquare N)
      ⟨x, by simpa [zfk_leftSquare] using
        (zbd_mem_box_iff_rect N x).mp hxN⟩ ⟨w.getVert m, hmRect⟩ := by
    have hsub : box 2 N ⊆ zfk_leftSquare N := by
      intro z hz
      simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N z).mp hz
    exact StatMech.RSW.Strip.connectedWithin_mono_set omega hsub hxm
  have hnextOutside : w.getVert (m + 1) ∉ box 2 N := by
    simpa [hm] using hjP
  have hadj := w.adj_getVert_succ hmlt
  rw [mem_box] at hnextOutside
  push Not at hnextOutside
  obtain ⟨i, hiOutside⟩ := hnextOutside
  have hmLe : ((w.getVert m) i).natAbs ≤ N := by
    rw [mem_box] at hmBox
    exact hmBox i
  have hdiff : (((w.getVert (m + 1)) i) - ((w.getVert m) i)).natAbs ≤ 1 := by
    have h := bxa_adj_coord_diff_le hadj.1 i
    rw [show (w.getVert (m + 1)) i - (w.getVert m) i =
      -((w.getVert m) i - (w.getVert (m + 1)) i) by ring, Int.natAbs_neg]
    exact h
  have htri : ((w.getVert (m + 1)) i).natAbs ≤
      (((w.getVert (m + 1)) i) - ((w.getVert m) i)).natAbs +
        ((w.getVert m) i).natAbs := by
    have h := Int.natAbs_add_le
      (((w.getVert (m + 1)) i) - ((w.getVert m) i)) ((w.getVert m) i)
    rw [show ((w.getVert (m + 1)) i - (w.getVert m) i) + (w.getVert m) i =
      (w.getVert (m + 1)) i by ring] at h
    exact h
  have hmEq : ((w.getVert m) i).natAbs = N := by omega
  change omega ∈ zfk_LeftArmEvent k N ∪
    zrs_rot (zrs_rot (zfk_LeftArmEvent k N)) ∪
    zrs_rot (zfk_LeftArmEvent k N) ∪
    zrs_rot (zrs_rot (zrs_rot (zfk_LeftArmEvent k N)))
  rw [zfk_rot_leftArmEvent_eq_top, zfk_rot_topArmEvent_eq_right,
    zfk_rot_rightArmEvent_eq_bottom]
  have hsign := Int.natAbs_eq ((w.getVert m) i)
  fin_cases i
  · rcases hsign with hpos | hneg
    · change (w.getVert m 0).natAbs = N at hmEq
      change w.getVert m 0 = ((w.getVert m 0).natAbs : ℤ) at hpos
      exact Or.inl (Or.inl (Or.inr ⟨x, hxK, hxInf,
        by simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N x).mp hxN,
        ⟨w.getVert m, hmRect, by rw [hpos, hmEq]⟩, hxmRect.symm⟩))
    · change (w.getVert m 0).natAbs = N at hmEq
      change w.getVert m 0 = -((w.getVert m 0).natAbs : ℤ) at hneg
      exact Or.inl (Or.inl (Or.inl ⟨x, hxK, hxInf,
        by simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N x).mp hxN,
        ⟨w.getVert m, hmRect, by rw [hneg, hmEq]⟩, hxmRect.symm⟩))
  · rcases hsign with hpos | hneg
    · change (w.getVert m 1).natAbs = N at hmEq
      change w.getVert m 1 = ((w.getVert m 1).natAbs : ℤ) at hpos
      exact Or.inl (Or.inr ⟨x, hxK, hxInf,
        by simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N x).mp hxN,
        ⟨w.getVert m, hmRect, by rw [hpos, hmEq]⟩, hxmRect.symm⟩)
    · change (w.getVert m 1).natAbs = N at hmEq
      change w.getVert m 1 = -((w.getVert m 1).natAbs : ℤ) at hneg
      exact Or.inr ⟨x, hxK, hxInf,
        by simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N x).mp hxN,
        ⟨w.getVert m, hmRect, by rw [hneg, hmEq]⟩, hxmRect.symm⟩

theorem zfk_armPair_eq_inter (k N : ℕ) :
    zfk_ArmPairEvent k N = zfk_LeftArmEvent k N ∩ zfk_RightArmEvent k N := by
  ext omega
  constructor
  · rintro ⟨x, hx, y, hy, hxInf, hyInf, hxArm, hyArm⟩
    exact ⟨⟨x, hx, hxInf, hxArm⟩, ⟨y, hy, hyInf, hyArm⟩⟩
  · rintro ⟨⟨x, hx, hxInf, hxArm⟩, ⟨y, hy, hyInf, hyArm⟩⟩
    exact ⟨x, hx, y, hy, hxInf, hyInf, hxArm, hyArm⟩

theorem zfk_LeftArmEvent_isIncreasing (k N : ℕ) :
    IsIncreasing (zfk_LeftArmEvent k N) := by
  intro omega omega' hle
  rintro ⟨x, hx, hxInf, hxS, a, hax⟩
  refine ⟨x, hx, hxInf.mono (cluster_mono hle x), hxS, a, ?_⟩
  exact StatMech.TwoDim.connectedWithin_mono hle hax

theorem zfk_RightArmEvent_isIncreasing (k N : ℕ) :
    IsIncreasing (zfk_RightArmEvent k N) := by
  intro omega omega' hle
  rintro ⟨y, hy, hyInf, hyS, b, hyb⟩
  refine ⟨y, hy, hyInf.mono (cluster_mono hle y), hyS, b, ?_⟩
  exact StatMech.TwoDim.connectedWithin_mono hle hyb

theorem zfk_LeftArmEvent_measurableSet (k N : ℕ) :
    MeasurableSet (zfk_LeftArmEvent k N) := by
  have heq : zfk_LeftArmEvent k N =
      ⋃ x : Site 2, ⋃ (_hx : x ∈ box 2 k),
        {omega | (cluster 2 omega x).Infinite} ∩
          ⋃ (hxS : x ∈ zfk_leftSquare N),
            ⋃ a : StatMech.RSW.Box.leftSide
              (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ),
              {omega | ConnectedWithin 2 omega (zfk_leftSquare N)
                ⟨(a : Site 2), StatMech.RSW.Box.leftSide_subset a.2⟩ ⟨x, hxS⟩} := by
    ext omega
    constructor
    · rintro ⟨x, hx, hxInf, hxS, a, hax⟩
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
        ⟨hxInf, Set.mem_iUnion.mpr ⟨hxS, Set.mem_iUnion.mpr ⟨a, hax⟩⟩⟩⟩⟩
    · intro h
      obtain ⟨x, hxrest⟩ := Set.mem_iUnion.mp h
      obtain ⟨hx, hxrest⟩ := Set.mem_iUnion.mp hxrest
      obtain ⟨hxInf, hxrest⟩ := hxrest
      obtain ⟨hxS, hxrest⟩ := Set.mem_iUnion.mp hxrest
      obtain ⟨a, hax⟩ := Set.mem_iUnion.mp hxrest
      exact ⟨x, hx, hxInf, hxS, a, hax⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  apply (measurableSet_clusterInfinite x).inter
  apply MeasurableSet.iUnion
  intro hxS
  apply MeasurableSet.iUnion
  intro a
  exact zbd_measurableSet_connectedWithin (zfk_leftSquare N)
    ⟨(a : Site 2), StatMech.RSW.Box.leftSide_subset a.2⟩ ⟨x, hxS⟩

theorem zfk_RightArmEvent_measurableSet (k N : ℕ) :
    MeasurableSet (zfk_RightArmEvent k N) := by
  have heq : zfk_RightArmEvent k N =
      ⋃ y : Site 2, ⋃ (_hy : y ∈ zfk_rightCentralBox k),
        {omega | (cluster 2 omega y).Infinite} ∩
          ⋃ (hyS : y ∈ zfk_rightSquare N),
            ⋃ b : StatMech.RSW.Box.rightSide
              (-(N : ℤ) + 1) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ),
              {omega | ConnectedWithin 2 omega (zfk_rightSquare N)
                ⟨y, hyS⟩
                ⟨(b : Site 2), StatMech.RSW.Box.rightSide_subset b.2⟩} := by
    ext omega
    constructor
    · rintro ⟨y, hy, hyInf, hyS, b, hyb⟩
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy,
        ⟨hyInf, Set.mem_iUnion.mpr ⟨hyS, Set.mem_iUnion.mpr ⟨b, hyb⟩⟩⟩⟩⟩
    · intro h
      obtain ⟨y, hyrest⟩ := Set.mem_iUnion.mp h
      obtain ⟨hy, hyrest⟩ := Set.mem_iUnion.mp hyrest
      obtain ⟨hyInf, hyrest⟩ := hyrest
      obtain ⟨hyS, hyrest⟩ := Set.mem_iUnion.mp hyrest
      obtain ⟨b, hyb⟩ := Set.mem_iUnion.mp hyrest
      exact ⟨y, hy, hyInf, hyS, b, hyb⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro y
  apply MeasurableSet.iUnion
  intro hy
  apply (measurableSet_clusterInfinite y).inter
  apply MeasurableSet.iUnion
  intro hyS
  apply MeasurableSet.iUnion
  intro b
  exact zbd_measurableSet_connectedWithin (zfk_rightSquare N) ⟨y, hyS⟩
    ⟨(b : Site 2), StatMech.RSW.Box.rightSide_subset b.2⟩


end StatMech.TwoDim
