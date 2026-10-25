/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part5
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


theorem zbd_rot_connected_iff (omega : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    Connected 2 (kdi_rotConfig omega) x y ↔
      Connected 2 omega (rot90Inv x) (rot90Inv y) := by
  exact (zbd_rotOpenIso omega).reachable_iff.symm

theorem zbd_rot_clusterInfinite_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (x : Site 2) :
    (cluster 2 (kdi_rotConfig omega) x).Infinite ↔
      (cluster 2 omega (rot90Inv x)).Infinite := by
  let e : Site 2 ≃ Site 2 := rot90Equiv.symm
  have himage : e '' cluster 2 (kdi_rotConfig omega) x = cluster 2 omega (e x) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (zbd_rot_connected_iff omega x y).mp hy
    · intro hz
      refine ⟨rot90Equiv z, ?_, ?_⟩
      · apply (zbd_rot_connected_iff omega x (rot90Equiv z)).mpr
        have hez : e (rot90Equiv z) = z := Equiv.symm_apply_apply rot90Equiv z
        change Connected 2 omega (e x) (e (rot90Equiv z))
        rw [hez]
        exact hz
      · exact Equiv.symm_apply_apply rot90Equiv z
  change (cluster 2 (kdi_rotConfig omega) x).Infinite ↔
    (cluster 2 omega (e x)).Infinite
  rw [← himage]
  exact (Set.infinite_image_iff e.injective.injOn).symm

theorem zbd_rotInv_sq (x : Site 2) : rot90Inv (rot90Inv x) = -x := by
  funext i
  fin_cases i <;> simp [rot90Inv]

theorem zbd_rotFun_sq (x : Site 2) : rot90Fun (rot90Fun x) = -x := by
  funext i
  fin_cases i <;> simp [rot90Fun]

theorem zbd_neg_mem_box (n : ℕ) {x : Site 2} (h : x ∈ box 2 n) : -x ∈ box 2 n := by
  rw [mem_box] at h ⊢
  intro i
  simpa using h i


theorem zbd_centered_opposite_rotation (n : ℕ) :
    zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 1 =
      zbd_sideHasInfinite (zbd_centeredRightSide n) := by
  ext omega
  change kdi_rotConfig (kdi_rotConfig omega) ∈
      zbd_sideHasInfinite (zbd_centeredLeftSide n) ↔ _
  constructor
  · rintro ⟨x, hx, hinf⟩
    refine ⟨rot90Inv (rot90Inv x), ?_, ?_⟩
    · rw [zbd_rotInv_sq]
      exact ⟨zbd_neg_mem_box n hx.1, by rw [Pi.neg_apply, hx.2]; simp⟩
    · exact (zbd_rot_clusterInfinite_iff omega (rot90Inv x)).mp
        ((zbd_rot_clusterInfinite_iff (kdi_rotConfig omega) x).mp hinf)
  · rintro ⟨y, hy, hinf⟩
    let x := rot90Fun (rot90Fun y)
    have hix : rot90Inv (rot90Inv x) = y := by
      rw [zbd_rotInv_sq]
      dsimp [x]
      rw [zbd_rotFun_sq]
      simp
    refine ⟨x, ?_, ?_⟩
    · dsimp [x]
      rw [zbd_rotFun_sq]
      exact ⟨zbd_neg_mem_box n hy.1, by rw [Pi.neg_apply, hy.2]⟩
    · apply (zbd_rot_clusterInfinite_iff (kdi_rotConfig omega) x).mpr
      apply (zbd_rot_clusterInfinite_iff omega (rot90Inv x)).mpr
      rw [hix]
      exact hinf

theorem zbd_rotInv_cube (x : Site 2) :
    rot90Inv (rot90Inv (rot90Inv x)) = rot90Fun x := by
  funext i
  fin_cases i <;> simp [rot90Inv, rot90Fun]

theorem zbd_rotFun_cube (x : Site 2) :
    rot90Fun (rot90Fun (rot90Fun x)) = rot90Inv x := by
  funext i
  fin_cases i <;> simp [rot90Inv, rot90Fun]

theorem zbd_centered_top_rotation (n : ℕ) :
    zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 2 =
      zbd_sideHasInfinite (zbd_centeredTopSide n) := by
  ext omega
  change kdi_rotConfig omega ∈ zbd_sideHasInfinite (zbd_centeredLeftSide n) ↔ _
  constructor
  · rintro ⟨x, hx, hinf⟩
    refine ⟨rot90Inv x, ?_, (zbd_rot_clusterInfinite_iff omega x).mp hinf⟩
    exact ⟨rot90Inv_mem_box n hx.1, by simp [rot90Inv, hx.2]⟩
  · rintro ⟨y, hy, hinf⟩
    refine ⟨rot90Fun y, ?_, ?_⟩
    · exact ⟨rot90Fun_mem_box n hy.1, by simp [rot90Fun, hy.2]⟩
    · apply (zbd_rot_clusterInfinite_iff omega (rot90Fun y)).mpr
      have hiy : rot90Inv (rot90Fun y) = y := Equiv.symm_apply_apply rot90Equiv y
      rw [hiy]
      exact hinf

theorem zbd_centered_bottom_rotation (n : ℕ) :
    zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 3 =
      zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
  ext omega
  change kdi_rotConfig (kdi_rotConfig (kdi_rotConfig omega)) ∈
      zbd_sideHasInfinite (zbd_centeredLeftSide n) ↔ _
  constructor
  · rintro ⟨x, hx, hinf⟩
    refine ⟨rot90Inv (rot90Inv (rot90Inv x)), ?_, ?_⟩
    · rw [zbd_rotInv_cube]
      exact ⟨rot90Fun_mem_box n hx.1, by simp [rot90Fun, hx.2]⟩
    · exact (zbd_rot_clusterInfinite_iff omega (rot90Inv (rot90Inv x))).mp
        ((zbd_rot_clusterInfinite_iff (kdi_rotConfig omega) (rot90Inv x)).mp
          ((zbd_rot_clusterInfinite_iff (kdi_rotConfig (kdi_rotConfig omega)) x).mp hinf))
  · rintro ⟨y, hy, hinf⟩
    let x := rot90Fun (rot90Fun (rot90Fun y))
    have hix : rot90Inv (rot90Inv (rot90Inv x)) = y := by
      rw [zbd_rotInv_cube]
      dsimp [x]
      rw [zbd_rotFun_cube]
      exact Equiv.symm_apply_apply rot90Equiv y
    refine ⟨x, ?_, ?_⟩
    · dsimp [x]
      rw [zbd_rotFun_cube]
      exact ⟨rot90Inv_mem_box n hy.1, by simp [rot90Inv, hy.2]⟩
    · apply (zbd_rot_clusterInfinite_iff (kdi_rotConfig (kdi_rotConfig omega)) x).mpr
      apply (zbd_rot_clusterInfinite_iff (kdi_rotConfig omega) (rot90Inv x)).mpr
      apply (zbd_rot_clusterInfinite_iff omega (rot90Inv (rot90Inv x))).mpr
      rw [hix]
      exact hinf

theorem zbd_boundaryInfinite_mem_sideUnion (n : ℕ)
    {omega : ConfigSpace (Sym2 (Site 2))} {z : Site 2}
    (hzbox : z ∈ box 2 n) (hzinf : (cluster 2 omega z).Infinite)
    (hbd : ∃ i : Fin 2, (z i).natAbs = n) :
    omega ∈ zbd_sideHasInfinite (zbd_centeredLeftSide n) ∪
      zbd_sideHasInfinite (zbd_centeredRightSide n) ∪
      zbd_sideHasInfinite (zbd_centeredTopSide n) ∪
      zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
  obtain ⟨i, hi⟩ := hbd
  have hsign := Int.natAbs_eq (z i)
  fin_cases i
  · rcases hsign with hpos | hneg
    · change (z 0).natAbs = n at hi
      change z 0 = ((z 0).natAbs : ℤ) at hpos
      exact Or.inl (Or.inl (Or.inr ⟨z, ⟨hzbox, by rw [hpos, hi]⟩, hzinf⟩))
    · change (z 0).natAbs = n at hi
      change z 0 = -((z 0).natAbs : ℤ) at hneg
      exact Or.inl (Or.inl (Or.inl ⟨z, ⟨hzbox, by rw [hneg, hi]⟩, hzinf⟩))
  · rcases hsign with hpos | hneg
    · change (z 1).natAbs = n at hi
      change z 1 = ((z 1).natAbs : ℤ) at hpos
      exact Or.inl (Or.inr ⟨z, ⟨hzbox, by rw [hpos, hi]⟩, hzinf⟩)
    · change (z 1).natAbs = n at hi
      change z 1 = -((z 1).natAbs : ℤ) at hneg
      exact Or.inr ⟨z, ⟨hzbox, by rw [hneg, hi]⟩, hzinf⟩


theorem zbd_boxHitsInfinite_subset_centeredSideUnion (n : ℕ) :
    zbd_boxHitsInfinite n ⊆
      zbd_sideHasInfinite (zbd_centeredLeftSide n) ∪
      zbd_sideHasInfinite (zbd_centeredRightSide n) ∪
      zbd_sideHasInfinite (zbd_centeredTopSide n) ∪
      zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
  intro omega
  rintro ⟨x, hxbox, hxinf⟩
  by_cases hxBoundary : ∃ i : Fin 2, (x i).natAbs = n
  · exact zbd_boundaryInfinite_mem_sideUnion n hxbox hxinf hxBoundary
  obtain ⟨y, hybox, hxy⟩ := (cluster_infinite_iff omega x).mp hxinf n
  rcases hxy with ⟨w⟩
  classical
  let P : ℕ → Prop := fun m => w.getVert m ∉ box 2 n
  have hPend : P w.length := by simpa [P] using hybox
  let j := Nat.find ⟨w.length, hPend⟩
  have hjP : w.getVert j ∉ box 2 n := Nat.find_spec ⟨w.length, hPend⟩
  have hjle : j ≤ w.length := Nat.find_le hPend
  have hj0 : j ≠ 0 := by
    intro hj
    rw [hj, w.getVert_zero] at hjP
    exact hjP hxbox
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hklt : k < w.length := by omega
  have hknotP : ¬ P k := Nat.find_min ⟨w.length, hPend⟩ (by omega)
  have hkbox : w.getVert k ∈ box 2 n := by simpa [P] using hknotP
  have hnextOutside : w.getVert (k + 1) ∉ box 2 n := by simpa [hk] using hjP
  have hadj := w.adj_getVert_succ hklt
  rw [mem_box] at hnextOutside
  push Not at hnextOutside
  obtain ⟨i, hiOutside⟩ := hnextOutside
  have hpredLe : ((w.getVert k) i).natAbs ≤ n := by
    rw [mem_box] at hkbox
    exact hkbox i
  have hdiff : (((w.getVert (k + 1)) i) - ((w.getVert k) i)).natAbs ≤ 1 := by
    have h := bxa_adj_coord_diff_le hadj.1 i
    rw [show (w.getVert (k + 1)) i - (w.getVert k) i =
      -((w.getVert k) i - (w.getVert (k + 1)) i) by ring, Int.natAbs_neg]
    exact h
  have htri : ((w.getVert (k + 1)) i).natAbs ≤
      (((w.getVert (k + 1)) i) - ((w.getVert k) i)).natAbs +
        ((w.getVert k) i).natAbs := by
    have h := Int.natAbs_add_le
      (((w.getVert (k + 1)) i) - ((w.getVert k) i)) ((w.getVert k) i)
    rw [show ((w.getVert (k + 1)) i - (w.getVert k) i) + (w.getVert k) i =
      (w.getVert (k + 1)) i by ring] at h
    exact h
  have hpredEq : ((w.getVert k) i).natAbs = n := by omega
  have hxz : Connected 2 omega x (w.getVert k) := ⟨w.take k⟩
  have hzinf : (cluster 2 omega (w.getVert k)).Infinite := by
    rw [← cluster_eq_of_connected hxz]
    exact hxinf
  exact zbd_boundaryInfinite_mem_sideUnion n hkbox hzinf ⟨i, hpredEq⟩

theorem zbd_boxHitsInfinite_tendsto_one
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto (fun n => halfMeasure.real (zbd_boxHitsInfinite n)) atTop (nhds 1) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := halfMeasure) zbd_boxHitsInfinite_mono
  rw [zbd_iUnion_boxHitsInfinite, zbd_existsInfinite_halfMeasure_one hpos] at hmeasure
  exact (ENNReal.tendsto_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).comp hmeasure


theorem zbd_centeredSide_union_tendsto
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto (fun n =>
      halfMeasure.real
        (zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 0 ∪
          zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 1 ∪
          zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 2 ∪
          zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 3))
      atTop (nhds 1) := by
  have hlower := zbd_boxHitsInfinite_tendsto_one hpos
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro n
    apply measureReal_mono (h₂ := measure_ne_top halfMeasure _)
    simpa [zbd_centered_opposite_rotation n, zbd_centered_top_rotation n,
      zbd_centered_bottom_rotation n] using
        (zbd_boxHitsInfinite_subset_centeredSideUnion n)
  · intro n
    exact measureReal_le_one

theorem zbd_natAbs_le_iff (x : ℤ) (n : ℕ) :
    x.natAbs ≤ n ↔ -(n : ℤ) ≤ x ∧ x ≤ n := by
  rw [show x.natAbs ≤ n ↔ |x| ≤ (n : ℤ) from by
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_le.symm]
  exact abs_le

theorem zbd_mem_box_iff_rect (n : ℕ) (x : Site 2) :
    x ∈ box 2 n ↔ x ∈ StatMech.RSW.Box.rect (-(n : ℤ)) n (-(n : ℤ)) n := by
  rw [mem_box, StatMech.RSW.Box.mem_rect]
  constructor
  · intro h
    have h0 : -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n := (zbd_natAbs_le_iff (x 0) n).mp (h 0)
    have h1 : -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n := (zbd_natAbs_le_iff (x 1) n).mp (h 1)
    exact ⟨h0.1, h0.2, h1.1, h1.2⟩
  · rintro ⟨h0l, h0r, h1l, h1r⟩ i
    fin_cases i
    · exact (zbd_natAbs_le_iff (x 0) n).mpr ⟨h0l, h0r⟩
    · exact (zbd_natAbs_le_iff (x 1) n).mpr ⟨h1l, h1r⟩


theorem zbd_horizontalCrossing_of_centeredSide_connection
    (n M : ℕ) (hn : 0 < n) (hnM : n ≤ M)
    {omega : ConfigSpace (Sym2 (Site 2))}
    {x y : Site 2} (hx : x ∈ zbd_centeredLeftSide n)
    (hy : y ∈ zbd_centeredRightSide n)
    (hconn : ConnectedWithin 2 omega (box 2 M)
      ⟨x, by exact box_mono 2 hnM hx.1⟩ ⟨y, by exact box_mono 2 hnM hy.1⟩) :
    StatMech.RSW.Box.HorizontalCrossing omega (-(n : ℤ)) n (-(M : ℤ)) M := by
  let S : Set (Site 2) := box 2 M
  let T1 : Set (Site 2) := {z | z ∈ S ∧ z 0 ≤ (n : ℤ)}
  have hxS : x ∈ S := box_mono 2 hnM hx.1
  have hyS : y ∈ S := box_mono 2 hnM hy.1
  obtain ⟨u, huS, hu0, huT1, hxT1, hxu⟩ :=
    bxa_connectedWithin_restrict (S := S) (T := T1) hxS hyS hconn 0 (n : ℤ)
      (by rw [hx.2]; omega) (by rw [hy.2])
      (fun z hz hzn => ⟨hz, hzn⟩)
  let T : Set (Site 2) := StatMech.RSW.Box.rect (-(n : ℤ)) n (-(M : ℤ)) M
  have hnegStep : ∀ {a b : Site 2}, (hypercubicLattice 2).Adj a b →
      ((-a 0) - (-b 0)).natAbs ≤ 1 := by
    intro a b hab
    rw [show (-a 0) - (-b 0) = -(a 0 - b 0) by ring, Int.natAbs_neg]
    exact bxa_adj_coord_diff_le hab 0
  obtain ⟨v, hvT1, hv0, hvT, huT, huv⟩ :=
    zbd_connectedWithin_restrict_fn (S := T1) (T := T) huT1 hxT1 hxu.symm
      (fun z => -z 0) (n : ℤ) hnegStep
      (by change -u 0 < (n : ℤ); rw [hu0]; omega)
      (by change (n : ℤ) ≤ -x 0; rw [hx.2]; omega)
      (fun z hz hza => by
        have hzbox : z ∈ box 2 M := hz.1
        have hzrect := (zbd_mem_box_iff_rect M z).mp hzbox
        rw [StatMech.RSW.Box.mem_rect] at hzrect ⊢
        constructor
        · change -z 0 ≤ (n : ℤ) at hza
          omega
        · exact ⟨hz.2, hzrect.2.2.1, hzrect.2.2.2⟩)
  refine ⟨⟨v, ?_⟩, ⟨u, ?_⟩, ?_⟩
  · exact ⟨hvT, by change v 0 = -(n : ℤ); omega⟩
  · exact ⟨huT, hu0⟩
  · simpa [T] using huv.symm


theorem zbd_centeredMerge_subset_horizontalCrossing
    (n M : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    zbd_twoScaleMerge (zbd_centeredLeftSide n) (zbd_centeredRightSide n) M ⊆
      StatMech.RSW.Box.horizontalCrossingEvent (-(n : ℤ)) n (-(M : ℤ)) M := by
  rintro omega ⟨x, hx, y, hy, _hxinf, _hyinf, hconn⟩
  obtain ⟨hxM, hyM, hwithin⟩ := hconn
  apply zbd_horizontalCrossing_of_centeredSide_connection n M hn hnM hx hy
  simpa using hwithin


end StatMech.TwoDim
