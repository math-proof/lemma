/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part12
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_sixVertexBetheInteriorSet {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) (i : Fin (n + 1)) :
    i ∈ sixVertexBetheInteriorSet N x q ↔
      q i ≠ sixVertexBetheShiftCoordinates N x i ∧ q i ≠ x i := by
  simp [sixVertexBetheInteriorSet]

theorem sixVertexBetheIntervalTupleWeight_eq_interior
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x q : Fin (n + 1) -> Int) :
    sixVertexBetheIntervalTupleWeight N c z x q =
      ((c : Complex) ^ 2) ^ (sixVertexBetheInteriorSet N x q).card *
        ∏ i, z i ^ q i := by
  unfold sixVertexBetheIntervalTupleWeight
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2
  ext i
  simp [sixVertexBetheInteriorSet]

theorem sixVertexSector_mem_iff_exists_position
    {N m : Nat} (x : SixVertexSector N m) (v : Fin N) :
    v ∈ (x : Finset (Fin N)) ↔ ∃ i, sixVertexSectorPosition x i = v := by
  constructor
  · intro hv
    have hrange : v ∈ Set.range (sixVertexSectorPosition x) := by
      unfold sixVertexSectorPosition
      rw [Finset.range_orderEmbOfFin (x : Finset (Fin N)) x.prop]
      exact hv
    exact hrange
  · rintro ⟨i, rfl⟩
    exact sixVertexSectorPosition_mem x i

theorem sixVertexForward_endpoint_iff_mem
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x))
    (i : Fin (n + 1)) :
    (sixVertexSectorIntCoordinates y i =
        sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i \/
      sixVertexSectorIntCoordinates y i = sixVertexSectorIntCoordinates x i) ↔
      sixVertexSectorPosition y i ∈ (x : Finset (Fin N)) := by
  have hpos := (sixVertexForwardInterlaced_iff_positions y x).mp hyx
  constructor
  · intro hend
    induction i using Fin.cases with
    | zero =>
        rcases hend with hlo | hhi
        · have hyzero : 0 ≤ sixVertexSectorIntCoordinates y 0 := by
            simp [sixVertexSectorIntCoordinates]
          have hxlast : sixVertexSectorIntCoordinates x (Fin.last n) < N := by
            unfold sixVertexSectorIntCoordinates
            exact_mod_cast (sixVertexSectorPosition x (Fin.last n)).prop
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at hlo
          omega
        · rw [sixVertexSector_mem_iff_exists_position]
          refine ⟨0, ?_⟩
          apply Fin.ext
          unfold sixVertexSectorIntCoordinates at hhi
          exact_mod_cast hhi.symm
    | succ k =>
        rw [sixVertexSector_mem_iff_exists_position]
        rcases hend with hlo | hhi
        · refine ⟨k.castSucc, ?_⟩
          apply Fin.ext
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ] at hlo
          unfold sixVertexSectorIntCoordinates at hlo
          exact_mod_cast hlo.symm
        · refine ⟨k.succ, ?_⟩
          apply Fin.ext
          unfold sixVertexSectorIntCoordinates at hhi
          exact_mod_cast hhi.symm
  · intro hmem
    obtain ⟨j, hj⟩ := (sixVertexSector_mem_iff_exists_position x _).mp hmem
    induction i using Fin.cases with
    | zero =>
        have hy_le_x : sixVertexSectorPosition y 0 ≤
            sixVertexSectorPosition x 0 := hpos.1 0
        have hjzero : j = 0 := by
          by_contra hne
          have hjpos : (0 : Fin (n + 1)) < j := by
            exact Fin.pos_iff_ne_zero.mpr hne
          have hxlt := (sixVertexSectorPosition x).strictMono hjpos
          rw [hj] at hxlt
          exact (not_lt_of_ge hy_le_x) hxlt
        right
        unfold sixVertexSectorIntCoordinates
        rw [hjzero] at hj
        exact_mod_cast congrArg Fin.val hj.symm
    | succ k =>
        have hlo : sixVertexSectorPosition x k.castSucc ≤
            sixVertexSectorPosition y k.succ := by
          exact hpos.2 k.val (by omega)
        have hhi : sixVertexSectorPosition y k.succ ≤
            sixVertexSectorPosition x k.succ := hpos.1 k.succ
        have hjlo : k.castSucc ≤ j := by
          by_contra h
          have hjlt : j < k.castSucc := lt_of_not_ge h
          have hxlt := (sixVertexSectorPosition x).strictMono hjlt
          rw [hj] at hxlt
          exact (not_lt_of_ge hlo) hxlt
        have hjhi : j ≤ k.succ := by
          by_contra h
          have hjgt : k.succ < j := lt_of_not_ge h
          have hxlt := (sixVertexSectorPosition x).strictMono hjgt
          rw [hj] at hxlt
          exact (not_lt_of_ge hhi) hxlt
        have hjcases : j = k.castSucc ∨ j = k.succ := by
          change k.val ≤ j.val at hjlo
          change j.val ≤ k.val + 1 at hjhi
          by_cases hjv : j.val = k.val
          · left; apply Fin.ext; exact hjv
          · right
            apply Fin.ext
            have hlt : k.val < j.val :=
              lt_of_le_of_ne hjlo (Ne.symm hjv)
            exact Nat.le_antisymm hjhi (Nat.succ_le_iff.mpr hlt)
        rcases hjcases with rfl | rfl
        · left
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ]
          unfold sixVertexSectorIntCoordinates
          rw [hj]
        · right
          unfold sixVertexSectorIntCoordinates
          rw [hj]

theorem sixVertexForward_interior_card
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    (sixVertexBetheInteriorSet N (sixVertexSectorIntCoordinates x)
      (sixVertexSectorIntCoordinates y)).card =
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card := by
  let I := sixVertexBetheInteriorSet N (sixVertexSectorIntCoordinates x)
    (sixVertexSectorIntCoordinates y)
  have hmap : Finset.map (sixVertexSectorPosition y).toEmbedding I =
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))) := by
    ext v
    constructor
    · intro hv
      simp only [Finset.mem_map] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      have hi' := (mem_sixVertexBetheInteriorSet N _ _ i).mp hi
      simp only [Finset.mem_sdiff]
      constructor
      · exact sixVertexSectorPosition_mem y i
      · intro hix
        have hend := (sixVertexForward_endpoint_iff_mem x y hyx i).mpr hix
        exact hend.elim hi'.1 hi'.2
    · intro hv
      simp only [Finset.mem_sdiff] at hv
      have hv' := hv
      obtain ⟨i, rfl⟩ := (sixVertexSector_mem_iff_exists_position y v).mp hv'.1
      simp only [Finset.mem_map]
      refine ⟨i, ?_, rfl⟩
      rw [mem_sixVertexBetheInteriorSet]
      have hnend := fun hend => hv'.2
        ((sixVertexForward_endpoint_iff_mem x y hyx i).mp hend)
      tauto
  rw [← hmap, Finset.card_map]

theorem sixVertexReverse_endpoint_iff_mem
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y))
    (i : Fin (n + 1)) :
    (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i =
        sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i \/
      sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i =
        sixVertexSectorIntCoordinates x i) ↔
      sixVertexSectorPosition y ((finRotate (n + 1)).symm i) ∈
        (x : Finset (Fin N)) := by
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hxy
  have hsymm0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
    apply Fin.ext
    simp [finRotate_symm_apply]
  have hsymmsucc (k : Fin n) :
      (finRotate (n + 1)).symm k.succ = k.castSucc := by
    apply Fin.ext
    simp [finRotate_symm_apply, Fin.coe_sub_one]
  constructor
  · intro hend
    induction i using Fin.cases with
    | zero =>
        rw [hsymm0]
        rw [sixVertexSector_mem_iff_exists_position]
        rcases hend with hlo | hhi
        · refine ⟨Fin.last n, ?_⟩
          apply Fin.ext
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at hlo
          unfold sixVertexSectorIntCoordinates at hlo
          omega
        · have hneg := sixVertexReverseTuple_first_neg y
          have hxzero : 0 ≤ sixVertexSectorIntCoordinates x 0 := by
            simp [sixVertexSectorIntCoordinates]
          exfalso
          exact (not_lt_of_ge hxzero) (hhi ▸ hneg)
    | succ k =>
        rw [hsymmsucc k]
        rw [sixVertexSector_mem_iff_exists_position]
        rcases hend with hlo | hhi
        · refine ⟨k.castSucc, ?_⟩
          apply Fin.ext
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ] at hlo
          unfold sixVertexSectorIntCoordinates at hlo
          exact_mod_cast hlo.symm
        · refine ⟨k.succ, ?_⟩
          apply Fin.ext
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ] at hhi
          unfold sixVertexSectorIntCoordinates at hhi
          exact_mod_cast hhi.symm
  · intro hmem
    obtain ⟨j, hj⟩ := (sixVertexSector_mem_iff_exists_position x _).mp hmem
    induction i using Fin.cases with
    | zero =>
        rw [hsymm0] at hmem
        change sixVertexSectorPosition x j =
          sixVertexSectorPosition y (Fin.last n) at hj
        have hx_le_y : sixVertexSectorPosition x (Fin.last n) ≤
            sixVertexSectorPosition y (Fin.last n) := hpos.1 (Fin.last n)
        have hjlast : j = Fin.last n := by
          by_contra hne
          have hjlt : j < Fin.last n := Fin.lt_last_iff_ne_last.mpr hne
          have hxlt := (sixVertexSectorPosition x).strictMono hjlt
          rw [hj] at hxlt
          exact (not_lt_of_ge hx_le_y) hxlt
        left
        simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero]
        rw [hjlast] at hj
        unfold sixVertexSectorIntCoordinates
        have hcast : ((sixVertexSectorPosition y (Fin.last n)).val : Int) =
            (sixVertexSectorPosition x (Fin.last n)).val := by
          exact_mod_cast congrArg Fin.val hj.symm
        exact congrArg (fun t : Int => t - N) hcast
    | succ k =>
        rw [hsymmsucc k] at hmem
        replace hj : sixVertexSectorPosition x j =
            sixVertexSectorPosition y k.castSucc := by
          simpa [hsymmsucc k] using hj
        have hlo : sixVertexSectorPosition x k.castSucc ≤
            sixVertexSectorPosition y k.castSucc := hpos.1 k.castSucc
        have hhi : sixVertexSectorPosition y k.castSucc ≤
            sixVertexSectorPosition x k.succ := hpos.2 k.val (by omega)
        have hjlo : k.castSucc ≤ j := by
          by_contra h
          have hjlt : j < k.castSucc := lt_of_not_ge h
          have hxlt := (sixVertexSectorPosition x).strictMono hjlt
          rw [hj] at hxlt
          exact (not_lt_of_ge hlo) hxlt
        have hjhi : j ≤ k.succ := by
          by_contra h
          have hjgt : k.succ < j := lt_of_not_ge h
          have hxlt := (sixVertexSectorPosition x).strictMono hjgt
          rw [hj] at hxlt
          exact (not_lt_of_ge hhi) hxlt
        have hjcases : j = k.castSucc ∨ j = k.succ := by
          change k.val ≤ j.val at hjlo
          change j.val ≤ k.val + 1 at hjhi
          by_cases hjv : j.val = k.val
          · left; apply Fin.ext; exact hjv
          · right
            apply Fin.ext
            have hlt : k.val < j.val :=
              lt_of_le_of_ne hjlo (Ne.symm hjv)
            exact Nat.le_antisymm hjhi (Nat.succ_le_iff.mpr hlt)
        rcases hjcases with rfl | rfl
        · left
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ]
          unfold sixVertexSectorIntCoordinates
          rw [hj]
        · right
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ]
          unfold sixVertexSectorIntCoordinates
          rw [hj]

theorem sixVertexReverse_interior_card
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    (sixVertexBetheInteriorSet N (sixVertexSectorIntCoordinates x)
      (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))).card =
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card := by
  let I := sixVertexBetheInteriorSet N (sixVertexSectorIntCoordinates x)
    (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
  let e : Fin (n + 1) ↪ Fin N :=
    (finRotate (n + 1)).symm.toEmbedding.trans
      (sixVertexSectorPosition y).toEmbedding
  have hmap : Finset.map e I =
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))) := by
    ext v
    constructor
    · intro hv
      simp only [Finset.mem_map] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      have hi' := (mem_sixVertexBetheInteriorSet N _ _ i).mp hi
      simp only [Finset.mem_sdiff]
      constructor
      · exact sixVertexSectorPosition_mem y _
      · intro hix
        have hend := (sixVertexReverse_endpoint_iff_mem x y hxy i).mpr hix
        exact hend.elim hi'.1 hi'.2
    · intro hv
      simp only [Finset.mem_sdiff] at hv
      obtain ⟨j, hj⟩ := (sixVertexSector_mem_iff_exists_position y v).mp hv.1
      let i := finRotate (n + 1) j
      have heq : (finRotate (n + 1)).symm i = j := by
        simp [i]
      simp only [Finset.mem_map]
      refine ⟨i, ?_, ?_⟩
      · rw [mem_sixVertexBetheInteriorSet]
        have hnend : ¬(
            sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i =
                sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i \/
              sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i =
                sixVertexSectorIntCoordinates x i) := by
          intro hend
          have hmemx := (sixVertexReverse_endpoint_iff_mem x y hxy i).mp hend
          rw [heq, hj] at hmemx
          exact hv.2 hmemx
        tauto
      · dsimp [e]
        rw [heq, hj]
  rw [← hmap, Finset.card_map]

theorem sixVertexBetheIntervalTupleWeight_forward
    {N n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    sixVertexBetheIntervalTupleWeight N c z
        (sixVertexSectorIntCoordinates x) (sixVertexSectorIntCoordinates y) =
      (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) *
        ∏ i, z i ^ sixVertexSectorIntCoordinates y i := by
  have hcard : ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card =
      ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop,
      Finset.inter_comm]
  rw [sixVertexBetheIntervalTupleWeight_eq_interior,
    sixVertexForward_interior_card x y hyx,
    hcard, sixVertexSectorRowDistance_eq_two_mul_sdiff]
  rw [pow_mul]

theorem sixVertexBetheIntervalTupleWeight_reverse
    {N n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    sixVertexBetheIntervalTupleWeight N c z
        (sixVertexSectorIntCoordinates x)
        (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y)) =
      (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) *
        ∏ i, z i ^
          (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i) := by
  have hcard : ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card =
      ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop,
      Finset.inter_comm]
  rw [sixVertexBetheIntervalTupleWeight_eq_interior,
    sixVertexReverse_interior_card x y hxy,
    hcard, sixVertexSectorRowDistance_eq_two_mul_sdiff]
  rw [pow_mul]

theorem sixVertexForwardInterlaced_refl {N m : Nat}
    (x : SixVertexSector N m) :
    SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow x) := by
  apply sixVertexForwardInterlaced_of_positions
  constructor
  · exact fun _ => le_rfl
  · intro k hk
    exact (sixVertexSectorPosition x).monotone (by
      apply Fin.mk_le_mk.mpr
      omega)

theorem sixVertexForwardInterlaced_antisymm
    {N m : Nat} (x y : SixVertexSector N m)
    (hxy : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hyx : SixVertexForwardInterlaced (sixVertexSectorRow y)
      (sixVertexSectorRow x)) : x = y := by
  have hpXY := (sixVertexForwardInterlaced_iff_positions x y).mp hxy
  have hpYX := (sixVertexForwardInterlaced_iff_positions y x).mp hyx
  apply (Set.powersetCard.ofFinEmbEquiv (n := m) (I := Fin N)).symm.injective
  change sixVertexSectorPosition x = sixVertexSectorPosition y
  ext i
  exact le_antisymm (hpXY.1 i) (hpYX.1 i)

end
end StatMech.FrontierD
