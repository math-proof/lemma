/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part7
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInteriorBlockSlabComplement_symmDiff_bottom
    (L p k : Nat) (hp : 0 < p) :
    cubicalInteriorBlockSlabComplement L p k ∆
        cubicalInteriorBlockBottomSheet L p k =
      cubicalInteriorBlockSlabSideWall L p k := by
  have hsub := cubicalInteriorBlockBottomSheet_subset_slabComplement L p k hp
  ext plaquette
  simp only [Finset.mem_symmDiff, cubicalInteriorBlockSlabSideWall,
    Finset.mem_sdiff]
  constructor
  · rintro (⟨hcomp, hnot⟩ | ⟨hbottom, hnot⟩)
    · exact ⟨hcomp, hnot⟩
    · exact (hnot (hsub hbottom)).elim
  · rintro ⟨hcomp, hnot⟩
    exact Or.inl ⟨hcomp, hnot⟩

theorem cubicalInteriorBlockSlabSideWall_subset_faces
    (L p k : Nat) (hp : 0 < p) :
    cubicalInteriorBlockSlabSideWall L p k ⊆
      cubicalInteriorBlockSideWallFaces L p k := by
  let N := cubicalInteriorBlockSide L p k
  have hpN : p <= N := by dsimp [N, cubicalInteriorBlockSide]; omega
  intro plaquette hplaquette
  have hcomp := (Finset.mem_sdiff.mp hplaquette).1
  have hcut := (Finset.mem_sdiff.mp hcomp).1
  cases plaquette with
  | xy i j f =>
      have hnotBottom := (Finset.mem_sdiff.mp hplaquette).2
      have hnotTop := (Finset.mem_sdiff.mp hcomp).2
      rw [mem_multibondCut] at hcut
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          exfalso
          apply hnotBottom
          unfold cubicalInteriorBlockBottomSheet cubicalXYSheet
          exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
      | some z =>
          cases hf : finForward f with
          | none =>
              have hflast : f = Fin.last N :=
                (finForward_eq_none_iff' f).mp hf
              have hfz : f = z.succ := (finBackward_eq_some_iff f z).mp hb
              have hz : z.val < p := by
                simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  cubicalInteriorBlockHeight] using hcut
              have hzlast := congrArg Fin.val (hfz.symm.trans hflast)
              simp at hzlast
              dsimp [N, cubicalInteriorBlockSide] at hzlast
              omega
          | some z' =>
              have hne : (z.val < p) ≠ (z'.val < p) := by
                simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  cubicalInteriorBlockHeight] using hcut
              have hfz : f = z.succ := (finBackward_eq_some_iff f z).mp hb
              have hfz' : f = z'.castSucc :=
                (finForward_eq_some_iff f z').mp hf
              have hsucc : z'.val = z.val + 1 := by
                have h := congrArg Fin.val (hfz.symm.trans hfz')
                simp at h
                omega
              have hfp : f.val = p := by
                by_cases hz : z.val < p <;>
                  by_cases hz' : z'.val < p <;>
                    simp [hz, hz'] at hne <;> rw [hfz] <;> simp <;> omega
              exfalso
              apply hnotTop
              unfold cubicalXYSheet
              exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, by
                rw [CubicalPlaquette.xy.injEq]
                exact ⟨rfl, rfl, Fin.ext hfp.symm⟩⟩
  | xz i f z =>
      rw [mem_multibondCut] at hcut
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          let y0 : Fin N := ⟨0, by dsimp [N, cubicalInteriorBlockSide]; omega⟩
          have hf : finForward (0 : Fin (N + 1)) = some y0 := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hz : z.val < p := by
            simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
              cubicalInteriorBlockHeight, y0] using hcut
          let zp : Fin p := ⟨z.val, hz⟩
          simp only [cubicalInteriorBlockSideWallFaces, Finset.mem_union,
            Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inl (Or.inl (Or.inl ⟨(i, zp), by
            congr 1⟩))
      | some y =>
          cases hf : finForward f with
          | none =>
              have hlast : f = Fin.last N := (finForward_eq_none_iff' f).mp hf
              have hz : z.val < p := by
                simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  cubicalInteriorBlockHeight] using hcut
              let zp : Fin p := ⟨z.val, hz⟩
              simp only [cubicalInteriorBlockSideWallFaces, Finset.mem_union,
                Finset.mem_image, Finset.mem_univ, true_and]
              exact Or.inl (Or.inl (Or.inr ⟨(i, zp), by
                rw [hlast]
                congr 1⟩))
          | some y' =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                cubicalInteriorBlockHeight] at hcut
  | yz f j z =>
      rw [mem_multibondCut] at hcut
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          let x0 : Fin N := ⟨0, by dsimp [N, cubicalInteriorBlockSide]; omega⟩
          have hf : finForward (0 : Fin (N + 1)) = some x0 := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hz : z.val < p := by
            simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
              cubicalInteriorBlockHeight, x0] using hcut
          let zp : Fin p := ⟨z.val, hz⟩
          simp only [cubicalInteriorBlockSideWallFaces, Finset.mem_union,
            Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inl (Or.inr ⟨(j, zp), by
            congr 1⟩)
      | some x =>
          cases hf : finForward f with
          | none =>
              have hlast : f = Fin.last N := (finForward_eq_none_iff' f).mp hf
              have hz : z.val < p := by
                simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  cubicalInteriorBlockHeight] using hcut
              let zp : Fin p := ⟨z.val, hz⟩
              simp only [cubicalInteriorBlockSideWallFaces, Finset.mem_union,
                Finset.mem_image, Finset.mem_univ, true_and]
              exact Or.inr ⟨(j, zp), by
                rw [hlast]
                congr 1⟩
          | some x' =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                cubicalInteriorBlockHeight] at hcut

theorem card_cubicalInteriorBlockSideWallFaces_le
    (L p k : Nat) :
    (cubicalInteriorBlockSideWallFaces L p k).card <=
      4 * cubicalInteriorBlockSide L p k * p := by
  let N := cubicalInteriorBlockSide L p k
  let castZ : Fin p -> Fin N := Fin.castLE (by
    dsimp [N, cubicalInteriorBlockSide]
    omega)
  let west := (Finset.univ : Finset (Fin N × Fin p)).image fun iz =>
    CubicalPlaquette.xz iz.1 (0 : Fin (N + 1)) (castZ iz.2)
  let east := (Finset.univ : Finset (Fin N × Fin p)).image fun iz =>
    CubicalPlaquette.xz iz.1 (Fin.last N) (castZ iz.2)
  let south := (Finset.univ : Finset (Fin N × Fin p)).image fun jz =>
    CubicalPlaquette.yz (0 : Fin (N + 1)) jz.1 (castZ jz.2)
  let north := (Finset.univ : Finset (Fin N × Fin p)).image fun jz =>
    CubicalPlaquette.yz (Fin.last N) jz.1 (castZ jz.2)
  have hcard (S : Finset (CubicalPlaquette N N N))
      (hS : S = west ∨ S = east ∨ S = south ∨ S = north) :
      S.card <= N * p := by
    rcases hS with rfl | rfl | rfl | rfl <;>
      exact (Finset.card_image_le.trans_eq (by simp)).trans le_rfl
  change (west ∪ east ∪ south ∪ north).card <= 4 * N * p
  calc
    (west ∪ east ∪ south ∪ north).card <=
        west.card + east.card + south.card + north.card := by
      calc
        _ <= (west ∪ east ∪ south).card + north.card :=
          Finset.card_union_le _ _
        _ <= ((west ∪ east).card + south.card) + north.card := by
          gcongr
          exact Finset.card_union_le _ _
        _ <= ((west.card + east.card) + south.card) + north.card := by
          gcongr
          exact Finset.card_union_le _ _
    _ <= N * p + N * p + N * p + N * p := by
      gcongr
      · exact hcard west (Or.inl rfl)
      · exact hcard east (Or.inr (Or.inl rfl))
      · exact hcard south (Or.inr (Or.inr (Or.inl rfl)))
      · exact hcard north (Or.inr (Or.inr (Or.inr rfl)))
    _ = 4 * N * p := by ring

theorem card_cubicalInteriorBlockSlabSideWall_le
    (L p k : Nat) (hp : 0 < p) :
    (cubicalInteriorBlockSlabSideWall L p k).card <=
      4 * cubicalInteriorBlockSide L p k * p := by
  exact Finset.card_le_card
    (cubicalInteriorBlockSlabSideWall_subset_faces L p k hp) |>.trans
      (card_cubicalInteriorBlockSideWallFaces_le L p k)


theorem cubicalInteriorBlockBottomDisorderFreeEnergy_le_full_add_sideWall
    {K : Real} (hK : 0 < K) (L p k : Nat) (hp : 0 < p) :
    multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
        (cubicalInteriorBlockBottomSheet L p k) <=
      multibondDisorderFreeEnergy cubicalDualEnds
          (fun _ : CubicalPlaquette
            (cubicalInteriorBlockSide L p k)
            (cubicalInteriorBlockSide L p k)
            (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
          (cubicalInteriorBlockFullSheet L p k) +
        2 * (cubicalInteriorBlockSlabSideWall L p k).card *
          gaugeDualCoupling K := by
  let J := fun _ : CubicalPlaquette
    (cubicalInteriorBlockSide L p k)
    (cubicalInteriorBlockSide L p k)
    (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K
  have hslab : multibondDisorderFreeEnergy cubicalDualEnds J
      (cubicalInteriorBlockFullSheet L p k) =
      multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockSlabComplement L p k) := by
    exact multibondDisorderFreeEnergy_sheet_eq_lowerComplementSurface
      (cubicalInteriorBlockHeight L p k) (by
        simp [cubicalInteriorBlockHeight, hp]) J
  have hdist := multibondDisorderFreeEnergy_sheet_sub_abs_le
    cubicalDualEnds J (cubicalInteriorBlockBottomSheet L p k)
      (cubicalInteriorBlockSlabComplement L p k)
  have hsym : cubicalInteriorBlockBottomSheet L p k ∆
      cubicalInteriorBlockSlabComplement L p k =
      cubicalInteriorBlockSlabSideWall L p k := by
    rw [symmDiff_comm]
    exact cubicalInteriorBlockSlabComplement_symmDiff_bottom L p k hp
  rw [hsym] at hdist
  have hJ : 0 < gaugeDualCoupling K := gaugeDualCoupling_pos hK
  have hsum : (∑ q ∈ cubicalInteriorBlockSlabSideWall L p k, |J q|) =
      ((cubicalInteriorBlockSlabSideWall L p k).card : Real) *
        gaugeDualCoupling K := by
    simp [J, abs_of_pos hJ]
  rw [hsum] at hdist
  have hone := (le_abs_self
    (multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockBottomSheet L p k) -
      multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockSlabComplement L p k))).trans hdist
  rw [← hslab] at hone
  dsimp [J] at hone ⊢
  linarith


theorem cubicalRectangularWilsonFreeEnergy_interiorBlock_le
    {K : Real} (hK : 0 < K) (L p k : Nat)
    (hL : 0 < L) (hp : 0 < p) (hk : 0 < k) :
    cubicalRectangularWilsonFreeEnergy K
        (cubicalInteriorBlockSide L p k)
        (cubicalInteriorBlockSide L p k) <=
      (k * k : Nat) *
          cubicalPaddedDisorderFreeEnergy K L L p p p p p p +
        16 * cubicalInteriorBlockSide L p k * p * gaugeDualCoupling K := by
  let N := cubicalInteriorBlockSide L p k
  let J := gaugeDualCoupling K
  let P := cubicalPaddedDisorderFreeEnergy K L L p p p p p p
  have hcentral := cubicalInteriorBlockCentralDisorderFreeEnergy_le_tiles
    hK L p k hL hp hk
  have hframe := cubicalInteriorBlockFullDisorderFreeEnergy_le_central_add_frame
    hK L p k
  have hside := cubicalInteriorBlockBottomDisorderFreeEnergy_le_full_add_sideWall
    hK L p k hp
  have hframeCard : (cubicalInteriorBlockFrame L p k).card <= 4 * N * p := by
    rw [card_cubicalInteriorBlockFrame]
    have hsq : N ^ 2 = (k * L) ^ 2 + 4 * p * (k * L + p) := by
      dsimp [N, cubicalInteriorBlockSide]
      ring
    rw [hsq, Nat.add_sub_cancel_left]
    dsimp [N, cubicalInteriorBlockSide]
    nlinarith
  have hsideCard : (cubicalInteriorBlockSlabSideWall L p k).card <=
      4 * N * p := card_cubicalInteriorBlockSlabSideWall_le L p k hp
  have hJ : 0 <= J := (gaugeDualCoupling_pos hK).le
  have hframeReal :
      ((cubicalInteriorBlockFrame L p k).card : Real) <= 4 * N * p := by
    exact_mod_cast hframeCard
  have hsideReal :
      ((cubicalInteriorBlockSlabSideWall L p k).card : Real) <= 4 * N * p := by
    exact_mod_cast hsideCard
  have hbottom :
      multibondDisorderFreeEnergy cubicalDualEnds
          (fun _ : CubicalPlaquette N N N => J)
          (cubicalInteriorBlockBottomSheet L p k) <=
        (k * k : Nat) * P + 16 * N * p * J := by
    dsimp [N, J, P] at hcentral hframe hside ⊢
    calc
      _ <= multibondDisorderFreeEnergy cubicalDualEnds
            (fun _ : CubicalPlaquette
              (cubicalInteriorBlockSide L p k)
              (cubicalInteriorBlockSide L p k)
              (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
            (cubicalInteriorBlockFullSheet L p k) +
          2 * (cubicalInteriorBlockSlabSideWall L p k).card *
            gaugeDualCoupling K := hside
      _ <= (multibondDisorderFreeEnergy cubicalDualEnds
              (fun _ : CubicalPlaquette
                (cubicalInteriorBlockSide L p k)
                (cubicalInteriorBlockSide L p k)
                (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
              (cubicalInteriorBlockCentralSheet L p k) +
            2 * (cubicalInteriorBlockFrame L p k).card *
              gaugeDualCoupling K) +
          2 * (cubicalInteriorBlockSlabSideWall L p k).card *
            gaugeDualCoupling K := by gcongr
      _ <= (k * k : Nat) *
            cubicalPaddedDisorderFreeEnergy K L L p p p p p p +
          2 * (cubicalInteriorBlockFrame L p k).card *
              gaugeDualCoupling K +
          2 * (cubicalInteriorBlockSlabSideWall L p k).card *
              gaugeDualCoupling K := by linarith
      _ <= (k * k : Nat) *
            cubicalPaddedDisorderFreeEnergy K L L p p p p p p +
          16 * cubicalInteriorBlockSide L p k * p * gaugeDualCoupling K := by
            have hf := mul_le_mul_of_nonneg_right hframeReal hJ
            have hs := mul_le_mul_of_nonneg_right hsideReal hJ
            norm_num at hf hs ⊢
            nlinarith
  have hN : 0 < N := by dsimp [N, cubicalInteriorBlockSide]; omega
  rw [cubicalRectangularWilsonFreeEnergy_eq_finiteIsingDisorder hK hN hN]
  unfold finiteRectangularIsingDisorderFreeEnergy
  rw [Nat.max_self]
  simpa [N, J, P, cubicalInteriorBlockBottomSheet] using hbottom


theorem rectangularIsingSurfaceTension_le_paddedDisorderDensity
    {K : Real} (hK : 0 < K) (L p : Nat) (hL : 0 < L) (hp : 0 < p) :
    rectangularIsingSurfaceTension (gaugeDualCoupling K) <=
      cubicalPaddedDisorderFreeEnergy K L L p p p p p p / (L : Real) ^ 2 := by
  let P := cubicalPaddedDisorderFreeEnergy K L L p p p p p p
  let J := gaugeDualCoupling K
  let upper : Nat -> Real := fun k =>
    let t : Nat := k + 1
    let N : Nat := cubicalInteriorBlockSide L p t
    (((t : Real) ^ 2 * P + 16 * (N : Real) * p * J) / (N : Real) ^ 2)
  have hrate : ∀ k : Nat,
      rectangularIsingSurfaceTension (gaugeDualCoupling K) <= upper k := by
    intro k
    let t : Nat := k + 1
    let N : Nat := cubicalInteriorBlockSide L p t
    have hN : 0 < N := by dsimp [N, cubicalInteriorBlockSide]; omega
    have hraw := cubicalRectangularWilsonFreeEnergy_interiorBlock_le
      hK L p t hL hp (by dsimp [t]; omega)
    have hrate0 := rectangularSurfaceRate_le_density
      (fun m n => cubicalRectangularWilsonFreeEnergy_nonneg hK m n) hN hN
    rw [cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension
      hK] at hrate0
    unfold rectangularSurfaceDensity at hrate0
    have hden : (0 : Real) < (N : Real) * (N : Real) := by positivity
    have hrawDiv := div_le_div_of_nonneg_right hraw hden.le
    dsimp [upper, t, N, P, J]
    rw [show ((N : Real) * (N : Real)) = (N : Real) ^ 2 by ring] at hrate0 hrawDiv
    simpa [t, N, pow_two] using hrate0.trans hrawDiv
  let u : Nat -> Real := fun k => (1 : Real) / (k + 1 : Real)
  let transformed : Nat -> Real := fun k =>
    (P + 16 * p * J * (L * u k + 2 * p * (u k) ^ 2)) /
      (L + 2 * p * u k) ^ 2
  have hu : Tendsto u atTop (nhds 0) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hnum : Tendsto
      (fun k => P + 16 * p * J * (L * u k + 2 * p * (u k) ^ 2))
      atTop (nhds P) := by
    have hinner : Tendsto
        (fun k => (L : Real) * u k + 2 * p * (u k) ^ 2)
        atTop (nhds 0) := by
      convert (tendsto_const_nhds.mul hu).add
        (tendsto_const_nhds.mul (hu.pow 2)) using 1 <;> norm_num
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hinner) using 1 <;>
      norm_num
  have hden : Tendsto (fun k => (L + 2 * p * u k) ^ 2)
      atTop (nhds ((L : Real) ^ 2)) := by
    have hbase : Tendsto (fun k => (L : Real) + 2 * p * u k)
        atTop (nhds ((L : Real) + 2 * p * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hu)
    simpa using hbase.pow 2
  have hLsq : ((L : Real) ^ 2) ≠ 0 := by positivity
  have htransformed : Tendsto transformed atTop
      (nhds (P / (L : Real) ^ 2)) := by
    exact hnum.div hden hLsq
  have heq : ∀ k, upper k = transformed k := by
    intro k
    dsimp [upper, transformed, u, P, J, cubicalInteriorBlockSide]
    push_cast
    field_simp
    ring
  have hupper : Tendsto upper atTop (nhds (P / (L : Real) ^ 2)) := by
    exact htransformed.congr' (Eventually.of_forall fun k => (heq k).symm)
  exact ge_of_tendsto hupper (Eventually.of_forall hrate)

end
end StatMech.FrontierA
