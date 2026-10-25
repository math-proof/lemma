/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part6


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

theorem closedBall_subset_finiteCenteredRadialGridDeeperInterior
    (n : Nat) (mesh R : Real) (hmesh : 0 < mesh) (hR : 0 ≤ R)
    (hwide : 2 * R + 5 * mesh ≤ mesh * n) :
    closedBall (0 : Complex) R ⊆
      finiteCenteredRadialGridDeeperInterior n mesh := by
  intro z hz
  have hnorm : norm z ≤ R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hrelo : -R ≤ z.re := by
    linarith [neg_le_of_abs_le (hre.trans hnorm)]
  have hrehi : z.re ≤ R := by
    linarith [le_of_abs_le (hre.trans hnorm)]
  have himlo : -R ≤ z.im := by
    linarith [neg_le_of_abs_le (him.trans hnorm)]
  have himhi : z.im ≤ R := by
    linarith [le_of_abs_le (him.trans hnorm)]
  have hq : 2 * R / mesh + 5 ≤ (n : Real) := by
    calc
      2 * R / mesh + 5 = (2 * R + 5 * mesh) / mesh := by
        field_simp [hmesh.ne']
      _ ≤ (mesh * (n : Real)) / mesh :=
        (div_le_div_iff_of_pos_right hmesh).mpr hwide
      _ = (n : Real) := by field_simp [hmesh.ne']
  have hsumlo : -2 * R / mesh ≤ (z.re + z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hsumhi : (z.re + z.im) / mesh ≤ 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdifflo : -2 * R / mesh ≤ (z.re - z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdiffhi : (z.re - z.im) / mesh ≤ 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hneg : -2 * R / mesh = -(2 * R / mesh) := by ring
  rw [hneg] at hsumlo hdifflo
  have hc1 : (isingCenteredRadialGridCoordinate mesh n z).1 =
      (n : Real) + (z.re + z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  have hc2 : (isingCenteredRadialGridCoordinate mesh n z).2 =
      (n : Real) + (z.re - z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  change 1 < (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 < (2 * n : Nat) - 3 ∧
    1 < (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 < (2 * n : Nat) - 3
  rw [hc1, hc2]
  constructor
  · linarith
  constructor
  · push_cast
    linarith
  constructor
  · linarith
  · push_cast
    linarith


theorem finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_neighbor
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (s : Set Complex) (hs : Convex Real s) (L : NNReal)
    (hinside : s ⊆ finiteCenteredRadialGridStrictInterior n mesh)
    (hI : ∀ a b : Nat, ∀ (ha : a + 1 < 2 * n) (hb : b < 2 * n),
      norm (value ⟨a + 1, ha⟩ ⟨b, hb⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real))
    (hJ : ∀ a b : Nat, ∀ (ha : a < 2 * n) (hb : b + 1 < 2 * n),
      norm (value ⟨a, ha⟩ ⟨b + 1, hb⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real)) :
    LipschitzOnWith (4 * L)
      (finiteCenteredRadialGridInterpolant n mesh value) s := by
  apply lipschitzOnWith_of_open_local_on_convex _ _ _ hs
  intro z hz
  have hzint := hinside hz
  obtain ⟨i, hi, hi0, hi2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate mesh n z).1 hzint.1 hzint.2.1
  obtain ⟨j, hj, hj0, hj2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate mesh n z).2
        hzint.2.2.1 hzint.2.2.2
  let U : Set Complex := {w |
    (i : Real) < (isingCenteredRadialGridCoordinate mesh n w).1 ∧
    (isingCenteredRadialGridCoordinate mesh n w).1 < (i : Real) + 2 ∧
    (j : Real) < (isingCenteredRadialGridCoordinate mesh n w).2 ∧
    (isingCenteredRadialGridCoordinate mesh n w).2 < (j : Real) + 2}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hc1 : Continuous (fun w : Complex =>
        (isingCenteredRadialGridCoordinate mesh n w).1) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    have hc2 : Continuous (fun w : Complex =>
        (isingCenteredRadialGridCoordinate mesh n w).2) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    exact (isOpen_lt continuous_const hc1).inter
      ((isOpen_lt hc1 continuous_const).inter
        ((isOpen_lt continuous_const hc2).inter
          (isOpen_lt hc2 continuous_const)))
  · exact ⟨hi0, hi2, hj0, hj2⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    let xp : Real := (isingCenteredRadialGridCoordinate mesh n p).1 - i
    let xq : Real := (isingCenteredRadialGridCoordinate mesh n q).1 - i
    let yp : Real := (isingCenteredRadialGridCoordinate mesh n p).2 - j
    let yq : Real := (isingCenteredRadialGridCoordinate mesh n q).2 - j
    have hxp0 : 0 <= xp := by dsimp only [xp]; linarith [hp.1.1]
    have hxp2 : xp <= 2 := by dsimp only [xp]; linarith [hp.1.2.1]
    have hxq0 : 0 <= xq := by dsimp only [xq]; linarith [hq.1.1]
    have hxq2 : xq <= 2 := by dsimp only [xq]; linarith [hq.1.2.1]
    have hyp0 : 0 <= yp := by dsimp only [yp]; linarith [hp.1.2.2.1]
    have hyp2 : yp <= 2 := by dsimp only [yp]; linarith [hp.1.2.2.2]
    have hyq0 : 0 <= yq := by dsimp only [yq]; linarith [hq.1.2.2.1]
    have hyq2 : yq <= 2 := by dsimp only [yq]; linarith [hq.1.2.2.2]
    have H := finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist
      n mesh hmesh value i j hi hj xp xq yp yq (L : Real)
      hxp0 hxp2 hxq0 hxq2 hyp0 hyp2 hyq0 hyq2 L.2
      (hI i j (by omega) (by omega))
      (hI (i + 1) j (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega))
      (hI (i + 1) (j + 1) (by omega) (by omega))
      (hI i (j + 2) (by omega) (by omega))
      (hI (i + 1) (j + 2) (by omega) (by omega))
      (hJ i j (by omega) (by omega))
      (hJ i (j + 1) (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega))
      (hJ (i + 1) (j + 1) (by omega) (by omega))
      (hJ (i + 2) j (by omega) (by omega))
      (hJ (i + 2) (j + 1) (by omega) (by omega))
    have hpPoint :
        isingCenteredRadialGridCellPoint mesh n i j xp yp = p :=
      isingCenteredRadialGridCellPoint_coordinate mesh hmesh.ne' n i j p
    have hqPoint :
        isingCenteredRadialGridCellPoint mesh n i j xq yq = q :=
      isingCenteredRadialGridCellPoint_coordinate mesh hmesh.ne' n i j q
    rw [hpPoint, hqPoint] at H
    simpa [dist_eq_norm] using H


theorem finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_strictNeighbor
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (s : Set Complex) (hs : Convex Real s) (L : NNReal)
    (hinside : s ⊆ finiteCenteredRadialGridDeeperInterior n mesh)
    (hI : ∀ a b : Nat, ∀ (ha : a + 1 < 2 * n) (hb : b < 2 * n),
      a + 2 < 2 * n → b + 1 < 2 * n →
      norm (value ⟨a + 1, ha⟩ ⟨b, hb⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real))
    (hJ : ∀ a b : Nat, ∀ (ha : a < 2 * n) (hb : b + 1 < 2 * n),
      a + 1 < 2 * n → b + 2 < 2 * n →
      norm (value ⟨a, ha⟩ ⟨b + 1, hb⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real)) :
    LipschitzOnWith (4 * L)
      (finiteCenteredRadialGridInterpolant n mesh value) s := by
  apply lipschitzOnWith_of_open_local_on_convex _ _ _ hs
  intro z hz
  have hzint := hinside hz
  obtain ⟨i, hi, hi0, hi2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate mesh n z).1 hzint.1 (by
        linarith [hzint.2.1])
  obtain ⟨j, hj, hj0, hj2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate mesh n z).2 hzint.2.2.1 (by
        linarith [hzint.2.2.2])
  have hi3 : i + 3 < 2 * n := by
    have hcast : (i : Real) + 3 < (2 * n : Nat) := by
      linarith [hi0, hzint.2.1]
    exact_mod_cast hcast
  have hj3 : j + 3 < 2 * n := by
    have hcast : (j : Real) + 3 < (2 * n : Nat) := by
      linarith [hj0, hzint.2.2.2]
    exact_mod_cast hcast
  let U : Set Complex := {w |
    (i : Real) < (isingCenteredRadialGridCoordinate mesh n w).1 ∧
    (isingCenteredRadialGridCoordinate mesh n w).1 < (i : Real) + 2 ∧
    (j : Real) < (isingCenteredRadialGridCoordinate mesh n w).2 ∧
    (isingCenteredRadialGridCoordinate mesh n w).2 < (j : Real) + 2}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hc1 : Continuous (fun w : Complex =>
        (isingCenteredRadialGridCoordinate mesh n w).1) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    have hc2 : Continuous (fun w : Complex =>
        (isingCenteredRadialGridCoordinate mesh n w).2) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    exact (isOpen_lt continuous_const hc1).inter
      ((isOpen_lt hc1 continuous_const).inter
        ((isOpen_lt continuous_const hc2).inter
          (isOpen_lt hc2 continuous_const)))
  · exact ⟨hi0, hi2, hj0, hj2⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    let xp : Real := (isingCenteredRadialGridCoordinate mesh n p).1 - i
    let xq : Real := (isingCenteredRadialGridCoordinate mesh n q).1 - i
    let yp : Real := (isingCenteredRadialGridCoordinate mesh n p).2 - j
    let yq : Real := (isingCenteredRadialGridCoordinate mesh n q).2 - j
    have hxp0 : 0 <= xp := by dsimp only [xp]; linarith [hp.1.1]
    have hxp2 : xp <= 2 := by dsimp only [xp]; linarith [hp.1.2.1]
    have hxq0 : 0 <= xq := by dsimp only [xq]; linarith [hq.1.1]
    have hxq2 : xq <= 2 := by dsimp only [xq]; linarith [hq.1.2.1]
    have hyp0 : 0 <= yp := by dsimp only [yp]; linarith [hp.1.2.2.1]
    have hyp2 : yp <= 2 := by dsimp only [yp]; linarith [hp.1.2.2.2]
    have hyq0 : 0 <= yq := by dsimp only [yq]; linarith [hq.1.2.2.1]
    have hyq2 : yq <= 2 := by dsimp only [yq]; linarith [hq.1.2.2.2]
    have H := finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist
      n mesh hmesh value i j hi hj xp xq yp yq (L : Real)
      hxp0 hxp2 hxq0 hxq2 hyp0 hyp2 hyq0 hyq2 L.2
      (hI i j (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) j (by omega) (by omega) (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hI i (j + 2) (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) (j + 2) (by omega) (by omega) (by omega) (by omega))
      (hJ i j (by omega) (by omega) (by omega) (by omega))
      (hJ i (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 2) j (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 2) (j + 1) (by omega) (by omega) (by omega) (by omega))
    have hpPoint :
        isingCenteredRadialGridCellPoint mesh n i j xp yp = p :=
      isingCenteredRadialGridCellPoint_coordinate mesh hmesh.ne' n i j p
    have hqPoint :
        isingCenteredRadialGridCellPoint mesh n i j xq yq = q :=
      isingCenteredRadialGridCellPoint_coordinate mesh hmesh.ne' n i j q
    rw [hpPoint, hqPoint] at H
    simpa [dist_eq_norm] using H


theorem isingLinearTent_mem_unit (x : Real) :
    0 <= isingLinearTent x ∧ isingLinearTent x <= 1 := by
  unfold isingLinearTent
  constructor
  · exact le_max_left _ _
  · rw [max_le_iff]
    exact ⟨by norm_num, by linarith [abs_nonneg x]⟩

theorem isingLinearTent_lipschitzWith :
    LipschitzWith 1 isingLinearTent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  unfold isingLinearTent
  calc
    |max 0 (1 - |x|) - max 0 (1 - |y|)| =
        |max (1 - |x|) 0 - max (1 - |y|) 0| := by
      rw [max_comm 0, max_comm 0]
    _ <= |(1 - |x|) - (1 - |y|)| :=
      abs_max_sub_max_le_abs _ _ _
    _ = abs (|x| - |y|) := by
      rw [show (1 - |x|) - (1 - |y|) = -(|x| - |y|) by ring, abs_neg]
    _ <= |x - y| := abs_abs_sub_abs_le_abs_sub x y

theorem locallyLipschitz_mul_of_mem_unit
    {f g : Complex -> Real} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g)
    (hfmem : ∀ z, 0 <= f z ∧ f z <= 1)
    (hgmem : ∀ z, 0 <= g z ∧ g z <= 1) :
    LocallyLipschitz (fun z => f z * g z) := by
  intro z
  obtain ⟨Kf, u, hu, hfu⟩ := hf z
  obtain ⟨Kg, v, hv, hgv⟩ := hg z
  refine ⟨Kf + Kg, u ∩ v, Filter.inter_mem hu hv, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  have hfp := hfmem p
  have hfq := hfmem q
  have hgp := hgmem p
  have hgq := hgmem q
  have hfd := hfu.dist_le_mul p hp.1 q hq.1
  have hgd := hgv.dist_le_mul p hp.2 q hq.2
  simp only [Real.dist_eq] at hfd hgd ⊢
  calc
    |f p * g p - f q * g q| =
        |(f p - f q) * g p + f q * (g p - g q)| := by
      congr 1
      ring
    _ <= |(f p - f q) * g p| + |f q * (g p - g q)| :=
      abs_add_le _ _
    _ = |f p - f q| * |g p| + |f q| * |g p - g q| := by
      rw [abs_mul, abs_mul]
    _ <= |f p - f q| + |g p - g q| := by
      rw [abs_of_nonneg hgp.1, abs_of_nonneg hfq.1]
      exact add_le_add
        (mul_le_of_le_one_right (abs_nonneg _) hgp.2)
        (mul_le_of_le_one_left (abs_nonneg _) hfq.2)
    _ <= (Kf : Real) * dist p q + (Kg : Real) * dist p q :=
      add_le_add hfd hgd
    _ = ((Kf + Kg : NNReal) : Real) * dist p q := by
      push_cast
      ring

theorem locallyLipschitz_complex_add
    {f g : Complex -> Complex} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g) : LocallyLipschitz (fun z => f z + g z) := by
  have hadd : LocallyLipschitz (fun p : Complex × Complex => p.1 + p.2) :=
    (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).locallyLipschitz
  exact hadd.comp (hf.prodMk hg)

theorem locallyLipschitz_finset_sum
    {α : Type*} (s : Finset α) (f : α -> Complex -> Complex)
    (hf : ∀ a ∈ s, LocallyLipschitz (f a)) :
    LocallyLipschitz (fun z => ∑ a ∈ s, f a z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (LocallyLipschitz.const (α := Complex) (0 : Complex))
  | @insert a s ha ih =>
      simp only [Finset.mem_insert] at hf
      simpa [Finset.sum_insert ha] using locallyLipschitz_complex_add
        (hf a (by simp)) (ih (fun b hb => hf b (by simp [hb])))


theorem finiteRadialGridInterpolant_locallyLipschitz
    (m : Nat) (mesh : Real)
    (value : Fin m -> Fin m -> Complex) :
    LocallyLipschitz (finiteRadialGridInterpolant m mesh value) := by
  classical
  have hre : LipschitzWith ‖mesh⁻¹‖₊ (fun z : Complex => z.re / mesh) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (lipschitzWith_smul (mesh⁻¹ : Real)).comp RCLike.lipschitzWith_re
  have him : LipschitzWith ‖mesh⁻¹‖₊ (fun z : Complex => z.im / mesh) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (lipschitzWith_smul (mesh⁻¹ : Real)).comp RCLike.lipschitzWith_im
  have hc1 : LocallyLipschitz (fun z : Complex =>
      (isingRadialGridCoordinate mesh z).1) := by
    unfold isingRadialGridCoordinate
    exact ((hre.vadd him).vsub
      (LipschitzWith.const (1 / 2))).locallyLipschitz
  have hc2 : LocallyLipschitz (fun z : Complex =>
      (isingRadialGridCoordinate mesh z).2) := by
    unfold isingRadialGridCoordinate
    exact ((hre.vsub him).vsub
      (LipschitzWith.const (1 / 2))).locallyLipschitz
  unfold finiteRadialGridInterpolant
  apply locallyLipschitz_finset_sum Finset.univ
  intro i _hi
  apply locallyLipschitz_finset_sum Finset.univ
  intro j _hj
  let fi : Complex -> Real := fun z =>
    isingLinearTent ((isingRadialGridCoordinate mesh z).1 - (i.1 : Real))
  let gj : Complex -> Real := fun z =>
    isingLinearTent ((isingRadialGridCoordinate mesh z).2 - (j.1 : Real))
  have hfi : LocallyLipschitz fi := by
    apply isingLinearTent_lipschitzWith.locallyLipschitz.comp
    exact ((LipschitzWith.prod_fst.vsub
      LipschitzWith.prod_snd).locallyLipschitz).comp
        (hc1.prodMk (LocallyLipschitz.const (i.1 : Real)))
  have hgj : LocallyLipschitz gj := by
    apply isingLinearTent_lipschitzWith.locallyLipschitz.comp
    exact ((LipschitzWith.prod_fst.vsub
      LipschitzWith.prod_snd).locallyLipschitz).comp
        (hc2.prodMk (LocallyLipschitz.const (j.1 : Real)))
  have hprod : LocallyLipschitz (fun z => fi z * gj z) :=
    locallyLipschitz_mul_of_mem_unit hfi hgj
      (fun _ => isingLinearTent_mem_unit _)
      (fun _ => isingLinearTent_mem_unit _)
  have hscale : LocallyLipschitz (fun r : Real =>
      ((r : Real) : Complex) * value i j) := by
    have h : LipschitzWith ‖value i j‖₊ (fun r : Real =>
        ((r : Real) : Complex) * value i j) := by
      apply LipschitzWith.of_dist_le_mul
      intro r t
      calc
        dist (((r : Real) : Complex) * value i j)
            (((t : Real) : Complex) * value i j) =
            |r - t| * norm (value i j) := by
          rw [dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
            Complex.norm_real, Real.norm_eq_abs]
        _ = (‖value i j‖₊ : Real) * dist r t := by
          simp only [Real.dist_eq, coe_nnnorm]
          ring
        _ <= (‖value i j‖₊ : Real) * dist r t := le_rfl
    exact h.locallyLipschitz
  exact hscale.comp hprod

theorem finiteCenteredRadialGridInterpolant_locallyLipschitz
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
    LocallyLipschitz (finiteCenteredRadialGridInterpolant n mesh value) := by
  unfold finiteCenteredRadialGridInterpolant
  apply (finiteRadialGridInterpolant_locallyLipschitz
    (2 * n) mesh value).comp
  exact (LipschitzWith.id.vadd
    (LipschitzWith.const ((mesh * n : Real) : Complex))).locallyLipschitz

theorem fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz
    (k : Nat) :
    LocallyLipschitz
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) := by
  unfold fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant
  apply (finiteCenteredRadialGridInterpolant_locallyLipschitz _ _ _).comp
  exact star_isometry.lipschitz.locallyLipschitz


theorem exists_lipschitzOnWith_forall_lt_of_locallyLipschitz
    (F : Nat -> Complex -> Complex) (hF : ∀ k, LocallyLipschitz (F k))
    (K : Set Complex) (hK : IsCompact K) (N : Nat) :
    ∃ C : NNReal, ∀ k < N, LipschitzOnWith C (F k) K := by
  induction N with
  | zero => exact ⟨0, by omega⟩
  | succ N ih =>
      obtain ⟨C, hC⟩ := ih
      obtain ⟨D, hD⟩ :=
        LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
          (hF N).locallyLipschitzOn
      refine ⟨max C D, ?_⟩
      intro k hk
      by_cases hkn : k < N
      · exact (hC k hkn).weaken (le_max_left _ _)
      · have hkeq : k = N := by omega
        subst k
        exact hD.weaken (le_max_right _ _)


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_neighbor
    (k : Nat) (R : Real) (L : NNReal) (hR : 0 <= R)
    (hwide : 2 * R + 4 * fkIsingExpandingSquareScale k <=
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
    (hI : ∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real))
    (hJ : ∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real)) :
    LipschitzOnWith (4 * L)
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
      (closedBall (0 : Complex) R) := by
  let value : Fin (2 * fkIsingExpandingSquareSide k) ->
      Fin (2 * fkIsingExpandingSquareSide k) -> Complex := fun i j =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) i j /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  have hinside := closedBall_subset_finiteCenteredRadialGridStrictInterior
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) R
    (fkIsingExpandingSquareScale_pos k) hR hwide
  have hf := finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_neighbor
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
    (fkIsingExpandingSquareScale_pos k) value (closedBall 0 R)
    (convex_closedBall 0 R) L hinside hI hJ
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hzs : star z ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hws : star w ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hw
  have h := hf.dist_le_mul (star z) hzs (star w) hws
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, value,
    star_isometry.dist_eq] using h


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_strictNeighbor
    (k : Nat) (R : Real) (L : NNReal) (hR : 0 <= R)
    (hwide : 2 * R + 5 * fkIsingExpandingSquareScale k <=
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
    (hI : ∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
      a + 2 < 2 * fkIsingExpandingSquareSide k →
      b + 1 < 2 * fkIsingExpandingSquareSide k →
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real))
    (hJ : ∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      a + 1 < 2 * fkIsingExpandingSquareSide k →
      b + 2 < 2 * fkIsingExpandingSquareSide k →
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real)) :
    LipschitzOnWith (4 * L)
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
      (closedBall (0 : Complex) R) := by
  let value : Fin (2 * fkIsingExpandingSquareSide k) ->
      Fin (2 * fkIsingExpandingSquareSide k) -> Complex := fun i j =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) i j /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  have hinside := closedBall_subset_finiteCenteredRadialGridDeeperInterior
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) R
    (fkIsingExpandingSquareScale_pos k) hR hwide
  have hf := finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_strictNeighbor
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
    (fkIsingExpandingSquareScale_pos k) value (closedBall 0 R)
    (convex_closedBall 0 R) L hinside hI hJ
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hzs : star z ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hws : star w ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hw
  have h := hf.dist_le_mul (star z) hzs (star w) hws
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, value,
    star_isometry.dist_eq] using h


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_horizontalAdjacent_norm_sub_le_of_neighbor
    (k i j : Nat)
    (hi : i + 2 < 2 * fkIsingExpandingSquareSide k)
    (hj : j + 1 < 2 * fkIsingExpandingSquareSide k)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (hI : forall a b
      (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * L)
    (hJ : forall a b
      (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * L) :
    norm
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          ((starRingEnd Complex)
            (isingCenteredRadialGridCellPoint
              (fkIsingExpandingSquareScale k)
              (fkIsingExpandingSquareSide k) i j x y)) -
        fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          ((starRingEnd Complex)
            (isingCenteredRadialGridCellPoint
              (fkIsingExpandingSquareScale k)
              (fkIsingExpandingSquareSide k) (i + 1) j x' y'))) <=
      (fkIsingExpandingSquareScale k * L) *
        ((1 - x) + x' + |y - y'|) := by
  let value : Fin (2 * fkIsingExpandingSquareSide k) ->
      Fin (2 * fkIsingExpandingSquareSide k) -> Complex := fun a b =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) a b /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  have h :=
    finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
      (fkIsingExpandingSquareScale_pos k).ne' value i j hi hj
      x x' y y' (fkIsingExpandingSquareScale k * L)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      (hI i j (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega))
      (hJ i j (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega))
      (hI (i + 1) j (by omega) (by omega))
      (hI (i + 1) (j + 1) (by omega) (by omega))
      (hJ (i + 2) j (by omega) (by omega))
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, value] using h


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_verticalAdjacent_norm_sub_le_of_neighbor
    (k i j : Nat)
    (hi : i + 1 < 2 * fkIsingExpandingSquareSide k)
    (hj : j + 2 < 2 * fkIsingExpandingSquareSide k)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (hI : forall a b
      (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * L)
    (hJ : forall a b
      (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * L) :
    norm
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          ((starRingEnd Complex)
            (isingCenteredRadialGridCellPoint
              (fkIsingExpandingSquareScale k)
              (fkIsingExpandingSquareSide k) i j x y)) -
        fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          ((starRingEnd Complex)
            (isingCenteredRadialGridCellPoint
              (fkIsingExpandingSquareScale k)
              (fkIsingExpandingSquareSide k) i (j + 1) x' y'))) <=
      (fkIsingExpandingSquareScale k * L) *
        (|x - x'| + (1 - y) + y') := by
  let value : Fin (2 * fkIsingExpandingSquareSide k) ->
      Fin (2 * fkIsingExpandingSquareSide k) -> Complex := fun a b =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) a b /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  have h :=
    finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
      (fkIsingExpandingSquareScale_pos k).ne' value i j hi hj
      x x' y y' (fkIsingExpandingSquareScale k * L)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      (hI i j (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega))
      (hJ i j (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega))
      (hI i (j + 2) (by omega) (by omega))
      (hJ i (j + 1) (by omega) (by omega))
      (hJ (i + 1) (j + 1) (by omega) (by omega))
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, value] using h


end
end StatMech.Universality
