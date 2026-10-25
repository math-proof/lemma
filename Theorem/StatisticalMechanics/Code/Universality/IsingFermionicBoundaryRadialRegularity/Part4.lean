/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryRadialPatchDeepVariation_nonneg
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) :
    0 ≤ fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r := by
  unfold fkIsingSquareBoundaryRadialPatchDeepVariation
  positivity


theorem fkIsingSquareBoundaryRadialPatchDeepVariation_le
    (n m r : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hr : 0 < r) :
    fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r ≤
      16 * (m : Real) ^ 2 / (r : Real) := by
  let Vp : Real :=
    ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm d.snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm d.fst|
  let Vd : Real :=
    ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2 d.snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2 d.fst|
  have hVp0 : 0 ≤ Vp := by
    dsimp only [Vp]
    positivity
  have hVd0 : 0 ≤ Vd := by
    dsimp only [Vd]
    positivity
  have hscaledVp0 : 0 ≤ (1 / (m : Real)) * Vp := by positivity
  have hscaledVd0 : 0 ≤ (1 / (m : Real)) * Vd := by positivity
  have htarget0 : 0 ≤ 8 * (m : Real) / (r : Real) := by positivity
  have hVpSq : ((1 / (m : Real)) * Vp) ^ 2 ≤
      (8 * (m : Real) / (r : Real)) ^ 2 := by
    calc
      _ ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 :=
        fkIsingSquareBoundaryRadialPatchPrimal_physicalDeepVariation_sq_le
          n m hn hm hm2 r hr
      _ = _ := by ring
  have hVdSq : ((1 / (m : Real)) * Vd) ^ 2 ≤
      (8 * (m : Real) / (r : Real)) ^ 2 := by
    calc
      _ ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 :=
        fkIsingSquareBoundaryRadialPatchDual_physicalDeepVariation_sq_le
          n m hn hm hm2 r hr
      _ = _ := by ring
  have hVpScaled : (1 / (m : Real)) * Vp ≤
      8 * (m : Real) / (r : Real) :=
    (sq_le_sq₀ hscaledVp0 htarget0).mp hVpSq
  have hVdScaled : (1 / (m : Real)) * Vd ≤
      8 * (m : Real) / (r : Real) :=
    (sq_le_sq₀ hscaledVd0 htarget0).mp hVdSq
  have hm0 : (m : Real) ≠ 0 := by positivity
  have hVp : Vp ≤ 8 * (m : Real) ^ 2 / (r : Real) := by
    calc
      Vp = (m : Real) * ((1 / (m : Real)) * Vp) := by field_simp
      _ ≤ (m : Real) * (8 * (m : Real) / (r : Real)) := by gcongr
      _ = _ := by ring
  have hVd : Vd ≤ 8 * (m : Real) ^ 2 / (r : Real) := by
    calc
      Vd = (m : Real) * ((1 / (m : Real)) * Vd) := by field_simp
      _ ≤ (m : Real) * (8 * (m : Real) / (r : Real)) := by gcongr
      _ = _ := by ring
  change Vp + Vd ≤ _
  calc
    Vp + Vd ≤ 8 * (m : Real) ^ 2 / (r : Real) +
        8 * (m : Real) ^ 2 / (r : Real) := add_le_add hVp hVd
    _ = 16 * (m : Real) ^ 2 / (r : Real) := by ring


theorem fkIsingSquareBoundaryRadialPatch_deepCell_physicalNormalized_energy_le
    (n m : Nat) (mesh : Real) (hn : 0 < n) (hm : m ≤ n)
    (hm2 : 2 ≤ m) (hmesh : 0 < mesh) (r : Nat) :
    mesh ^ 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh * fkIsingSquareBoundaryRadialPatchDeepVariation
        n m hn hm hm2 r := by
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  have hraw :=
    fkIsingSquareBoundaryRadialPatch_deepCell_normSq_sum_le_variation
      n m hn hm hm2 r
  simp_rw [hnorm]
  rw [← Finset.sum_div]
  calc
    mesh ^ 2 *
        ((∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) / (2 * mesh)) =
      mesh / 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩) := by
        field_simp
    _ ≤ mesh / 2 *
        (2 * fkIsingSquareBoundaryRadialPatchDeepVariation
          n m hn hm hm2 r) :=
      mul_le_mul_of_nonneg_left (by
        simpa [fkIsingSquareBoundaryRadialPatchDeepVariation] using hraw)
        (by positivity)
    _ = _ := by ring


theorem fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_energy_le
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
    mesh ^ 2 *
        ∑ p : IsingLeapfrogBox R,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservableWindow
                n m baseI baseJ R hn hm hfitI hfitJ p /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh * fkIsingSquareBoundaryRadialPatchDeepVariation
        n m hn hm hm2 r := by
  have hwindow :=
    fkIsingSquareBoundaryRadialPatchNormalizedWindow_energy_le_deepCell
      n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ r hdeep
  have hscaled := mul_le_mul_of_nonneg_left hwindow (sq_nonneg mesh)
  have hdeepEnergy :=
    fkIsingSquareBoundaryRadialPatch_deepCell_physicalNormalized_energy_le
      n m mesh hn hm hm2 hmesh r
  exact hscaled.trans hdeepEnergy


theorem fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_diffusive
    (n m baseI baseJ R rho : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    mesh ^ 2 * Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
          fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)) ≤
      (1032080 / (rho : Real) ^ 3) * mesh *
        fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r := by
  have hgradient :=
    fkIsingSquareBoundaryRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive
      n m baseI baseJ R rho mesh hn hm hfitI hfitJ hmesh
      p p' hrho hp hp' hpp'
  have henergy :=
    fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_energy_le
      n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ hmesh r hdeep
  have hfactor : 0 ≤ 1032080 / (rho : Real) ^ 3 := by positivity
  calc
    _ ≤ mesh ^ 2 *
        ((1032080 / (rho : Real) ^ 3) *
          ∑ q : IsingLeapfrogBox R,
            Complex.normSq
              (fkIsingSquareBoundaryRadialPatchFullObservableWindow
                  n m baseI baseJ R hn hm hfitI hfitJ q /
                (Real.sqrt (2 * mesh) : Complex))) :=
      mul_le_mul_of_nonneg_left hgradient (sq_nonneg mesh)
    _ = (1032080 / (rho : Real) ^ 3) *
        (mesh ^ 2 *
          ∑ q : IsingLeapfrogBox R,
            Complex.normSq
              (fkIsingSquareBoundaryRadialPatchFullObservableWindow
                  n m baseI baseJ R hn hm hfitI hfitJ q /
                (Real.sqrt (2 * mesh) : Complex))) := by ring
    _ ≤ (1032080 / (rho : Real) ^ 3) *
        (mesh * fkIsingSquareBoundaryRadialPatchDeepVariation
          n m hn hm hm2 r) := mul_le_mul_of_nonneg_left henergy hfactor
    _ = _ := by ring


theorem fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
    (n m baseI baseJ R rho : Nat) (mesh d H V : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r ≤ V)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hradius : d ≤ mesh * (rho : Real))
    (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    ‖fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p /
          (Real.sqrt (2 * mesh) : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p' /
          (Real.sqrt (2 * mesh) : Complex)‖ ≤ mesh * H := by
  let F := fun q : IsingLeapfrogBox R ↦
    fkIsingSquareBoundaryRadialPatchFullObservableWindow
      n m baseI baseJ R hn hm hfitI hfitJ q /
        (Real.sqrt (2 * mesh) : Complex)
  have hdiff : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * mesh *
        fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r := by
    simpa [F] using
      fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_diffusive
        n m baseI baseJ R rho mesh hn hm hm2 hfitI hfitJ hmesh r
        hdeep p p' hrho hp hp' hpp'
  have hfactor : 0 ≤ (1032080 / (rho : Real) ^ 3) * mesh := by positivity
  have hdiffV : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * mesh * V :=
    hdiff.trans (mul_le_mul_of_nonneg_left hV hfactor)
  have hrhoReal : 0 < (rho : Real) := by positivity
  have hradiusPow : d ^ 3 ≤ (mesh * (rho : Real)) ^ 3 :=
    pow_le_pow_left₀ hd hradius 3
  have hscale' : 1032080 * V ≤
      H ^ 2 * (mesh * (rho : Real)) ^ 3 :=
    hscale.trans (mul_le_mul_of_nonneg_left hradiusPow (sq_nonneg H))
  have hdiv : 1032080 * V / (rho : Real) ^ 3 ≤ H ^ 2 * mesh ^ 3 := by
    apply (div_le_iff₀ (pow_pos hrhoReal 3)).2
    calc
      1032080 * V ≤ H ^ 2 * (mesh * (rho : Real)) ^ 3 := hscale'
      _ = (H ^ 2 * mesh ^ 3) * (rho : Real) ^ 3 := by ring
  have hrhs : (1032080 / (rho : Real) ^ 3) * mesh * V ≤
      mesh ^ 4 * H ^ 2 := by
    calc
      (1032080 / (rho : Real) ^ 3) * mesh * V =
          mesh * (1032080 * V / (rho : Real) ^ 3) := by ring
      _ ≤ mesh * (H ^ 2 * mesh ^ 3) :=
        mul_le_mul_of_nonneg_left hdiv hmesh.le
      _ = mesh ^ 4 * H ^ 2 := by ring
  have hfinal : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      mesh ^ 4 * H ^ 2 := hdiffV.trans hrhs
  have hmult : mesh ^ 2 * ‖F p - F p'‖ ^ 2 ≤
      mesh ^ 2 * (mesh * H) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hfinal.trans_eq (by ring)
  have hsquare : ‖F p - F p'‖ ^ 2 ≤ (mesh * H) ^ 2 :=
    le_of_mul_le_mul_left hmult (pow_pos hmesh 2)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hmesh.le hH)).mp hsquare


theorem fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_halfScale
    (n m baseI baseJ R rho r : Nat)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hr : 0 < r)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hmr : m ≤ 2 * r) (hmrho : m ≤ 2 * rho)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    ‖fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p /
          (Real.sqrt (2 * (1 / (m : Real))) : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p' /
          (Real.sqrt (2 * (1 / (m : Real))) : Complex)‖ ≤
      (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real)) := by
  have hmpos : 0 < (m : Real) := by positivity
  have hmesh : 0 < 1 / (m : Real) := by positivity
  have hV : fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r ≤ 32 * (m : Real) := by
    calc
      _ ≤ 16 * (m : Real) ^ 2 / (r : Real) :=
        fkIsingSquareBoundaryRadialPatchDeepVariation_le
          n m r hn hm hm2 hr
      _ ≤ 32 * (m : Real) := by
        apply (div_le_iff₀ (by positivity : (0 : Real) < r)).2
        have hmr' : (m : Real) ≤ 2 * (r : Real) := by exact_mod_cast hmr
        nlinarith
  have hradius : (1 / 2 : Real) ≤
      (1 / (m : Real)) * (rho : Real) := by
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hmpos).2
    have hmrho' : (m : Real) ≤ 2 * (rho : Real) := by exact_mod_cast hmrho
    linarith
  have hH : 0 ≤ Real.sqrt (264212480 * (m : Real)) :=
    Real.sqrt_nonneg _
  have hscale :
      1032080 * (32 * (m : Real)) ≤
        Real.sqrt (264212480 * (m : Real)) ^ 2 * (1 / 2 : Real) ^ 3 := by
    rw [Real.sq_sqrt (by positivity)]
    norm_num
    ring_nf
    rfl
  exact
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
      n m baseI baseJ R rho (1 / (m : Real)) (1 / 2)
      (Real.sqrt (264212480 * (m : Real))) (32 * (m : Real))
      hn hm hm2 hfitI hfitJ hmesh r hdeep hV (by norm_num) hH
      hradius hscale p p' hrho hp hp' hpp'

end
end StatMech.Universality
