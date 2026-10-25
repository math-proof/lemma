/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalAverageAnchor
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part2


namespace StatMech.Universality

open Finset

noncomputable section

theorem fkIsingSquareRadialPatchWindowCarrier_normalized_normSq_le
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (p : IsingLeapfrogBox R) :
    Complex.normSq
        ((fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable
          mesh (fkIsingSquareRadialPatchWindowCarrier
            n m baseI baseJ R hm hfitI hfitJ p)) ≤
      Complex.normSq
        (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ p /
          (Real.sqrt (2 * mesh) : Complex)) := by
  let i : Fin m := ⟨baseI + p.1.1, by have := p.1.2; omega⟩
  let j : Fin m := ⟨baseJ + p.2.1, by have := p.2.2; omega⟩
  let e := fkIsingSquareWiredDirectedTangent n hn
    (.dart (fkIsingSquareRadialPatchEdge n m hm i j, .west))
  let F := fkIsingSquareRadialPatchFullObservable n m hn hm i j
  have he : Complex.normSq e = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [e, fkIsingSquareWiredDirectedTangent, Complex.norm_exp]
  have hproj : Complex.normSq (isingProj e F) ≤ Complex.normSq F := by
    have hpair := isingProj_normSq_add_neg e F he
    have hnonneg := Complex.normSq_nonneg (isingProj (-e) F)
    linarith
  have hobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, .west)) =
        isingProj e F := by
    exact (fkIsingSquareRadialPatchFullObservable_projection
      n m hn hm i j .west).symm
  have hsqrt : 0 < Real.sqrt (2 * mesh) := Real.sqrt_pos.2 (by positivity)
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt, Real.sq_sqrt (by positivity)]
  change Complex.normSq
      ((fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, .west)) /
        (Real.sqrt (2 * mesh) : Complex)) ≤
    Complex.normSq (F / (Real.sqrt (2 * mesh) : Complex))
  rw [hobs, hnorm, hnorm]
  exact div_le_div_of_nonneg_right hproj (by positivity)


theorem fkIsingSquareRadialPatchWindowCarrier_average_normSq_le
    (n m baseI baseJ R r : Nat) (K Q base : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hr : 0 < r)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hmr : (m : Real) ≤ K * (r : Real))
    (hmR : (m : Real) ≤ Q * (R + 1 : Nat))
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hprimalLower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
    (hdualUpper : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
    (∑ a ∈ Finset.univ.map
          (fkIsingSquareRadialPatchWindowCarrierEmbedding
            n m baseI baseJ R hm hfitI hfitJ),
        Complex.normSq
          ((fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable
            (1 / (m : Real)) a)) ≤
      ((Finset.univ.map
          (fkIsingSquareRadialPatchWindowCarrierEmbedding
            n m baseI baseJ R hm hfitI hfitJ)).card : Real) *
        (16 * K * Q ^ 2) := by
  let window := fkIsingSquareRadialPatchWindowCarrierEmbedding
    n m baseI baseJ R hm hfitI hfitJ
  let abstract := fun a : FKIsingSquareWiredCarrier n ↦
    (fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable
      (1 / (m : Real)) a
  let concrete := fun p : IsingLeapfrogBox R ↦ abstract (window p)
  have hmesh : 0 < 1 / (m : Real) := by positivity
  have hpointwise (p : IsingLeapfrogBox R) :
      Complex.normSq (concrete p) ≤
        Complex.normSq
          (fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * (1 / (m : Real))) : Complex)) := by
    exact fkIsingSquareRadialPatchWindowCarrier_normalized_normSq_le
      n m baseI baseJ R (1 / (m : Real)) hn hm hfitI hfitJ hmesh p
  have hfull :=
    fkIsingSquareRadialPatchPhysicalNormalizedWindow_average_normSq_le
      n m baseI baseJ R r K Q base hn hm hm2 hr hfitI hfitJ hK hQ
      hmr hmR hdeep hprimalLower hdualUpper
  have haverage :
      (∑ p : IsingLeapfrogBox R, Complex.normSq (concrete p)) ≤
        (Fintype.card (IsingLeapfrogBox R) : Real) * (16 * K * Q ^ 2) :=
    (Finset.sum_le_sum fun p _ ↦ hpointwise p).trans hfull
  exact finiteWindow_average_normSq_le_of_embedding
    window concrete abstract (16 * K * Q ^ 2) (fun _ ↦ rfl) haverage

end
end StatMech.Universality
