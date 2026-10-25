/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalLimit.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLfromHC.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivative
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB StatMech.Probability

noncomputable section

variable {d : Nat}


theorem khc_walshChar_eq_negOnePow_spinProd
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (sigma : ConfigSpace V) :
    khc_walshChar B sigma = (-1 : Real) ^ B.card * spinProd B sigma := by
  unfold khc_walshChar spinProd
  have hsign (x : V) : khc_sign (sigma x) = (-1 : Real) * spin sigma x := by
    unfold khc_sign spin
    split <;> norm_num
  simp_rw [hsign]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem walshChar_torusRestriction
    (A : Finset (Site d)) (B : Finset {x // x ∈ A}) (n : Nat)
    (hinj : Set.InjOn (isingSiteToDyadicTorus n) (↑A : Set (Site d)))
    (sigma : ConfigSpace (IsingDyadicTorus d n)) :
    khc_walshChar B (criticalTorusLocalRestriction A n sigma) =
      (-1 : Real) ^ B.card *
        spinProd ((B.map (Function.Embedding.subtype fun x ↦ x ∈ A)).image
          (isingSiteToDyadicTorus n)) sigma := by
  rw [khc_walshChar_eq_negOnePow_spinProd]
  congr 1
  unfold spinProd criticalTorusLocalRestriction
  rw [Finset.prod_image]
  · rw [Finset.prod_map]
    rfl
  · intro x hx y hy hxy
    apply hinj
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      exact u.2
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hy
      exact u.2
    · exact hxy

theorem walshChar_infiniteRestriction
    (A : Finset (Site d)) (B : Finset {x // x ∈ A})
    (omega : ConfigSpace (Site d)) :
    khc_walshChar B (criticalInfiniteLocalRestriction A omega) =
      (-1 : Real) ^ B.card *
        spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
  rw [khc_walshChar_eq_negOnePow_spinProd]
  congr 1
  unfold spinProd criticalInfiniteLocalRestriction
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro x hx
  unfold spin
  rfl

theorem eventually_injectiveOn_fixedSupport
    (A : Finset (Site d)) :
    ∀ᶠ n in atTop,
      Set.InjOn (isingSiteToDyadicTorus n) (↑A : Set (Site d)) := by
  obtain ⟨R, hAR⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  filter_upwards [eventually_ge_atTop R] with n hn
  have hAn : (↑A : Set (Site d)) ⊆ box d n := hAR.trans (box_mono d hn)
  exact isingSiteToDyadicTorus_injectiveOn_finset A hAn
    (lt_of_lt_of_le (by omega : 2 * n < 2 * (n + 1))
      (two_mul_succ_lt_isingDyadicSide n).le)

set_option maxHeartbeats 800000 in


theorem criticalTorusLocalObservableExpectation_tendsto
    (hd : 2 < d) (A : Finset (Site d))
    (f : ConfigSpace {x // x ∈ A} → Real) :
    Tendsto (criticalTorusLocalObservableExpectation A f) atTop
      (nhds (criticalFreeLocalObservableExpectation A f)) := by
  let c : Finset {x // x ∈ A} → Real := fun B ↦
    khc_fourierCoeff f B * (-1 : Real) ^ B.card
  have htorus : ∀ᶠ n in atTop,
      criticalTorusLocalObservableExpectation A f n =
        ∑ B : Finset {x // x ∈ A},
          c B * criticalTorusLocalSpinProd d
            (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) n := by
    filter_upwards [eventually_injectiveOn_fixedSupport A] with n hinj
    unfold criticalTorusLocalObservableExpectation
    have hpoint (sigma : ConfigSpace (IsingDyadicTorus d n)) :
        f (criticalTorusLocalRestriction A n sigma) =
          ∑ B : Finset {x // x ∈ A},
            c B * spinProd
              ((B.map (Function.Embedding.subtype fun x ↦ x ∈ A)).image
                (isingSiteToDyadicTorus n)) sigma := by
      rw [← khc_fourier_expansion f (criticalTorusLocalRestriction A n sigma)]
      apply Finset.sum_congr rfl
      intro B _
      rw [walshChar_torusRestriction A B n hinj sigma]
      dsimp [c]
      ring
    simp_rw [hpoint]
    rw [expJ_sum]
    apply Finset.sum_congr rfl
    intro B _
    rw [expJ_const_mul]
    rfl
  have hsum : Tendsto
      (fun n ↦ ∑ B : Finset {x // x ∈ A},
        c B * criticalTorusLocalSpinProd d
          (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) n)
      atTop
      (nhds (∑ B : Finset {x // x ∈ A},
        c B * ∫ omega,
          spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
            ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
              Measure (ConfigSpace (Site d))))) := by
    apply tendsto_finsetSum
    intro B hB
    exact (criticalTorusLocalSpinProd_tendsto hd
      (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))).const_mul (c B)
  have hlimit : (∑ B : Finset {x // x ∈ A},
      c B * ∫ omega,
        spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
          ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
            Measure (ConfigSpace (Site d)))) =
      criticalFreeLocalObservableExpectation A f := by
    unfold criticalFreeLocalObservableExpectation
    have hpoint (omega : ConfigSpace (Site d)) :
        f (criticalInfiniteLocalRestriction A omega) =
          ∑ B : Finset {x // x ∈ A},
            c B * spinProd
              (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
      rw [← khc_fourier_expansion f (criticalInfiniteLocalRestriction A omega)]
      apply Finset.sum_congr rfl
      intro B _
      rw [walshChar_infiniteRestriction A B omega]
      dsimp [c]
      ring
    simp_rw [hpoint]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_const_mul]
    · intro B hB
      exact ((spinProdBCF d
        (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))).integrable _).const_mul (c B)
  rw [← hlimit]
  exact hsum.congr' (htorus.mono fun n hn ↦ hn.symm)

set_option maxHeartbeats 800000 in


theorem criticalTorusLocalObservableExpectation_tendsto_varying
    (hd : 2 < d) (A : Finset (Site d))
    (f : Nat → ConfigSpace {x // x ∈ A} → Real)
    (limit : ConfigSpace {x // x ∈ A} → Real)
    (hf : ∀ sigma, Tendsto (fun n ↦ f n sigma) atTop (nhds (limit sigma))) :
    Tendsto (fun n ↦ criticalTorusLocalObservableExpectation A (f n) n)
      atTop (nhds (criticalFreeLocalObservableExpectation A limit)) := by
  let c : Nat → Finset {x // x ∈ A} → Real := fun n B ↦
    khc_fourierCoeff (f n) B * (-1 : Real) ^ B.card
  let cLimit : Finset {x // x ∈ A} → Real := fun B ↦
    khc_fourierCoeff limit B * (-1 : Real) ^ B.card
  have hc (B : Finset {x // x ∈ A}) :
      Tendsto (fun n ↦ c n B) atTop (nhds (cLimit B)) := by
    unfold c cLimit khc_fourierCoeff bnt_uexp
    apply Tendsto.mul_const
    apply Tendsto.div_const
    apply tendsto_finsetSum
    intro sigma hsigma
    exact (hf sigma).mul_const (khc_walshChar B sigma)
  have htorus : ∀ᶠ n in atTop,
      criticalTorusLocalObservableExpectation A (f n) n =
        ∑ B : Finset {x // x ∈ A},
          c n B * criticalTorusLocalSpinProd d
            (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) n := by
    filter_upwards [eventually_injectiveOn_fixedSupport A] with n hinj
    unfold criticalTorusLocalObservableExpectation
    have hpoint (sigma : ConfigSpace (IsingDyadicTorus d n)) :
        f n (criticalTorusLocalRestriction A n sigma) =
          ∑ B : Finset {x // x ∈ A},
            c n B * spinProd
              ((B.map (Function.Embedding.subtype fun x ↦ x ∈ A)).image
                (isingSiteToDyadicTorus n)) sigma := by
      rw [← khc_fourier_expansion (f n)
        (criticalTorusLocalRestriction A n sigma)]
      apply Finset.sum_congr rfl
      intro B _
      rw [walshChar_torusRestriction A B n hinj sigma]
      dsimp [c]
      ring
    simp_rw [hpoint]
    rw [expJ_sum]
    apply Finset.sum_congr rfl
    intro B _
    rw [expJ_const_mul]
    rfl
  have hsum : Tendsto
      (fun n ↦ ∑ B : Finset {x // x ∈ A},
        c n B * criticalTorusLocalSpinProd d
          (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) n)
      atTop
      (nhds (∑ B : Finset {x // x ∈ A},
        cLimit B * ∫ omega,
          spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
            ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
              Measure (ConfigSpace (Site d))))) := by
    apply tendsto_finsetSum
    intro B hB
    exact (hc B).mul (criticalTorusLocalSpinProd_tendsto hd
      (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)))
  have hlimit : (∑ B : Finset {x // x ∈ A},
      cLimit B * ∫ omega,
        spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
          ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
            Measure (ConfigSpace (Site d)))) =
      criticalFreeLocalObservableExpectation A limit := by
    unfold criticalFreeLocalObservableExpectation
    have hpoint (omega : ConfigSpace (Site d)) :
        limit (criticalInfiniteLocalRestriction A omega) =
          ∑ B : Finset {x // x ∈ A},
            cLimit B * spinProd
              (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
      rw [← khc_fourier_expansion limit
        (criticalInfiniteLocalRestriction A omega)]
      apply Finset.sum_congr rfl
      intro B _
      rw [walshChar_infiniteRestriction A B omega]
      dsimp [cLimit]
      ring
    simp_rw [hpoint]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_const_mul]
    · intro B hB
      exact ((spinProdBCF d
        (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))).integrable _).const_mul
          (cLimit B)
  rw [← hlimit]
  exact hsum.congr' (htorus.mono fun n hn ↦ hn.symm)


end
end StatMech.FrontierA
