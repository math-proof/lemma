/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorVanishing.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Def.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing
open Filter MeasureTheory Set Topology Function
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

theorem eventIndicator_mem_Icc {Omega : Type*} (A : Set Omega) (x : Omega) :
    eventIndicator A x ∈ Set.Icc (0 : Real) 1 := by
  by_cases hx : x ∈ A <;> simp [eventIndicator, hx]

theorem eventBirkhoffAverage_mem_Icc {Omega : Type*}
    (T : Omega → Omega) (A : Set Omega) (n : Nat) (x : Omega) :
    birkhoffAverage Real T (eventIndicator A) n x ∈ Set.Icc (0 : Real) 1 := by
  rcases n with _ | n
  · simp [birkhoffAverage]
  · have hterm : ∀ k ∈ Finset.range (n + 1),
        eventIndicator A (T^[k] x) ∈ Set.Icc (0 : Real) 1 :=
      fun k hk => eventIndicator_mem_Icc A _
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range (n + 1),
        eventIndicator A (T^[k] x) :=
      Finset.sum_nonneg fun k hk => (hterm k hk).1
    have hsum1 : (∑ k ∈ Finset.range (n + 1),
        eventIndicator A (T^[k] x)) ≤ (n + 1 : Real) := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (n + 1), (1 : Real) :=
          Finset.sum_le_sum fun k hk => (hterm k hk).2
        _ = (n + 1 : Real) := by simp
    simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
    norm_num [Nat.cast_add, Nat.cast_one] at hsum1 ⊢
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (by positivity)) hsum0
    · calc
        (n + 1 : Real)⁻¹ *
            (∑ k ∈ Finset.range (n + 1), eventIndicator A (T^[k] x)) ≤
            (n + 1 : Real)⁻¹ * (n + 1 : Real) :=
          mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr (by positivity))
        _ = 1 := inv_mul_cancel₀ (by positivity)

theorem freeInfiniteVolume_eventPairCorrelationAverage_tendsto
    (hd : 1 ≤ d) {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A B : Set (ConfigSpace (Sym2 (Site d))))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
        mu.real (A ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' B))
      atTop (nhds (mu.real A * mu.real B)) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  let T := (shift (FK.freeAxisTranslation hd) :
    ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
  have herg : _root_.Ergodic T mu :=
    FK.freeInfiniteVolume_axisShift_ergodic hd hp hp1
  have hIA : Integrable (eventIndicator A) mu :=
    (integrable_const (1 : Real)).indicator hA
  have hIB : Integrable (eventIndicator B) mu :=
    (integrable_const (1 : Real)).indicator hB
  have hbirk := StatMech.BirkhoffAE.Ergodic.tendsto_birkhoffAverage_integral_ae
    herg hIB
  let F : Nat → ConfigSpace (Sym2 (Site d)) → Real := fun n omega =>
    eventIndicator A omega * birkhoffAverage Real T (eventIndicator B) n omega
  have hmassB : (∫ x, eventIndicator B x ∂mu) = mu.real B := by
    unfold eventIndicator
    rw [MeasureTheory.integral_indicator_const (1 : Real) hB]
    simp
  have hlim : ∀ᵐ omega ∂mu, Tendsto (fun n => F n omega) atTop
      (nhds (eventIndicator A omega * mu.real B)) := by
    filter_upwards [hbirk] with omega homega
    rw [hmassB] at homega
    exact tendsto_const_nhds.mul homega
  have hmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    exact hIA.aestronglyMeasurable.mul
      (StatMech.BirkhoffAE.aestronglyMeasurable_birkhoffAverage
        herg.toMeasurePreserving hIB n)
  have hbound : ∀ n, ∀ᵐ omega ∂mu, ‖F n omega‖ ≤ (1 : Real) := by
    intro n
    filter_upwards with omega
    have ha := eventIndicator_mem_Icc A omega
    have hb := eventBirkhoffAverage_mem_Icc T B n omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.1 hb.1)]
    exact mul_le_one₀ ha.2 hb.1 hb.2
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := mu) (fun _ => (1 : Real)) hmeas (by fun_prop) hbound hlim
  have hlimit : (∫ omega, eventIndicator A omega * mu.real B ∂mu) =
      mu.real A * mu.real B := by
    unfold eventIndicator
    rw [MeasureTheory.integral_mul_const,
      MeasureTheory.integral_indicator_const (1 : Real) hA]
    simp
  rw [hlimit] at hdct
  apply hdct.congr'
  filter_upwards with n
  have hpoint : (fun omega => F n omega) = fun omega =>
      (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
        eventIndicator (A ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' B) omega := by
    funext omega
    simp only [F, T, birkhoffAverage, birkhoffSum, smul_eq_mul,
      FK.shift_freeAxisTranslationPower]
    calc
      eventIndicator A omega * ((n : Real)⁻¹ *
          ∑ k ∈ Finset.range n, eventIndicator B
            ((shift (FK.freeAxisTranslation hd))^[k] omega)) =
          (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
            (eventIndicator A omega * eventIndicator B
              ((shift (FK.freeAxisTranslation hd))^[k] omega)) := by
        rw [mul_comm (eventIndicator A omega), mul_assoc, Finset.sum_mul]
        conv_lhs => rw [Finset.mul_sum]
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        by_cases ha : omega ∈ A <;>
          by_cases hb : (shift (FK.freeAxisTranslation hd))^[k] omega ∈ B <;>
          simp [eventIndicator, ha, hb]
  rw [hpoint, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    unfold eventIndicator
    rw [MeasureTheory.integral_indicator_const (1 : Real)]
    · simp only [smul_eq_mul, mul_one, mu]
    · exact hA.inter (hB.preimage
        (measurable_shift (FK.freeAxisTranslationPower hd k)))
  · intro k hk
    exact (integrable_const (1 : Real)).indicator
      (hA.inter (hB.preimage
        (measurable_shift (FK.freeAxisTranslationPower hd k))))

theorem markReachableCount_shift_eq
    (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d)) (x : Site d) :
    markReachableCount (hypercubicLattice d) (shift g omega) A x =
      markReachableCount (hypercubicLattice d) omega
        (A.image fun y => g⁻¹ • y) (g⁻¹ • x) := by
  classical
  letI : DecidableRel (openSub (hypercubicLattice d) (shift g omega)).Reachable :=
    Classical.decRel _
  letI : DecidableRel (openSub (hypercubicLattice d) omega).Reachable :=
    Classical.decRel _
  unfold markReachableCount
  apply Finset.card_bij (fun y _ => g⁻¹ • y)
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_image.2 ⟨y, hy.1, rfl⟩, ?_⟩
    simpa only [openSub, openSubgraph, FK.Connected] using
      (connected_shift g omega (g⁻¹ • x) (g⁻¹ • y)).mp (by
        simpa using hy.2)
  · intro a ha b hb hab
    exact MulAction.injective g⁻¹ hab
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨z, hzA, hzy⟩ := Finset.mem_image.1 hy.1
    refine ⟨z, ?_, hzy⟩
    rw [Finset.mem_filter]
    refine ⟨hzA, ?_⟩
    have hconn : Lattice.Connected d omega (g⁻¹ • x) (g⁻¹ • z) := by
      rw [hzy]
      exact hy.2
    have := (connected_shift g omega (g⁻¹ • x) (g⁻¹ • z)).mpr hconn
    simpa using this

theorem allClustersEven_shift_iff
    (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d)) :
    AllClustersEven (hypercubicLattice d) (shift g omega) A ↔
      AllClustersEven (hypercubicLattice d) omega
        (A.image fun x => g⁻¹ • x) := by
  rw [allClustersEven_iff_mark_reachability,
    allClustersEven_iff_mark_reachability]
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [← markReachableCount_shift_eq g omega A x]
    exact h x hx
  · intro h x hx
    rw [markReachableCount_shift_eq g omega A x]
    exact h (g⁻¹ • x) (Finset.mem_image.2 ⟨x, hx, rfl⟩)

theorem preimage_allClustersEvenEvent_shift
    (g : Multiplicative (Site d)) (A : Finset (Site d)) :
    shift g ⁻¹' allClustersEvenEvent (hypercubicLattice d) A =
      allClustersEvenEvent (hypercubicLattice d)
        (A.image fun x => g⁻¹ • x) := by
  ext omega
  exact allClustersEven_shift_iff g omega A

end StatMech.FrontierB
