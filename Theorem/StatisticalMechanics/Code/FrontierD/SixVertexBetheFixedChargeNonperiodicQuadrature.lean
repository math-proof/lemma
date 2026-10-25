/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeNonperiodicQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTestQuadrature
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sum_cyclicRootPartition_eq_sum_roots_add_boundary
    {n : Nat} (p : Fin (n + 1) -> Real) (f : Real -> Real) :
    (∑ k ∈ range (n + 1), f (sixVertexCyclicRootPartition p k)) =
      (∑ j, f (p j)) +
        f (p (Fin.last n) - 2 * Real.pi) - f (p (Fin.last n)) := by
  rw [Finset.sum_range_succ', sixVertexCyclicRootPartition_zero]
  have hmid :
      (∑ k ∈ range n, f (sixVertexCyclicRootPartition p (k + 1))) =
        ∑ j : Fin n, f (p j.castSucc) := by
    apply Finset.sum_bij
      (fun k hk => ⟨k, Finset.mem_range.mp hk⟩ :
        (k : Nat) -> k ∈ Finset.range n -> Fin n)
    · intro k hk
      exact Finset.mem_univ _
    · intro a ha b hb hab
      exact congrArg Fin.val hab
    · intro j _
      refine ⟨j.val, Finset.mem_range.mpr j.isLt, ?_⟩
      exact Fin.ext rfl
    · intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      rw [sixVertexCyclicRootPartition_succ p hklt.le]
      rfl
  rw [hmid, Fin.sum_univ_castSucc]
  ring

theorem abs_intervalIntegral_le_const_mul_length
    {f : Real -> Real} {a b H : Real} (hab : a <= b)
    (hbound : forall x, |f x| <= H) :
    |∫ x in a..b, f x| <= H * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := H) (f := f) (fun x _ => by
      simpa only [Real.norm_eq_abs] using hbound x)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h


theorem abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x,
      lower <= sixVertexFiniteRootDensity c N (n + 1) p x)
    {f : Real -> Real} {C : NNReal} {F : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hfBound : forall x, |f x| <= F) :
    |(∑ j, f (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c N (n + 1) p y| <=
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
          ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
            (2 * Real.pi) +
        (2 * (r : Real) / N) * F +
        2 * F / N +
        sixVertexFiniteRootDensityUniformBound c * F *
          ((2 * (r : Real) + 1) / ((N : Real) * lower)) := by
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  let a := p (Fin.last n) - 2 * Real.pi
  let b := p (Fin.last n)
  let mesh := (2 * (r : Real) + 1) / ((N : Real) * lower)
  let U := (∑ j, f (p j)) / (N : Real)
  let V := ∑ k ∈ range (n + 1),
    (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k)
  let Ic := ∫ y in a..b, f y * rho y
  let I := ∫ y in -Real.pi..Real.pi, f y * rho y
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hF : 0 <= F := (abs_nonneg (f 0)).trans (hfBound 0)
  have hB : 0 <= sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hmesh : 0 <= mesh := by
    dsimp [mesh]
    positivity
  have hmeshBound := sixVertexCyclicRootPartition_mesh_fixedCharge
    hc hN hcharge hopen hsol hlower hdensity
  have hquad :=
    abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_fixedCharge
      hc hN hcharge hopen hsol hmeshBound hf hlip hfBound
  have hquad' : |V - Ic| <=
      (C : Real) * sixVertexFiniteRootDensityUniformBound c * mesh *
          (2 * Real.pi) + (2 * (r : Real) / N) * F := by
    simpa [V, Ic, a, b, mesh, sixVertexCyclicRootPartition_zero,
      sixVertexCyclicRootPartition_end] using hquad
  have hsymm : p 0 = -p (Fin.last n) := by
    simpa using hopen.2.1 (Fin.last n)
  have hbpi : b < Real.pi := by
    dsimp [b]
    exact (hopen.2.2 (Fin.last n)).2
  have hapi : a < -Real.pi := by
    dsimp [a]
    linarith [hbpi]
  have hgap : 2 * (Real.pi - b) <= mesh := by
    have hboundary := hmeshBound 0 (by omega)
    rw [sixVertexCyclicRootPartition_zero,
      sixVertexCyclicRootPartition_succ p (Nat.zero_le n)] at hboundary
    dsimp [a, b, mesh] at hboundary ⊢
    rw [hsymm] at hboundary
    linarith
  have hrhoCont : Continuous rho :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have hgCont : Continuous (fun y => f y * rho y) := hf.mul hrhoCont
  have hgBound : forall y,
      |f y * rho y| <= sixVertexFiniteRootDensityUniformBound c * F := by
    intro y
    rw [abs_mul]
    calc
      |f y| * |rho y| <= F * sixVertexFiniteRootDensityUniformBound c :=
        mul_le_mul (hfBound y)
          (abs_sixVertexFiniteRootDensity_le hc hN (by omega) p y)
          (abs_nonneg _) hF
      _ = sixVertexFiniteRootDensityUniformBound c * F := mul_comm _ _
  have hleft := abs_intervalIntegral_le_const_mul_length
    hapi.le hgBound
  have hright := abs_intervalIntegral_le_const_mul_length
    hbpi.le hgBound
  have hIcI : |Ic - I| <=
      sixVertexFiniteRootDensityUniformBound c * F * mesh := by
    have hsplitC := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (b := -Real.pi)
      (hgCont.intervalIntegrable a (-Real.pi))
      (hgCont.intervalIntegrable (-Real.pi) b)
    have hsplitI := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (b := b)
      (hgCont.intervalIntegrable (-Real.pi) b)
      (hgCont.intervalIntegrable b Real.pi)
    have hid : Ic - I =
        (∫ y in a..-Real.pi, f y * rho y) -
          ∫ y in b..Real.pi, f y * rho y := by
      dsimp [Ic, I]
      rw [← hsplitC, ← hsplitI]
      ring
    rw [hid]
    calc
      _ <= |∫ y in a..-Real.pi, f y * rho y| +
          |∫ y in b..Real.pi, f y * rho y| := abs_sub _ _
      _ <= (sixVertexFiniteRootDensityUniformBound c * F) *
              (-Real.pi - a) +
            (sixVertexFiniteRootDensityUniformBound c * F) *
              (Real.pi - b) := add_le_add hleft hright
      _ = sixVertexFiniteRootDensityUniformBound c * F *
            (2 * (Real.pi - b)) := by
          dsimp [a]
          ring
      _ <= sixVertexFiniteRootDensityUniformBound c * F * mesh := by
          exact mul_le_mul_of_nonneg_left hgap (mul_nonneg hB hF)
  have hVU : |V - U| <= 2 * F / N := by
    have hsum := sum_cyclicRootPartition_eq_sum_roots_add_boundary p f
    have hdiff : V - U =
        (f a - f b) / (N : Real) := by
      dsimp [V, U, a, b]
      rw [← Finset.mul_sum, hsum]
      ring
    rw [hdiff, abs_div, abs_of_pos hNreal]
    calc
      |f a - f b| / (N : Real) <=
          (|f a| + |f b|) / (N : Real) :=
        div_le_div_of_nonneg_right (abs_sub _ _) hNreal.le
      _ <= (F + F) / (N : Real) :=
        div_le_div_of_nonneg_right
          (add_le_add (hfBound a) (hfBound b)) hNreal.le
      _ = 2 * F / (N : Real) := by ring
  change |U - I| <= _
  calc
    |U - I| = |-(V - U) + (V - Ic) + (Ic - I)| := by ring_nf
    _ <= |V - U| + |V - Ic| + |Ic - I| := by
      calc
        _ <= |-(V - U)| + |V - Ic| + |Ic - I| :=
          (abs_add_three _ _ _)
        _ = _ := by rw [abs_neg]
    _ <= 2 * F / N +
          ((C : Real) * sixVertexFiniteRootDensityUniformBound c * mesh *
            (2 * Real.pi) + (2 * (r : Real) / N) * F) +
          sixVertexFiniteRootDensityUniformBound c * F * mesh :=
      add_le_add (add_le_add hVU hquad') hIcI
    _ = _ := by
      dsimp [mesh]
      ring

end
end StatMech.FrontierD
