/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
import Theorem.StatisticalMechanics.Code.FK.ConvexDerivLimit
import Theorem.StatisticalMechanics.Code.FK.IVPressureConvex.Part5
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Def.StatisticalMechanics.Code.FK.FKPressureDeriv
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fpd_deriv_interchange_of_differentiable {κ : Type*} {l : Filter κ} [l.NeBot]
    (gn : κ → ℝ → ℝ) (g : ℝ → ℝ) (dn : κ → ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (gn i))
    (hderiv : ∀ i t, HasDerivAt (gn i) (dn i t) t)
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x)))
    (t : ℝ) (hg : ConvexOn ℝ univ g)
    (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
    Tendsto (fun i => dn i t) l (𝓝 (pressureRightDeriv g t)) := by
  set L := pressureRightDeriv g t with hL
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hr := cdl_rightDeriv_tendsto_slope hg t
  have hlft := cdl_leftDeriv_tendsto_slope hg t
  rw [hdiff] at hlft
  rw [Metric.tendsto_nhdsWithin_nhds] at hr hlft
  obtain ⟨δr, hδr, hrr⟩ := hr (ε/2) (by linarith)
  obtain ⟨δl, hδl, hll⟩ := hlft (ε/2) (by linarith)
  set y := t + δr/2 with hy
  set z := t - δl/2 with hz
  have hyt : t < y := by rw [hy]; linarith
  have hzt : z < t := by rw [hz]; linarith
  have hsy : slope g t y < L + ε/2 := by
    have hyd : dist y t < δr := by
      rw [Real.dist_eq, hy, show t + δr/2 - t = δr/2 by ring, abs_of_pos (by linarith)]; linarith
    have h2 := hrr (x := y) (by rw [hy]; exact mem_Ioi.mpr (by linarith)) hyd
    rw [Real.dist_eq] at h2
    have := (abs_lt.mp h2).2; linarith
  have hsz : L - ε/2 < slope g z t := by
    have hzd : dist z t < δl := by
      rw [Real.dist_eq, hz, show t - δl/2 - t = -(δl/2) by ring, abs_of_neg (by linarith)]
      linarith
    have h2 := hll (x := z) (by rw [hz]; exact mem_Iio.mpr (by linarith)) hzd
    rw [Real.dist_eq, slope_comm] at h2
    have := (abs_lt.mp h2).1; linarith
  have hslz := cdl_slope_tendsto gn g hlim z t
  have hsly := cdl_slope_tendsto gn g hlim t y
  have hmemz : slope g z t ∈ Ioi (L - ε) := mem_Ioi.mpr (by linarith)
  have hmemy : slope g t y ∈ Iio (L + ε) := mem_Iio.mpr (by linarith)
  have hez : ∀ᶠ i in l, L - ε < slope (gn i) z t := by
    filter_upwards [hslz.eventually (isOpen_Ioi.mem_nhds hmemz)] with i hi; exact hi
  have hey : ∀ᶠ i in l, slope (gn i) t y < L + ε := by
    filter_upwards [hsly.eventually (isOpen_Iio.mem_nhds hmemy)] with i hi; exact hi
  filter_upwards [hez, hey] with i hiz hiy
  have hmem : t ∈ interior (univ : Set ℝ) := by rw [interior_univ]; trivial
  have hr' : derivWithin (gn i) (Ioi t) t = dn i t :=
    ((hderiv i t).hasDerivWithinAt (s := Ioi t)).derivWithin (uniqueDiffWithinAt_Ioi t)
  have hl' : derivWithin (gn i) (Iio t) t = dn i t :=
    ((hderiv i t).hasDerivWithinAt (s := Iio t)).derivWithin (uniqueDiffWithinAt_Iio t)
  have hle1 : slope (gn i) z t ≤ dn i t := by
    have h3 := (hconv i).slope_le_leftDeriv_of_mem_interior (mem_univ z) hmem hzt
    rwa [hl'] at h3
  have hle2 : dn i t ≤ slope (gn i) t y := by
    have h3 := (hconv i).rightDeriv_le_slope_of_mem_interior hmem (mem_univ y) hyt
    rwa [hr'] at h3
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith


theorem fpd_ivPressureDeriv_eq_avgDensity_limit
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : ℕ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (t : ℝ) (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
    Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop (𝓝 (pressureRightDeriv g t)) :=
  fpd_deriv_interchange_of_differentiable
    (fun n => ivp2_tiltFreeEnergy (Gn n) 2) g
    (fun n => fpd_avgDensity (Gn n))
    (fun n => ivp2_tiltFreeEnergy_convexOn (Gn n) 2 (by norm_num) (hE n))
    (fun n s => fpd_tiltFreeEnergy_deriv_eq_avgDensity (Gn n) (hE n) s)
    hlim t hg hdiff


end FK
end StatMech
