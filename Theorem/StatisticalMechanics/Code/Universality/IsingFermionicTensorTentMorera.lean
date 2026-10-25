/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem complex_wedgeIntegral_tendsto_of_locallyUniform
    {F : Nat -> Complex -> Complex} {f : Complex -> Complex}
    (hF : forall n, Continuous (F n))
    (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ)
    (z w : Complex) :
    Tendsto (fun n => Complex.wedgeIntegral z w (F n)) atTop
      (nhds (Complex.wedgeIntegral z w f)) := by
  have hhorizontal : TendstoUniformlyOn
      (fun n (x : Real) => F n (x + z.im * Complex.I))
      (fun x : Real => f (x + z.im * Complex.I)) atTop
      (Set.uIcc z.re w.re) := by
    have hcomp : TendstoLocallyUniformlyOn
        (fun n (x : Real) => F n (x + z.im * Complex.I))
        (fun x : Real => f (x + z.im * Complex.I)) atTop
        (Set.uIcc z.re w.re) :=
      hlimit.comp (t := Set.uIcc z.re w.re)
        (fun x : Real => x + z.im * Complex.I)
        (fun _ _ => Set.mem_univ _) (by fun_prop)
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_uIcc).mp hcomp
  have hvertical : TendstoUniformlyOn
      (fun n (y : Real) => F n (w.re + y * Complex.I))
      (fun y : Real => f (w.re + y * Complex.I)) atTop
      (Set.uIcc z.im w.im) := by
    have hcomp : TendstoLocallyUniformlyOn
        (fun n (y : Real) => F n (w.re + y * Complex.I))
        (fun y : Real => f (w.re + y * Complex.I)) atTop
        (Set.uIcc z.im w.im) :=
      hlimit.comp (t := Set.uIcc z.im w.im)
        (fun y : Real => w.re + y * Complex.I)
        (fun _ _ => Set.mem_univ _) (by fun_prop)
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_uIcc).mp hcomp
  have hhorizontalContinuous : forall n,
      ContinuousOn (fun x : Real => F n (x + z.im * Complex.I))
        (Set.uIcc z.re w.re) := fun n => by
    exact ((hF n).comp (by fun_prop)).continuousOn
  have hverticalContinuous : forall n,
      ContinuousOn (fun y : Real => F n (w.re + y * Complex.I))
        (Set.uIcc z.im w.im) := fun n => by
    exact ((hF n).comp (by fun_prop)).continuousOn
  have hhorizontalIntegral :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (μ := MeasureTheory.volume)
      (Filter.Eventually.of_forall hhorizontalContinuous) hhorizontal
  have hverticalIntegral :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (μ := MeasureTheory.volume)
      (Filter.Eventually.of_forall hverticalContinuous) hvertical
  simpa [Complex.wedgeIntegral] using hhorizontalIntegral.add
    (hverticalIntegral.const_smul Complex.I)


theorem continuous_wedgeContour (f : Complex -> Complex) (hf : Continuous f) :
    Continuous (fun p : Complex × Complex =>
      Complex.wedgeIntegral p.1 p.2 f +
        Complex.wedgeIntegral p.2 p.1 f) := by
  let H : Real × Real -> Complex := fun p =>
    ∫ x : Real in 0..p.2, f (x + p.1 * Complex.I)
  let V : Real × Real -> Complex := fun p =>
    ∫ y : Real in 0..p.2, f (p.1 + y * Complex.I)
  have hH : Continuous H := by
    dsimp only [H]
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun y x : Real => f (x + y * Complex.I)) (by fun_prop)
  have hV : Continuous V := by
    dsimp only [V]
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun x y : Real => f (x + y * Complex.I)) (by fun_prop)
  have hHorizontal (y a b : Real) :
      (∫ x : Real in a..b, f (x + y * Complex.I)) =
        H (y, b) - H (y, a) := by
    have h0a : IntervalIntegrable (fun x : Real =>
        f (x + y * Complex.I)) MeasureTheory.volume 0 a :=
      (hf.comp (by fun_prop)).intervalIntegrable _ _
    have hab : IntervalIntegrable (fun x : Real =>
        f (x + y * Complex.I)) MeasureTheory.volume a b :=
      (hf.comp (by fun_prop)).intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hab
    dsimp only [H]
    linear_combination hadd
  have hVertical (x a b : Real) :
      (∫ y : Real in a..b, f (x + y * Complex.I)) =
        V (x, b) - V (x, a) := by
    have h0a : IntervalIntegrable (fun y : Real =>
        f (x + y * Complex.I)) MeasureTheory.volume 0 a :=
      (hf.comp (by fun_prop)).intervalIntegrable _ _
    have hab : IntervalIntegrable (fun y : Real =>
        f (x + y * Complex.I)) MeasureTheory.volume a b :=
      (hf.comp (by fun_prop)).intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hab
    dsimp only [V]
    linear_combination hadd
  simp_rw [Complex.wedgeIntegral, hHorizontal, hVertical]
  fun_prop


end
end StatMech.Universality
