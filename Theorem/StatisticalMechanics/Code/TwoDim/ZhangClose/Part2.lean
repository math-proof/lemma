/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangLowerBound
import Def.StatisticalMechanics.Code.TwoDim.ZhangClose
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality


theorem zhg_union_of_geometricData {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : ℕ → Set (ConfigSpace E)} (hgeo : ZhangGeometricData μ A B) :
    Tendsto (fun n => μ.real (A n ∪ B n)) atTop (𝓝 1) := by
  
  set S₀ := hgeo.S 0 with hS0
  set S₁ := hgeo.S 1 with hS1
  set S₂ := hgeo.S 2 with hS2
  set S₃ := hgeo.S 3 with hS3
  
  have hsideL : Tendsto (fun n => μ.real (S₀ n)) atTop (𝓝 1) :=
    zhg_side_tendsto_one μ hpa (hgeo.Sinc 0) (hgeo.Sinc 1) (hgeo.Sinc 2) (hgeo.Sinc 3)
      (hgeo.Sm 0) (hgeo.Sm 1) (hgeo.Sm 2) (hgeo.Sm 3)
      (fun n => (hgeo.Ssym 1 n).symm) (fun n => (hgeo.Ssym 2 n).symm)
      (fun n => (hgeo.Ssym 3 n).symm) hgeo.unionTendsto
  
  
  have hsideR : Tendsto (fun n => μ.real (S₁ n)) atTop (𝓝 1) := by
    have hrw : (fun n => μ.real (S₁ n)) = fun n => μ.real (S₀ n) :=
      funext fun n => (hgeo.Ssym 1 n)
    rw [hrw]; exact hsideL
  
  have hinter : Tendsto (fun n => μ.real (S₀ n ∩ S₁ n)) atTop (𝓝 1) :=
    zhg_inter_tendsto_one μ hpa (hgeo.Sinc 0) (hgeo.Sinc 1) hsideL hsideR
  
  exact zhg_union_tendsto_one_of_merge μ (A := A) (B := B) (Err := hgeo.Err)
    (Cap := fun n => S₀ n ∩ S₁ n) hgeo.merge hinter hgeo.errTendsto


theorem zhg_zhangUnion
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (hgeo : ZhangGeometricData halfMeasure A B) :
    BoxCrossingProperty halfMeasure 2 →
      0 < halfMeasure.real (percolationEvent 2) →
      Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1) :=
  fun _ _ => zhg_union_of_geometricData halfMeasure hpa hgeo


theorem zhg_corLowerBound
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (hAinc : ∀ n, IsIncreasing (A n)) (hBinc : ∀ n, IsIncreasing (B n))
    (hBm : ∀ n, MeasurableSet (B n))
    (hHm : ∀ n, MeasurableSet (A n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (A n)ᶜ = (R ∘ dualConfig) ⁻¹' (A n))
    (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
    (hgeo : ZhangGeometricData halfMeasure A B) :
    BoxCrossingProperty halfMeasure 2 →
      percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0 :=
  kzh_corLowerBound hpa hAinc hBinc hBm hHm hRmeas hRpres hdich heq
    (zhg_zhangUnion hpa hgeo)

end TwoDim
end StatMech
