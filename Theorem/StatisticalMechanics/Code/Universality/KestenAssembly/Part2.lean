/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.BXPTransfer.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
import Theorem.StatisticalMechanics.Code.Universality.KestenHalf
import Structure.StatisticalMechanics.Code.Universality.KestenAssembly
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


theorem ka_twoDim_horizontalCrossingEvent_eq (a b : ℤ) :
    TwoDim.horizontalCrossingEvent a b
      = StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
  ext ω
  rw [TwoDim.mem_horizontalCrossingEvent, StatMech.RSW.Box.mem_horizontalCrossingEvent,
    StatMech.RSW.Box.horizontalCrossing_eq_twoDim]


theorem ka_twoDim_verticalCrossingEvent_eq (a b : ℤ) :
    TwoDim.verticalCrossingEvent a b
      = StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := rfl


theorem ka_bxp_half_of_rsw
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure) :
    BoxCrossingProperty halfMeasure 2 := by
  refine ka_bxp_of_box_seed halfMeasure hseed.c_pos ?_ ?_
  · intro n τ
    rw [htinv.horiz τ (2 * (n : ℤ)) (n : ℤ),
      ka_twoDim_horizontalCrossingEvent_eq (2 * (n : ℤ)) (n : ℤ)]
    exact hseed.wide n
  · intro n τ
    rw [htinv.vert τ (n : ℤ) (2 * (n : ℤ)),
      ka_twoDim_verticalCrossingEvent_eq (n : ℤ) (2 * (n : ℤ))]
    exact hseed.tall n


theorem ka_kesten_pc_eq_half
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure)
    
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0)
    
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    
    (hSharpThreshold : ∀ (p : NNReal) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 :=
  kesten_pc_eq_half_of_bxp (ρ := 2) (R := R) (boxFam := boxFam)
    (ka_bxp_half_of_rsw hseed htinv) hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold


theorem ka_kesten_no_percolation_at_pc
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure)
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : NNReal) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 ∧
      percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0 :=
  ⟨ka_kesten_pc_eq_half hseed htinv hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold,
    hCorLowerBound (ka_bxp_half_of_rsw hseed htinv)⟩

end Universality
end StatMech
