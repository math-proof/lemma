import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.KestenAssembly.Part2
open MeasureTheory Set Filter Topology StatMech StatMech.Universality


/--
[ka_rsw_strip_glue_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_rsw_strip_glue_extend_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
  {cL cV cR : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d)
  (hL : cL ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a m' c d))
  (hV : cV ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent m m' c d))
  (hR : cR ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent m b c d))
  (hcV0 : 0 ≤ cV)
  (hcR0 : 0 ≤ cR) :
-- imply
  cL * cV * cR ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.ka_rsw_strip_glue_extend μ hpa ham hmm' hm'b hamL hmbR hcd hL hV hR hcV0 hcR0

/--
[ka_wide_box_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_wide_box_extend_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {cW cS : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 < n)
  (hcW0 : 0 ≤ cW)
  (hcS0 : 0 ≤ cS)
  (hW1 : cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (2 * n) 0 n))
  (hW2 : cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent n (3 * n) 0 n))
  (hS : cS ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent n (2 * n) 0 n)) :
-- imply
  cW * cS * cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (3 * n) 0 n) := by
-- proof
  apply StatMech.Universality.ka_wide_box_extend μ hpa hn hcW0 hcS0 hW1 hW2 hS

/--
[ka_floor_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_floor_two_mul_eq
  {n : ℕ} :
-- imply
  ⌊(2 : ℝ) * (n : ℝ)⌋ = (2 * n : ℤ) := by
-- proof
  apply StatMech.Universality.ka_floor_two_mul n

/--
[ka_bxp_of_box_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_bxp_of_box_seed_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {c : ℝ}
-- given
  (hc : 0 < c)
  (hH : ∀ (n : ℕ) (τ : Site 2), c ≤ μ.real (translatedHorizontalCrossingEvent τ (2 * (n : ℤ)) (n : ℤ)))
  (hV : ∀ (n : ℕ) (τ : Site 2), c ≤ μ.real (translatedVerticalCrossingEvent τ (n : ℤ) (2 * (n : ℤ)))) :
-- imply
  BoxCrossingProperty μ 2 := by
-- proof
  apply StatMech.Universality.ka_bxp_of_box_seed μ hc hH hV

/--
[ka_twoDim_horizontalCrossingEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_twoDim_horizontalCrossingEvent_eq_eq
  {a b : ℤ} :
-- imply
  TwoDim.horizontalCrossingEvent a b = StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
-- proof
  apply StatMech.Universality.ka_twoDim_horizontalCrossingEvent_eq a b

/--
[ka_twoDim_verticalCrossingEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_twoDim_verticalCrossingEvent_eq_eq
  {a b : ℤ} :
-- imply
  TwoDim.verticalCrossingEvent a b = StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := by
-- proof
  apply StatMech.Universality.ka_twoDim_verticalCrossingEvent_eq a b

/--
[ka_bxp_half_of_rsw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_bxp_half_of_rsw_eq
-- given
  (hseed : KaSelfDualBoxSeed halfMeasure)
  (htinv : KaCrossingTranslationInvariant halfMeasure) :
-- imply
  BoxCrossingProperty halfMeasure 2 := by
-- proof
  apply StatMech.Universality.ka_bxp_half_of_rsw hseed htinv

/--
[ka_kesten_pc_eq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_kesten_pc_eq_half_eq
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hseed : KaSelfDualBoxSeed halfMeasure)
  (htinv : KaCrossingTranslationInvariant halfMeasure)
  (hCorLowerBound : BoxCrossingProperty halfMeasure 2 → percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0)
  (hHm : ∀ n, MeasurableSet (boxFam n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
  (hSharpThreshold : ∀ (p : NNReal) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 → Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
-- imply
  criticalProbability 2 = 1 / 2 := by
-- proof
  apply StatMech.Universality.ka_kesten_pc_eq_half hseed htinv hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold

/--
[ka_kesten_no_percolation_at_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean)
-/
@[path]
private lemma ka_kesten_no_percolation_at_pc_eq
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hseed : KaSelfDualBoxSeed halfMeasure)
  (htinv : KaCrossingTranslationInvariant halfMeasure)
  (hCorLowerBound : BoxCrossingProperty halfMeasure 2 → percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0)
  (hHm : ∀ n, MeasurableSet (boxFam n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
  (hSharpThreshold : ∀ (p : NNReal) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 → Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
-- imply
  criticalProbability 2 = 1 / 2 ∧ percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0 := by
-- proof
  apply StatMech.Universality.ka_kesten_no_percolation_at_pc hseed htinv hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold


-- created on 2026-10-23
