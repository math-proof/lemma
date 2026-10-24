import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.TwoDim.ZhangClose
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[zhg_complUnion_fkg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_complUnion_fkg_four_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B C D : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hC : IsIncreasing C)
  (hD : IsIncreasing D)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B)
  (hCm : MeasurableSet C)
  (hDm : MeasurableSet D) :
-- imply
  (1 - μ.real A) * (1 - μ.real B) * (1 - μ.real C) * (1 - μ.real D) ≤ 1 - μ.real (A ∪ B ∪ C ∪ D) := by
-- proof
  apply StatMech.TwoDim.zhg_complUnion_fkg_four μ hpa hA hB hC hD hAm hBm hCm hDm

/--
[zhg_sqrt_trick_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_sqrt_trick_four_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B C D : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hC : IsIncreasing C)
  (hD : IsIncreasing D)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B)
  (hCm : MeasurableSet C)
  (hDm : MeasurableSet D)
  (hAB : μ.real A = μ.real B)
  (hAC : μ.real A = μ.real C)
  (hAD : μ.real A = μ.real D) :
-- imply
  1 - (1 - μ.real (A ∪ B ∪ C ∪ D)) ^ ((1 : ℝ) / 4) ≤ μ.real A := by
-- proof
  apply StatMech.TwoDim.zhg_sqrt_trick_four μ hpa hA hB hC hD hAm hBm hCm hDm hAB hAC hAD

/--
[zhg_oneSubRpow_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_oneSubRpow_tendsto_one_eq
  {u : ℕ → ℝ}
-- given
  (hu : Tendsto u atTop (𝓝 1)) :
-- imply
  Tendsto (fun n => 1 - (1 - u n) ^ ((1 : ℝ) / 4)) atTop (𝓝 1) := by
-- proof
  apply StatMech.TwoDim.zhg_oneSubRpow_tendsto_one hu

/--
[zhg_side_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_side_tendsto_one_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {S₀ S₁ S₂ S₃ : ℕ → Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (h0inc : ∀ n, IsIncreasing (S₀ n))
  (h1inc : ∀ n, IsIncreasing (S₁ n))
  (h2inc : ∀ n, IsIncreasing (S₂ n))
  (h3inc : ∀ n, IsIncreasing (S₃ n))
  (h0m : ∀ n, MeasurableSet (S₀ n))
  (h1m : ∀ n, MeasurableSet (S₁ n))
  (h2m : ∀ n, MeasurableSet (S₂ n))
  (h3m : ∀ n, MeasurableSet (S₃ n))
  (hsym1 : ∀ n, μ.real (S₀ n) = μ.real (S₁ n))
  (hsym2 : ∀ n, μ.real (S₀ n) = μ.real (S₂ n))
  (hsym3 : ∀ n, μ.real (S₀ n) = μ.real (S₃ n))
  (hunion : Tendsto (fun n => μ.real (S₀ n ∪ S₁ n ∪ S₂ n ∪ S₃ n)) atTop (𝓝 1)) :
-- imply
  Tendsto (fun n => μ.real (S₀ n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.TwoDim.zhg_side_tendsto_one μ hpa h0inc h1inc h2inc h3inc h0m h1m h2m h3m hsym1 hsym2 hsym3 hunion

/--
[zhg_inter_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_inter_tendsto_one_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {L R : ℕ → Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hLinc : ∀ n, IsIncreasing (L n))
  (hRinc : ∀ n, IsIncreasing (R n))
  (hL : Tendsto (fun n => μ.real (L n)) atTop (𝓝 1))
  (hR : Tendsto (fun n => μ.real (R n)) atTop (𝓝 1)) :
-- imply
  Tendsto (fun n => μ.real (L n ∩ R n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.TwoDim.zhg_inter_tendsto_one μ hpa hLinc hRinc hL hR

/--
[zhg_union_tendsto_one_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_union_tendsto_one_of_merge_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B Err Cap : ℕ → Set (ConfigSpace E)}
-- given
  (hsub : ∀ n, Cap n ⊆ (A n ∪ B n) ∪ Err n)
  (hcap : Tendsto (fun n => μ.real (Cap n)) atTop (𝓝 1))
  (herr : Tendsto (fun n => μ.real (Err n)) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => μ.real (A n ∪ B n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.TwoDim.zhg_union_tendsto_one_of_merge μ hsub hcap herr

/--
[zhg_union_of_geometricData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_union_of_geometricData_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B : ℕ → Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hgeo : ZhangGeometricData μ A B) :
-- imply
  Tendsto (fun n => μ.real (A n ∪ B n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.TwoDim.zhg_union_of_geometricData μ hpa hgeo

/--
[zhg_zhangUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_zhangUnion_eq
  {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hgeo : ZhangGeometricData halfMeasure A B) :
-- imply
  BoxCrossingProperty halfMeasure 2 → 0 < halfMeasure.real (percolationEvent 2) → Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.TwoDim.zhg_zhangUnion hpa hgeo

/--
[zhg_corLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean)
-/
@[path]
private lemma zhg_corLowerBound_eq
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
  {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hAinc : ∀ n, IsIncreasing (A n))
  (hBinc : ∀ n, IsIncreasing (B n))
  (hBm : ∀ n, MeasurableSet (B n))
  (hHm : ∀ n, MeasurableSet (A n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (A n)ᶜ = (R ∘ dualConfig) ⁻¹' (A n))
  (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
  (hgeo : ZhangGeometricData halfMeasure A B) :
-- imply
  BoxCrossingProperty halfMeasure 2 → percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.TwoDim.zhg_corLowerBound hpa hAinc hBinc hBm hHm hRmeas hRpres hdich heq hgeo


-- created on 2026-10-23
