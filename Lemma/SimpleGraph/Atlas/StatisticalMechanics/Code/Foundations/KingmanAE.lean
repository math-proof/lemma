import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.KingmanAE.Part4
open MeasureTheory Filter Topology StatMech StatMech.KingmanAE


/--
[ae_all_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma ae_all_subadditive_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, ∀ m n, X (m + n) x ≤ X m x + X n (T^[m] x) := by
-- proof
  apply StatMech.KingmanAE.ae_all_subadditive h

/--
[ae_le_block_birkhoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma ae_le_block_birkhoffSum_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, ∀ k q, 1 ≤ q → X (q * k) x ≤ birkhoffSum (T^[k]) (X k) q x := by
-- proof
  apply StatMech.KingmanAE.ae_le_block_birkhoffSum h

/--
[tendsto_comp_div_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma tendsto_comp_div_atTop_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {g : α → ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hg : Integrable g μ) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun m : ℕ => g (T^[m] x) / m) atTop (𝓝 0) := by
-- proof
  apply StatMech.KingmanAE.tendsto_comp_div_atTop hT hg

/--
[tendsto_natDiv_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma tendsto_natDiv_atTop_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {k : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  Tendsto (fun n : ℕ => n / k) atTop atTop := by
-- proof
  apply StatMech.KingmanAE.tendsto_natDiv_atTop hk

/--
[tendsto_natDiv_div_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma tendsto_natDiv_div_atTop_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {k : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (k : ℝ))) := by
-- proof
  apply StatMech.KingmanAE.tendsto_natDiv_div_atTop hk

/--
[remDom_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma remDom_integrable_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {k : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Integrable (remDom X k) μ := by
-- proof
  apply StatMech.KingmanAE.remDom_integrable h k

/--
[remDom_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma remDom_nonneg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {X : ℕ → α → ℝ}
  {k : ℕ}
  {y : α} :
-- imply
  0 ≤ remDom X k y := by
-- proof
  apply StatMech.KingmanAE.remDom_nonneg X k y

/--
[le_remDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma le_remDom_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {X : ℕ → α → ℝ}
  {k r : ℕ}
  {y : α}
-- given
  (hr : r < k) :
-- imply
  X r y ≤ remDom X k y := by
-- proof
  apply StatMech.KingmanAE.le_remDom X hr y

/--
[gStar_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma gStar_le_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {k : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hk : 1 ≤ k) :
-- imply
  ∀ᵐ x ∂μ, limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop ≤ ((birkhoffLimit (T^[k]) (X k) x / k : ℝ) : EReal) := by
-- proof
  apply StatMech.KingmanAE.gStar_le h hk

/--
[gStarLow_le_gStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma gStarLow_le_gStar_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {x : α} :
-- imply
  gStarLow T X x ≤ gStar T X x := by
-- proof
  apply StatMech.KingmanAE.gStarLow_le_gStar x

/--
[gStar_le_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma gStar_le_comp_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, gStar T X x ≤ gStar T X (T x) := by
-- proof
  apply StatMech.KingmanAE.gStar_le_comp h

/--
[gStar_le_birkhoffLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma gStar_le_birkhoffLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {k : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hk : 1 ≤ k) :
-- imply
  ∀ᵐ x ∂μ, gStar T X x ≤ ((birkhoffLimit (T^[k]) (X k) x / k : ℝ) : EReal) := by
-- proof
  apply StatMech.KingmanAE.gStar_le_birkhoffLimit h hk

/--
[gStar_lt_top_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma gStar_lt_top_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, gStar T X x < ⊤ := by
-- proof
  apply StatMech.KingmanAE.gStar_lt_top_ae h

/--
[gStar_le_birkhoffLimit_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma gStar_le_birkhoffLimit_one_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, gStar T X x ≤ ((birkhoffLimit T (X 1) x : ℝ) : EReal) := by
-- proof
  apply StatMech.KingmanAE.gStar_le_birkhoffLimit_one h

/--
[tendsto_div_kingmanLimit_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma tendsto_div_kingmanLimit_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (heq : ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x)
  (hbot : ∀ᵐ x ∂μ, ⊥ < gStar T X x) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
-- proof
  apply StatMech.KingmanAE.tendsto_div_kingmanLimit_ae h heq hbot

/--
[limit_le_comp_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma limit_le_comp_of_tendsto_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ℓ : α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (ℓ x))) :
-- imply
  ∀ᵐ x ∂μ, ℓ x ≤ ℓ (T x) := by
-- proof
  apply StatMech.KingmanAE.limit_le_comp_of_tendsto h hconv

/--
[kingmanLimit_comp_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma kingmanLimit_comp_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (heq : ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x)
  (hbot : ∀ᵐ x ∂μ, ⊥ < gStar T X x)
  (hint : Integrable (kingmanLimit T X) μ) :
-- imply
  ∀ᵐ x ∂μ, kingmanLimit T X (T x) = kingmanLimit T X x := by
-- proof
  apply StatMech.KingmanAE.kingmanLimit_comp_ae h heq hbot hint

/--
[aemeasurable_gStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma aemeasurable_gStar_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  AEMeasurable (gStar T X) μ := by
-- proof
  apply StatMech.KingmanAE.aemeasurable_gStar h

/--
[aemeasurable_kingmanLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma aemeasurable_kingmanLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  AEMeasurable (kingmanLimit T X) μ := by
-- proof
  apply StatMech.KingmanAE.aemeasurable_kingmanLimit h

/--
[gStar_nonneg_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma gStar_nonneg_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, (0 : EReal) ≤ gStar T X x := by
-- proof
  apply StatMech.KingmanAE.gStar_nonneg_ae hnn

/--
[kingmanLimit_nonneg_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma kingmanLimit_nonneg_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, 0 ≤ kingmanLimit T X x := by
-- proof
  apply StatMech.KingmanAE.kingmanLimit_nonneg_ae hnn

/--
[kingmanLimit_le_birkhoffLimit_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma kingmanLimit_le_birkhoffLimit_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {k : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
  (hk : 1 ≤ k) :
-- imply
  ∀ᵐ x ∂μ, kingmanLimit T X x ≤ birkhoffLimit (T^[k]) (X k) x / k := by
-- proof
  apply StatMech.KingmanAE.kingmanLimit_le_birkhoffLimit_ae h hnn hk

/--
[integrable_kingmanLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma integrable_kingmanLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  Integrable (kingmanLimit T X) μ := by
-- proof
  apply StatMech.KingmanAE.integrable_kingmanLimit h hnn

/--
[integral_birkhoffLimit_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma integral_birkhoffLimit_block_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {k : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∫ x, birkhoffLimit (T^[k]) (X k) x ∂μ = ∫ x, X k x ∂μ := by
-- proof
  apply StatMech.KingmanAE.integral_birkhoffLimit_block h k

/--
[integral_kingmanLimit_le_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma integral_kingmanLimit_le_div_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {k : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
  (hk : 1 ≤ k) :
-- imply
  (∫ x, kingmanLimit T X x ∂μ) ≤ (∫ x, X k x ∂μ) / k := by
-- proof
  apply StatMech.KingmanAE.integral_kingmanLimit_le_div h hnn hk

/--
[integral_kingmanLimit_le_gamma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean)
-/
@[path]
private lemma integral_kingmanLimit_le_gamma_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  (∫ x, kingmanLimit T X x ∂μ) ≤ SubadditiveCocycle.gamma h := by
-- proof
  apply StatMech.KingmanAE.integral_kingmanLimit_le_gamma h hnn


-- created on 2026-10-23
