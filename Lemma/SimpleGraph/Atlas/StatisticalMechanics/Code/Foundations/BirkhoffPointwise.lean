import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Foundations.BirkhoffPointwise
open MeasureTheory Filter Finset Function MeasurableSpace StatMech StatMech.BirkhoffAE


/--
[IsInvariantSet.iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma iterate_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {E : Set α}
  {k : ℕ}
  {x : α}
-- given
  (hE : IsInvariantSet T E) :
-- imply
  x ∈ E ↔ T^[k] x ∈ E := by
-- proof
  apply StatMech.BirkhoffAE.IsInvariantSet.iterate hE k x

/--
[birkhoffSum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma birkhoffSum_indicator_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {E : Set α}
  {g : α → ℝ}
  {n : ℕ}
  {x : α}
-- given
  (hE : IsInvariantSet T E) :
-- imply
  birkhoffSum T (E.indicator g) n x = E.indicator (fun y => birkhoffSum T g n y) x := by
-- proof
  apply StatMech.BirkhoffAE.birkhoffSum_indicator hE g n x

/--
[maxPartialSum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma maxPartialSum_indicator_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {E : Set α}
  {g : α → ℝ}
  {N : ℕ}
  {x : α}
-- given
  (hE : IsInvariantSet T E)
  (hN : 1 ≤ N) :
-- imply
  maxPartialSum T (E.indicator g) N hN x = E.indicator (fun y => maxPartialSum T g N hN y) x := by
-- proof
  apply StatMech.BirkhoffAE.maxPartialSum_indicator hE g hN x

/--
[setOf_maxPartialSum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma setOf_maxPartialSum_indicator_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {E : Set α}
  {g : α → ℝ}
  {N : ℕ}
-- given
  (hE : IsInvariantSet T E)
  (hN : 1 ≤ N) :
-- imply
  {x | 0 < maxPartialSum T (E.indicator g) N hN x} = E ∩ {x | 0 < maxPartialSum T g N hN x} := by
-- proof
  apply StatMech.BirkhoffAE.setOf_maxPartialSum_indicator hE g hN

/--
[maxPartialSum_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma maxPartialSum_mono_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {g : α → ℝ}
  {N M : ℕ}
  {x : α}
-- given
  (hN : 1 ≤ N)
  (hM : 1 ≤ M)
  (hNM : N ≤ M) :
-- imply
  maxPartialSum T g N hN x ≤ maxPartialSum T g M hM x := by
-- proof
  apply StatMech.BirkhoffAE.maxPartialSum_mono g hN hM hNM x

/--
[cocycle_avg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma cocycle_avg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α}
  {n : ℕ} :
-- imply
  ((n : ℝ) + 1) * birkhoffAverage ℝ T f (n + 1) x = f x + (n : ℝ) * birkhoffAverage ℝ T f n (T x) := by
-- proof
  apply StatMech.BirkhoffAE.cocycle_avg x n

/--
[avg_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma avg_comp_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  birkhoffAverage ℝ T f n (T x) = (((n : ℝ) + 1) / n) * birkhoffAverage ℝ T f (n + 1) x - (f x) / n := by
-- proof
  apply StatMech.BirkhoffAE.avg_comp_eq x hn

/--
[avg_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma avg_succ_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α}
  {n : ℕ} :
-- imply
  birkhoffAverage ℝ T f (n + 1) x = ((n : ℝ) / (n + 1)) * birkhoffAverage ℝ T f n (T x) + (f x) / (n + 1) := by
-- proof
  apply StatMech.BirkhoffAE.avg_succ_eq x n

/--
[limsup_avg_comp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma limsup_avg_comp_le_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α} :
-- imply
  limsup (fun n => ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop ≤ limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop := by
-- proof
  apply StatMech.BirkhoffAE.limsup_avg_comp_le x

/--
[limsup_avg_le_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma limsup_avg_le_comp_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α} :
-- imply
  limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop ≤ limsup (fun n => ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop := by
-- proof
  apply StatMech.BirkhoffAE.limsup_avg_le_comp x

/--
[fStar_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma fStar_comp_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α} :
-- imply
  fStar T f (T x) = fStar T f x := by
-- proof
  apply StatMech.BirkhoffAE.fStar_comp x

/--
[coe_avg_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma coe_avg_neg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α}
  {n : ℕ} :
-- imply
  ((birkhoffAverage ℝ T (-f) n x : ℝ) : EReal) = -((birkhoffAverage ℝ T f n x : ℝ) : EReal) := by
-- proof
  apply StatMech.BirkhoffAE.coe_avg_neg x n

/--
[fStarLow_eq_neg_fStar_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma fStarLow_eq_neg_fStar_neg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α} :
-- imply
  fStarLow T f x = -fStar T (-f) x := by
-- proof
  apply StatMech.BirkhoffAE.fStarLow_eq_neg_fStar_neg x

/--
[fStarLow_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma fStarLow_comp_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {x : α} :
-- imply
  fStarLow T f (T x) = fStarLow T f x := by
-- proof
  apply StatMech.BirkhoffAE.fStarLow_comp x

/--
[setIntegral_nonneg_of_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma setIntegral_nonneg_of_invariant_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {g : α → ℝ}
  {E : Set α}
-- given
  (hT : MeasurePreserving T μ μ)
  (hg : Integrable g μ)
  (hEmeas : NullMeasurableSet E μ)
  (hEinv : IsInvariantSet T E)
  (hpos : ∀ x ∈ E, ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n x) :
-- imply
  0 ≤ ∫ x in E, g x ∂μ := by
-- proof
  apply StatMech.BirkhoffAE.setIntegral_nonneg_of_invariant hT hg hEmeas hEinv hpos

/--
[aestronglyMeasurable_birkhoffAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma aestronglyMeasurable_birkhoffAverage_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  AEStronglyMeasurable (fun x => birkhoffAverage ℝ T f n x) μ := by
-- proof
  apply StatMech.BirkhoffAE.aestronglyMeasurable_birkhoffAverage hT hf n

/--
[aemeasurable_coe_birkhoffAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma aemeasurable_coe_birkhoffAverage_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  AEMeasurable (fun x => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) μ := by
-- proof
  apply StatMech.BirkhoffAE.aemeasurable_coe_birkhoffAverage hT hf n

/--
[aemeasurable_fStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma aemeasurable_fStar_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  AEMeasurable (fStar T f) μ := by
-- proof
  apply StatMech.BirkhoffAE.aemeasurable_fStar hT hf

/--
[aemeasurable_fStarLow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma aemeasurable_fStarLow_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  AEMeasurable (fStarLow T f) μ := by
-- proof
  apply StatMech.BirkhoffAE.aemeasurable_fStarLow hT hf

/--
[birkhoffSum_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma birkhoffSum_sub_const_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {b : ℝ}
  {n : ℕ}
  {x : α} :
-- imply
  birkhoffSum T (fun y => f y - b) n x = birkhoffSum T f n x - n • b := by
-- proof
  apply StatMech.BirkhoffAE.birkhoffSum_sub_const b n x

/--
[exists_birkhoffSum_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma exists_birkhoffSum_sub_pos_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {b : ℝ}
  {x : α}
-- given
  (hx : (b : EReal) < fStar T f x) :
-- imply
  ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y => f y - b) n x := by
-- proof
  apply StatMech.BirkhoffAE.exists_birkhoffSum_sub_pos hx

/--
[exists_birkhoffSum_sub_pos'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma exists_birkhoffSum_sub_pos'_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  {a : ℝ}
  {x : α}
-- given
  (hx : fStarLow T f x < (a : EReal)) :
-- imply
  ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y => a - f y) n x := by
-- proof
  apply StatMech.BirkhoffAE.exists_birkhoffSum_sub_pos' hx

/--
[isInvariantSet_levelSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma isInvariantSet_levelSet_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {a b : ℝ} :
-- imply
  IsInvariantSet T (levelSet T f a b) := by
-- proof
  apply StatMech.BirkhoffAE.isInvariantSet_levelSet a b

/--
[nullMeasurableSet_levelSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma nullMeasurableSet_levelSet_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {a b : ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  NullMeasurableSet (levelSet T f a b) μ := by
-- proof
  apply StatMech.BirkhoffAE.nullMeasurableSet_levelSet hT hf a b

/--
[setIntegral_ge_of_lt_fStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma setIntegral_ge_of_lt_fStar_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {b : ℝ}
  {E : Set α}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hEmeas : NullMeasurableSet E μ)
  (hEinv : IsInvariantSet T E)
  (hE : ∀ x ∈ E, (b : EReal) < fStar T f x) :
-- imply
  b * (μ E).toReal ≤ ∫ x in E, f x ∂μ := by
-- proof
  apply StatMech.BirkhoffAE.setIntegral_ge_of_lt_fStar hT hf hEmeas hEinv hE

/--
[setIntegral_le_of_fStarLow_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma setIntegral_le_of_fStarLow_lt_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {a : ℝ}
  {E : Set α}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hEmeas : NullMeasurableSet E μ)
  (hEinv : IsInvariantSet T E)
  (hE : ∀ x ∈ E, fStarLow T f x < (a : EReal)) :
-- imply
  ∫ x in E, f x ∂μ ≤ a * (μ E).toReal := by
-- proof
  apply StatMech.BirkhoffAE.setIntegral_le_of_fStarLow_lt hT hf hEmeas hEinv hE

/--
[measure_levelSet_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma measure_levelSet_eq_zero_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {a b : ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hab : a < b) :
-- imply
  μ (levelSet T f a b) = 0 := by
-- proof
  apply StatMech.BirkhoffAE.measure_levelSet_eq_zero hT hf hab

/--
[fStar_lt_top_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma fStar_lt_top_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, fStar T f x < ⊤ := by
-- proof
  apply StatMech.BirkhoffAE.fStar_lt_top_ae hT hf

/--
[fStarLow_bot_lt_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma fStarLow_bot_lt_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, ⊥ < fStarLow T f x := by
-- proof
  apply StatMech.BirkhoffAE.fStarLow_bot_lt_ae hT hf

/--
[fStarLow_ae_eq_fStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma fStarLow_ae_eq_fStar_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  fStarLow T f =ᵐ[μ] fStar T f := by
-- proof
  apply StatMech.BirkhoffAE.fStarLow_ae_eq_fStar hT hf

/--
[tendsto_birkhoffAverage_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma tendsto_birkhoffAverage_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (birkhoffLimit T f x)) := by
-- proof
  apply StatMech.BirkhoffAE.tendsto_birkhoffAverage_ae hT hf

/--
[birkhoffLimit_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma birkhoffLimit_comp_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {x : α} :
-- imply
  birkhoffLimit T f (T x) = birkhoffLimit T f x := by
-- proof
  apply StatMech.BirkhoffAE.birkhoffLimit_comp x

/--
[aemeasurable_birkhoffLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma aemeasurable_birkhoffLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  AEMeasurable (birkhoffLimit T f) μ := by
-- proof
  apply StatMech.BirkhoffAE.aemeasurable_birkhoffLimit hT hf

/--
[eLpNorm_birkhoffAverage_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma eLpNorm_birkhoffAverage_le_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  eLpNorm (fun x => birkhoffAverage ℝ T f n x) 1 μ ≤ eLpNorm f 1 μ := by
-- proof
  apply StatMech.BirkhoffAE.eLpNorm_birkhoffAverage_le hT hf n

/--
[integrable_birkhoffLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma integrable_birkhoffLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  Integrable (birkhoffLimit T f) μ := by
-- proof
  apply StatMech.BirkhoffAE.integrable_birkhoffLimit hT hf

/--
[birkhoffAverage_sub_birkhoffLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma birkhoffAverage_sub_birkhoffLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {n : ℕ}
  {x : α}
-- given
  (hn : 1 ≤ n) :
-- imply
  birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x = birkhoffAverage ℝ T f n x - birkhoffLimit T f x := by
-- proof
  apply StatMech.BirkhoffAE.birkhoffAverage_sub_birkhoffLimit n hn x

/--
[tendsto_birkhoffAverage_sub_birkhoffLimit_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma tendsto_birkhoffAverage_sub_birkhoffLimit_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x) atTop (𝓝 0) := by
-- proof
  apply StatMech.BirkhoffAE.tendsto_birkhoffAverage_sub_birkhoffLimit_ae hT hf

/--
[fStar_sub_birkhoffLimit_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma fStar_sub_birkhoffLimit_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, fStar T (fun y => f y - birkhoffLimit T f y) x = 0 := by
-- proof
  apply StatMech.BirkhoffAE.fStar_sub_birkhoffLimit_ae hT hf

/--
[fStarLow_sub_birkhoffLimit_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma fStarLow_sub_birkhoffLimit_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, fStarLow T (fun y => f y - birkhoffLimit T f y) x = 0 := by
-- proof
  apply StatMech.BirkhoffAE.fStarLow_sub_birkhoffLimit_ae hT hf

/--
[ae_mem_setOf_fStarLow_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma ae_mem_setOf_fStarLow_lt_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {g : α → ℝ}
  {c : ℝ}
-- given
  (hc : 0 < c)
  (hg0 : ∀ᵐ x ∂μ, fStarLow T g x = 0) :
-- imply
  ∀ᵐ x ∂μ, fStarLow T g x < (c : EReal) := by
-- proof
  apply StatMech.BirkhoffAE.ae_mem_setOf_fStarLow_lt hc hg0

/--
[ae_mem_setOf_lt_fStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma ae_mem_setOf_lt_fStar_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {g : α → ℝ}
  {c : ℝ}
-- given
  (hc : c < 0)
  (hg0 : ∀ᵐ x ∂μ, fStar T g x = 0) :
-- imply
  ∀ᵐ x ∂μ, (c : EReal) < fStar T g x := by
-- proof
  apply StatMech.BirkhoffAE.ae_mem_setOf_lt_fStar hc hg0

/--
[setIntegral_birkhoffLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma setIntegral_birkhoffLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {E : Set α}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hEmeas : MeasurableSet E)
  (hEinv : IsInvariantSet T E) :
-- imply
  ∫ x in E, f x ∂μ = ∫ x in E, birkhoffLimit T f x ∂μ := by
-- proof
  apply StatMech.BirkhoffAE.setIntegral_birkhoffLimit hT hf hEmeas hEinv

/--
[measurable_birkhoffAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma measurable_birkhoffAverage_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {f₀ : α → ℝ}
  {n : ℕ}
-- given
  (hT : Measurable T)
  (hf₀ : Measurable f₀) :
-- imply
  Measurable (fun x => birkhoffAverage ℝ T f₀ n x) := by
-- proof
  apply StatMech.BirkhoffAE.measurable_birkhoffAverage hT hf₀ n

/--
[measurable_fStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma measurable_fStar_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {f₀ : α → ℝ}
-- given
  (hT : Measurable T)
  (hf₀ : Measurable f₀) :
-- imply
  Measurable (fStar T f₀) := by
-- proof
  apply StatMech.BirkhoffAE.measurable_fStar hT hf₀

/--
[measurable_invariants_birkhoffLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma measurable_invariants_birkhoffLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
  {f₀ : α → ℝ}
-- given
  (hT : Measurable T)
  (hf₀ : Measurable f₀) :
-- imply
  Measurable[MeasurableSpace.invariants T] (birkhoffLimit T f₀) := by
-- proof
  apply StatMech.BirkhoffAE.measurable_invariants_birkhoffLimit hT hf₀

/--
[birkhoffLimit_ae_eq_condExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma birkhoffLimit_ae_eq_condExp_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  birkhoffLimit T f =ᵐ[μ] μ[f | MeasurableSpace.invariants T] := by
-- proof
  apply StatMech.BirkhoffAE.birkhoffLimit_ae_eq_condExp hT hf

/--
[tendsto_birkhoffAverage_condExp_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean)
-/
@[path]
private lemma tendsto_birkhoffAverage_condExp_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 ((μ[f | MeasurableSpace.invariants T]) x)) := by
-- proof
  apply StatMech.BirkhoffAE.tendsto_birkhoffAverage_condExp_ae hT hf


-- created on 2026-10-23
