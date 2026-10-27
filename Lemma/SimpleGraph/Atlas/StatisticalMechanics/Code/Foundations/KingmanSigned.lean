import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.KingmanSigned.Part2
open MeasureTheory Filter Topology ENNReal StatMech StatMech.KingmanSigned


/--
[addCoc_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma addCoc_add_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {m n : ℕ}
  {x : α} :
-- imply
  addCoc T X (m + n) x = addCoc T X m x + addCoc T X n (T^[m] x) := by
-- proof
  apply StatMech.KingmanSigned.addCoc_add m n x

/--
[Wc_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Wc_eq_neg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
  {x : α} :
-- imply
  Wc T X n x = - Zc T X n x := by
-- proof
  apply StatMech.KingmanSigned.Wc_eq_neg n x

/--
[Zc_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Zc_one_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {x : α} :
-- imply
  Zc T X 1 x = 0 := by
-- proof
  apply StatMech.KingmanSigned.Zc_one x

/--
[Zc_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Zc_div_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
  {x : α}
-- given
  (hn : 1 ≤ n) :
-- imply
  Zc T X n x / n = (addCoc T X n x - X n x) / n := by
-- proof
  apply StatMech.KingmanSigned.Zc_div_eq hn x

/--
[integrable_addCoc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma integrable_addCoc_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Integrable (addCoc T X n) μ := by
-- proof
  apply StatMech.KingmanSigned.integrable_addCoc h n

/--
[integrable_Wc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma integrable_Wc_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Integrable (Wc T X n) μ := by
-- proof
  apply StatMech.KingmanSigned.integrable_Wc h n

/--
[integrable_Zc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma integrable_Zc_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Integrable (Zc T X n) μ := by
-- proof
  apply StatMech.KingmanSigned.integrable_Zc h n

/--
[Wc_subaddCocycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Wc_subaddCocycle_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  SubadditiveCocycle T μ (Wc T X) := by
-- proof
  apply StatMech.KingmanSigned.Wc_subaddCocycle h

/--
[Wc_nonpos_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Wc_nonpos_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hn : 1 ≤ n) :
-- imply
  Wc T X n ≤ᵐ[μ] 0 := by
-- proof
  apply StatMech.KingmanSigned.Wc_nonpos_ae h hn

/--
[Zc_nonneg_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Zc_nonneg_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hn : 1 ≤ n) :
-- imply
  0 ≤ᵐ[μ] Zc T X n := by
-- proof
  apply StatMech.KingmanSigned.Zc_nonneg_ae h hn

/--
[Zc_nonneg_ae_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Zc_nonneg_ae_all_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  0 ≤ᵐ[μ] Zc T X n := by
-- proof
  apply StatMech.KingmanSigned.Zc_nonneg_ae_all h n

/--
[Sc_eq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Sc_eq_sub_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {M : ℝ}
  {n : ℕ}
  {x : α}
-- given
  (hn : 1 ≤ n) :
-- imply
  Sc T X M n x = M * n - Zc T X n x := by
-- proof
  apply StatMech.KingmanSigned.Sc_eq_sub M hn x

/--
[Vc_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Vc_nonneg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {M : ℝ}
  {n : ℕ}
  {x : α} :
-- imply
  0 ≤ Vc T X M n x := by
-- proof
  apply StatMech.KingmanSigned.Vc_nonneg M n x

/--
[integrable_Sc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma integrable_Sc_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {M : ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Integrable (Sc T X M n) μ := by
-- proof
  apply StatMech.KingmanSigned.integrable_Sc h M n

/--
[integrable_Vc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma integrable_Vc_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {M : ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Integrable (Vc T X M n) μ := by
-- proof
  apply StatMech.KingmanSigned.integrable_Vc h M n

/--
[Vc_subaddCocycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Vc_subaddCocycle_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {M : ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  SubadditiveCocycle T μ (Vc T X M) := by
-- proof
  apply StatMech.KingmanSigned.Vc_subaddCocycle h M

/--
[Vc_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma Vc_div_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {M : ℝ}
  {n : ℕ}
  {x : α}
-- given
  (hn : 1 ≤ n) :
-- imply
  Vc T X M n x / n = M - min (Zc T X n x / n) M := by
-- proof
  apply StatMech.KingmanSigned.Vc_div_eq M hn x

/--
[integral_addCoc_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma integral_addCoc_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∫ x, addCoc T X n x ∂μ = n * ∫ x, X 1 x ∂μ := by
-- proof
  apply StatMech.KingmanSigned.integral_addCoc_eq h n

/--
[integral_Zc_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma integral_Zc_div_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hn : 1 ≤ n) :
-- imply
  ∫ x, Zc T X n x / n ∂μ = (∫ x, X 1 x ∂μ) - (∫ x, X n x ∂μ) / n := by
-- proof
  apply StatMech.KingmanSigned.integral_Zc_div h hn

/--
[aemeasurable_liminf_ennreal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma aemeasurable_liminf_ennreal_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (g : ℕ → α → ℝ≥0∞)
  (hg : ∀ n, AEMeasurable (g n) μ) :
-- imply
  AEMeasurable (fun x => liminf (fun n => g n x) atTop) μ := by
-- proof
  apply StatMech.KingmanSigned.aemeasurable_liminf_ennreal g hg

/--
[ae_liminf_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma ae_liminf_lt_top_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n)) :
-- imply
  ∀ᵐ x ∂μ, liminf (fun n => ENNReal.ofReal (Zc T X n x / n)) atTop < ∞ := by
-- proof
  apply StatMech.KingmanSigned.ae_liminf_lt_top h hbdd

/--
[core_conv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma core_conv_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {a : ℕ → ℝ}
  {M m : ℝ}
-- given
  (hconv : Tendsto (fun n => min (a n) M) atTop (𝓝 m))
  (hmM : m < M) :
-- imply
  Tendsto a atTop (𝓝 m) := by
-- proof
  apply StatMech.KingmanSigned.core_conv a M m hconv hmM

/--
[pointwise_conv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma pointwise_conv_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {a : ℕ → ℝ}
  {mfun : ℕ → ℝ}
-- given
  (hconv : ∀ M : ℕ, Tendsto (fun n => min (a n) (M : ℝ)) atTop (𝓝 (mfun M)))
  (hLtop : liminf (fun n => ENNReal.ofReal (a n)) atTop < ∞) :
-- imply
  ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
-- proof
  apply StatMech.KingmanSigned.pointwise_conv a mfun hconv hLtop

/--
[ae_truncated_conv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma ae_truncated_conv_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, ∀ M : ℕ, Tendsto (fun n => min (Zc T X n x / n) (M : ℝ)) atTop (𝓝 ((M : ℝ) - kingmanLimit T (Vc T X (M : ℝ)) x)) := by
-- proof
  apply StatMech.KingmanSigned.ae_truncated_conv h

/--
[ae_tendsto_Zc_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma ae_tendsto_Zc_div_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n)) :
-- imply
  ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n => Zc T X n x / n) atTop (𝓝 L) := by
-- proof
  apply StatMech.KingmanSigned.ae_tendsto_Zc_div h hbdd

/--
[ae_tendsto_X_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma ae_tendsto_X_div_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n)) :
-- imply
  ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n => X n x / n) atTop (𝓝 L) := by
-- proof
  apply StatMech.KingmanSigned.ae_tendsto_X_div h hbdd

/--
[tendsto_X_div_kingmanLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma tendsto_X_div_kingmanLimit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {x : α}
  {L : ℝ}
-- given
  (hL : Tendsto (fun n => X n x / n) atTop (𝓝 L)) :
-- imply
  Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
-- proof
  apply StatMech.KingmanSigned.tendsto_X_div_kingmanLimit hL

/--
[kingman_ae_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean)
-/
@[path]
private lemma kingman_ae_general_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n)) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
-- proof
  apply StatMech.KingmanSigned.kingman_ae_general h hbdd


-- created on 2026-10-23
