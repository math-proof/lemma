import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Foundations.Kingman.Part3
open MeasureTheory Filter Topology StatMech StatMech.Kingman StatMech.Kingman.SubadditiveCocycle


/--
[integral_comp_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma integral_comp_measurePreserving_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {g : α → ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hg : AEStronglyMeasurable g μ) :
-- imply
  ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
-- proof
  apply StatMech.Kingman.integral_comp_measurePreserving T hT g hg

/--
[integral_comp_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma integral_comp_iterate_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {g : α → ℝ}
  {m : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hg : AEStronglyMeasurable g μ) :
-- imply
  ∫ x, g (T^[m] x) ∂μ = ∫ x, g x ∂μ := by
-- proof
  apply StatMech.Kingman.integral_comp_iterate T hT g hg m

/--
[expSeq_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma expSeq_subadditive_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {m n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  expSeq X μ (m + n) ≤ expSeq X μ m + expSeq X μ n := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.expSeq_subadditive h m n

/--
[subadditive_expSeq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma subadditive_expSeq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Subadditive (expSeq X μ) := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.subadditive_expSeq h

/--
[ae_le_birkhoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma ae_le_birkhoffSum_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, ∀ n, 1 ≤ n → X n x ≤ birkhoffSum T (X 1) n x := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.ae_le_birkhoffSum h

/--
[integrable_birkhoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma integrable_birkhoffSum_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Integrable (fun x => birkhoffSum T (X 1) n x) μ := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.integrable_birkhoffSum h n

/--
[expSeq_le_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma expSeq_le_nsmul_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hn : 1 ≤ n) :
-- imply
  expSeq X μ n ≤ n • expSeq X μ 1 := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.expSeq_le_nsmul h hn

/--
[tendsto_expSeq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma tendsto_expSeq_div_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) :
-- imply
  Tendsto (fun n => expSeq X μ n / n) atTop (𝓝 (gamma h)) := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.tendsto_expSeq_div h hbdd

/--
[gamma_le_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma gamma_le_div_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n))
  (hn : n ≠ 0) :
-- imply
  gamma h ≤ expSeq X μ n / n := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.gamma_le_div h hbdd hn

/--
[gamma_le_expSeq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma gamma_le_expSeq_one_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) :
-- imply
  gamma h ≤ expSeq X μ 1 := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.gamma_le_expSeq_one h hbdd

/--
[bddBelow_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean)
-/
@[path]
private lemma bddBelow_of_nonneg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (_h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  BddBelow (Set.range fun n => expSeq X μ n / n) := by
-- proof
  apply StatMech.Kingman.SubadditiveCocycle.bddBelow_of_nonneg _h hnn


-- created on 2026-10-23
