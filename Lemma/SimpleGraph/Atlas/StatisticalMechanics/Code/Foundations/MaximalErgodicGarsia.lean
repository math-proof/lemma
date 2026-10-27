import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
open MeasureTheory Filter Finset Function StatMech StatMech.GarsiaMax


/--
[birkhoffSum_le_maxPartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma birkhoffSum_le_maxPartialSum_eq
  {T : α → α}
  {f : α → ℝ}
  {N : ℕ}
  {n : ℕ}
  {x : α}
-- given
  (hN : 1 ≤ N)
  (hn1 : 1 ≤ n)
  (hn2 : n ≤ N) :
-- imply
  birkhoffSum T f n x ≤ maxPartialSum T f N hN x := by
-- proof
  apply StatMech.GarsiaMax.birkhoffSum_le_maxPartialSum hN hn1 hn2 x

/--
[exists_eq_maxPartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma exists_eq_maxPartialSum_eq
  {T : α → α}
  {f : α → ℝ}
  {N : ℕ}
  {x : α}
-- given
  (hN : 1 ≤ N) :
-- imply
  ∃ n, 1 ≤ n ∧ n ≤ N ∧ birkhoffSum T f n x = maxPartialSum T f N hN x := by
-- proof
  apply StatMech.GarsiaMax.exists_eq_maxPartialSum hN x

/--
[birkhoffSum_le_add_posPart_maxPartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma birkhoffSum_le_add_posPart_maxPartialSum_eq
  {T : α → α}
  {f : α → ℝ}
  {N : ℕ}
  {n : ℕ}
  {x : α}
-- given
  (hN : 1 ≤ N)
  (hn1 : 1 ≤ n)
  (hn2 : n ≤ N) :
-- imply
  birkhoffSum T f n x ≤ f x + max (maxPartialSum T f N hN (T x)) 0 := by
-- proof
  apply StatMech.GarsiaMax.birkhoffSum_le_add_posPart_maxPartialSum hN hn1 hn2 x

/--
[maxPartialSum_le_add_posPart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma maxPartialSum_le_add_posPart_eq
  {T : α → α}
  {f : α → ℝ}
  {N : ℕ}
  {x : α}
-- given
  (hN : 1 ≤ N) :
-- imply
  maxPartialSum T f N hN x ≤ f x + max (maxPartialSum T f N hN (T x)) 0 := by
-- proof
  apply StatMech.GarsiaMax.maxPartialSum_le_add_posPart hN x

/--
[integrable_comp_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma integrable_comp_iterate_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {k : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  Integrable (fun x => f (T^[k] x)) μ := by
-- proof
  apply StatMech.GarsiaMax.integrable_comp_iterate hT hf k

/--
[integrable_birkhoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma integrable_birkhoffSum_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  Integrable (fun x => birkhoffSum T f n x) μ := by
-- proof
  apply StatMech.GarsiaMax.integrable_birkhoffSum hT hf n

/--
[maxPartialSum_eq_sup'_fun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma maxPartialSum_eq_sup'_fun_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {N : ℕ}
-- given
  (hN : 1 ≤ N) :
-- imply
  (fun x => maxPartialSum T f N hN x) = (Finset.Icc 1 N).sup' (by rw [Finset.nonempty_Icc]; exact hN) (fun n => fun x => birkhoffSum T f n x) := by
-- proof
  apply StatMech.GarsiaMax.maxPartialSum_eq_sup'_fun hN

/--
[integrable_maxPartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma integrable_maxPartialSum_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {N : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hN : 1 ≤ N) :
-- imply
  Integrable (fun x => maxPartialSum T f N hN x) μ := by
-- proof
  apply StatMech.GarsiaMax.integrable_maxPartialSum hT hf hN

/--
[integrable_posPart_maxPartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma integrable_posPart_maxPartialSum_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {N : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hN : 1 ≤ N) :
-- imply
  Integrable (fun x => max (maxPartialSum T f N hN x) 0) μ := by
-- proof
  apply StatMech.GarsiaMax.integrable_posPart_maxPartialSum hT hf hN

/--
[integrable_posPart_maxPartialSum_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma integrable_posPart_maxPartialSum_comp_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {N : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hN : 1 ≤ N) :
-- imply
  Integrable (fun x => max (maxPartialSum T f N hN (T x)) 0) μ := by
-- proof
  apply StatMech.GarsiaMax.integrable_posPart_maxPartialSum_comp hT hf hN

/--
[integral_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma integral_comp_eq_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {g : α → ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hg : AEStronglyMeasurable g μ) :
-- imply
  ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
-- proof
  apply StatMech.GarsiaMax.integral_comp_eq hT hg

/--
[integral_posPart_maxPartialSum_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma integral_posPart_maxPartialSum_comp_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {N : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hN : 1 ≤ N) :
-- imply
  ∫ x, max (maxPartialSum T f N hN (T x)) 0 ∂μ = ∫ x, max (maxPartialSum T f N hN x) 0 ∂μ := by
-- proof
  apply StatMech.GarsiaMax.integral_posPart_maxPartialSum_comp hT hf hN

/--
[garsia_maximal_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean)
-/
@[path]
private lemma garsia_maximal_inequality_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {N : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ)
  (hN : 1 ≤ N) :
-- imply
  0 ≤ ∫ x in {x | 0 < maxPartialSum T f N hN x}, f x ∂μ := by
-- proof
  apply StatMech.GarsiaMax.garsia_maximal_inequality hT hf hN


-- created on 2026-10-23
