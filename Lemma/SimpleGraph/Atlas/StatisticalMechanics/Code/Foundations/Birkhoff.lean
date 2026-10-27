import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.Birkhoff.Part2
open MeasureTheory Filter Finset Function StatMech StatMech.Birkhoff


/--
[maxBirkhoff_eq_sup'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma maxBirkhoff_eq_sup'_eq
  {T : α → α}
  {f : α → ℝ}
  {n : ℕ}
  {x : α} :
-- imply
  maxBirkhoff T f n x = (Finset.range (n + 1)).sup' (Finset.nonempty_range_iff.mpr n.succ_ne_zero) (fun k => birkhoffSum T f k x) := by
-- proof
  apply StatMech.Birkhoff.maxBirkhoff_eq_sup' n x

/--
[birkhoffSum_le_maxBirkhoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma birkhoffSum_le_maxBirkhoff_eq
  {T : α → α}
  {f : α → ℝ}
  {n k : ℕ}
  {x : α}
-- given
  (hk : k ≤ n) :
-- imply
  birkhoffSum T f k x ≤ maxBirkhoff T f n x := by
-- proof
  apply StatMech.Birkhoff.birkhoffSum_le_maxBirkhoff hk x

/--
[maxBirkhoff_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma maxBirkhoff_nonneg_eq
  {T : α → α}
  {f : α → ℝ}
  {n : ℕ}
  {x : α} :
-- imply
  0 ≤ maxBirkhoff T f n x := by
-- proof
  apply StatMech.Birkhoff.maxBirkhoff_nonneg n x

/--
[exists_eq_maxBirkhoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma exists_eq_maxBirkhoff_eq
  {T : α → α}
  {f : α → ℝ}
  {n : ℕ}
  {x : α} :
-- imply
  ∃ k ≤ n, birkhoffSum T f k x = maxBirkhoff T f n x := by
-- proof
  apply StatMech.Birkhoff.exists_eq_maxBirkhoff n x

/--
[birkhoffSum_le_add_maxBirkhoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma birkhoffSum_le_add_maxBirkhoff_eq
  {T : α → α}
  {f : α → ℝ}
  {n k : ℕ}
  {x : α}
-- given
  (hk1 : 1 ≤ k)
  (hk2 : k ≤ n + 1) :
-- imply
  birkhoffSum T f k x ≤ f x + maxBirkhoff T f n (T x) := by
-- proof
  apply StatMech.Birkhoff.birkhoffSum_le_add_maxBirkhoff hk1 hk2 x

/--
[maxBirkhoff_le_add_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma maxBirkhoff_le_add_of_pos_eq
  {T : α → α}
  {f : α → ℝ}
  {n : ℕ}
  {x : α}
-- given
  (hx : 0 < maxBirkhoff T f n x) :
-- imply
  maxBirkhoff T f n x ≤ f x + maxBirkhoff T f n (T x) := by
-- proof
  apply StatMech.Birkhoff.maxBirkhoff_le_add_of_pos hx

/--
[birkhoffSum_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma birkhoffSum_sub_const_eq
  {T : α → α}
  {f : α → ℝ}
  {a : ℝ}
  {k : ℕ}
  {x : α} :
-- imply
  birkhoffSum T (fun y => f y - a) k x = birkhoffSum T f k x - k • a := by
-- proof
  apply StatMech.Birkhoff.birkhoffSum_sub_const a k x

/--
[integrable_comp_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
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
  apply StatMech.Birkhoff.integrable_comp_iterate hT hf k

/--
[integrable_birkhoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma integrable_birkhoffSum_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {k : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  Integrable (fun x => birkhoffSum T f k x) μ := by
-- proof
  apply StatMech.Birkhoff.integrable_birkhoffSum hT hf k

/--
[maxBirkhoff_eq_sup'_fun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma maxBirkhoff_eq_sup'_fun_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {n : ℕ} :
-- imply
  (fun x => maxBirkhoff T f n x) = (Finset.range (n + 1)).sup' (Finset.nonempty_range_iff.mpr n.succ_ne_zero) (fun k => fun x => birkhoffSum T f k x) := by
-- proof
  apply StatMech.Birkhoff.maxBirkhoff_eq_sup'_fun n

/--
[integrable_maxBirkhoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma integrable_maxBirkhoff_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  Integrable (fun x => maxBirkhoff T f n x) μ := by
-- proof
  apply StatMech.Birkhoff.integrable_maxBirkhoff hT hf n

/--
[integrable_maxBirkhoff_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma integrable_maxBirkhoff_comp_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  Integrable (fun x => maxBirkhoff T f n (T x)) μ := by
-- proof
  apply StatMech.Birkhoff.integrable_maxBirkhoff_comp hT hf n

/--
[integral_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
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
  apply StatMech.Birkhoff.integral_comp_eq hT hg

/--
[integral_maxBirkhoff_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma integral_maxBirkhoff_comp_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  ∫ x, maxBirkhoff T f n (T x) ∂μ = ∫ x, maxBirkhoff T f n x ∂μ := by
-- proof
  apply StatMech.Birkhoff.integral_maxBirkhoff_comp hT hf n

/--
[maximal_ergodic_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma maximal_ergodic_inequality_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  0 ≤ ∫ x in {x | 0 < maxBirkhoff T f n x}, f x ∂μ := by
-- proof
  apply StatMech.Birkhoff.maximal_ergodic_inequality hT hf n

/--
[hopf_maximal_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean)
-/
@[path]
private lemma hopf_maximal_inequality_eq
  {T : α → α}
  {f : α → ℝ}
  [MeasurableSpace α]
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {a : ℝ}
  {n : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Integrable f μ) :
-- imply
  a * (μ (maximalLevelSet T f a n)).toReal ≤ ∫ x in maximalLevelSet T f a n, f x ∂μ := by
-- proof
  apply StatMech.Birkhoff.hopf_maximal_inequality hT hf a n


-- created on 2026-10-23
