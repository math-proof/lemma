import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
open MeasureTheory TopologicalSpace Filter Topology MeasurableSpace StatMech


/--
[isClopen_cylinderEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma isClopen_cylinderEvent_eq
  [Countable E]
  {s : Finset E}
-- given
  (S : Set (∀ _i : s, Bool)) :
-- imply
  IsClopen (cylinder (α := fun _ : E => Bool) s S) := by
-- proof
  apply StatMech.isClopen_cylinderEvent s S

/--
[IsClopen.measurableSet_configSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma measurableSet_configSpace_eq
  [Countable E]
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsClopen A) :
-- imply
  MeasurableSet A := by
-- proof
  apply StatMech.IsClopen.measurableSet_configSpace hA

/--
[ProbabilityMeasure.coe_apply_eq_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma coe_apply_eq_real_eq
  [Countable E]
  {μ : ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)} :
-- imply
  ((μ A : NNReal) : ℝ) = (μ : Measure (ConfigSpace E)).real A := by
-- proof
  apply StatMech.ProbabilityMeasure.coe_apply_eq_real μ A

/--
[WeakConvergesTo.tendsto_real_of_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma tendsto_real_of_isClopen_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (h : WeakConvergesTo μ ν)
  (hA : IsClopen A) :
-- imply
  Tendsto (fun n => (μ n : Measure (ConfigSpace E)).real A) atTop (𝓝 ((ν : Measure (ConfigSpace E)).real A)) := by
-- proof
  apply StatMech.WeakConvergesTo.tendsto_real_of_isClopen h hA

/--
[monotone_real_of_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma monotone_real_of_chain_eq
  [Countable E]
  {μ : ℕ → Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (hchain : ∀ n, μ n ≼ μ (n + 1))
  (hAmeas : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  Monotone (fun n => (μ n).real A) := by
-- proof
  apply StatMech.monotone_real_of_chain hchain hAmeas hAinc

/--
[antitone_real_of_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma antitone_real_of_chain_eq
  [Countable E]
  {μ : ℕ → Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (hchain : ∀ n, μ (n + 1) ≼ μ n)
  (hAmeas : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  Antitone (fun n => (μ n).real A) := by
-- proof
  apply StatMech.antitone_real_of_chain hchain hAmeas hAinc

/--
[WeakConvergesTo.le_real_of_monotone_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma le_real_of_monotone_isIncreasing_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
  {n : ℕ}
-- given
  (h : WeakConvergesTo μ ν)
  (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A) :
-- imply
  (μ n : Measure (ConfigSpace E)).real A ≤ (ν : Measure (ConfigSpace E)).real A := by
-- proof
  apply StatMech.WeakConvergesTo.le_real_of_monotone_isIncreasing h hchain hAclopen hAinc n

/--
[WeakConvergesTo.ge_real_of_antitone_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma ge_real_of_antitone_isIncreasing_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
  {n : ℕ}
-- given
  (h : WeakConvergesTo μ ν)
  (hchain : ∀ n, (μ (n + 1) : Measure (ConfigSpace E)) ≼ (μ n : Measure (ConfigSpace E)))
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A) :
-- imply
  (ν : Measure (ConfigSpace E)).real A ≤ (μ n : Measure (ConfigSpace E)).real A := by
-- proof
  apply StatMech.WeakConvergesTo.ge_real_of_antitone_isIncreasing h hchain hAclopen hAinc n

/--
[le_real_of_weakLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma le_real_of_weakLimit_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {ρ : Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (h : WeakConvergesTo μ ν)
  (hAclopen : IsClopen A)
  (_hAinc : IsIncreasing A)
  (hbound : ∀ n, ρ.real A ≤ (μ n : Measure (ConfigSpace E)).real A) :
-- imply
  ρ.real A ≤ (ν : Measure (ConfigSpace E)).real A := by
-- proof
  apply StatMech.le_real_of_weakLimit h hAclopen _hAinc hbound

/--
[real_le_of_weakLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma real_le_of_weakLimit_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {ρ : Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (h : WeakConvergesTo μ ν)
  (hAclopen : IsClopen A)
  (hbound : ∀ n, (μ n : Measure (ConfigSpace E)).real A ≤ ρ.real A) :
-- imply
  (ν : Measure (ConfigSpace E)).real A ≤ ρ.real A := by
-- proof
  apply StatMech.real_le_of_weakLimit h hAclopen hbound

/--
[dominated_weakLimit_of_forall_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma dominated_weakLimit_of_forall_dominated_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {ρ : Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (h : WeakConvergesTo μ ν)
  (hdom : ∀ n, ρ ≼ (μ n : Measure (ConfigSpace E)))
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A) :
-- imply
  ρ.real A ≤ (ν : Measure (ConfigSpace E)).real A := by
-- proof
  apply StatMech.dominated_weakLimit_of_forall_dominated h hdom hAclopen hAinc

/--
[weakLimit_dominated_of_forall_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma weakLimit_dominated_of_forall_dominated_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {ρ : Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (h : WeakConvergesTo μ ν)
  (hdom : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ ρ)
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A) :
-- imply
  (ν : Measure (ConfigSpace E)).real A ≤ ρ.real A := by
-- proof
  apply StatMech.weakLimit_dominated_of_forall_dominated h hdom hAclopen hAinc

/--
[ProbabilityMeasure.ext_of_forall_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma ext_of_forall_isClopen_eq
  [Countable E]
  {μ ν : ProbabilityMeasure (ConfigSpace E)}
-- given
  (h : ∀ A : Set (ConfigSpace E), IsClopen A → μ A = ν A) :
-- imply
  μ = ν := by
-- proof
  apply StatMech.ProbabilityMeasure.ext_of_forall_isClopen h

/--
[isClopen_apply_eq_of_subseq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma isClopen_apply_eq_of_subseq_tendsto_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {L : Set (ConfigSpace E) → NNReal}
  {ξ : ProbabilityMeasure (ConfigSpace E)}
  {ψ : ℕ → ℕ}
  {A : Set (ConfigSpace E)}
-- given
  (hconv : ∀ A : Set (ConfigSpace E), IsClopen A → Tendsto (fun n => (μ n) A) atTop (𝓝 (L A)))
  (hψ : StrictMono ψ)
  (htends : Tendsto (μ ∘ ψ) atTop (𝓝 ξ))
  (hA : IsClopen A) :
-- imply
  (ξ A : NNReal) = L A := by
-- proof
  apply StatMech.isClopen_apply_eq_of_subseq_tendsto hconv hψ htends hA

/--
[tendsto_weakly_of_forall_isClopen_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma tendsto_weakly_of_forall_isClopen_tendsto_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {L : Set (ConfigSpace E) → NNReal}
-- given
  (hconv : ∀ A : Set (ConfigSpace E), IsClopen A → Tendsto (fun n => (μ n) A) atTop (𝓝 (L A))) :
-- imply
  ∃ ν : ProbabilityMeasure (ConfigSpace E), WeakConvergesTo μ ν := by
-- proof
  apply StatMech.tendsto_weakly_of_forall_isClopen_tendsto hconv

/--
[apply_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma apply_le_one_eq
  [Countable E]
  {μ : ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)} :
-- imply
  (μ A : NNReal) ≤ 1 := by
-- proof
  apply StatMech.apply_le_one μ A

/--
[tendsto_NNReal_of_monotone_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MonotoneLimit.lean)
-/
@[path]
private lemma tendsto_NNReal_of_monotone_isIncreasing_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A) :
-- imply
  Tendsto (fun n => (μ n) A) atTop (𝓝 (⨆ n, (μ n) A)) := by
-- proof
  apply StatMech.tendsto_NNReal_of_monotone_isIncreasing hchain hAclopen hAinc


-- created on 2026-10-23
