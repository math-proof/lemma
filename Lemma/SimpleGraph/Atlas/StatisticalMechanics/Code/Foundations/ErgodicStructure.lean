import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.ErgodicStructure.Part2
open MeasureTheory Filter Function MeasurableSpace StatMech StatMech.ErgodicStructure


/--
[measurable_invariants_of_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma measurable_invariants_of_comp_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
-- given
  (hf : Measurable f)
  (hcomp : f ∘ T = f) :
-- imply
  Measurable[MeasurableSpace.invariants T] f := by
-- proof
  apply StatMech.ErgodicStructure.measurable_invariants_of_comp_eq hf hcomp

/--
[condExp_invariants_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma condExp_invariants_self_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hf : StronglyMeasurable[MeasurableSpace.invariants T] f)
  (hfi : Integrable f μ) :
-- imply
  μ[f | MeasurableSpace.invariants T] = f := by
-- proof
  apply StatMech.ErgodicStructure.condExp_invariants_self hf hfi

/--
[condExp_of_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma condExp_of_comp_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (hf : Measurable f)
  (hfi : Integrable f μ)
  (hcomp : f ∘ T = f) :
-- imply
  μ[f | MeasurableSpace.invariants T] = f := by
-- proof
  apply StatMech.ErgodicStructure.condExp_of_comp_eq hf hfi hcomp

/--
[tendsto_birkhoffAverage_self_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma tendsto_birkhoffAverage_self_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ]
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Measurable f)
  (hfi : Integrable f μ)
  (hcomp : f ∘ T = f) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (f x)) := by
-- proof
  apply StatMech.ErgodicStructure.tendsto_birkhoffAverage_self_ae hT hf hfi hcomp

/--
[invariantsTrivial_iff_preErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma invariantsTrivial_iff_preErgodic_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ] :
-- imply
  InvariantsTrivial T μ ↔ PreErgodic T μ := by
-- proof
  apply StatMech.ErgodicStructure.invariantsTrivial_iff_preErgodic

/--
[ergodic_iff_invariantsTrivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma ergodic_iff_invariantsTrivial_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ] :
-- imply
  Ergodic T μ ↔ MeasurePreserving T μ μ ∧ InvariantsTrivial T μ := by
-- proof
  apply StatMech.ErgodicStructure.ergodic_iff_invariantsTrivial

/--
[preErgodic_iff_forall_invariant_ae_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma preErgodic_iff_forall_invariant_ae_const_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ] :
-- imply
  PreErgodic T μ ↔ ∀ g : α → ℝ, Measurable[MeasurableSpace.invariants T] g → ∃ c, g =ᵐ[μ] fun _ => c := by
-- proof
  apply StatMech.ErgodicStructure.preErgodic_iff_forall_invariant_ae_const

/--
[ae_eq_mean_of_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma ae_eq_mean_of_invariants_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ]
-- given
  (hT : Ergodic T μ)
  (hf : Integrable f μ)
  (hfm : StronglyMeasurable[MeasurableSpace.invariants T] f) :
-- imply
  f =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
-- proof
  apply StatMech.ErgodicStructure.ae_eq_mean_of_invariants hT hf hfm

/--
[condExp_invariants_ae_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma condExp_invariants_ae_eq_mean_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ]
-- given
  (hT : Ergodic T μ)
  (_hf : Integrable f μ) :
-- imply
  μ[f | MeasurableSpace.invariants T] =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
-- proof
  apply StatMech.ErgodicStructure.condExp_invariants_ae_eq_mean hT _hf

/--
[tendsto_birkhoffAverage_mean_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean)
-/
@[path]
private lemma tendsto_birkhoffAverage_mean_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ]
-- given
  (hT : Ergodic T μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
-- proof
  apply StatMech.ErgodicStructure.tendsto_birkhoffAverage_mean_ae hT hf


-- created on 2026-10-23
