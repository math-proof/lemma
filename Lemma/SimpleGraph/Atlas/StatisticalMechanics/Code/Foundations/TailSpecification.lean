import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Foundations.TailSpecification
open MeasureTheory ProbabilityTheory MeasurableSpace Set StatMech


/--
[ts_trim_restrict_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_trim_restrict_comm_eq
  [Countable E]
  {m mOmega : MeasurableSpace Omega}
  {mu : @Measure Omega mOmega}
  {s : Set Omega}
-- given
  (hm : m ≤ mOmega)
  (hs : @MeasurableSet Omega m s) :
-- imply
  @Measure.trim Omega m mOmega (@Measure.restrict Omega mOmega mu s) hm = @Measure.restrict Omega m (@Measure.trim Omega m mOmega mu hm) s := by
-- proof
  apply StatMech.ts_trim_restrict_comm mu hm s hs

/--
[ts_compProd_restrict_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_compProd_restrict_left_eq
  [Countable E]
  {mAlpha : MeasurableSpace alpha}
  {mBeta : MeasurableSpace beta}
  {mu : @Measure alpha mAlpha}
  [SFinite mu]
  {K : @Kernel alpha beta mAlpha mBeta}
  [IsSFiniteKernel K]
  {s : Set alpha}
-- given
  (hs : MeasurableSet s) :
-- imply
  (mu.restrict s) ⊗ₘ K = (mu ⊗ₘ K).restrict (s ×ˢ Set.univ) := by
-- proof
  apply StatMech.ts_compProd_restrict_left mu K s hs

/--
[ts_map_diag_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_map_diag_restrict_eq
  [Countable E]
  {m mOmega : MeasurableSpace Omega}
  {mu : @Measure Omega mOmega}
  {s : Set Omega}
-- given
  (hs : @MeasurableSet Omega m s)
  (hf : @Measurable Omega (Omega × Omega) mOmega (m.prod mOmega) (fun omega => (id omega, id omega))) :
-- imply
  @Measure.restrict (Omega × Omega) (m.prod mOmega) (@Measure.map Omega (Omega × Omega) mOmega (m.prod mOmega) (fun omega => (id omega, id omega)) mu) (s ×ˢ Set.univ) = @Measure.map Omega (Omega × Omega) mOmega (m.prod mOmega) (fun omega => (id omega, id omega)) (@Measure.restrict Omega mOmega mu s) := by
-- proof
  apply StatMech.ts_map_diag_restrict mu s hs hf

/--
[ts_trim_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_trim_smul_eq
  [Countable E]
  {m mOmega : MeasurableSpace Omega}
  {mu : @Measure Omega mOmega}
-- given
  (hm : m ≤ mOmega)
  (a : ℝ≥0∞) :
-- imply
  (a • mu).trim hm = a • (mu.trim hm) := by
-- proof
  apply StatMech.ts_trim_smul mu hm a

/--
[ts_restrict_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_restrict_state_eq
  [Countable E]
  {window : ℕ → Set E}
  {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E) (outsideSigma (window n)) inferInstance}
  [∀ n, IsSFiniteKernel (K n)]
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
  {s : Set (ConfigSpace E)}
  {n : ℕ}
-- given
  (hmu : IsTailSpecificationState window K mu)
  (hs : AtiTailEvent window s) :
-- imply
  ((mu.restrict s).trim (outsideSigma_le (window n))) ⊗ₘ K n = @Measure.map (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _ ((outsideSigma (window n)).prod inferInstance) (fun omega => (id omega, id omega)) (mu.restrict s) := by
-- proof
  apply StatMech.ts_restrict_state mu hmu hs n

/--
[ts_smul_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_smul_state_eq
  [Countable E]
  {window : ℕ → Set E}
  {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E) (outsideSigma (window n)) inferInstance}
  [∀ n, IsSFiniteKernel (K n)]
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
-- given
  (c : ℝ≥0∞)
  (hc : c ≠ ⊤)
  (hmu : IsTailSpecificationState window K mu) :
-- imply
  haveI : IsFiniteMeasure (c • mu) := by
-- proof
  apply StatMech.ts_smul_state c hc mu hmu

/--
[ts_cond_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_cond_state_eq
  [Countable E]
  {window : ℕ → Set E}
  {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E) (outsideSigma (window n)) inferInstance}
  [∀ n, IsSFiniteKernel (K n)]
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
  {s : Set (ConfigSpace E)}
-- given
  (hmu : IsTailSpecificationState window K mu)
  (hs : AtiTailEvent window s)
  (hs0 : mu s ≠ 0) :
-- imply
  IsTailSpecificationState window K (mu[|s]) := by
-- proof
  apply StatMech.ts_cond_state mu hmu hs hs0

/--
[ts_cond_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_cond_congr_eq
  [Countable E]
  [MeasurableSpace Omega]
  {mu : Measure Omega}
  {s t : Set Omega}
-- given
  (h : s =ᵐ[mu] t) :
-- imply
  (mu[|s]) = (mu[|t]) := by
-- proof
  apply StatMech.ts_cond_congr mu h

/--
[ts_cond_state_of_ae_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_cond_state_of_ae_tail_eq
  [Countable E]
  {window : ℕ → Set E}
  {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E) (outsideSigma (window n)) inferInstance}
  [∀ n, IsSFiniteKernel (K n)]
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
  {s t : Set (ConfigSpace E)}
-- given
  (hmu : IsTailSpecificationState window K mu)
  (ht : AtiTailEvent window t)
  (hae : s =ᵐ[mu] t)
  (hs0 : mu s ≠ 0) :
-- imply
  IsTailSpecificationState window K (mu[|s]) := by
-- proof
  apply StatMech.ts_cond_state_of_ae_tail mu hmu ht hae hs0

/--
[ts_isErgodic_of_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean)
-/
@[path]
private lemma ts_isErgodic_of_extreme_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E) (outsideSigma (window n)) inferInstance}
  [∀ n, IsSFiniteKernel (K n)]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
-- given
  (hwindow : Monotone window)
  (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H, (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
  (hti : IsTranslationInvariant (G := H) mu)
  (hstate : IsTailSpecificationState window K mu)
  (hext : ∀ (nu₁ nu₂ : Measure (ConfigSpace E)) (a b : ℝ≥0∞), IsProbabilityMeasure nu₁ → IsProbabilityMeasure nu₂ → IsTailSpecificationMeasure window K nu₁ → IsTailSpecificationMeasure window K nu₂ → 0 < a → 0 < b → a + b = 1 → a ≠ ⊤ → b ≠ ⊤ → mu = a • nu₁ + b • nu₂ → nu₁ = nu₂) :
-- imply
  IsErgodic (G := H) mu := by
-- proof
  apply StatMech.ts_isErgodic_of_extreme window hwindow hescape hti hstate hext


-- created on 2026-10-23
