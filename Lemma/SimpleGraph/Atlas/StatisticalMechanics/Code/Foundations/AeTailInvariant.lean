import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Foundations.AeTailInvariant
open MeasureTheory MeasurableSpace Set Filter StatMech


/--
[atiFinSig_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiFinSig_mono_eq
  [Countable E]
  [DecidableEq E]
  {F K : Finset E}
-- given
  (h : F ⊆ K) :
-- imply
  atiFinSig F ≤ atiFinSig K := by
-- proof
  apply StatMech.atiFinSig_mono h

/--
[atiCylinderRing_isSetRing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiCylinderRing_isSetRing_eq
  [Countable E]
  [DecidableEq E] :
-- imply
  IsSetRing (atiCylinderRing E) := by
-- proof
  apply StatMech.atiCylinderRing_isSetRing

/--
[atiCylinderRing_univ_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiCylinderRing_univ_mem_eq
  [Countable E]
  [DecidableEq E] :
-- imply
  (Set.univ : Set (ConfigSpace E)) ∈ atiCylinderRing E := by
-- proof
  apply StatMech.atiCylinderRing_univ_mem

/--
[atiCylinderRing_generateFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiCylinderRing_generateFrom_eq
  [Countable E]
  [DecidableEq E] :
-- imply
  (inferInstance : MeasurableSpace (ConfigSpace E)) = generateFrom (atiCylinderRing E) := by
-- proof
  apply StatMech.atiCylinderRing_generateFrom

/--
[atiExteriorCylinderRing_isSetRing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiExteriorCylinderRing_isSetRing_eq
  [Countable E]
  [DecidableEq E]
  {window : Set E} :
-- imply
  IsSetRing (atiExteriorCylinderRing (E := E) window) := by
-- proof
  apply StatMech.atiExteriorCylinderRing_isSetRing window

/--
[atiExteriorCylinderRing_univ_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiExteriorCylinderRing_univ_mem_eq
  [Countable E]
  [DecidableEq E]
  {window : Set E} :
-- imply
  (Set.univ : Set (ConfigSpace E)) ∈ atiExteriorCylinderRing (E := E) window := by
-- proof
  apply StatMech.atiExteriorCylinderRing_univ_mem window

/--
[ati_restrict_measurable_finSig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma ati_restrict_measurable_finSig_eq
  [Countable E]
  [DecidableEq E]
  {F : Finset E} :
-- imply
  @Measurable (ConfigSpace E) (ConfigSpace F) (atiFinSig F) inferInstance F.restrict := by
-- proof
  apply StatMech.ati_restrict_measurable_finSig F

/--
[atiExteriorCylinderRing_generateFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiExteriorCylinderRing_generateFrom_eq
  [Countable E]
  [DecidableEq E]
  {window : Set E} :
-- imply
  outsideSigma window = generateFrom (atiExteriorCylinderRing (E := E) window) := by
-- proof
  apply StatMech.atiExteriorCylinderRing_generateFrom window

/--
[ati_exterior_approx_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma ati_exterior_approx_cylinder_eq
  [Countable E]
  [DecidableEq E]
  {window : Set E}
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
  {s : Set (ConfigSpace E)}
  {ε : ℝ≥0∞}
-- given
  (hs : @MeasurableSet _ (outsideSigma window) s)
  (hε : 0 < ε) :
-- imply
  ∃ (F : Finset E) (S : Set (ConfigSpace F)), (↑F : Set E) ⊆ windowᶜ ∧ mu (s ∆ MeasureTheory.cylinder F S) < ε := by
-- proof
  apply StatMech.ati_exterior_approx_cylinder window hs hε

/--
[atiShift_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiShift_measurable_eq
  [Countable E]
  [DecidableEq E]
  {g : H}
  {F : Finset E} :
-- imply
  @Measurable (ConfigSpace E) (ConfigSpace E) (atiFinSig (F.image (fun e => g⁻¹ • e))) (atiFinSig F) (shift g) := by
-- proof
  apply StatMech.atiShift_measurable g F

/--
[atiFinSig_le_outsideSigma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiFinSig_le_outsideSigma_eq
  [Countable E]
  [DecidableEq E]
  {F : Finset E}
  {window : Set E}
-- given
  (h : (↑F : Set E) ⊆ windowᶜ) :
-- imply
  atiFinSig F ≤ outsideSigma window := by
-- proof
  apply StatMech.atiFinSig_le_outsideSigma F window h

/--
[ati_symmDiff_preimage_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma ati_symmDiff_preimage_invariant_eq
  [Countable E]
  [DecidableEq E]
  {mu : Measure (ConfigSpace E)}
  {s A : Set (ConfigSpace E)}
  {g : H}
-- given
  (hmu : IsTranslationInvariant (G := H) mu)
  (hs : MeasurableSet s)
  (hA : MeasurableSet A)
  (hinv : shift g ⁻¹' s = s) :
-- imply
  mu (s ∆ (shift g ⁻¹' A)) = mu (s ∆ A) := by
-- proof
  apply StatMech.ati_symmDiff_preimage_invariant hmu hs hA g hinv

/--
[ati_invariant_approx](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma ati_invariant_approx_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
  {s : Set (ConfigSpace E)}
  {k : ℕ}
  {ε : ℝ≥0∞}
-- given
  (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H, (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
  (hmu : IsTranslationInvariant (G := H) mu)
  (hs : MeasurableSet s)
  (hinv : ∀ g : H, shift g ⁻¹' s = s)
  (hε : 0 < ε) :
-- imply
  ∃ A : Set (ConfigSpace E), @MeasurableSet _ (outsideSigma (window k)) A ∧ mu (s ∆ A) < ε := by
-- proof
  apply StatMech.ati_invariant_approx window hescape hmu hs hinv k hε

/--
[ati_sequenceInvariant_approx](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma ati_sequenceInvariant_approx_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {g : ℕ → H}
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
  {s : Set (ConfigSpace E)}
  {k : ℕ}
  {ε : ℝ≥0∞}
-- given
  (hescape : ∀ (F : Finset E) (k : ℕ), ∃ n : ℕ, (↑(F.image (fun e => (g n)⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
  (hmu : IsTranslationInvariant (G := H) mu)
  (hs : MeasurableSet s)
  (hinv : ∀ n : ℕ, shift (g n) ⁻¹' s = s)
  (hε : 0 < ε) :
-- imply
  ∃ A : Set (ConfigSpace E), @MeasurableSet _ (outsideSigma (window k)) A ∧ mu (s ∆ A) < ε := by
-- proof
  apply StatMech.ati_sequenceInvariant_approx window g hescape hmu hs hinv k hε

/--
[AtiTailEvent.measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma measurableSet_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {s : Set (ConfigSpace E)}
-- given
  (hs : AtiTailEvent window s) :
-- imply
  MeasurableSet s := by
-- proof
  apply StatMech.AtiTailEvent.measurableSet hs

/--
[AtiTailEvent.compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma compl_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {s : Set (ConfigSpace E)}
-- given
  (hs : AtiTailEvent window s) :
-- imply
  AtiTailEvent window sᶜ := by
-- proof
  apply StatMech.AtiTailEvent.compl hs

/--
[atiOutsideSigma_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiOutsideSigma_antitone_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {j n : ℕ}
-- given
  (hwindow : Monotone window)
  (h : j ≤ n) :
-- imply
  outsideSigma (window n) ≤ outsideSigma (window j) := by
-- proof
  apply StatMech.atiOutsideSigma_antitone hwindow h

/--
[atiTailEvent_liminf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma atiTailEvent_liminf_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {A : ℕ → Set (ConfigSpace E)}
-- given
  (hwindow : Monotone window)
  (hA : ∀ n, @MeasurableSet _ (outsideSigma (window n)) (A n)) :
-- imply
  AtiTailEvent window (⋃ N, ⋂ i, A (i + N)) := by
-- proof
  apply StatMech.atiTailEvent_liminf hwindow A hA

/--
[ati_aeTail_of_approxFarOut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma ati_aeTail_of_approxFarOut_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
  {s : Set (ConfigSpace E)}
-- given
  (hwindow : Monotone window)
  (happ : AtiApproxFarOut window mu s) :
-- imply
  ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
-- proof
  apply StatMech.ati_aeTail_of_approxFarOut hwindow happ

/--
[ati_invariant_aeTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma ati_invariant_aeTail_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
-- given
  (hwindow : Monotone window)
  (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H, (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
  (hmu : IsTranslationInvariant (G := H) mu) :
-- imply
  ∀ s : Set (ConfigSpace E), MeasurableSet s → (∀ g : H, shift g ⁻¹' s = s) → ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
-- proof
  apply StatMech.ati_invariant_aeTail window hwindow hescape hmu

/--
[ati_sequenceInvariant_aeTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean)
-/
@[path]
private lemma ati_sequenceInvariant_aeTail_eq
  [Countable E]
  [DecidableEq E]
  {window : ℕ → Set E}
  {g : ℕ → H}
  {mu : Measure (ConfigSpace E)}
  [IsFiniteMeasure mu]
-- given
  (hwindow : Monotone window)
  (hescape : ∀ (F : Finset E) (k : ℕ), ∃ n : ℕ, (↑(F.image (fun e => (g n)⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
  (hmu : IsTranslationInvariant (G := H) mu) :
-- imply
  ∀ s : Set (ConfigSpace E), MeasurableSet s → (∀ n : ℕ, shift (g n) ⁻¹' s = s) → ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
-- proof
  apply StatMech.ati_sequenceInvariant_aeTail window hwindow g hescape hmu


-- created on 2026-10-23
