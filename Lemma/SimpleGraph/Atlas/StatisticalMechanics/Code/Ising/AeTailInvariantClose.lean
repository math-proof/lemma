import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.AeTailInvariantClose.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology StatMech StatMech.Ising


/--
[aetc_finSig_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_finSig_mono_eq
  {d : ℕ}
  {F G : Finset (Site d)}
-- given
  (h : F ⊆ G) :
-- imply
  aetc_finSig F ≤ aetc_finSig G := by
-- proof
  apply StatMech.Ising.aetc_finSig_mono h

/--
[aetc_isSetRing_Cring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_isSetRing_Cring_eq
  {d : ℕ} :
-- imply
  IsSetRing (aetc_Cring d) := by
-- proof
  apply StatMech.Ising.aetc_isSetRing_Cring

/--
[aetc_univ_mem_Cring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_univ_mem_Cring_eq
  {d : ℕ} :
-- imply
  (Set.univ : Set (ConfigSpace (Site d))) ∈ aetc_Cring d := by
-- proof
  apply StatMech.Ising.aetc_univ_mem_Cring

/--
[aetc_generateFrom_Cring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_generateFrom_Cring_eq
  {d : ℕ} :
-- imply
  (inferInstance : MeasurableSpace (ConfigSpace (Site d))) = generateFrom (aetc_Cring d) := by
-- proof
  apply StatMech.Ising.aetc_generateFrom_Cring

/--
[aetc_shift_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_shift_measurable_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {F : Finset (Site d)} :
-- imply
  @Measurable (ConfigSpace (Site d)) (ConfigSpace (Site d)) (aetc_finSig (F.image (fun e => g⁻¹ • e))) (aetc_finSig F) (shift g) := by
-- proof
  apply StatMech.Ising.aetc_shift_measurable g F

/--
[aetc_finSig_le_outsideSigma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_finSig_le_outsideSigma_eq
  {d : ℕ}
  {F : Finset (Site d)}
  {Λ : Set (Site d)}
-- given
  (h : (↑F : Set (Site d)) ⊆ Λᶜ) :
-- imply
  aetc_finSig F ≤ outsideSigma Λ := by
-- proof
  apply StatMech.Ising.aetc_finSig_le_outsideSigma F Λ h

/--
[aetc_exists_shift_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_exists_shift_outside_eq
  {d : ℕ}
  {F : Finset (Site d)}
  {k : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ g : Multiplicative (Site d), (↑(F.image (fun e => g⁻¹ • e)) : Set (Site d)) ⊆ (box d k)ᶜ := by
-- proof
  apply StatMech.Ising.aetc_exists_shift_outside hd F k

/--
[aetc_symmDiff_preimage_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_symmDiff_preimage_invariant_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  {s A : Set (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
-- given
  (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hs : MeasurableSet s)
  (hA : MeasurableSet A)
  (hinv : shift g ⁻¹' s = s) :
-- imply
  μ (s ∆ (shift g ⁻¹' A)) = μ (s ∆ A) := by
-- proof
  apply StatMech.Ising.aetc_symmDiff_preimage_invariant hμ hs hA g hinv

/--
[aetc_invariant_approx](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_invariant_approx_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
  {s : Set (ConfigSpace (Site d))}
  {k : ℕ}
  {ε : ENNReal}
-- given
  (hd : 1 ≤ d)
  (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hs : MeasurableSet s)
  (hinv : ∀ g : Multiplicative (Site d), (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s)
  (hε : 0 < ε) :
-- imply
  ∃ A : Set (ConfigSpace (Site d)), @MeasurableSet _ (outsideSigma (box d k)) A ∧ μ (s ∆ A) < ε := by
-- proof
  apply StatMech.Ising.aetc_invariant_approx hd hμ hs hinv k hε

/--
[aetc_outsideSigma_box_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_outsideSigma_box_antitone_eq
  {d : ℕ}
  {j n : ℕ}
-- given
  (h : j ≤ n) :
-- imply
  outsideSigma (box d n) ≤ outsideSigma (box d j) := by
-- proof
  apply StatMech.Ising.aetc_outsideSigma_box_antitone h

/--
[aetc_isTailEvent_liminf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_isTailEvent_liminf_eq
  {d : ℕ}
  {A : ℕ → Set (ConfigSpace (Site d))}
-- given
  (hA : ∀ n, @MeasurableSet _ (outsideSigma (box d n)) (A n)) :
-- imply
  IsTailEvent (d := d) (⋃ N, ⋂ i, A (i + N)) := by
-- proof
  apply StatMech.Ising.aetc_isTailEvent_liminf A hA

/--
[aetc_aeTail_of_approxFarOut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_aeTail_of_approxFarOut_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
  {s : Set (ConfigSpace (Site d))}
-- given
  (happ : AeApproxFarOut μ s) :
-- imply
  ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s' ∧ s =ᵐ[μ] s' := by
-- proof
  apply StatMech.Ising.aetc_aeTail_of_approxFarOut happ

/--
[aetc_haeTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_haeTail_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
-- given
  (hd : 1 ≤ d)
  (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ∀ s : Set (ConfigSpace (Site d)), MeasurableSet s → (∀ g : Multiplicative (Site d), (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) → ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s' ∧ s =ᵐ[μ] s' := by
-- proof
  apply StatMech.Ising.aetc_haeTail hd hμ

/--
[aetc_plusState_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_plusState_isErgodic_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.aetc_plusState_isErgodic β h hd hβ hh hti hdlr

/--
[aetc_minusState_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_minusState_isErgodic_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.aetc_minusState_isErgodic β h hd hβ hh hti hdlr

/--
[aetc_dirac_const_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_dirac_const_isTranslationInvariant_eq
  {d : ℕ} :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.aetc_dirac_const_isTranslationInvariant

/--
[aetc_haeTail_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean)
-/
@[path]
private lemma aetc_haeTail_nonvacuous_eq
  {d : ℕ} :
-- imply
  ∃ s' : Set (ConfigSpace (Site 1)), IsTailEvent (d := 1) s' ∧ (Set.univ : Set (ConfigSpace (Site 1))) =ᵐ[(Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site 1)))] s' := by
-- proof
  apply StatMech.Ising.aetc_haeTail_nonvacuous


-- created on 2026-10-23
