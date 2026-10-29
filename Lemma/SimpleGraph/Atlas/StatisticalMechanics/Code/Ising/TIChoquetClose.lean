import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.TIChoquetClose.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology StatMech StatMech.Ising


/--
[tic_trim_restrict_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_trim_restrict_comm_eq
  {d : ℕ}
  {m mΩ : MeasurableSpace Ω}
  {μ : @Measure Ω mΩ}
  {s : Set Ω}
-- given
  (hm : m ≤ mΩ)
  (hs : @MeasurableSet Ω m s) :
-- imply
  @Measure.trim Ω m mΩ (@Measure.restrict Ω mΩ μ s) hm = @Measure.restrict Ω m (@Measure.trim Ω m mΩ μ hm) s := by
-- proof
  apply StatMech.Ising.tic_trim_restrict_comm μ hm s hs

/--
[tic_compProd_restrict_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_compProd_restrict_left_eq
  {d : ℕ}
  {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β}
  {μ : @Measure α mα}
  [SFinite μ]
  {K : @Kernel α β mα mβ}
  [IsSFiniteKernel K]
  {s : Set α}
-- given
  (hs : MeasurableSet s) :
-- imply
  (μ.restrict s) ⊗ₘ K = (μ ⊗ₘ K).restrict (s ×ˢ Set.univ) := by
-- proof
  apply StatMech.Ising.tic_compProd_restrict_left μ K s hs

/--
[tic_map_diag_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_map_diag_restrict_eq
  {d : ℕ}
  {m mΩ : MeasurableSpace Ω}
  {μ : @Measure Ω mΩ}
  {s : Set Ω}
-- given
  (hs : @MeasurableSet Ω m s)
  (hf : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω => (id ω, id ω))) :
-- imply
  @Measure.restrict (Ω × Ω) (m.prod mΩ) (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ) (s ×ˢ Set.univ) = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) (@Measure.restrict Ω mΩ μ s) := by
-- proof
  apply StatMech.Ising.tic_map_diag_restrict μ s hs hf

/--
[IsTailEvent.measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma measurableSet_eq
  {d : ℕ}
  {s : Set (ConfigSpace (Site d))}
-- given
  (hs : IsTailEvent s) :
-- imply
  MeasurableSet s := by
-- proof
  apply StatMech.Ising.IsTailEvent.measurableSet hs

/--
[IsTailEvent.compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma compl_eq
  {d : ℕ}
  {s : Set (ConfigSpace (Site d))}
-- given
  (hs : IsTailEvent s) :
-- imply
  IsTailEvent sᶜ := by
-- proof
  apply StatMech.Ising.IsTailEvent.compl hs

/--
[isTailEvent_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma isTailEvent_univ_eq
  {d : ℕ} :
-- imply
  IsTailEvent (d := d) (Set.univ) := by
-- proof
  apply StatMech.Ising.isTailEvent_univ

/--
[isTailEvent_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma isTailEvent_empty_eq
  {d : ℕ} :
-- imply
  IsTailEvent (d := d) (∅ : Set (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.isTailEvent_empty

/--
[tic_restrict_compProd_trim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_restrict_compProd_trim_eq_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
  {s : Set (ConfigSpace (Site d))}
  {n : ℕ}
-- given
  (β h : ℝ)
  (hμ : IsDLRState d β h μ)
  (hs : IsTailEvent s) :
-- imply
  (((μ.restrict s).trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)) = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _ ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) (μ.restrict s) := by
-- proof
  apply StatMech.Ising.tic_restrict_compProd_trim_eq β h μ hμ hs n

/--
[tic_smul_compProd_trim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_smul_compProd_trim_eq_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
  {n : ℕ}
-- given
  (β h : ℝ)
  (c : ENNReal)
  (hc : c ≠ ⊤)
  (hμ : ∀ n, (μ.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h) = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _ ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ) :
-- imply
  haveI : IsFiniteMeasure (c • μ) := by
-- proof
  apply StatMech.Ising.tic_smul_compProd_trim_eq β h c hc μ hμ n

/--
[tic_isDLRState_cond_of_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_isDLRState_cond_of_tail_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
  {s : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hμ : IsDLRState d β h μ)
  (hs : IsTailEvent s)
  (hs0 : μ s ≠ 0) :
-- imply
  haveI : IsFiniteMeasure (μ[|s]) := by
-- proof
  apply StatMech.Ising.tic_isDLRState_cond_of_tail β h μ hμ hs hs0

/--
[tic_cond_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_cond_congr_eq
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {s s' : Set Ω}
-- given
  (h : s =ᵐ[μ] s') :
-- imply
  (μ[|s]) = (μ[|s']) := by
-- proof
  apply StatMech.Ising.tic_cond_congr μ h

/--
[tic_isDLRState_cond_of_aeTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_isDLRState_cond_of_aeTail_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
  {s s' : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hμ : IsDLRState d β h μ)
  (hs' : IsTailEvent s')
  (hae : s =ᵐ[μ] s')
  (hs0 : μ s ≠ 0) :
-- imply
  haveI : IsFiniteMeasure (μ[|s]) := by
-- proof
  apply StatMech.Ising.tic_isDLRState_cond_of_aeTail β h μ hμ hs' hae hs0

/--
[tic_plusState_closure_of_aeTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_plusState_closure_of_aeTail_eq
  {d : ℕ}
  {s s₁ s₂ : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
  (hs1 : IsTailEvent s₁)
  (hs2 : IsTailEvent s₂)
  (haes : s =ᵐ[(plusState d β h : Measure (ConfigSpace (Site d)))] s₁)
  (haesc : sᶜ =ᵐ[(plusState d β h : Measure (ConfigSpace (Site d)))] s₂)
  (hs0 : (plusState d β h : Measure (ConfigSpace (Site d))) s ≠ 0)
  (hsc0 : (plusState d β h : Measure (ConfigSpace (Site d))) sᶜ ≠ 0) :
-- imply
  IsDLRState d β h ((plusState d β h : Measure (ConfigSpace (Site d)))[|s]) ∧ IsDLRState d β h ((plusState d β h : Measure (ConfigSpace (Site d)))[|sᶜ]) := by
-- proof
  apply StatMech.Ising.tic_plusState_closure_of_aeTail β h hdlr hs1 hs2 haes haesc hs0 hsc0

/--
[tic_minusState_closure_of_aeTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_minusState_closure_of_aeTail_eq
  {d : ℕ}
  {s s₁ s₂ : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
  (hs1 : IsTailEvent s₁)
  (hs2 : IsTailEvent s₂)
  (haes : s =ᵐ[(minusState d β h : Measure (ConfigSpace (Site d)))] s₁)
  (haesc : sᶜ =ᵐ[(minusState d β h : Measure (ConfigSpace (Site d)))] s₂)
  (hs0 : (minusState d β h : Measure (ConfigSpace (Site d))) s ≠ 0)
  (hsc0 : (minusState d β h : Measure (ConfigSpace (Site d))) sᶜ ≠ 0) :
-- imply
  IsDLRState d β h ((minusState d β h : Measure (ConfigSpace (Site d)))[|s]) ∧ IsDLRState d β h ((minusState d β h : Measure (ConfigSpace (Site d)))[|sᶜ]) := by
-- proof
  apply StatMech.Ising.tic_minusState_closure_of_aeTail β h hdlr hs1 hs2 haes haesc hs0 hsc0

/--
[tic_plusState_isErgodic_of_aeTailInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_plusState_isErgodic_of_aeTailInvariant_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
  (haeTail : ∀ s : Set (ConfigSpace (Site d)), MeasurableSet s → (∀ g : Multiplicative (Site d), (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) → ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s' ∧ s =ᵐ[(plusState d β h : Measure (ConfigSpace (Site d)))] s') :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.tic_plusState_isErgodic_of_aeTailInvariant β h hβ hh hti hdlr haeTail

/--
[tic_minusState_isErgodic_of_aeTailInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean)
-/
@[path]
private lemma tic_minusState_isErgodic_of_aeTailInvariant_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
  (haeTail : ∀ s : Set (ConfigSpace (Site d)), MeasurableSet s → (∀ g : Multiplicative (Site d), (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) → ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s' ∧ s =ᵐ[(minusState d β h : Measure (ConfigSpace (Site d)))] s') :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.tic_minusState_isErgodic_of_aeTailInvariant β h hβ hh hti hdlr haeTail


-- created on 2026-10-23
