import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.AeTailInvariantProve2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology StatMech StatMech.Ising


/--
[atip2_plusState_invariant_zeroOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_plusState_invariant_zeroOne_eq
  {d : ℕ}
  {s : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
  (hs : MeasurableSet s)
  (hinv : ∀ g : Multiplicative (Site d), (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) :
-- imply
  (plusState d β h : Measure (ConfigSpace (Site d))) s = 0 ∨ (plusState d β h : Measure (ConfigSpace (Site d))) s = 1 := by
-- proof
  apply StatMech.Ising.atip2_plusState_invariant_zeroOne β h hd hβ hh hti hdlr hs hinv

/--
[atip2_minusState_invariant_zeroOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_minusState_invariant_zeroOne_eq
  {d : ℕ}
  {s : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
  (hs : MeasurableSet s)
  (hinv : ∀ g : Multiplicative (Site d), (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) :
-- imply
  (minusState d β h : Measure (ConfigSpace (Site d))) s = 0 ∨ (minusState d β h : Measure (ConfigSpace (Site d))) s = 1 := by
-- proof
  apply StatMech.Ising.atip2_minusState_invariant_zeroOne β h hd hβ hh hti hdlr hs hinv

/--
[atip2_plusState_ae_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_plusState_ae_const_eq
  {d : ℕ}
  [Countable β']
  [MeasurableSpace β']
  [MeasurableSingletonClass β']
  {f : ConfigSpace (Site d) → β'}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
  (hf : Measurable f)
  (hinv : ∀ (g : Multiplicative (Site d)) (ω : ConfigSpace (Site d)), f (shift g ω) = f ω) :
-- imply
  ∃ k : β', (plusState d β h : Measure (ConfigSpace (Site d))) {ω | f ω = k} = 1 := by
-- proof
  apply StatMech.Ising.atip2_plusState_ae_const β h hd hβ hh hti hdlr f hf hinv

/--
[atip2_minusState_ae_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_minusState_ae_const_eq
  {d : ℕ}
  [Countable β']
  [MeasurableSpace β']
  [MeasurableSingletonClass β']
  {f : ConfigSpace (Site d) → β'}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
  (hf : Measurable f)
  (hinv : ∀ (g : Multiplicative (Site d)) (ω : ConfigSpace (Site d)), f (shift g ω) = f ω) :
-- imply
  ∃ k : β', (minusState d β h : Measure (ConfigSpace (Site d))) {ω | f ω = k} = 1 := by
-- proof
  apply StatMech.Ising.atip2_minusState_ae_const β h hd hβ hh hti hdlr f hf hinv

/--
[atip2_plusState_isDLRExtremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_plusState_isDLRExtremePoint_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.atip2_plusState_isDLRExtremePoint β h hβ hh

/--
[atip2_minusState_isDLRExtremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_minusState_isDLRExtremePoint_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.atip2_minusState_isDLRExtremePoint β h hβ hh

/--
[atip2_plusState_isErgodic_extremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_plusState_isErgodic_extremePoint_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.atip2_plusState_isErgodic_extremePoint β h hd hβ hh hti hdlr

/--
[atip2_minusState_isErgodic_extremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_minusState_isErgodic_extremePoint_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))))
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.atip2_minusState_isErgodic_extremePoint β h hd hβ hh hti hdlr

/--
[atip2_dirac_const_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_dirac_const_isErgodic_eq
  {d : ℕ} :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.atip2_dirac_const_isErgodic

/--
[atip2_ergodic_zeroOne_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean)
-/
@[path]
private lemma atip2_ergodic_zeroOne_nonvacuous_eq
  {d : ℕ} :
-- imply
  (Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site 1))) {ω : ConfigSpace (Site 1) | ∀ e, ω e = true} = 1 := by
-- proof
  apply StatMech.Ising.atip2_ergodic_zeroOne_nonvacuous


-- created on 2026-10-23
