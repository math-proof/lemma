import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.STTFull.Part3
open MeasureTheory ProbabilityTheory Finset StatMech StatMech.Universality


/--
[stt_localWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_localWeight_nonneg_eq
  {p0 p1 p2 : ℝ}
  {ω : LocalConfig}
-- given
  (h0 : 0 ≤ p0)
  (h0' : p0 ≤ 1)
  (h1 : 0 ≤ p1)
  (h1' : p1 ≤ 1)
  (h2 : 0 ≤ p2)
  (h2' : p2 ≤ 1) :
-- imply
  0 ≤ localWeight p0 p1 p2 ω := by
-- proof
  apply StatMech.Universality.stt_localWeight_nonneg p0 p1 p2 h0 h0' h1 h1' h2 h2' ω

/--
[stt_sum_weighted_dirac_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_sum_weighted_dirac_singleton_eq
  [MeasurableSpace α]
  [MeasurableSingletonClass α]
  [DecidableEq α]
  {f : LocalConfig → α}
  {a : α}
-- given
  (g : LocalConfig → ℝ≥0∞) :
-- imply
  (∑ ω : LocalConfig, g ω • Measure.dirac (f ω)) {a} = ∑ ω : LocalConfig, if f ω = a then g ω else 0 := by
-- proof
  apply StatMech.Universality.stt_sum_weighted_dirac_singleton g f a

/--
[stt_map_triLocalMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_map_triLocalMeasure_eq
  {p0 p1 p2 : ℝ}
  {f : LocalConfig → Bool × Bool × Bool} :
-- imply
  Measure.map f (stt_triLocalMeasure p0 p1 p2) = ∑ ω : LocalConfig, ENNReal.ofReal (localWeight p0 p1 p2 ω) • Measure.dirac (f ω) := by
-- proof
  apply StatMech.Universality.stt_map_triLocalMeasure p0 p1 p2 f

/--
[stt_triLocalMeasure_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_triLocalMeasure_univ_eq
  {p0 p1 p2 : ℝ}
-- given
  (h0 : 0 ≤ p0)
  (h0' : p0 ≤ 1)
  (h1 : 0 ≤ p1)
  (h1' : p1 ≤ 1)
  (h2 : 0 ≤ p2)
  (h2' : p2 ≤ 1) :
-- imply
  stt_triLocalMeasure p0 p1 p2 Set.univ = 1 := by
-- proof
  apply StatMech.Universality.stt_triLocalMeasure_univ p0 p1 p2 h0 h0' h1 h1' h2 h2'

/--
[stt_isProbabilityMeasure_triLocalMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_isProbabilityMeasure_triLocalMeasure_eq
  {p0 p1 p2 : ℝ}
-- given
  (h0 : 0 ≤ p0)
  (h0' : p0 ≤ 1)
  (h1 : 0 ≤ p1)
  (h1' : p1 ≤ 1)
  (h2 : 0 ≤ p2)
  (h2' : p2 ≤ 1) :
-- imply
  IsProbabilityMeasure (stt_triLocalMeasure p0 p1 p2) := by
-- proof
  apply StatMech.Universality.stt_isProbabilityMeasure_triLocalMeasure p0 p1 p2 h0 h0' h1 h1' h2 h2'

/--
[stt_connWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_connWeight_eq_eq
  {p0 p1 p2 : ℝ}
  {c : Bool × Bool × Bool}
-- given
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  (∑ ω : LocalConfig, if stt_triConn ω = c then localWeight p0 p1 p2 ω else 0) = ∑ ω : LocalConfig, if stt_starConn ω = c then localWeight (1-p0) (1-p1) (1-p2) ω else 0 := by
-- proof
  apply StatMech.Universality.stt_connWeight_eq p0 p1 p2 h c

/--
[stt_ennreal_sum_ofReal_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_ennreal_sum_ofReal_indicator_eq
  {g : LocalConfig → ℝ}
  [DecidablePred P]
-- given
  (P : LocalConfig → Prop)
  (hg : ∀ ω, 0 ≤ g ω) :
-- imply
  (∑ ω : LocalConfig, if P ω then ENNReal.ofReal (g ω) else 0) = ENNReal.ofReal (∑ ω : LocalConfig, if P ω then g ω else 0) := by
-- proof
  apply StatMech.Universality.stt_ennreal_sum_ofReal_indicator g P hg

/--
[stt_map_conn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_map_conn_eq_eq
  {p0 p1 p2 : ℝ}
-- given
  (h0 : 0 ≤ p0)
  (h0' : p0 ≤ 1)
  (h1 : 0 ≤ p1)
  (h1' : p1 ≤ 1)
  (h2 : 0 ≤ p2)
  (h2' : p2 ≤ 1)
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  Measure.map stt_triConn (stt_triLocalMeasure p0 p1 p2) = Measure.map stt_starConn (stt_triLocalMeasure (1 - p0) (1 - p1) (1 - p2)) := by
-- proof
  apply StatMech.Universality.stt_map_conn_eq p0 p1 p2 h0 h0' h1 h1' h2 h2' h

/--
[stt_starMass_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_starMass_ne_top_eq
  {p0 p1 p2 : ℝ}
  {c : Bool × Bool × Bool} :
-- imply
  stt_starMass p0 p1 p2 c ≠ ⊤ := by
-- proof
  apply StatMech.Universality.stt_starMass_ne_top p0 p1 p2 c

/--
[stt_mass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_mass_eq_eq
  {p0 p1 p2 : ℝ}
  {c : Bool × Bool × Bool}
-- given
  (h0 : 0 ≤ p0)
  (h0' : p0 ≤ 1)
  (h1 : 0 ≤ p1)
  (h1' : p1 ≤ 1)
  (h2 : 0 ≤ p2)
  (h2' : p2 ≤ 1)
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  stt_triMass p0 p1 p2 c = stt_starMass (1 - p0) (1 - p1) (1 - p2) c := by
-- proof
  apply StatMech.Universality.stt_mass_eq p0 p1 p2 h0 h0' h1 h1' h2 h2' h c

/--
[stt_triLocalMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_triLocalMeasure_singleton_eq
  {p0 p1 p2 : ℝ}
  {ω0 : LocalConfig} :
-- imply
  stt_triLocalMeasure p0 p1 p2 {ω0} = stt_triW p0 p1 p2 ω0 := by
-- proof
  apply StatMech.Universality.stt_triLocalMeasure_singleton p0 p1 p2 ω0

/--
[stt_const_mul_sum_ite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_const_mul_sum_ite_eq
  [DecidablePred P]
-- given
  (a : ℝ≥0∞)
  (g : LocalConfig → ℝ≥0∞)
  (P : LocalConfig → Prop) :
-- imply
  (∑ ω : LocalConfig, if P ω then a * g ω else 0) = a * ∑ ω : LocalConfig, if P ω then g ω else 0 := by
-- proof
  apply StatMech.Universality.stt_const_mul_sum_ite a g P

/--
[stt_coupling_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_coupling_supported_eq
  {p0 p1 p2 : ℝ}
  {ωt ωs : LocalConfig}
-- given
  (hne : stt_triConn ωt ≠ stt_starConn ωs) :
-- imply
  stt_coupling p0 p1 p2 {(ωt, ωs)} = 0 := by
-- proof
  apply StatMech.Universality.stt_coupling_supported p0 p1 p2 ωt ωs hne

/--
[stt_coupling_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_coupling_snd_eq
  {p0 p1 p2 : ℝ}
-- given
  (h0 : 0 ≤ p0)
  (h0' : p0 ≤ 1)
  (h1 : 0 ≤ p1)
  (h1' : p1 ≤ 1)
  (h2 : 0 ≤ p2)
  (h2' : p2 ≤ 1)
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  Measure.map Prod.snd (stt_coupling p0 p1 p2) = stt_triLocalMeasure (1 - p0) (1 - p1) (1 - p2) := by
-- proof
  apply StatMech.Universality.stt_coupling_snd p0 p1 p2 h0 h0' h1 h1' h2 h2' h

/--
[stt_coupling_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_coupling_fst_eq
  {p0 p1 p2 : ℝ}
-- given
  (h0 : 0 ≤ p0)
  (h0' : p0 ≤ 1)
  (h1 : 0 ≤ p1)
  (h1' : p1 ≤ 1)
  (h2 : 0 ≤ p2)
  (h2' : p2 ≤ 1)
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  Measure.map Prod.fst (stt_coupling p0 p1 p2) = stt_triLocalMeasure p0 p1 p2 := by
-- proof
  apply StatMech.Universality.stt_coupling_fst p0 p1 p2 h0 h0' h1 h1' h2 h2' h

/--
[stt_exists_starTriangle_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean)
-/
@[path]
private lemma stt_exists_starTriangle_coupling_eq
  {p0 p1 p2 : ℝ}
-- given
  (h0 : 0 ≤ p0)
  (h0' : p0 ≤ 1)
  (h1 : 0 ≤ p1)
  (h1' : p1 ≤ 1)
  (h2 : 0 ≤ p2)
  (h2' : p2 ≤ 1)
  (h : IsCriticalTri p0 p1 p2) :
-- imply
  ∃ γ : Measure (LocalConfig × LocalConfig), Measure.map Prod.fst γ = stt_triLocalMeasure p0 p1 p2 ∧ Measure.map Prod.snd γ = stt_triLocalMeasure (1 - p0) (1 - p1) (1 - p2) ∧ ∀ ωt ωs : LocalConfig, stt_triConn ωt ≠ stt_starConn ωs → γ {(ωt, ωs)} = 0 := by
-- proof
  apply StatMech.Universality.stt_exists_starTriangle_coupling p0 p1 p2 h0 h0' h1 h1' h2 h2' h


-- created on 2026-10-23
