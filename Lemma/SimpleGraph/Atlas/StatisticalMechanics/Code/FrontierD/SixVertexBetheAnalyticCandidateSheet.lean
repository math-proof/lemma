import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[continuous_sixVertexCoordinateBetheWave_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma continuous_sixVertexCoordinateBetheWave_branch_eq
  {N n : Nat}
  {p : Real → Fin n → Real}
-- given
  (hp : Continuous p) :
-- imply
  Continuous (fun c => sixVertexCoordinateBetheWave (N := N) c (p c)) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexCoordinateBetheWave_branch p hp

/--
[sixVertexBetheEigenvalueCandidate_evenSymmetricLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexBetheEigenvalueCandidate_evenSymmetricLift_eq
  {m : Nat}
  {c : Real}
  {q : Fin m → Real} :
-- imply
  sixVertexBetheEigenvalueCandidate c (sixVertexEvenSymmetricLift m q) = sixVertexSymmetricBetheEigenvalueCandidate c q := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheEigenvalueCandidate_evenSymmetricLift c q

/--
[sixVertexBetheEigenvalueCandidate_evenSymmetricLift_eq_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexBetheEigenvalueCandidate_evenSymmetricLift_eq_value_eq
  {m : Nat}
  {c : Real}
  {q : Fin m → Real} :
-- imply
  sixVertexBetheEigenvalueCandidate c (sixVertexEvenSymmetricLift m q) = (sixVertexSymmetricBetheEigenvalueValue c q : Complex) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheEigenvalueCandidate_evenSymmetricLift_eq_value c q

/--
[sixVertexSymmetricBetheEigenvalueKernel_eq_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexSymmetricBetheEigenvalueKernel_eq_value_eq
  {m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hq : ∀ j, q j ∈ Set.Ioo 0 Real.pi) :
-- imply
  sixVertexSymmetricBetheEigenvalueKernel c q = sixVertexSymmetricBetheEigenvalueValue c q := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricBetheEigenvalueKernel_eq_value c q hq

/--
[analyticOnNhd_sixVertexSymmetricBetheEigenvalueKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma analyticOnNhd_sixVertexSymmetricBetheEigenvalueKernel_eq
  {m : Nat}
  {U : Set Real}
  {q : Real → Fin m → Real}
-- given
  (hqAnalytic : AnalyticOnNhd Real q U)
  (hq : ∀ c ∈ U, ∀ j, q c j ∈ Set.Ioo 0 Real.pi) :
-- imply
  AnalyticOnNhd Real (fun c => sixVertexSymmetricBetheEigenvalueKernel c (q c)) U := by
-- proof
  apply StatMech.FrontierD.analyticOnNhd_sixVertexSymmetricBetheEigenvalueKernel q hqAnalytic hq

/--
[sixVertexEvenSymmetricLift_positive_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_positive_mem_Ioo_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
-- imply
  q j ∈ Set.Ioo 0 Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_positive_mem_Ioo hopen j

/--
[sixVertexEvenSymmetricLift_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_ne_zero_eq
  {m : Nat}
  {q : Fin m → Real}
  {i : Fin (m + m)}
-- given
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
-- imply
  sixVertexEvenSymmetricLift m q i ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_ne_zero hopen i

/--
[sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top_eq
  {N m : Nat}
  {U : Set Real}
  {roots : C(Real, Fin (m + m) → Real)}
  {c₀ : Real}
-- given
  (hm : 0 < m)
  (hn : m + m ≤ N)
  (hU : IsPreconnected U)
  (hUopen : IsOpen U)
  (hUtwo : U ⊆ Set.Ioi 2)
  (hopen : ∀ t ∈ U, SixVertexOpenRootSimplex (roots t))
  (hsol : ∀ t ∈ U, SixVertexSatisfiesBetheEquations t N (m + m) (roots t))
  (hrootAnalytic : AnalyticOnNhd Real roots U)
  (hc₀U : c₀ ∈ U)
  (hwave : sixVertexCoordinateBetheWave (N := N) c₀ (roots c₀) ≠ 0)
  (hbase : sixVertexSymmetricBetheEigenvalueKernel c₀ (sixVertexEvenPositiveHalfProjection m (roots c₀)) = sixVertexSectorTopEigenvalue N (m + m) hn c₀) :
-- imply
  Set.EqOn (fun t => sixVertexSymmetricBetheEigenvalueKernel t (sixVertexEvenPositiveHalfProjection m (roots t))) (sixVertexSectorTopEigenvalue N (m + m) hn) U := by
-- proof
  apply StatMech.FrontierD.sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top hm hn hU hUopen hUtwo roots hopen hsol hrootAnalytic hc₀U hwave hbase

/--
[eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero_eq
  {k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, ∀ hc : 2 < c, sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc k) = sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega) c ∧ sixVertexCoordinateBetheWave (N := sixVertexFourWidth 0 k) c (sixVertexHalfFilledBetheRoots hc k) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero k

/--
[sixVertexHalfFilledBetheContinuationPoint_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheContinuationPoint_parameter_eq
  {a b c₀ : Real}
  {k : Nat}
-- given
  (ha : 2 < a)
  (hc₀ : c₀ ∈ Set.Icc a b) :
-- imply
  (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k).1.1 = c₀ := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheContinuationPoint_parameter ha hc₀ k

/--
[sixVertexHalfFilledBetheContinuationPoint_roots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheContinuationPoint_roots_eq
  {a b c₀ : Real}
  {k : Nat}
-- given
  (ha : 2 < a)
  (hc₀ : c₀ ∈ Set.Icc a b) :
-- imply
  (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k).1.2 = sixVertexHalfFilledBetheRoots (ha.trans_le hc₀.1) k := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheContinuationPoint_roots ha hc₀ k

/--
[sixVertexHalfFilledBetheContinuationPoint_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheContinuationPoint_projection_eq
  {a b c₀ : Real}
  {k : Nat}
-- given
  (ha : 2 < a)
  (hc₀ : c₀ ∈ Set.Icc a b) :
-- imply
  sixVertexBetheContinuationProjection (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k) = ⟨c₀, hc₀⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheContinuationPoint_projection ha hc₀ k

/--
[exists_sixVertexHalfFilledPerronSheet_of_densityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean)
-/
@[path]
private lemma exists_sixVertexHalfFilledPerronSheet_of_densityGauge_eq
  {a b c₀ : Real}
  {k : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower inner outer : Real}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Ioo a b)
  (hrhoEq : ∀ t : Set.Icc a b, SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt rho t))
  (hrhoMass : ∀ t : Set.Icc a b, ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (hio : inner < outer)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hinner : ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFiniteDensityContinuumErrorOfLower t.1 (sixVertexFourWidth 0 k) (rhoLower / 2) ≤ inner)
  (hmargin : ∀ t : Set.Icc a b, sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 (sixVertexFourWidth 0 k) (rhoLower / 2) < 2 * Real.pi)
  (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) rho (sixVertexHalfFilledBetheContinuationPoint ha ⟨hc₀.1.le, hc₀.2.le⟩ k) < outer)
  (hbase : sixVertexSymmetricBetheEigenvalueValue c₀ (sixVertexPositiveHalfBetheRoots (ha.trans hc₀.1) k) = sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega) c₀)
  (hwave : sixVertexCoordinateBetheWave (N := sixVertexFourWidth 0 k) c₀ (sixVertexHalfFilledBetheRoots (ha.trans hc₀.1) k) ≠ 0) :
-- imply
  ∃ roots : C(Real, Fin ((k + 1) + (k + 1)) → Real), roots c₀ = sixVertexHalfFilledBetheRoots (ha.trans hc₀.1) k ∧ (∀ t ∈ Set.Icc a b, SixVertexOpenRootSimplex (roots t) ∧ SixVertexSatisfiesBetheEquations t (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (roots t)) ∧ AnalyticOnNhd Real roots (Set.Ioo a b) ∧ Set.EqOn (fun t => sixVertexSymmetricBetheEigenvalueKernel t (sixVertexEvenPositiveHalfProjection (k + 1) (roots t))) (sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega)) (Set.Ioo a b) ∧ ∀ t (ht : t ∈ Set.Icc a b), ∃ z : SixVertexBetheContinuationSpace a b (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)), sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) rho z ≤ inner ∧ z.1.1 = t ∧ z.1.2 = roots t := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexHalfFilledPerronSheet_of_densityGauge ha hab hc₀ k rho hrhoEq hrhoMass hrhoLower hrho hio houter hinner hmargin hz₀g hbase hwave


-- created on 2026-10-23
