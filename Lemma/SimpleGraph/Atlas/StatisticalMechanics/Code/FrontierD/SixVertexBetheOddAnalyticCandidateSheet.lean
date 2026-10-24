import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddAnalyticCandidateSheet
open Finset Filter Topology Matrix StatMech StatMech.FrontierD


/--
[sixVertexZeroPhaseBetheEigenvalueCandidate_oddSymmetric_eq_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexZeroPhaseBetheEigenvalueCandidate_oddSymmetric_eq_value_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q)) :
-- imply
  sixVertexZeroPhaseBetheEigenvalueCandidate c N (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) = (sixVertexZeroPhaseBetheEigenvalueValue c N (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) : Complex) := by
-- proof
  apply StatMech.FrontierD.sixVertexZeroPhaseBetheEigenvalueCandidate_oddSymmetric_eq_value hc q hopen

/--
[analyticOnNhd_sixVertexOddZeroPhaseBetheEigenvalueValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddAnalyticCandidateSheet.lean)
-/
@[path]
private lemma analyticOnNhd_sixVertexOddZeroPhaseBetheEigenvalueValue_eq
  {N m : Nat}
  {U : Set Real}
  {roots : C(Real, Fin ((m + 1) + m) → Real)}
-- given
  (hUopen : IsOpen U)
  (hUtwo : U ⊆ Set.Ioi 2)
  (hrootAnalytic : AnalyticOnNhd Real roots U)
  (hopen : ∀ t ∈ U, SixVertexOpenRootSimplex (roots t)) :
-- imply
  AnalyticOnNhd Real (fun t => sixVertexZeroPhaseBetheEigenvalueValue t N (roots t) (sixVertexOddCentralIndex m)) U := by
-- proof
  apply StatMech.FrontierD.analyticOnNhd_sixVertexOddZeroPhaseBetheEigenvalueValue hUopen hUtwo roots hrootAnalytic hopen

/--
[sixVertexZeroPhase_characteristicDet_eq_zero_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexZeroPhase_characteristicDet_eq_zero_of_nonzero_eq
  {N n : Nat}
  {c mu : Real}
  {p : Fin n → Real}
  {ell : Fin n}
-- given
  (heigen : SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p ell)
  (hcandidate : sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell = (mu : Complex))
  (hwave : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
-- imply
  Matrix.det (mu • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) - sixVertexSectorTransfer N n c) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexZeroPhase_characteristicDet_eq_zero_of_nonzero heigen hcandidate hwave

/--
[sixVertexAnalyticOddSymmetricBetheCandidate_eqOn_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddAnalyticCandidateSheet.lean)
-/
@[path]
private lemma sixVertexAnalyticOddSymmetricBetheCandidate_eqOn_top_eq
  {N m : Nat}
  {U : Set Real}
  {roots : C(Real, Fin ((m + 1) + m) → Real)}
  {c₀ : Real}
-- given
  (hm : 0 < m)
  (hn : (m + 1) + m ≤ N)
  (hU : IsPreconnected U)
  (hUopen : IsOpen U)
  (hUtwo : U ⊆ Set.Ioi 2)
  (hopen : ∀ t ∈ U, SixVertexOpenRootSimplex (roots t))
  (hsol : ∀ t ∈ U, SixVertexSatisfiesBetheEquations t N ((m + 1) + m) (roots t))
  (hrootAnalytic : AnalyticOnNhd Real roots U)
  (hc₀U : c₀ ∈ U)
  (hwave : sixVertexCoordinateBetheWave (N := N) c₀ (roots c₀) ≠ 0)
  (hbase : sixVertexZeroPhaseBetheEigenvalueValue c₀ N (roots c₀) (sixVertexOddCentralIndex m) = sixVertexSectorTopEigenvalue N ((m + 1) + m) hn c₀) :
-- imply
  Set.EqOn (fun t => sixVertexZeroPhaseBetheEigenvalueValue t N (roots t) (sixVertexOddCentralIndex m)) (sixVertexSectorTopEigenvalue N ((m + 1) + m) hn) U := by
-- proof
  apply StatMech.FrontierD.sixVertexAnalyticOddSymmetricBetheCandidate_eqOn_top hm hn hU hUopen hUtwo roots hopen hsol hrootAnalytic hc₀U hwave hbase


-- created on 2026-10-23
