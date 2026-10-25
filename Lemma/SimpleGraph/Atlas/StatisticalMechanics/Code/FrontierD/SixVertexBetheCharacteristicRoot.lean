import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCharacteristicRoot
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexCoordinateBethe_characteristicDet_eq_zero_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCharacteristicRoot.lean)
-/
@[path]
private lemma sixVertexCoordinateBethe_characteristicDet_eq_zero_of_nonzero_eq
  {N n : Nat}
  {c mu : Real}
  {p : Fin n → Real}
-- given
  (heigen : SixVertexCoordinateBetheEigenrelation (N := N) c p)
  (hcandidate : sixVertexBetheEigenvalueCandidate c p = (mu : Complex))
  (hwave : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
-- imply
  Matrix.det (mu • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) - sixVertexSectorTransfer N n c) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBethe_characteristicDet_eq_zero_of_nonzero heigen hcandidate hwave

/--
[sixVertexBetheCandidate_eqOn_top_of_analyticSheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCharacteristicRoot.lean)
-/
@[path]
private lemma sixVertexBetheCandidate_eqOn_top_of_analyticSheet_eq
  {N n : Nat}
  {U : Set Real}
  {c : Real}
  {p : Real → Fin n → Real}
  {f : Real → Real}
-- given
  (hn : n ≤ N)
  (hU : IsPreconnected U)
  (hUopen : IsOpen U)
  (hUpos : U ⊆ Set.Ioi 0)
  (hcU : c ∈ U)
  (hc : 0 < c)
  (hanalytic : AnalyticOnNhd Real f U)
  (heigen : ∀ t ∈ U, SixVertexCoordinateBetheEigenrelation (N := N) t (p t))
  (hcandidate : ∀ t ∈ U, sixVertexBetheEigenvalueCandidate t (p t) = (f t : Complex))
  (hwave : ∀ t ∈ U, sixVertexCoordinateBetheWave (N := N) t (p t) ≠ 0)
  (hbase : f c = sixVertexSectorTopEigenvalue N n hn c) :
-- imply
  Set.EqOn f (sixVertexSectorTopEigenvalue N n hn) U := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCandidate_eqOn_top_of_analyticSheet hn hU hUopen hUpos hcU hc p f hanalytic heigen hcandidate hwave hbase

/--
[sixVertexBetheCandidate_eqOn_top_of_analyticSheet_of_nonzero_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCharacteristicRoot.lean)
-/
@[path]
private lemma sixVertexBetheCandidate_eqOn_top_of_analyticSheet_of_nonzero_at_eq
  {N n : Nat}
  {U : Set Real}
  {c : Real}
  {p : Real → Fin n → Real}
  {f : Real → Real}
-- given
  (hn : n ≤ N)
  (hU : IsPreconnected U)
  (hUopen : IsOpen U)
  (hUpos : U ⊆ Set.Ioi 0)
  (hcU : c ∈ U)
  (hc : 0 < c)
  (hanalytic : AnalyticOnNhd Real f U)
  (heigen : ∀ t ∈ U, SixVertexCoordinateBetheEigenrelation (N := N) t (p t))
  (hcandidate : ∀ t ∈ U, sixVertexBetheEigenvalueCandidate t (p t) = (f t : Complex))
  (hwaveContinuous : ContinuousAt (fun t => sixVertexCoordinateBetheWave (N := N) t (p t)) c)
  (hwave : sixVertexCoordinateBetheWave (N := N) c (p c) ≠ 0)
  (hbase : f c = sixVertexSectorTopEigenvalue N n hn c) :
-- imply
  Set.EqOn f (sixVertexSectorTopEigenvalue N n hn) U := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCandidate_eqOn_top_of_analyticSheet_of_nonzero_at hn hU hUopen hUpos hcU hc p f hanalytic heigen hcandidate hwaveContinuous hwave hbase

/--
[sixVertexSymmetricBethe_characteristicDet_eq_zero_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCharacteristicRoot.lean)
-/
@[path]
private lemma sixVertexSymmetricBethe_characteristicDet_eq_zero_of_nonzero_eq
  {N k : Nat}
  {c : Real}
  {p : Fin k → Real}
-- given
  (heigen : SixVertexCoordinateBetheEigenrelation (N := N) c (sixVertexPairedRootFamily p))
  (hwave : sixVertexCoordinateBetheWave (N := N) c (sixVertexPairedRootFamily p) ≠ 0) :
-- imply
  Matrix.det (sixVertexSymmetricBetheEigenvalueValue c p • (1 : Matrix (SixVertexSector N (k + k)) (SixVertexSector N (k + k)) Real) - sixVertexSectorTransfer N (k + k) c) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricBethe_characteristicDet_eq_zero_of_nonzero heigen hwave

/--
[sixVertexSymmetricBetheCandidate_eqOn_top_of_analyticSheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCharacteristicRoot.lean)
-/
@[path]
private lemma sixVertexSymmetricBetheCandidate_eqOn_top_of_analyticSheet_eq
  {N k : Nat}
  {U : Set Real}
  {c : Real}
  {p : Real → Fin k → Real}
-- given
  (hn : k + k ≤ N)
  (hU : IsPreconnected U)
  (hUopen : IsOpen U)
  (hUpos : U ⊆ Set.Ioi 0)
  (hcU : c ∈ U)
  (hc : 0 < c)
  (hanalytic : AnalyticOnNhd Real (fun t => sixVertexSymmetricBetheEigenvalueValue t (p t)) U)
  (heigen : ∀ t ∈ U, SixVertexCoordinateBetheEigenrelation (N := N) t (sixVertexPairedRootFamily (p t)))
  (hwave : ∀ t ∈ U, sixVertexCoordinateBetheWave (N := N) t (sixVertexPairedRootFamily (p t)) ≠ 0)
  (hbase : sixVertexSymmetricBetheEigenvalueValue c (p c) = sixVertexSectorTopEigenvalue N (k + k) hn c) :
-- imply
  Set.EqOn (fun t => sixVertexSymmetricBetheEigenvalueValue t (p t)) (sixVertexSectorTopEigenvalue N (k + k) hn) U := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricBetheCandidate_eqOn_top_of_analyticSheet hn hU hUopen hUpos hcU hc p hanalytic heigen hwave hbase


-- created on 2026-10-23
