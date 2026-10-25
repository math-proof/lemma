import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexSectorPosition_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexSectorPosition_singleton_eq
  {N : ℕ}
  {i : Fin N} :
-- imply
  sixVertexSectorPosition (sixVertexSingletonSector i) 0 = i := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_singleton i

/--
[sixVertexSector_eq_singleton_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexSector_eq_singleton_position_eq
  {N : ℕ}
  {x : SixVertexSector N 1} :
-- imply
  x = sixVertexSingletonSector (sixVertexSectorPosition x 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_eq_singleton_position x

/--
[sixVertexOne_interlaced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexOne_interlaced_eq
  {N : ℕ}
  {x y : SixVertexSector N 1} :
-- imply
  SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) := by
-- proof
  apply StatMech.FrontierD.sixVertexOne_interlaced x y

/--
[sixVertexOne_rowDistance_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexOne_rowDistance_eq_two_eq
  {N : ℕ}
  {x y : SixVertexSector N 1}
-- given
  (hxy : x ≠ y) :
-- imply
  sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexOne_rowDistance_eq_two hxy

/--
[sixVertexSectorTransfer_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_one_apply_eq
  {N : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N 1} :
-- imply
  sixVertexSectorTransfer N 1 c x y = if x = y then 2 else c ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_one_apply c x y

/--
[sixVertexBetheAmplitude_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_one_eq
  {c : ℝ}
  {p : Fin 1 → ℝ}
  {σ : Equiv.Perm (Fin 1)} :
-- imply
  sixVertexBetheAmplitude c p σ = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_one c p σ

/--
[sixVertexCoordinateBetheWave_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheWave_one_eq
  {N : ℕ}
  {c : ℝ}
  {p : Fin 1 → ℝ}
  {x : SixVertexSector N 1} :
-- imply
  sixVertexCoordinateBetheWave c p x = sixVertexBethePhase (p 0) ^ (sixVertexSectorPosition x 0).val := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheWave_one c p x

/--
[sixVertexBetheEigenvalueCandidate_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexBetheEigenvalueCandidate_one_eq
  {c : ℝ}
  {p : Fin 1 → ℝ}
-- given
  (hphase : sixVertexBethePhase (p 0) ≠ 1) :
-- imply
  sixVertexBetheEigenvalueCandidate c p = 2 - c ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheEigenvalueCandidate_one p hphase

/--
[sum_sixVertexBethePhase_pow_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sum_sixVertexBethePhase_pow_eq_zero_eq
  {N : ℕ}
  {p : ℝ}
-- given
  (hphase : sixVertexBethePhase p ≠ 1)
  (hperiodic : sixVertexBethePhase p ^ N = 1) :
-- imply
  ∑ i : Fin N, sixVertexBethePhase p ^ i.val = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePhase_pow_eq_zero hphase hperiodic

/--
[sixVertexMultiplicativeBethe_one_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexMultiplicativeBethe_one_periodic_eq
  {c : ℝ}
  {N : ℕ}
  {p : Fin 1 → ℝ}
-- given
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N 1 p) :
-- imply
  sixVertexBethePhase (p 0) ^ N = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexMultiplicativeBethe_one_periodic p hp

/--
[sixVertexBethePhase_ne_one_of_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexBethePhase_ne_one_of_mem_Ioo_eq
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (-Real.pi) Real.pi)
  (hp0 : p ≠ 0) :
-- imply
  sixVertexBethePhase p ≠ 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePhase_ne_one_of_mem_Ioo hp hp0

/--
[sixVertexCoordinateBetheEigenrelation_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheEigenrelation_one_eq
  {N : ℕ}
  {c : ℝ}
  {p : Fin 1 → ℝ}
-- given
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N 1 p)
  (hphase : sixVertexBethePhase (p 0) ≠ 1) :
-- imply
  SixVertexCoordinateBetheEigenrelation (N := N) c p := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheEigenrelation_one c p hp hphase

/--
[sixVertexCoordinateBetheEigenrelation_one_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheEigenrelation_one_of_nonzero_eq
  {N : ℕ}
  {c : ℝ}
  {p : Fin 1 → ℝ}
-- given
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N 1 p)
  (hmem : p 0 ∈ Set.Ioo (-Real.pi) Real.pi)
  (hp0 : p 0 ≠ 0) :
-- imply
  SixVertexCoordinateBetheEigenrelation (N := N) c p := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheEigenrelation_one_of_nonzero c p hp hmem hp0


-- created on 2026-10-23
