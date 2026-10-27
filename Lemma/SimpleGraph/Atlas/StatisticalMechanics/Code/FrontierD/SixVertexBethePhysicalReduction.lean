import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexBetheMonomial_eq_intMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalReduction.lean)
-/
@[path]
private lemma sixVertexBetheMonomial_eq_intMonomial_eq
  {N n : Nat}
  {sigma : Equiv.Perm (Fin n)}
  {x : SixVertexSector N n}
-- given
  (p : Fin n -> Real) :
-- imply
  sixVertexBetheMonomial p sigma x = sixVertexBetheIntMonomial p sigma (sixVertexSectorIntCoordinates x) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheMonomial_eq_intMonomial p sigma x

/--
[sixVertexCoordinateBetheWave_eq_intWave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalReduction.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheWave_eq_intWave_eq
  {N n : Nat}
  {c : Real}
  {x : SixVertexSector N n}
-- given
  (p : Fin n -> Real) :
-- imply
  sixVertexCoordinateBetheWave c p x = sixVertexCoordinateBetheIntWave c p (sixVertexSectorIntCoordinates x) := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheWave_eq_intWave c p x

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.cyclicWordEigenvalue_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalReduction.lean)
-/
@[path]
private lemma cyclicWordEigenvalue_sector_eq
  {c : Real}
  {N n : Nat}
  {x : SixVertexSector N (n + 1)}
-- given
  (hc : 2 < c)
  (p : Fin (n + 1) -> Real)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hphase : forall j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ w : Finset (Fin (n + 1)), ∑ sigma, sixVertexBetheAmplitude c p sigma * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) sigma w * sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) sigma (sixVertexSectorIntCoordinates x) w) = sixVertexBetheEigenvalueCandidate c p * sixVertexCoordinateBetheWave c p x := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.cyclicWordEigenvalue_sector hc p hp x hphase

/--
[sixVertexCoordinateBetheEigenrelation_of_physicalWordExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalReduction.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheEigenrelation_of_physicalWordExpansion_eq
  {c : Real}
  {N n : Nat}
-- given
  (hc : 2 < c)
  (p : Fin (n + 1) -> Real)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hphase : forall j, sixVertexBethePhase (p j) ≠ 1)
  (hexpand : SixVertexPhysicalWordExpansion (N := N) c p) :
-- imply
  SixVertexCoordinateBetheEigenrelation (N := N) c p := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheEigenrelation_of_physicalWordExpansion hc p hp hphase hexpand


-- created on 2026-10-23
