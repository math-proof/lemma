import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
open StatMech StatMech.Universality


/--
[tailDependentEndpointRace_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTailEndpointRace.lean)
-/
@[path]
private lemma tailDependentEndpointRace_weight_le_eq
  {m t : Nat}
  {level : Int}
-- given
  (target : (j : Fin (t + 1)) -> IsingLineFirstBoundaryFamily m j -> IsingEndpointRaceTail t j -> Int)
  (hm : 0 < m)
  (ht : t <= m * m) :
-- imply
  Nat.card (IsingTailDependentEndpointRaceFamily m t level target) / (4 : Real) ^ t <= 24 / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.tailDependentEndpointRace_weight_le m t level target hm ht

/--
[tailDependentEndpointRace_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTailEndpointRace.lean)
-/
@[path]
private lemma tailDependentEndpointRace_diffusive_weight_le_eq
  {rho m : Nat}
  {level : Int}
-- given
  (target : (j : Fin (rho * rho + 1)) -> IsingLineFirstBoundaryFamily m j -> IsingEndpointRaceTail (rho * rho) j -> Int)
  (hρ : 0 < rho)
  (hm : rho <= m) :
-- imply
  Nat.card (IsingTailDependentEndpointRaceFamily m (rho * rho) level target) / (4 : Real) ^ (rho * rho) <= 24 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.tailDependentEndpointRace_diffusive_weight_le rho m level target hρ hm


-- created on 2026-10-23
