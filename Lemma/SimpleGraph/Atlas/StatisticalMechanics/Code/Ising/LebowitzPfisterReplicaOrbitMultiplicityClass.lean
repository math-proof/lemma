import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitMultiplicityClass
open Finset StatMech StatMech.Ising


/--
[lpReplicaEligibleInactivePairs_card_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitMultiplicityClass.lean)
-/
@[path]
private lemma lpReplicaEligibleInactivePairs_card_le_three_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (edge : α -> β) :
-- imply
  (lpReplicaEligibleInactivePairs edge).card ≤ 3 := by
-- proof
  apply StatMech.Ising.lpReplicaEligibleInactivePairs_card_le_three edge


-- created on 2026-10-23
