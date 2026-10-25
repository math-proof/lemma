import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc62fixpointfin3
open Finset StatMech StatMech.Walls


/--
[rc62_fixpoint_wall_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62fixpointfin3.lean)
-/
@[path]
private lemma rc62_fixpoint_wall_fin3_eq :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 3)), rc62_isDown3 𝒜 = true → rc62_isUp3 ℬ = true → (rc20_famCylBoxComp 3 𝒜 ℬ).card ≤ (rc20_reflInterComp 3 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc62_fixpoint_wall_fin3


-- created on 2026-10-23
