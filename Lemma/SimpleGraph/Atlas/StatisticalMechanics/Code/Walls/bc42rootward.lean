import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc42rootward.Part2
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc42_removeSite_openSubgraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc42rootward.lean)
-/
@[path]
private lemma bc42_removeSite_openSubgraph_le_eq
  {d : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  openSubgraph d (removeSite y ω) ≤ openSubgraph d ω := by
-- proof
  apply StatMech.Walls.bc42_removeSite_openSubgraph_le y ω

/--
[bc42_avoidingWalk_of_connected_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc42rootward.lean)
-/
@[path]
private lemma bc42_avoidingWalk_of_connected_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y z : Site d}
-- given
  (hxy : x ≠ y)
  (h : Connected d (removeSite y ω) x z) :
-- imply
  ∃ p : (openSubgraph d ω).Walk x z, ∀ v ∈ p.support, v ≠ y := by
-- proof
  apply StatMech.Walls.bc42_avoidingWalk_of_connected_removeSite ω hxy h

/--
[bc42_avoidingWalk_iff_connected_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc42rootward.lean)
-/
@[path]
private lemma bc42_avoidingWalk_iff_connected_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y z : Site d}
-- given
  (hxy : x ≠ y) :
-- imply
  (∃ p : (openSubgraph d ω).Walk x z, ∀ v ∈ p.support, v ≠ y) ↔ Connected d (removeSite y ω) x z := by
-- proof
  apply StatMech.Walls.bc42_avoidingWalk_iff_connected_removeSite ω hxy

/--
[bc42_rootWardAvoidingWalk_allParRank_false_of_farParent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc42rootward.lean)
-/
@[path]
private lemma bc42_rootWardAvoidingWalk_allParRank_false_of_farParent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ z₀ : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hy0box : y₀ ∈ box d n)
  (htriy0 : IsTrifurcation d ω y₀)
  (hne : x₀ ≠ y₀)
  (hconn : Connected d ω x₀ y₀)
  (hadj : bc37_ArmAdjacent ω n y₀ z₀)
  (hx0z0 : x₀ ≠ z₀)
  (hfar : ¬ Connected d (removeSite y₀ ω) x₀ z₀) :
-- imply
  ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootWardAvoidingWalk ω n rank par := by
-- proof
  apply StatMech.Walls.bc42_rootWardAvoidingWalk_allParRank_false_of_farParent ω n hx0box htri0 hy0box htriy0 hne hconn hadj hx0z0 hfar

/--
[bc42_chainFar_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc42rootward.lean)
-/
@[path]
private lemma bc42_chainFar_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (x₀ y₀ z₀ : Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop), (∀ c u v, R c u v ↔ bc42_chainFarLab c u = bc42_chainFarLab c v) ∧ x₀ ≠ y₀ ∧ x₀ ≠ z₀ ∧ y₀ ≠ z₀ ∧ R 0 y₀ z₀ ∧ ¬ R 1 x₀ z₀ := by
-- proof
  apply StatMech.Walls.bc42_chainFar_consistent


-- created on 2026-10-23
