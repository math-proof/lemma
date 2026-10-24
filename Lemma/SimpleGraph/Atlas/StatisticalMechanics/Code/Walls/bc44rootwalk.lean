import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc44rootwalk
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc44_farWitnessRank_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc44rootwalk.lean)
-/
@[path]
private lemma bc44_farWitnessRank_distinct_eq
  {d : ℕ}
  {x₀ y₀ z₀ : Site d}
  {a b : Site d}
-- given
  (hxy : x₀ ≠ y₀)
  (hxz : x₀ ≠ z₀)
  (hyz : y₀ ≠ z₀)
  (ha : a = x₀ ∨ a = y₀ ∨ a = z₀)
  (hb : b = x₀ ∨ b = y₀ ∨ b = z₀)
  (hab : a ≠ b) :
-- imply
  bc44_farWitnessRank y₀ z₀ a ≠ bc44_farWitnessRank y₀ z₀ b := by
-- proof
  apply StatMech.Walls.bc44_farWitnessRank_distinct hxy hxz hyz ha hb hab

/--
[bc44_farWitness_rank_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc44rootwalk.lean)
-/
@[path]
private lemma bc44_farWitness_rank_injective_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ z₀ : Site d}
-- given
  (hxy : x₀ ≠ y₀)
  (hxz : x₀ ≠ z₀)
  (hyz : y₀ ≠ z₀)
  (hexhaust : ∀ a, a ∈ box d n → IsTrifurcation d ω a → a = x₀ ∨ a = y₀ ∨ a = z₀) :
-- imply
  ∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b → a ≠ b → Connected d ω a b → bc44_farWitnessRank y₀ z₀ a ≠ bc44_farWitnessRank y₀ z₀ b := by
-- proof
  apply StatMech.Walls.bc44_farWitness_rank_injective ω n hxy hxz hyz hexhaust

/--
[bc44_rootWardRootParent_allRankPar_false_of_farParent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc44rootwalk.lean)
-/
@[path]
private lemma bc44_rootWardRootParent_allRankPar_false_of_farParent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ z₀ : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hy0box : y₀ ∈ box d n)
  (htriy0 : IsTrifurcation d ω y₀)
  (hz0box : z₀ ∈ box d n)
  (htriz0 : IsTrifurcation d ω z₀)
  (hxy : x₀ ≠ y₀)
  (hxz : x₀ ≠ z₀)
  (hyz : y₀ ≠ z₀)
  (hexhaust : ∀ a, a ∈ box d n → IsTrifurcation d ω a → a = x₀ ∨ a = y₀ ∨ a = z₀)
  (hconn : Connected d ω x₀ y₀)
  (hadj : bc37_ArmAdjacent ω n y₀ z₀)
  (hfar : ¬ Connected d (removeSite y₀ ω) x₀ z₀) :
-- imply
  ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc43_RootWardRootParent ω n rank par := by
-- proof
  apply StatMech.Walls.bc44_rootWardRootParent_allRankPar_false_of_farParent ω n hx0box htri0 hy0box htriy0 hz0box htriz0 hxy hxz hyz hexhaust hconn hadj hfar

/--
[bc44_chainFar_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc44rootwalk.lean)
-/
@[path]
private lemma bc44_chainFar_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (x₀ y₀ z₀ : Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop), (∀ c u v, R c u v ↔ bc44_chainLab c u = bc44_chainLab c v) ∧ x₀ ≠ y₀ ∧ x₀ ≠ z₀ ∧ y₀ ≠ z₀ ∧ R 2 x₀ y₀ ∧ R 2 x₀ z₀ ∧ R 0 y₀ z₀ ∧ ¬ R 1 x₀ z₀ := by
-- proof
  apply StatMech.Walls.bc44_chainFar_consistent

/--
[bc44_geometryConsistentRootWard_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc44rootwalk.lean)
-/
@[path]
private lemma bc44_geometryConsistentRootWard_true_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {par : Site d → Site d} :
-- imply
  bc44_GeometryConsistentRootWard ω n rank par := by
-- proof
  apply StatMech.Walls.bc44_geometryConsistentRootWard_true ω n rank par


-- created on 2026-10-23
