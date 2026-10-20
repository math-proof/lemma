import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MinimalLatticeWalkCount
open scoped BigOperators
open MetaMathlibExt


/--
[minimal_lattice_walk_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalLatticeWalkCount.lean)
-/
@[path]
private lemma minimal_lattice_walk_count_eq
  {a b : ℕ} :
-- imply
  Finset.card (Finset.univ.filter (fun f : Fin (max a b) → Fin 3 =>
    (∑ i, (![1, 0, 1] : Fin 3 → ℕ) (f i)) = a ∧
    (∑ i, (![0, 1, 1] : Fin 3 → ℕ) (f i)) = b)) =
    Nat.choose (max a b) (min a b) := by
-- proof
  apply MetaMathlibExt.minimal_lattice_walk_count a b


-- created on 2026-10-20
