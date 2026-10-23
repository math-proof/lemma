import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Arrow
open BooleanFourier


/--
[prefersOver_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma prefersOver_of_lt_eq
  {m : ℕ}
  {σ : Equiv.Perm (Fin m)}
  {a b : Fin m}
-- given
  (h : σ a < σ b) :
-- imply
  prefersOver σ a b = true := by
-- proof
  apply BooleanFourier.prefersOver_of_lt h

/--
[not_prefersOver_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma not_prefersOver_of_lt_eq
  {m : ℕ}
  {σ : Equiv.Perm (Fin m)}
  {a b : Fin m}
-- given
  (h : σ b < σ a) :
-- imply
  prefersOver σ a b = false := by
-- proof
  apply BooleanFourier.not_prefersOver_of_lt h

/--
[exists_perm_placing_at_positions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma exists_perm_placing_at_positions_eq
  {m : ℕ}
  {a b c : Fin m}
-- given
  (hm : m ≥ 3)
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c) :
-- imply
  ∃ σ : Equiv.Perm (Fin m), σ a = ⟨0, by omega⟩ ∧ σ b = ⟨1, by omega⟩ ∧ σ c = ⟨2, by omega⟩ := by
-- proof
  apply BooleanFourier.exists_perm_placing_at_positions hm a b c hab hbc hac

/--
[exists_perm_for_valid_triple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma exists_perm_for_valid_triple_eq
  {m : ℕ}
  {a b c : Fin m}
  {pab pbc pac : Bool}
-- given
  (hm : m ≥ 3)
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c)
  (hvalid : pab = pbc → pac = pab) :
-- imply
  ∃ σ : Equiv.Perm (Fin m), prefersOver σ a b = pab ∧ prefersOver σ b c = pbc ∧ prefersOver σ a c = pac := by
-- proof
  apply BooleanFourier.exists_perm_for_valid_triple hm a b c hab hbc hac pab pbc pac hvalid

/--
[arrow_viable_subcube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma arrow_viable_subcube_eq
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
  {u v w : Fin n → Bool}
-- given
  (hm : m ≥ 3)
  (hviable : IsArrowViable f m)
  (hfu : f u = true)
  (hfv : f v = true)
  (hw : ∀ k : Fin n, u k = v k → w k = u k) :
-- imply
  f w = true := by
-- proof
  apply BooleanFourier.arrow_viable_subcube hm f hviable u v w hfu hfv hw

/--
[arrow_viable_implies_unique_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma arrow_viable_implies_unique_pivot_eq
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i j : Fin n}
-- given
  (hm : m ≥ 3)
  (hviable : IsArrowViable f m)
  (hodd : IsOdd f)
  (hi : influence f i > 0)
  (hj : influence f j > 0) :
-- imply
  i = j := by
-- proof
  apply BooleanFourier.arrow_viable_implies_unique_pivot hm f hviable hodd i j hi hj

/--
[arrow_impossibility](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma arrow_impossibility_eq
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
-- given
  (hm : m ≥ 3)
  (hunanimous : IsUnanimous f)
  (hodd : IsOdd f)
  (hviable : IsArrowViable f m) :
-- imply
  IsDictator f := by
-- proof
  apply BooleanFourier.arrow_impossibility hm f hunanimous hodd hviable


-- created on 2026-10-23
