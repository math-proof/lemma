import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.Factor
open InfiniteWord


/--
[factor_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma factor_apply_eq
  {u : ℕ → α}
  {k i : ℕ}
  {s : Fin k} :
-- imply
  factor u k i s = u (i + s) := by
-- proof
  apply InfiniteWord.factor_apply u k i s

/--
[mem_factorSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma mem_factorSet_eq
  {u : ℕ → α}
  {k : ℕ}
  {v : Fin k → α} :
-- imply
  v ∈ factorSet u k ↔ ∃ i, factor u k i = v := by
-- proof
  apply InfiniteWord.mem_factorSet

/--
[initial_eq_factor_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma initial_eq_factor_zero_eq
  {u : ℕ → α}
  {k : ℕ} :
-- imply
  initial u k = factor u k 0 := by
-- proof
  apply InfiniteWord.initial_eq_factor_zero u k

/--
[initial_mem_factorSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma initial_mem_factorSet_eq
  {u : ℕ → α}
  {k : ℕ} :
-- imply
  initial u k ∈ factorSet u k := by
-- proof
  apply InfiniteWord.initial_mem_factorSet u k

/--
[finite_factorSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma finite_factorSet_eq
  [Finite α]
  {u : ℕ → α}
  {k : ℕ} :
-- imply
  (factorSet u k).Finite := by
-- proof
  apply InfiniteWord.finite_factorSet u k

/--
[factorList_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma factorList_length_eq
  {u : ℕ → α}
  {k i : ℕ} :
-- imply
  (factorList u k i).length = k := by
-- proof
  apply InfiniteWord.factorList_length u k i

/--
[isFactor_iff_exists_factorList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma isFactor_iff_exists_factorList_eq
  {w : List α}
  {u : ℕ → α} :
-- imply
  IsFactor w u ↔ ∃ i, factorList u w.length i = w := by
-- proof
  apply InfiniteWord.isFactor_iff_exists_factorList w u

/--
[isNonemptyFactor_iff_exists_factorList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma isNonemptyFactor_iff_exists_factorList_eq
  {w : List α}
  {u : ℕ → α} :
-- imply
  IsNonemptyFactor w u ↔
    w ≠ [] ∧ ∃ i, factorList u w.length i = w := by
-- proof
  apply InfiniteWord.isNonemptyFactor_iff_exists_factorList w u

/--
[isNonemptyFactor_iff_isFactor_and_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma isNonemptyFactor_iff_isFactor_and_ne_nil_eq
  {w : List α}
  {u : ℕ → α} :
-- imply
  IsNonemptyFactor w u ↔ w ≠ [] ∧ IsFactor w u := by
-- proof
  apply InfiniteWord.isNonemptyFactor_iff_isFactor_and_ne_nil w u

/--
[isFactor_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma isFactor_nil_eq
  {u : ℕ → α} :
-- imply
  IsFactor [] u := by
-- proof
  apply InfiniteWord.isFactor_nil u

/--
[not_isNonemptyFactor_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma not_isNonemptyFactor_nil_eq
  {u : ℕ → α} :
-- imply
  ¬IsNonemptyFactor [] u := by
-- proof
  apply InfiniteWord.not_isNonemptyFactor_nil u

/--
[isFactor_ofFn_iff_mem_factorSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
private lemma isFactor_ofFn_iff_mem_factorSet_eq
  {k : ℕ}
  {v : Fin k → α}
  {u : ℕ → α} :
-- imply
  IsFactor (List.ofFn v) u ↔ v ∈ factorSet u k := by
-- proof
  apply InfiniteWord.isFactor_ofFn_iff_mem_factorSet v u


-- created on 2026-10-20
