import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.InfiniteWord.Factor
open InfiniteWord


namespace InfiniteWord

/--
[factor_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma factor_apply
  {u : ℕ → α}
  {k i : ℕ}
  {s : Fin k} :
-- imply
  factor u k i s = u (i + s) :=
-- proof
  rfl

end InfiniteWord

namespace InfiniteWord

/--
[mem_factorSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma mem_factorSet
  {u : ℕ → α}
  {k : ℕ}
  {v : Fin k → α} :
-- imply
  v ∈ factorSet u k ↔ ∃ i, factor u k i = v :=
-- proof
  Iff.rfl

end InfiniteWord

namespace InfiniteWord

/--
[initial_eq_factor_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma initial_eq_factor_zero
  {u : ℕ → α}
  {k : ℕ} :
-- imply
  initial u k = factor u k 0 :=
-- proof
  rfl

end InfiniteWord

namespace InfiniteWord

/--
[initial_mem_factorSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma initial_mem_factorSet
  {u : ℕ → α}
  {k : ℕ} :
-- imply
  initial u k ∈ factorSet u k :=
-- proof
  ⟨0, rfl⟩

end InfiniteWord

namespace InfiniteWord

/--
[finite_factorSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma finite_factorSet
  [Finite α]
  {u : ℕ → α}
  {k : ℕ} :
-- imply
  (factorSet u k).Finite :=
-- proof
  Set.toFinite _

end InfiniteWord

namespace InfiniteWord

/--
[factorList_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma factorList_length
  {u : ℕ → α}
  {k i : ℕ} :
-- imply
  (factorList u k i).length = k := by
-- proof
  simp [factorList]

end InfiniteWord

namespace InfiniteWord

/--
[isFactor_iff_exists_factorList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma isFactor_iff_exists_factorList
  {w : List α}
  {u : ℕ → α} :
-- imply
  IsFactor w u ↔ ∃ i, factorList u w.length i = w :=
-- proof
  Iff.rfl

end InfiniteWord

namespace InfiniteWord

/--
[isNonemptyFactor_iff_exists_factorList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma isNonemptyFactor_iff_exists_factorList
  {w : List α}
  {u : ℕ → α} :
-- imply
  IsNonemptyFactor w u ↔
    w ≠ [] ∧ ∃ i, factorList u w.length i = w := by
-- proof
  constructor
  · rintro ⟨hne, i, hi⟩
    refine ⟨hne, i, ?_⟩
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      have hn : n < w.length := h2
      simp only [factorList, List.getElem_ofFn, factor_apply, hi n hn]
  · rintro ⟨hne, i, hi⟩
    refine ⟨hne, i, fun j hj => ?_⟩
    have h_congr : (factorList u w.length i)[j]? = w[j]? :=
      congrArg (fun l : List α => l[j]?) hi
    have h_factor : (factorList u w.length i)[j]? = some (u (i + j)) := by
      simp [factorList, hj, factor_apply]
    have h_w : w[j]? = some (w[j]'hj) := by
      simp [hj]
    have h_opt : some (w[j]'hj) = some (u (i + j)) := by
      calc
        some (w[j]'hj) = w[j]? := h_w.symm
        _ = (factorList u w.length i)[j]? := h_congr.symm
        _ = some (u (i + j)) := h_factor
    exact Option.some_inj.mp h_opt

end InfiniteWord

namespace InfiniteWord

/--
[isNonemptyFactor_iff_isFactor_and_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma isNonemptyFactor_iff_isFactor_and_ne_nil
  {w : List α}
  {u : ℕ → α} :
-- imply
  IsNonemptyFactor w u ↔ w ≠ [] ∧ IsFactor w u := by
-- proof
  rw [isNonemptyFactor_iff_exists_factorList, isFactor_iff_exists_factorList]

end InfiniteWord

namespace InfiniteWord

/--
[isFactor_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma isFactor_nil
  {u : ℕ → α} :
-- imply
  IsFactor [] u :=
-- proof
⟨0, by simp [factorList]⟩

end InfiniteWord

namespace InfiniteWord

/--
[not_isNonemptyFactor_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma not_isNonemptyFactor_nil
  {u : ℕ → α} :
-- imply
  ¬IsNonemptyFactor [] u := by
-- proof
  simp [IsNonemptyFactor]

end InfiniteWord

namespace InfiniteWord

/--
[isFactor_ofFn_iff_mem_factorSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean)
-/
@[path]
lemma isFactor_ofFn_iff_mem_factorSet
  {k : ℕ}
  {v : Fin k → α}
  {u : ℕ → α} :
-- imply
  IsFactor (List.ofFn v) u ↔ v ∈ factorSet u k := by
-- proof
  rw [isFactor_iff_exists_factorList, mem_factorSet]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hi' : (fun j : Fin k => u (i + j)) = v := by
      simpa [factorList] using hi
    change (fun j : Fin k => u (i + j)) = v
    exact hi'
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hi' : (fun j : Fin k => u (i + j)) = v := by
      change (fun j : Fin k => u (i + j)) = v at hi
      exact hi
    simpa [factorList] using congrArg List.ofFn hi'

end InfiniteWord


-- created on 2026-10-20
-- updated on 2026-10-26
