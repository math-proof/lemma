import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Sequences.AronsonTransform
open MetaMathlibExt


/--
[aronsonTransform_existsUnique_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/AronsonTransform.lean)
-/
@[path]
private lemma aronsonTransform_existsUnique_general_eq
  {n₀ : ℕ}
  {β : ℕ → ℕ}
-- given
  (hβ_strictMono : StrictMono β)
  (hβ_complement : Set.Infinite {m : ℕ | n₀ ≤ m ∧ m ∉ Set.range β}) :
-- imply
  ∃! α : ℕ → ℕ,
    StrictMono α ∧
    (∀ i, n₀ ≤ α i) ∧
    (((α 0 = n₀) ↔ α 0 ∈ Set.range β) ∧
    ∀ m, n₀ ≤ m →
    ((m = n₀) ↔ m ∈ Set.range β) →
    α 0 ≤ m) ∧
    ∀ i,
    let n := by
-- proof
  apply MetaMathlibExt.aronsonTransform_existsUnique_general n₀ β hβ_strictMono hβ_complement

/--
[aronsonTransform_existsUnique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/AronsonTransform.lean)
-/
@[path]
private lemma aronsonTransform_existsUnique_eq
  {n₀ : ℕ}
  {β : ℕ → ℕ}
-- given
  (hβ_strictMono : StrictMono β)
  (hβ_lower : ∀ i, n₀ ≤ β i)
  (hβ_complement : Set.Infinite {m : ℕ | n₀ ≤ m ∧ m ∉ Set.range β}) :
-- imply
  ∃! α : ℕ → ℕ,
    StrictMono α ∧
    (∀ i, n₀ ≤ α i) ∧
    (((α 0 = n₀) ↔ α 0 ∈ Set.range β) ∧
    ∀ m, n₀ ≤ m →
    ((m = n₀) ↔ m ∈ Set.range β) →
    α 0 ≤ m) ∧
    ∀ i,
    let n := by
-- proof
  apply MetaMathlibExt.aronsonTransform_existsUnique n₀ β hβ_strictMono hβ_lower hβ_complement


-- created on 2026-10-20
