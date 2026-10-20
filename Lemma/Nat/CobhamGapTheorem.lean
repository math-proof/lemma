import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.CobhamGapTheorem
open MetaMathlibExt


/--
[cobham_gap_theorem_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean)
-/
@[path]
private lemma cobham_gap_theorem_general_eq
  {k : ℕ}
  {x : ℕ → ℕ}
-- given
  (hx : StrictMono x)
  (hX : IsBaseRecognizable k (Set.range x)) :
-- imply
  Filter.limsup
    (fun i => ((x (i + 1) : ENNReal) / (x i : ENNReal)))
    Filter.atTop > 1 ∨
    ∃ C : ℕ, ∀ i : ℕ, x (i + 1) - x i ≤ C := by
-- proof
  apply MetaMathlibExt.cobham_gap_theorem_general hx hX

/--
[cobham_gap_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean)
-/
@[path]
private lemma cobham_gap_theorem_eq
  {k : ℕ}
  {x : ℕ → ℕ}
-- given
  (hx : StrictMono x)
  (hk : 2 ≤ k)
  (hX : IsBaseRecognizable k (Set.range x)) :
-- imply
  Filter.limsup
    (fun i => ((x (i + 1) : ENNReal) / (x i : ENNReal)))
    Filter.atTop > 1 ∨
    ∃ C : ℕ, ∀ i : ℕ, x (i + 1) - x i ≤ C := by
-- proof
  apply MetaMathlibExt.cobham_gap_theorem hx hk hX


-- created on 2026-10-20
