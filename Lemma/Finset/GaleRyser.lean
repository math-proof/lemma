import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.GaleRyser
open MathlibExt.Combinatorics.GaleRyserWanted


/--
[prefixSum_eq_sum_fin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GaleRyser.lean)
-/
@[path]
private lemma prefixSum_eq_sum_fin_eq
  {m : ℕ}
  {r : Fin m → ℕ}
  {k : ℕ}
-- given
  (hk : k ≤ m) :
-- imply
  prefixSum r k = ∑ i : Fin k, r ⟨i.val, lt_of_lt_of_le i.2 hk⟩ := by
-- proof
  apply MathlibExt.Combinatorics.GaleRyserWanted.prefixSum_eq_sum_fin r hk

/--
[gale_ryser](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GaleRyser.lean)
-/
@[path]
private lemma gale_ryser_eq
  {m n : ℕ}
  {r : Fin m → ℕ}
  {c : Fin n → ℕ}
-- given
  (hr : Antitone r)
  (hc : Antitone c) :
-- imply
  (∃ X : Fin m → Fin n → Fin 2,
    (∀ i, ∑ j : Fin n, (X i j).val = r i) ∧
    ∀ j, ∑ i : Fin m, (X i j).val = c j) ↔
    (∑ i : Fin m, r i = ∑ j : Fin n, c j ∧
    ∀ k, k ≤ m → prefixSum r k ≤ ∑ j : Fin n, min k (c j)) := by
-- proof
  apply MathlibExt.Combinatorics.GaleRyserWanted.gale_ryser r c hr hc


-- created on 2026-10-20
