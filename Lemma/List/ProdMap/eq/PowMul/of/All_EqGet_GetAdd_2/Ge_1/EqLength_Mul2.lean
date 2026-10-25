import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.UnluckyCase
open CoxeterSystemFromDeletion


namespace CoxeterSystemFromDeletion

/--
[alternating_word_prod_eq_pow_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnluckyCase.lean)
-/
@[path]
lemma alternating_word_prod_eq_pow_local
  [Group G]
  {f : B' → G}
  {word : List B'}
  {m : ℕ}
-- given
  (hlen : word.length = 2 * m)
  (hm : m ≥ 1)
  (halt : ∀ (k : ℕ) (hk : k + 2 < word.length), word.get ⟨k, by omega⟩ = word.get ⟨k + 2, hk⟩) :
-- imply
  (word.map f).prod = (f (word.get ⟨0, by omega⟩) * f (word.get ⟨1, by omega⟩)) ^ m := by
-- proof
  induction m using Nat.strongRecOn generalizing word with
  | ind n ih =>
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, word = a :: b :: rest := by
      match word, show word.length ≥ 2 by omega with
      | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    simp only [List.map_cons, List.prod_cons]
    have hget0 : (a :: b :: rest).get ⟨0, by omega⟩ = a := rfl
    have hget1 : (a :: b :: rest).get ⟨1, by omega⟩ = b := rfl
    rw [hget0, hget1]
    by_cases hn1 : n = 1
    · subst hn1
      simp only [List.length_cons] at hlen
      have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp [pow_one]
    · have hrest_len : rest.length = 2 * (n - 1) := by
      simp only [List.length_cons] at hlen; omega
      have hge : n - 1 ≥ 1 := by omega
      have hrest0 : rest.get ⟨0, by omega⟩ = a := by
        have := halt 0 (by simp only [List.length_cons]; omega)
        simpa using this.symm
      have hrest1 : rest.get ⟨1, by omega⟩ = b := by
        have := halt 1 (by simp only [List.length_cons]; omega)
        simpa using this.symm
      have halt_rest : ∀ (k : ℕ) (hk : k + 2 < rest.length),
        rest.get ⟨k, by omega⟩ = rest.get ⟨k + 2, hk⟩ := by
        intro k hk
        have := halt (k + 2) (by simp only [List.length_cons]; omega)
        simp only [List.get_cons_succ] at this; exact this
      have ih_rest := ih (n - 1) (by omega) rest hrest_len hge halt_rest
      have hget0' : rest.get ⟨0, by omega⟩ = a := hrest0
      have hget1' : rest.get ⟨1, by omega⟩ = b := hrest1
      rw [hget0', hget1'] at ih_rest
      rw [ih_rest, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]

end CoxeterSystemFromDeletion


-- created on 2026-10-23
