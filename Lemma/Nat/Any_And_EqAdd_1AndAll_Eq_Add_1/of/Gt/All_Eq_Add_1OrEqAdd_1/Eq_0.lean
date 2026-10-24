import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.DeletionCondition
open Garrett Garrett.ExchangeDeletion


namespace Definitions
end Definitions
namespace Garrett.ExchangeDeletion

/--
[exists_first_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionCondition.lean)
-/
@[path]
private lemma exists_first_decreasing
  {f : ℕ → ℕ}
  {n : ℕ}
-- given
  (h0 : f 0 = 0)
  (hstep : ∀ j, j < n → (f (j + 1) = f j + 1 ∨ f (j + 1) + 1 = f j))
  (hlt : n > f n) :
-- imply
  ∃ j, j < n ∧ f (j + 1) + 1 = f j ∧ (∀ k, k < j → f (k + 1) = f k + 1) := by
-- proof
  have hex : ∃ j, j < n ∧ f (j + 1) + 1 = f j := by
    induction n with
    | zero => omega
    | succ m ihm =>
      obtain hup | hdown := hstep m (by omega)
      · obtain ⟨j, hj, hjd⟩ := ihm (fun j hj => hstep j (by omega)) (by omega)
        exact ⟨j, by omega, hjd⟩
      · exact ⟨m, by omega, hdown⟩
  let j₀ := Nat.find hex
  have hj₀ := Nat.find_spec hex
  refine ⟨j₀, hj₀.1, hj₀.2, ?_⟩
  intro k hk
  by_contra hk_not_up
  have hk_lt_n : k < n := by have := hj₀.1; omega
  obtain hup | hdown := hstep k hk_lt_n
  · exact hk_not_up hup
  · exact absurd ⟨hk_lt_n, hdown⟩ (Nat.find_min hex hk)

end Garrett.ExchangeDeletion

namespace Garrett.ExchangeDeletion

/--
[deletion_of_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionCondition.lean)
-/
@[path]
private lemma deletion_of_exchange
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
-- given
  (hex : SatisfiesExchangeCondition M cs) :
-- imply
  SatisfiesDeletionCondition M cs := by
-- proof
  intro word hlong
  set f := fun k => cs.length (cs.wordProd (word.take k)) with hf_def
  have hf0 : f 0 = 0 := by simp [hf_def, cs.wordProd_nil, cs.length_one]
  have hfstep : ∀ k, k < word.length → (f (k + 1) = f k + 1 ∨ f (k + 1) + 1 = f k) := by
    intro k hk; simp only [hf_def]
    rw [List.take_succ_eq_append_getElem hk, cs.wordProd_append, cs.wordProd_singleton]
    exact cs.length_mul_simple _ _
  have hfn : word.length > f word.length := by
    simp [hf_def, List.take_length]; exact hlong
  obtain ⟨j, hj_lt, hj_down, hj_first⟩ := exists_first_decreasing (f := f) (n := word.length) hf0 hfstep hfn
  have htake_red : cs.IsReduced (word.take j) := by
    unfold CoxeterSystem.IsReduced
    rw [List.length_take, Nat.min_eq_left (by omega : j ≤ word.length)]
    suffices h : ∀ m, m ≤ j → f m = m from h j le_rfl
    intro m hm
    induction m with
    | zero => exact hf0
    | succ n ih => rw [hj_first n (by omega), ih (by omega)]
  have htake_len : (word.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hprod_succ : cs.wordProd (word.take (j + 1)) =
    cs.wordProd (word.take j) * cs.simple word[j] := by
    rw [List.take_succ_eq_append_getElem hj_lt, cs.wordProd_append, cs.wordProd_singleton]
  have hlen_drop : cs.length (cs.wordProd (word.take j) * cs.simple word[j]) <
    cs.length (cs.wordProd (word.take j)) := by
    rw [← hprod_succ]; simp only [hf_def] at hj_down; omega
  obtain ⟨⟨i_val, hi_bound⟩, hi_eq⟩ :=
    hex (word.take j) word[j] htake_red hlen_drop
  rw [← hprod_succ] at hi_eq
  rw [htake_len] at hi_bound
  refine ⟨⟨i_val, by omega⟩, ⟨j, hj_lt⟩, hi_bound, ?_⟩
  have hlist : (word.eraseIdx j).eraseIdx i_val =
    (word.take j).eraseIdx i_val ++ word.drop (j + 1) := by
    conv_lhs => rw [List.eraseIdx_eq_take_drop_succ word j]
    exact List.eraseIdx_append_of_lt_length (by rwa [htake_len]) _
  rw [hlist, cs.wordProd_append, hi_eq, ← cs.wordProd_append, List.take_append_drop]

end Garrett.ExchangeDeletion

namespace Garrett.ExchangeDeletion

/--
[corollary_of_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionCondition.lean)
-/
@[path]
private lemma corollary_of_exchange
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
-- given
  (hex : SatisfiesExchangeCondition M cs) :
-- imply
  ExchangeCorollary M cs := by
-- proof
  intro w s t hsw hwt
  obtain ⟨ω, hωred, hωprod⟩ := cs.exists_isReduced w
  have hωlen : cs.length w = ω.length := hωprod ▸ hωred
  have hsω_reduced : cs.IsReduced (s :: ω) := by
    unfold CoxeterSystem.IsReduced
    rw [cs.wordProd_cons, List.length_cons, ← hωprod, hsw, hωlen]
  have hsω_prod : cs.wordProd (s :: ω) = cs.simple s * w := by
    rw [cs.wordProd_cons, hωprod]
  have hassoc : cs.simple s * w * cs.simple t = cs.simple s * (w * cs.simple t) :=
    mul_assoc _ _ _
  obtain hup | hdown := cs.length_mul_simple (cs.simple s * w) t
  ·
    left; rw [hassoc] at hup ⊢; omega
  ·
    rw [hassoc] at hdown
    have hlt : cs.length (cs.wordProd (s :: ω) * cs.simple t) <
      cs.length (cs.wordProd (s :: ω)) := by
      rw [hsω_prod, hassoc]; omega
    obtain ⟨i, hi⟩ := hex (s :: ω) t hsω_reduced hlt
    rw [hsω_prod, hassoc] at hi
    if hi0 : i.val = 0 then
      right
      have herase : (s :: ω).eraseIdx i = ω := by simp [hi0]
      rw [herase] at hi
      rwa [← hassoc, ← hωprod, eq_comm] at hi
    else
      exfalso
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi0
      obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 :=
        ⟨i.val - 1, (Nat.succ_pred_eq_of_pos hi_pos).symm⟩
      have herase : (s :: ω).eraseIdx i.val = s :: (ω.eraseIdx j) := by
        rw [hj, List.eraseIdx_cons_succ]
      change cs.wordProd ((s :: ω).eraseIdx i.val) = _ at hi
      rw [herase, cs.wordProd_cons] at hi
      have hprod_erased : cs.wordProd (ω.eraseIdx j) = w * cs.simple t :=
        mul_left_cancel hi
      have hj_lt : j < ω.length := by
        have := i.isLt; simp [List.length_cons] at this; omega
      have hlen_erased : (ω.eraseIdx j).length = ω.length - 1 :=
        List.length_eraseIdx_of_lt hj_lt
      have := cs.length_wordProd_le (ω.eraseIdx j)
      rw [hprod_erased, hwt, hlen_erased, hωlen] at this
      omega

end Garrett.ExchangeDeletion


-- created on 2026-10-24
