import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers
open CoxeterSystemFromDeletion


namespace CoxeterSystemFromDeletion

/--
[eraseIdx_eraseIdx_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma eraseIdx_eraseIdx_length
  [Group W]
  {l : List α}
  {i j : ℕ}
-- given
  (hij : i < j)
  (hj : j < l.length) :
-- imply
  ((l.eraseIdx j).eraseIdx i).length + 2 = l.length := by
-- proof
  have hi_bound : i < (l.eraseIdx j).length := by
    rw [List.length_eraseIdx_of_lt hj]
    omega
  rw [List.length_eraseIdx_of_lt hi_bound, List.length_eraseIdx_of_lt hj]
  omega

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[deletion_relation_even_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma deletion_relation_even_length
  [Group W]
  [Group W]
  {gen : B → W}
  {word : List B}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hDel : SatisfiesDeletionConditionGen gen)
  (hw : (word.map gen).prod = 1) :
-- imply
  Even word.length := by
-- proof
  suffices ∀ (n : ℕ), ∀ (w : List B), w.length = n →
    (w.map gen).prod = 1 → Even w.length from this _ word rfl hw
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro w hlen hw'
  by_cases hpos : n = 0
  · subst hpos; simp [hlen]
  ·
    have hnonred : ∃ (shorter : List B), shorter.length < w.length ∧
      (shorter.map gen).prod = (w.map gen).prod :=
      ⟨[], by simp [hlen]; omega, by simp [hw']⟩
    obtain ⟨i, j, hij, hj, hprod⟩ := hDel w hnonred
    set w' := (w.eraseIdx j).eraseIdx i with hw'_def
    have hlen' : w'.length + 2 = w.length := eraseIdx_eraseIdx_length hij hj
    have hw'_prod : (w'.map gen).prod = 1 := by rw [hw'_def, hprod, hw']
    have hlt : w'.length < n := by omega
    have heven' := ih w'.length hlt w' rfl hw'_prod
    obtain ⟨k, hk⟩ := heven'
    exact ⟨k + 1, by omega⟩

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[inv_eq_self_of_involution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma inv_eq_self_of_involution
  [Group W]
  [Group G]
  {g : G}
-- given
  (h : g * g = 1) :
-- imply
  g⁻¹ = g := by
-- proof
  rw [mul_eq_one_iff_eq_inv] at h; exact h.symm

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[map_inv_eq_self_of_involutions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma map_inv_eq_self_of_involutions
  [Group W]
  {gen : B → W}
  {l : List B}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1) :
-- imply
  (l.map gen).map (·⁻¹) = l.map gen := by
-- proof
  simp only [List.map_map]; congr 1; ext s
  exact inv_eq_self_of_involution (hgen_inv s)

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[reverse_map_prod_inv_of_involutions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma reverse_map_prod_inv_of_involutions
  [Group W]
  {gen : B → W}
  {l : List B}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1) :
-- imply
  ((l.reverse).map gen).prod = ((l.map gen).prod)⁻¹ := by
-- proof
  rw [List.map_reverse, List.prod_reverse_noncomm,
    map_inv_eq_self_of_involutions gen hgen_inv l]

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[first_half_nonreduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma first_half_nonreduced
  [Group W]
  {gen : B → W}
  {word : List B}
  {m : ℕ}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hlen : word.length = 2 * m)
  (hm : m > 1)
  (hw : (word.map gen).prod = 1) :
-- imply
  ∃ (shorter : List B), shorter.length < (word.take (m + 1)).length ∧ (shorter.map gen).prod = ((word.take (m + 1)).map gen).prod := by
-- proof
  refine ⟨(word.drop (m + 1)).reverse, ?_, ?_⟩
  ·
    rw [List.length_reverse, List.length_drop, List.length_take]; omega
  ·
    have hsplit : ((word.take (m + 1)).map gen).prod *
      ((word.drop (m + 1)).map gen).prod = 1 := by
      rw [← List.prod_append, ← List.map_append, List.take_append_drop]; exact hw
    rw [mul_eq_one_iff_eq_inv] at hsplit
    rw [reverse_map_prod_inv_of_involutions gen hgen_inv, hsplit]

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[alternating_word_maps_to_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma alternating_word_maps_to_one
  [Group W]
  {gen : B → W}
  {s t : B}
  {m : ℕ}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
  (h_prod : (gen s * gen t) ^ m = 1) :
-- imply
  let M := deletionCoxeterMatrix gen hgen_inv hgen_ne (M.simple s * M.simple t) ^ m = 1 := by
-- proof
  intro M
  have h_dvd : orderOf (gen s * gen t) ∣ m := orderOf_dvd_of_pow_eq_one h_prod
  have h_M_eq : M s t = orderOf (gen s * gen t) := by
    simp only [M, deletionCoxeterMatrix, Matrix.of_apply]
  have h_M_dvd : M s t ∣ m := h_M_eq ▸ h_dvd
  have h_rel : (M.simple s * M.simple t) ^ (M s t) = 1 :=
    M.toCoxeterSystem.simple_mul_simple_pow s t
  obtain ⟨k, hk⟩ := h_M_dvd
  rw [hk, pow_mul, h_rel, one_pow]

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[consecProd_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma consecProd_succ
  [Group W]
  [Monoid W']
  {g : ℕ → W'}
  {k m : ℕ} :
-- imply
  consecProd g k (m + 1) = g k * consecProd g (k + 1) m := by
-- proof
  simp only [consecProd]
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.prod_cons, List.map_map]
  have : (fun i => g (k + i)) ∘ Nat.succ = fun i => g (k + 1 + i) := by
    ext i; show g (k + (i + 1)) = g (k + 1 + i); ring_nf
  rw [this]; simp

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[consecProd_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma consecProd_succ_succ
  [Group W]
  [Monoid W']
  {g : ℕ → W'}
  {k m : ℕ} :
-- imply
  consecProd g k (m + 2) = g k * g (k + 1) * consecProd g (k + 2) m := by
-- proof
  rw [consecProd_succ, consecProd_succ, mul_assoc]

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[cycling_alternating_of_L_type](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma cycling_alternating_of_L_type
  [Group W]
  {g : ℕ → W}
  {m : ℕ}
-- given
  (hm : m ≥ 2)
  (h_L : ∀ k, consecProd g k m = g (k + 2) * g (k + 1) * consecProd g (k + 2) (m - 2)) :
-- imply
  ∀ k, g k = g (k + 2) := by
-- proof
  intro k
  have hpeel : consecProd g k m =
    g k * g (k + 1) * consecProd g (k + 2) (m - 2) := by
    conv_lhs => rw [show m = (m - 2) + 2 from by omega]
    exact consecProd_succ_succ g k (m - 2)
  have hLk := h_L k
  rw [hpeel] at hLk
  exact mul_right_cancel (mul_right_cancel hLk)

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[cycling_forces_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivityHelpers.lean)
-/
@[path]
lemma cycling_forces_alternating
  [Group W]
  [Group W]
  {gen : B → W}
  {word : List B}
  {m : ℕ}
-- given
  (hlen : word.length = 2 * m)
  (hm : m ≥ 2)
  (h_L_type : ∀ k, consecProd (wordCyclicGen gen word (2 * m) hlen (by omega)) k m = wordCyclicGen gen word (2 * m) hlen (by omega) (k + 2) * wordCyclicGen gen word (2 * m) hlen (by omega) (k + 1) * consecProd (wordCyclicGen gen word (2 * m) hlen (by omega)) (k + 2) (m - 2)) :
-- imply
  ∀ (k : ℕ) (hk : k + 2 < word.length), gen (word.get ⟨k, by omega⟩) = gen (word.get ⟨k + 2, by omega⟩) := by
-- proof
  intro k hk
  have h := cycling_alternating_of_L_type
    (wordCyclicGen gen word (2 * m) hlen (by omega)) m hm h_L_type k
  simp only [wordCyclicGen, Nat.mod_eq_of_lt (show k < 2 * m by omega),
    Nat.mod_eq_of_lt (show k + 2 < 2 * m by omega)] at h
  exact h

end CoxeterSystemFromDeletion


-- created on 2026-10-23
