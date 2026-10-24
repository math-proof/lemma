import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers
import Lemma.List.AddLengthEraseIdxEraseIdx2.eq.Length.of.Lt_Length.Lt
import Lemma.List.ProdMap.eq.PowMul.of.All_EqGet_GetAdd_2.Ge_1.EqLength_Mul2
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.UnluckyCase


namespace CoxeterSystemFromDeletion

/--
[gen_injective_of_involution_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionWordRelation.lean)
-/
@[path]
private lemma gen_injective_of_involution_ne
  [Group W]
  {gen : B → W}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
-- imply
  Function.Injective gen := by
-- proof
  intro s t hst
  by_contra h
  have := hgen_ne s t h
  rw [hst, hgen_inv] at this
  exact this rfl

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[alternating_word_prod_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionWordRelation.lean)
-/
@[path]
private lemma alternating_word_prod_eq_pow
  [Group W]
  [Group G]
  {f : B → G}
  {s t : B}
  {m : ℕ}
  {word : List B}
-- given
  (hlen : word.length = 2 * m)
  (hm : m ≥ 1)
  (halt : ∀ (k : ℕ) (hk : k + 2 < word.length),
    word.get ⟨k, Nat.lt_of_le_of_lt (Nat.le_add_right k 2) hk⟩ =
      word.get ⟨k + 2, hk⟩)
  (h0 : 0 < word.length)
  (h1 : 1 < word.length)
  (hs : word.get ⟨0, h0⟩ = s)
  (ht : word.get ⟨1, h1⟩ = t) :
-- imply
  (word.map f).prod = (f s * f t) ^ m := by
-- proof
  induction m using Nat.strongRecOn generalizing word s t with
  | ind n ih =>
    have hlen2 : word.length ≥ 2 := by omega
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, word = a :: b :: rest := by
      cases word with
      | nil => cases hlen2
      | cons a tail =>
        cases tail with
        | nil =>
          simp at hlen2
        | cons b rest =>
          exact ⟨a, b, rest, rfl⟩
    have ha : a = s := by simpa using hs
    have hb : b = t := by simpa using ht
    subst ha; subst hb
    simp only [List.map_cons, List.prod_cons]
    if hn1 : n = 1 then
      subst hn1
      simp only [List.length_cons] at hlen
      have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp [pow_one]
    else
      have hrest_len : rest.length = 2 * (n - 1) := by
        simp only [List.length_cons] at hlen; omega
      have hge : n - 1 ≥ 1 := by omega
      have hrest0 : 0 < rest.length := by omega
      have hrest1 : 1 < rest.length := by omega
      have hs0 : rest.get ⟨0, hrest0⟩ = a := by
        have := halt 0 (by simp only [List.length_cons]; omega)
        simpa using this.symm
      have hs1 : rest.get ⟨1, hrest1⟩ = b := by
        have := halt 1 (by simp only [List.length_cons]; omega)
        simpa using this.symm
      have halt_rest : ∀ (k : ℕ) (hk : k + 2 < rest.length),
          rest.get ⟨k, Nat.lt_of_le_of_lt (Nat.le_add_right k 2) hk⟩ =
            rest.get ⟨k + 2, hk⟩ := by
        intro k hk
        have := halt (k + 2) (by simp only [List.length_cons]; omega)
        simp only [List.get_cons_succ] at this; exact this
      have ih_rest :=
        ih (n - 1) (by omega) (word := rest) (s := a) (t := b) hrest_len hge
          halt_rest hrest0 hrest1 hs0 hs1
      rw [ih_rest]
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]

end CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

/--
[alternating_word_trivial_in_coxeter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionWordRelation.lean)
-/
@[path]
private lemma alternating_word_trivial_in_coxeter
  [Group W]
  {gen : B → W}
  {word : List B}
  {m : ℕ}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
  (hw : (word.map gen).prod = 1)
  (hlen : word.length = 2 * m)
  (hm : m ≥ 1)
  (halt : ∀ (k : ℕ) (hk : k + 2 < word.length),
    word.get ⟨k, Nat.lt_of_le_of_lt (Nat.le_add_right k 2) hk⟩ =
      word.get ⟨k + 2, hk⟩) :
-- imply
  (word.map (deletionCoxeterMatrix gen hgen_inv hgen_ne).simple).prod = 1 := by
-- proof
  let M := deletionCoxeterMatrix gen hgen_inv hgen_ne
  have h0 : 0 < word.length := by omega
  have h1 : 1 < word.length := by omega
  set s := word.get ⟨0, h0⟩
  set t := word.get ⟨1, h1⟩
  have hgen_prod :=
    alternating_word_prod_eq_pow (f := gen) (s := s) (t := t) (m := m) (word := word)
      hlen hm halt h0 h1 rfl rfl
  rw [hgen_prod] at hw
  have hcox := alternating_word_maps_to_one gen hgen_inv hgen_ne s t m hw
  have hsimp_prod :=
    alternating_word_prod_eq_pow (f := M.simple) (s := s) (t := t) (m := m) (word := word)
      hlen hm halt h0 h1 rfl rfl
  rwa [hsimp_prod]

end CoxeterSystemFromDeletion


-- created on 2026-10-24
