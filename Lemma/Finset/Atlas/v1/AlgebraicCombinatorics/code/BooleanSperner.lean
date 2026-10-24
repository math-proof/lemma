import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.BooleanSperner
open Finset SpernerProperty


namespace SpernerProperty

/--
[booleanComplement_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanSperner.lean)
-/
@[path]
lemma booleanComplement_card
  {n : ℕ}
  {s : BooleanPoset n} :
-- imply
  (booleanComplement n s).card = n - s.card := by
-- proof
  unfold booleanComplement
  rw [card_sdiff_of_subset (subset_univ s), card_univ, Fintype.card_fin]

end SpernerProperty

namespace SpernerProperty

/--
[booleanComplement_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanSperner.lean)
-/
@[path]
lemma booleanComplement_involutive
  {n : ℕ} :
-- imply
  Function.Involutive (booleanComplement n) := by
-- proof
  intro s
  unfold booleanComplement
  exact _root_.sdiff_sdiff_eq_self (subset_univ s)

end SpernerProperty

namespace SpernerProperty

/--
[booleanComplement_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanSperner.lean)
-/
@[path]
lemma booleanComplement_antitone
  {n : ℕ} :
-- imply
  Antitone (booleanComplement n) := by
-- proof
  intro a b hab
  exact sdiff_subset_sdiff Subset.rfl hab

end SpernerProperty

namespace SpernerProperty

/--
[booleanComplement_grade](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanSperner.lean)
-/
@[path]
lemma booleanComplement_grade
  {n : ℕ}
  {s : BooleanPoset n} :
-- imply
  grade ℕ (booleanComplement n s) = n - grade ℕ s := by
-- proof
  rw [grade_eq, booleanComplement_card, grade_eq]
set_option maxHeartbeats 400000 in

end SpernerProperty

namespace SpernerProperty

/--
[booleanPoset_hasOrderLoweringMatching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanSperner.lean)
-/
@[path]
lemma booleanPoset_hasOrderLoweringMatching
  {n : ℕ}
  {i : ℕ}
-- given
  (hi : n + 1 ≤ 2 * i)
  (hin : i ≤ n) :
-- imply
  HasOrderLoweringMatching (α := BooleanPoset n) i := by
-- proof
  have hn_raise : 2 * (n - i) + 1 ≤ n := by omega
  obtain ⟨φ, hφ_grade, hφ_lt, hφ_inj⟩ := booleanPoset_hasOrderRaisingMatching n (n - i) hn_raise
  let ψ := fun (x : BooleanPoset n) => booleanComplement n (φ (booleanComplement n x))
  refine ⟨ψ, ?_, ?_, ?_⟩
  ·
    intro x hx
    simp only [ψ]
    rw [booleanComplement_grade]
    have hcx : grade ℕ (booleanComplement n x) = n - i := by
      rw [booleanComplement_grade, hx]
    rw [hφ_grade _ hcx]
    omega
  ·
    intro x hx
    simp only [ψ]
    have hcx : grade ℕ (booleanComplement n x) = n - i := by
      rw [booleanComplement_grade, hx]
    have hlt := hφ_lt _ hcx
    have h_le := booleanComplement_antitone n (le_of_lt hlt)
    rw [booleanComplement_involutive] at h_le
    have hne : booleanComplement n (φ (booleanComplement n x)) ≠ x := by
      intro heq
      have : φ (booleanComplement n x) = booleanComplement n x := by
        have := congr_arg (booleanComplement n) heq
        rwa [booleanComplement_involutive] at this
      exact absurd this (ne_of_gt hlt)
    exact lt_of_le_of_ne h_le hne
  ·
    intro x y hx hy hxy
    simp only [ψ] at hxy
    have hcx : grade ℕ (booleanComplement n x) = n - i := by
      rw [booleanComplement_grade, hx]
    have hcy : grade ℕ (booleanComplement n y) = n - i := by
      rw [booleanComplement_grade, hy]
    have hinj := (booleanComplement_involutive n).injective
    have hφeq := hφ_inj _ _ hcx hcy (hinj hxy)
    exact hinj hφeq

end SpernerProperty

namespace SpernerProperty

/--
[booleanPoset_hasOrderMatchings](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanSperner.lean)
-/
@[path]
lemma booleanPoset_hasOrderMatchings
  {n : ℕ} :
-- imply
  HasOrderMatchings (α := BooleanPoset n) (n / 2) := by
-- proof
  refine ⟨Nat.div_le_self n 2, ?_, ?_⟩
  ·
    intro i hi
    exact booleanPoset_hasOrderRaisingMatching n i (by omega)
  ·
    intro i hi hin
    exact booleanPoset_hasOrderLoweringMatching n i (by omega) hin

end SpernerProperty

namespace SpernerProperty

/--
[boolean_sperner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanSperner.lean)
-/
@[path]
lemma boolean_sperner
  {n : ℕ} :
-- imply
  HasSpernerProperty (α := BooleanPoset n) :=
-- proof
  orderMatchings_imp_sperner (n / 2) (booleanPoset_hasOrderMatchings n)

end SpernerProperty


-- created on 2026-10-23
