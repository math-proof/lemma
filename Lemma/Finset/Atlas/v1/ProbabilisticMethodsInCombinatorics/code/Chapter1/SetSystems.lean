import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.SetSystems
open Finset Nat SetSystems


namespace SetSystems

/--
[lym_inequality_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/SetSystems.lean)
-/
@[path]
lemma lym_inequality_general
  [Fintype α]
  {F : Finset (Finset α)}
-- given
  (hF : IsAntichain (· ⊆ ·) (F : Set (Finset α))) :
-- imply
  ∑ A ∈ F, ((Fintype.card α).choose A.card : ℚ)⁻¹ ≤ 1 :=
-- proof
  Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose hF

end SetSystems

namespace SetSystems

/--
[lym_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/SetSystems.lean)
-/
@[path]
lemma lym_inequality
  {n : ℕ}
  {F : Finset (Finset (Fin n))}
-- given
  (hF : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))) :
-- imply
  ∑ A ∈ F, (1 : ℚ) / (n.choose A.card) ≤ 1 := by
-- proof
  simp only [one_div]
  have h := lym_inequality_general hF
  convert h using 2 with A
  simp [Fintype.card_fin]

end SetSystems

namespace SetSystems

/--
[sperner_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/SetSystems.lean)
-/
@[path]
lemma sperner_theorem
  {n : ℕ}
  {F : Finset (Finset (Fin n))}
-- given
  (hF : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))) :
-- imply
  F.card ≤ n.choose (n / 2) := by
-- proof
  have hLYM : ∑ A ∈ F, ((n.choose A.card : ℚ))⁻¹ ≤ 1 := by
    have h := lym_inequality_general hF
    simp only [Fintype.card_fin] at h
    exact h
  have hpos : (0 : ℚ) < (n.choose (n / 2)) := by
    exact_mod_cast Nat.choose_pos (Nat.div_le_self n 2)
  have hstep : ∑ _A ∈ F, ((n.choose (n / 2) : ℚ))⁻¹ ≤ 1 := by
    calc ∑ _A ∈ F, ((n.choose (n / 2) : ℚ))⁻¹
      ≤ ∑ A ∈ F, ((n.choose A.card : ℚ))⁻¹ := by
        apply Finset.sum_le_sum
        intro A _hA
        have hAcard : A.card ≤ n := by
          simpa [Fintype.card_fin] using A.card_le_univ
        exact inv_anti₀
          (by exact_mod_cast Nat.choose_pos hAcard)
          (by exact_mod_cast Nat.choose_le_middle A.card n)
      _ ≤ 1 := hLYM
  rw [Finset.sum_const, nsmul_eq_mul] at hstep
  rw [mul_inv_le_iff₀' hpos] at hstep
  simp only [mul_one] at hstep
  exact_mod_cast hstep

end SetSystems


-- created on 2026-10-23
