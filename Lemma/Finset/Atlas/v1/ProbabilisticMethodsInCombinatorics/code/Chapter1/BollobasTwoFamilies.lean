import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.BollobasTwoFamilies
open Finset Nat BigOperators BollobasTwoFamilies


namespace BollobasTwoFamilies

/--
[disjoint_goodPerms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BollobasTwoFamilies.lean)
-/
@[path]
lemma disjoint_goodPerms
  [DecidableEq α]
  [Fintype α]
  {S₁ T₁ S₂ T₂ : Finset α}
-- given
  (h₁ : (S₁ ∩ T₂).Nonempty)
  (h₂ : (S₂ ∩ T₁).Nonempty) :
-- imply
  Disjoint (goodPerms S₁ T₁) (goodPerms S₂ T₂) := by
-- proof
  simp only [goodPerms]
  apply Finset.disjoint_filter.mpr
  intro σ _ hσ₁ hσ₂
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₂
  rw [Finset.mem_inter] at hx hy
  have hxy := hσ₁ x hx.1 y hy.2
  have hyx := hσ₂ y hy.1 x hx.2
  exact absurd (lt_trans hxy hyx) (lt_irrefl _)

end BollobasTwoFamilies

namespace BollobasTwoFamilies

/--
[choose_pos_of_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BollobasTwoFamilies.lean)
-/
@[path]
lemma choose_pos_of_add
  [DecidableEq α]
  [Fintype α]
  {a b : ℕ} :
-- imply
  0 < (a + b).choose a :=
-- proof
  Nat.choose_pos (Nat.le_add_right a b)
/-- (Theorem 1.2.4, Bollobás Two Families Theorem, weighted form) Given families
$(A_i)_{i < m}$ and $(B_i)_{i < m}$ with $A_i \cap B_j = \varnothing$ iff $i = j$, then
$$\sum_{i < m} \binom{|A_i| + |B_i|}{|A_i|}^{-1} \le 1.$$ -/

end BollobasTwoFamilies


-- created on 2026-10-23
