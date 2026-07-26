import Lemma.Hyperreal.Infinitesimal.is.Infinitesimal.of.XEq
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Hyperreal.XEqMulS.of.XEq.XEq.Or_NotOr
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


set_option maxHeartbeats 800000


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h_not_or : ¬((b → 0) ∨ y → 0))
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a / x ≈ b / y := by
-- proof
  have hb0 := Ne_0.of.NotInfinitesimal fun h => h_not_or (Or.inl h)
  have h_not_x : ¬x → 0 := fun h => h_not_or (Or.inr ((Infinitesimal.is.Infinitesimal.of.XEq h₁).mp h))
  have hx0 := Ne_0.of.NotInfinitesimal h_not_x
  have hy0 := Ne_0.of.NotInfinitesimal fun h => h_not_or (Or.inr h)
  have h_not_or_x : ¬((b → 0) ∨ x → 0) := fun h =>
    match h with
    | Or.inl hb => h_not_or (Or.inl hb)
    | Or.inr hx => h_not_or (Or.inr ((Infinitesimal.is.Infinitesimal.of.XEq h₁).mp hx))
  have h_cross := XEqMulS.of.XEq.XEq.Or_NotOr (Or.inr h_not_or_x) h₀ h₁.symm
  if h_by : (b / y) → 0 then
    left
    obtain ⟨hay, _⟩ | ⟨hr, hbx⟩ := OrAndS.of.XEq h_cross
    ·
      exfalso
      have ha : a → 0 := by
        by_contra h_a
        have h_not := NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a (fun h => h_not_or (Or.inr h))
        exact h_not hay
      exact h_not_or (Or.inl ((Infinitesimal.is.Infinitesimal.of.XEq h₀).mp ha))
    ·
      constructor
      ·
        rw [show a / x = (a * y) / (b * x) * (b / y) by field_simp [hx0, hy0, hb0]]
        rw [show (a * y) / (b * x) * (b / y) = ((a * y) / (b * x) - 1) * (b / y) + (b / y) by ring]
        apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal
        ·
          apply InfinitesimalMul.of.Infinitesimal.NotInfinite hr
          intro h_infty
          grind
        ·
          exact h_by
      ·
        exact h_by
  else
    apply XEq.of.OrAndS
    obtain ⟨hay, _⟩ | ⟨hr, hbx⟩ := OrAndS.of.XEq h_cross
    ·
      exfalso
      have ha : a → 0 := by
        by_contra h_a
        have h_not := NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a (fun h => h_not_or (Or.inr h))
        exact h_not hay
      exact h_not_or (Or.inl ((Infinitesimal.is.Infinitesimal.of.XEq h₀).mp ha))
    ·
      right
      constructor
      ·
        rw [show (a / x) / (b / y) - 1 = (a * y) / (b * x) - 1 by
          conv_lhs => rw [Div.eq.Mul_Inv, Div.eq.Mul_Inv]
          have hbz : b * x ≠ 0 := by
            intro h
            rw [h] at hbx
            simp at hbx
          field_simp [hbz]]
        exact hr
      ·
        intro h_aby
        exact h_by h_aby


-- created on 2026-07-26
