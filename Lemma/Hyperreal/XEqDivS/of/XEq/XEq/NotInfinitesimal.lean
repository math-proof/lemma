import Lemma.Hyperreal.Infinitesimal.is.Infinitesimal.of.XEq
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Hyperreal.XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h_not_y : ¬(y → 0))
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a / x ≈ b / y := by
-- proof
  have h_not_x := NotInfinitesimal.of.NotInfinitesimal.XEq h₁ h_not_y
  if hb : b → 0 then
    apply XEq.of.OrAndS
    left
    constructor
    ·
      have ha := Infinitesimal.of.Infinitesimal.XEq h₀.symm hb
      exact InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal ha h_not_x
    ·
      exact InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hb h_not_y
  else
    have hb0 := Ne_0.of.NotInfinitesimal hb
    have hx0 := Ne_0.of.NotInfinitesimal h_not_x
    have hy0 := Ne_0.of.NotInfinitesimal h_not_y
    have h_not_or_x : ¬((b → 0) ∨ x → 0) := fun h =>
      match h with
      | Or.inl hb' => hb hb'
      | Or.inr hx => h_not_x hx
    have h_cross := XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS (by grind) h₀ h₁.symm
    if h_by : (b / y) → 0 then
      left
      obtain ⟨hay, _⟩ | ⟨hr, hbx⟩ := OrAndS.of.XEq h_cross
      ·
        exfalso
        have ha : a → 0 := by
          by_contra h_a
          have h_not := NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a h_not_y
          exact h_not hay
        exact hb (Infinitesimal.of.Infinitesimal.XEq h₀ ha)
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
          have h_not := NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a h_not_y
          exact h_not hay
        exact hb (Infinitesimal.of.Infinitesimal.XEq h₀ ha)
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
