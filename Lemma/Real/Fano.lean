import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset BigOperators


namespace MathlibExt.InformationTheory.Fano

/--
[fano_inequality_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Fano.lean)
-/
@[path]
lemma fano_inequality_general
  [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [DecidableEq α]
  {p : α → β → ℝ}
  {g : β → α}
-- given
  (hp_pos : ∀ a b, 0 < p a b)
  (hp_sum : ∑ a : α, ∑ b : β, p a b = 1)
  (hcard : 2 ≤ Fintype.card α) :
-- imply
  let pY : β → ℝ := by
-- proof
  intro pY Pe HXY
  have hpY_eq : ∀ b, pY b = ∑ a : α, p a b := fun b => rfl
  have hHXY_eq : HXY = -(∑ a : α, ∑ b : β, p a b * Real.log (p a b / pY b)) := rfl
  let eb : β → ℝ := fun b => ∑ a : α, if g b ≠ a then p a b else 0
  have heb : ∀ b, eb b = ∑ a : α, if g b ≠ a then p a b else 0 := fun b => rfl
  have hPe : Pe = ∑ b : β, eb b := rfl
  have hKpos : 0 < ((Fintype.card α - 1 : ℕ) : ℝ) := by
    have h1 : 0 < Fintype.card α - 1 := by omega
    exact_mod_cast h1
  have hKne : ((Fintype.card α - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hKpos
  have hunivα : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
  have hunivβ : (Finset.univ : Finset β).Nonempty := Finset.univ_nonempty
  have hqpos : ∀ b, 0 < pY b := by
    intro b
    rw [hpY_eq b]
    exact Finset.sum_pos (fun a _ => hp_pos a b) hunivα
  have hcpos : ∀ b, 0 < p (g b) b := fun b => hp_pos _ _
  -- error sum equals sum over the erased finset
  have hsum_erase : ∀ b, (∑ a, if g b ≠ a then p a b else 0)
    = ∑ a ∈ Finset.univ.erase (g b), p a b := by
    intro b
    have h1 : (∑ a ∈ Finset.univ.erase (g b), (if g b ≠ a then p a b else 0))
      = ∑ a, if g b ≠ a then p a b else 0 :=
      Finset.sum_subset (Finset.erase_subset _ _) (by
        intro x _ hnot
        have hx : x = g b := by
          by_contra hne
          exact hnot (Finset.mem_erase.mpr ⟨show x ≠ g b from hne, Finset.mem_univ x⟩)
        subst hx
        simp)
    have h2 : (∑ a ∈ Finset.univ.erase (g b), (if g b ≠ a then p a b else 0))
      = ∑ a ∈ Finset.univ.erase (g b), p a b := by
      apply Finset.sum_congr rfl
      intro x hx
      have hne : g b ≠ x := Ne.symm (Finset.mem_erase.mp hx).1
      exact ite_eq_left hne
    exact h1.symm.trans h2
  have hcard_erase : ∀ b, (Finset.univ.erase (g b)).card = Fintype.card α - 1 := by
    intro b
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have herase_nonempty : ∀ b, (Finset.univ.erase (g b)).Nonempty := by
    intro b
    rw [← Finset.card_pos, hcard_erase b]
    omega
  have hepos : ∀ b, 0 < eb b := by
    intro b
    rw [heb b, hsum_erase b]
    exact Finset.sum_pos (fun a _ => hp_pos a b) (herase_nonempty b)
  have hP : ∀ b, (∑ a ∈ Finset.univ.erase (g b), p a b) = eb b :=
    fun b => (hsum_erase b).symm.trans (heb b).symm
  -- split marginal into correct + error
  have hsplit : ∀ b, pY b = p (g b) b + eb b := by
    intro b
    have h1 := (Finset.add_sum_erase Finset.univ (fun a => p a b)
      (Finset.mem_univ (g b))).symm
    rw [← hsum_erase b, ← heb b] at h1
    rwa [hpY_eq b]
  -- split per-b entropy into correct + error indices
  have hentsplit : ∀ b, (∑ a, p a b * Real.log (p a b / pY b))
    = p (g b) b * Real.log (p (g b) b / pY b)
      + ∑ a ∈ Finset.univ.erase (g b), p a b * Real.log (p a b / pY b) :=
    fun b => (Finset.add_sum_erase Finset.univ
      (fun a => p a b * Real.log (p a b / pY b)) (Finset.mem_univ (g b))).symm
  -- expand log(p/q) = log(p/e) + log(e/q)
  have hexpand : ∀ b, ∀ a ∈ Finset.univ.erase (g b),
    p a b * Real.log (p a b / pY b)
      = p a b * Real.log (p a b / eb b) + p a b * Real.log (eb b / pY b) := by
    intro b a ha
    have hpa : p a b ≠ 0 := ne_of_gt (hp_pos a b)
    have hebe : eb b ≠ 0 := ne_of_gt (hepos b)
    have hqbe : pY b ≠ 0 := ne_of_gt (hqpos b)
    rw [Real.log_div hpa hqbe, Real.log_div hpa hebe, Real.log_div hebe hqbe]
    ring
  have hEsplit : ∀ b, (∑ a ∈ Finset.univ.erase (g b), p a b * Real.log (p a b / pY b))
    = (∑ a ∈ Finset.univ.erase (g b), p a b * Real.log (p a b / eb b))
      + eb b * Real.log (eb b / pY b) := by
    intro b
    have e1 : (∑ a ∈ Finset.univ.erase (g b), p a b * Real.log (p a b / pY b))
      = ∑ a ∈ Finset.univ.erase (g b),
        (p a b * Real.log (p a b / eb b) + p a b * Real.log (eb b / pY b)) :=
      Finset.sum_congr rfl (fun a ha => hexpand b a ha)
    rw [e1, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_mul, hP b]
  -- inner entropy bound via uniform log-sum
  have hinner : ∀ b, -(∑ a ∈ Finset.univ.erase (g b), p a b * Real.log (p a b / eb b))
    ≤ eb b * Real.log ((Fintype.card α - 1 : ℕ) : ℝ) := by
    intro b
    have hg := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div
      (Finset.univ.erase (g b)) (fun a => p a b)
      (fun _ => eb b / ((Fintype.card α - 1 : ℕ) : ℝ))
      (fun a _ => le_of_lt (hp_pos a b))
      (fun _ _ => div_pos (hepos b) hKpos)
    rw [hP b] at hg
    have hQ : (∑ _a ∈ Finset.univ.erase (g b),
      eb b / ((Fintype.card α - 1 : ℕ) : ℝ)) = eb b := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard_erase b, ← mul_div_assoc,
        mul_div_cancel_left₀ _ hKne]
    rw [hQ] at hg
    rw [div_self (ne_of_gt (hepos b)), Real.log_one, mul_zero] at hg
    have hexp : ∀ a ∈ Finset.univ.erase (g b),
      p a b * Real.log (p a b / (eb b / ((Fintype.card α - 1 : ℕ) : ℝ)))
      = p a b * Real.log (p a b / eb b)
        + p a b * Real.log ((Fintype.card α - 1 : ℕ) : ℝ) := by
      intro a ha
      have hpa : p a b ≠ 0 := ne_of_gt (hp_pos a b)
      have hebe : eb b ≠ 0 := ne_of_gt (hepos b)
      have hdiv : p a b / (eb b / ((Fintype.card α - 1 : ℕ) : ℝ))
        = (p a b / eb b) * ((Fintype.card α - 1 : ℕ) : ℝ) := by
        rw [div_div_eq_mul_div, div_mul_eq_mul_div]
      rw [hdiv, Real.log_mul (div_ne_zero hpa hebe) hKne, mul_add]
    have h3 : (∑ a ∈ Finset.univ.erase (g b),
      p a b * Real.log (p a b / (eb b / ((Fintype.card α - 1 : ℕ) : ℝ))))
      = (∑ a ∈ Finset.univ.erase (g b), p a b * Real.log (p a b / eb b))
        + eb b * Real.log ((Fintype.card α - 1 : ℕ) : ℝ) := by
      have e1 := Finset.sum_congr rfl (fun a ha => hexp a ha)
      rw [e1, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul, hP b]
    rw [h3] at hg
    linarith
  -- per-b Fano bound
  have hperb : ∀ b, -(∑ a, p a b * Real.log (p a b / pY b))
    ≤ (-(p (g b) b * Real.log (p (g b) b / pY b)) - eb b * Real.log (eb b / pY b))
      + eb b * Real.log ((Fintype.card α - 1 : ℕ) : ℝ) := by
    intro b
    rw [hentsplit b, hEsplit b]
    have h := hinner b
    linarith
  -- reassemble joint entropy
  have hHXY_sum : HXY = ∑ b, -(∑ a, p a b * Real.log (p a b / pY b)) := by
    rw [hHXY_eq, Finset.sum_comm, ← Finset.sum_neg_distrib]
  have hQtot : (∑ b, pY b) = 1 := by
    simp only [hpY_eq]
    rwa [Finset.sum_comm]
  have hCtot : (∑ b, p (g b) b) + (∑ b, eb b) = 1 := by
    rw [← Finset.sum_add_distrib]
    have h1 : (∑ b : β, (p (g b) b + eb b)) = ∑ b : β, ∑ a : α, p a b :=
      Finset.sum_congr rfl (fun b _ => (hsplit b).symm)
    rwa [h1, Finset.sum_comm]
  -- grouping bounds
  have hgroup_c : (∑ b, p (g b) b) * Real.log ((∑ b, p (g b) b) / (∑ b, pY b))
    ≤ ∑ b, p (g b) b * Real.log (p (g b) b / pY b) :=
    Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div Finset.univ _ _
      (fun b _ => le_of_lt (hcpos b)) (fun b _ => hqpos b)
  rw [hQtot, div_one] at hgroup_c
  have hgroup_e : (∑ b, eb b) * Real.log ((∑ b, eb b) / (∑ b, pY b))
    ≤ ∑ b, eb b * Real.log (eb b / pY b) :=
    Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div Finset.univ _ _
      (fun b _ => le_of_lt (hepos b)) (fun b _ => hqpos b)
  rw [hQtot, div_one] at hgroup_e
  have hsplit_sum : (∑ b : β, (-(p (g b) b * Real.log (p (g b) b / pY b))
    - eb b * Real.log (eb b / pY b)))
    = -(∑ b, p (g b) b * Real.log (p (g b) b / pY b))
      - (∑ b, eb b * Real.log (eb b / pY b)) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_neg_distrib _
  have hS : (∑ b : β, (-(p (g b) b * Real.log (p (g b) b / pY b))
    - eb b * Real.log (eb b / pY b)))
    ≤ -((∑ b, p (g b) b) * Real.log (∑ b, p (g b) b))
      - ((∑ b, eb b) * Real.log (∑ b, eb b)) := by
    rw [hsplit_sum]
    simp only [sub_eq_add_neg]
    exact add_le_add (neg_le_neg hgroup_c) (neg_le_neg hgroup_e)
  have htot : HXY ≤ (∑ b : β, (-(p (g b) b * Real.log (p (g b) b / pY b))
    - eb b * Real.log (eb b / pY b)))
    + (∑ b, eb b) * Real.log ((Fintype.card α - 1 : ℕ) : ℝ) := by
    rw [hHXY_sum]
    have hle : ∀ b ∈ (Finset.univ : Finset β), -(∑ a, p a b * Real.log (p a b / pY b))
      ≤ (-(p (g b) b * Real.log (p (g b) b / pY b)) - eb b * Real.log (eb b / pY b))
        + eb b * Real.log ((Fintype.card α - 1 : ℕ) : ℝ) := fun b _ => hperb b
    have hs := Finset.sum_le_sum hle
    rw [Finset.sum_add_distrib] at hs
    rwa [← Finset.sum_mul] at hs
  have hC : (∑ b, p (g b) b) = 1 - (∑ b, eb b) := by linarith
  rw [hPe]
  rw [hC] at hS
  linarith
set_option linter.unusedDecidableInType false in

end MathlibExt.InformationTheory.Fano

namespace MathlibExt.InformationTheory.Fano

/--
[fano_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Fano.lean)
-/
@[path]
lemma fano_inequality
  [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [DecidableEq α] [DecidableEq β]
  {p : α → β → ℝ}
  {g : β → α}
-- given
  (hp_pos : ∀ a b, 0 < p a b)
  (hp_sum : ∑ a : α, ∑ b : β, p a b = 1)
  (hcard : 2 ≤ Fintype.card α) :
-- imply
  let pY : β → ℝ :=
-- proof
  fano_inequality_general p hp_pos hp_sum g hcard

end MathlibExt.InformationTheory.Fano


-- created on 2026-10-20
-- updated on 2026-10-26
