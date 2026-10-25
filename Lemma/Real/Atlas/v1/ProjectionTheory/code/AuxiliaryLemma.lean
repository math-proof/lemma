import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.AuxiliaryLemma
open Finset IncidenceGeometry


namespace IncidenceGeometry

/--
[AffineLine.card_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/AuxiliaryLemma.lean)
-/
@[path]
lemma AffineLine.card_toFinset
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {L : AffineLine p} :
-- imply
  L.toFinset.card = p := by
-- proof
  unfold toFinset
  obtain ha | hb := L.nondegenerate
  · have h1 : ∀ y : ZMod p, ∃! x : ZMod p, L.a * x + L.b * y = L.c := by
    intro y
    use L.a⁻¹ * (L.c - L.b * y)
    refine ⟨?_, ?_⟩
    · have : L.a * (L.a⁻¹ * (L.c - L.b * y)) = L.c - L.b * y := by
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      linear_combination this
    · intro x' hx'
      have hax : L.a * x' = L.c - L.b * y := by linear_combination hx'
      calc x' = L.a⁻¹ * (L.a * x') := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
        _ = L.a⁻¹ * (L.c - L.b * y) := by rw [hax]
    have h2 : (univ.filter (fun pt : ZMod p × ZMod p => L.a * pt.1 + L.b * pt.2 = L.c)).card =
      (univ : Finset (ZMod p)).card := by
      apply Finset.card_bij (fun pt _ => pt.2)
      · intro pt _; exact mem_univ _
      · intro ⟨x₁, y₁⟩ h1m ⟨x₂, y₂⟩ h2m heq
        simp only [mem_filter, mem_univ, true_and] at h1m h2m
        simp only at heq; subst heq
        exact Prod.ext ((h1 y₁).unique h1m h2m) rfl
      · intro y _
        obtain ⟨x, hx, _⟩ := h1 y
        exact ⟨⟨x, y⟩, by simp [hx], rfl⟩
    rw [h2]; exact ZMod.card p
  · have h1 : ∀ x : ZMod p, ∃! y : ZMod p, L.a * x + L.b * y = L.c := by
    intro x
    use L.b⁻¹ * (L.c - L.a * x)
    refine ⟨?_, ?_⟩
    · have : L.b * (L.b⁻¹ * (L.c - L.a * x)) = L.c - L.a * x := by
      rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      linear_combination this
    · intro y' hy'
      have hby : L.b * y' = L.c - L.a * x := by linear_combination hy'
      calc y' = L.b⁻¹ * (L.b * y') := by rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]
        _ = L.b⁻¹ * (L.c - L.a * x) := by rw [hby]
    have h2 : (univ.filter (fun pt : ZMod p × ZMod p => L.a * pt.1 + L.b * pt.2 = L.c)).card =
      (univ : Finset (ZMod p)).card := by
      apply Finset.card_bij (fun pt _ => pt.1)
      · intro pt _; exact mem_univ _
      · intro ⟨x₁, y₁⟩ h1m ⟨x₂, y₂⟩ h2m heq
        simp only [mem_filter, mem_univ, true_and] at h1m h2m
        simp only at heq; subst heq
        exact Prod.ext rfl ((h1 x₁).unique h1m h2m)
      · intro x _
        obtain ⟨y, hy, _⟩ := h1 x
        exact ⟨⟨x, y⟩, by simp [hy], rfl⟩
    rw [h2]; exact ZMod.card p

end IncidenceGeometry

namespace IncidenceGeometry

/--
[perp_transitivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/AuxiliaryLemma.lean)
-/
@[path]
lemma perp_transitivity
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  [Field F]
  {a₁ b₁ a₂ b₂ dx dy ux uy : F}
-- given
  (hnd1 : a₁ ≠ 0 ∨ b₁ ≠ 0)
  (hdir : dx ≠ 0 ∨ dy ≠ 0)
  (h0 : a₁ * dx + b₁ * dy = 0)
  (h1 : a₂ * dx + b₂ * dy = 0)
  (h2 : a₁ * ux + b₁ * uy = 0) :
-- imply
  a₂ * ux + b₂ * uy = 0 := by
-- proof
  by_cases heq : uy * dx = ux * dy
  · have key : (a₂ * ux + b₂ * uy) * dx = 0 := by
    have : (a₂ * ux + b₂ * uy) * dx = ux * (a₂ * dx + b₂ * dy) := by
      linear_combination b₂ * heq
    rw [this, h2, mul_zero]
    have key2 : (a₂ * ux + b₂ * uy) * dy = 0 := by
      have : (a₂ * ux + b₂ * uy) * dy = uy * (a₂ * dx + b₂ * dy) := by
        linear_combination (-a₂) * heq
      rw [this, h2, mul_zero]
    obtain hdx | hdy := hdir
    · exact mul_right_cancel₀ hdx (by rw [key, zero_mul])
    · exact mul_right_cancel₀ hdy (by rw [key2, zero_mul])
  · exfalso
    have ha : a₁ * (uy * dx - ux * dy) = 0 := by linear_combination uy * h1 - dy * h3
    have hb : b₁ * (uy * dx - ux * dy) = 0 := by linear_combination (-ux) * h1 + dx * h3
    have hdet : uy * dx - ux * dy ≠ 0 := sub_ne_zero.mpr heq
    obtain ha1 | hb1 := hnd1
    · exact ha1 ((mul_eq_zero.mp ha).elim id (fun h => absurd h hdet))
    · exact hb1 ((mul_eq_zero.mp hb).elim id (fun h => absurd h hdet))

end IncidenceGeometry

namespace IncidenceGeometry

/--
[AffineLine.inter_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/AuxiliaryLemma.lean)
-/
@[path]
lemma AffineLine.inter_card_le_one
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {L₁ L₂ : AffineLine p}
-- given
  (h : ¬ L₁.SamePointSet L₂) :
-- imply
  (L₁.toFinset ∩ L₂.toFinset).card ≤ 1 := by
-- proof
  rw [Finset.card_le_one]
  intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2
  simp only [AffineLine.toFinset, mem_inter, mem_filter, mem_univ, true_and] at h1 h2
  by_contra hne
  exfalso; apply h
  unfold SamePointSet toFinset
  ext ⟨x, y⟩
  simp only [mem_filter, mem_univ, true_and]
  have hne' : (x₁, y₁) ≠ (x₂, y₂) := hne
  have hdir : x₁ - x₂ ≠ 0 ∨ y₁ - y₂ ≠ 0 := by
    by_contra hall
    simp only [not_or, Classical.not_not] at hall
    exact hne' (Prod.ext (sub_eq_zero.mp hall.1) (sub_eq_zero.mp hall.2))
  have hd1 : L₁.a * (x₁ - x₂) + L₁.b * (y₁ - y₂) = 0 := by linear_combination h1.1 - h2.1
  have hd2 : L₂.a * (x₁ - x₂) + L₂.b * (y₁ - y₂) = 0 := by linear_combination h1.2 - h2.2
  constructor
  · intro hL1
    have hu : L₁.a * (x - x₁) + L₁.b * (y - y₁) = 0 := by linear_combination hL1 - h1.1
    linear_combination (perp_transitivity L₁.nondegenerate hdir hd1 hd2 hu) + h1.2
  · intro hL2
    have hu : L₂.a * (x - x₁) + L₂.b * (y - y₁) = 0 := by linear_combination hL2 - h1.2
    linear_combination (perp_transitivity L₂.nondegenerate hdir hd2 hd1 hu) + h1.1

end IncidenceGeometry


-- created on 2026-10-23
