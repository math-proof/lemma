/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean -/

import Mathlib.Data.Fintype.Basic
import sympy.atlas.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred

section
namespace MathlibExt.GameTheory.SocialChoice.ArrowWanted

/-! # Arrow's impossibility theorem

Records Pareto and IIA for social welfare functions over strict total orders.
-/

/-- Strict total order for strict preference, reusing the shared `MathlibExt.Order` bundle. -/
abbrev StrictTotalOrder := MathlibExt.Order.StrictTotalOrder

namespace StrictTotalOrder

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.mk` constructor.

For new code, use `MathlibExt.Order.StrictTotalOrder.mk` directly. -/
abbrev mk {α : Type*} (lt : α → α → Prop)
    (irrefl : ∀ a, ¬lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a) :
    StrictTotalOrder α :=
  MathlibExt.Order.StrictTotalOrder.mk lt irrefl trans total

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.lt` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.lt` directly. -/
abbrev lt {α : Type*} (self : StrictTotalOrder α) : α → α → Prop :=
  MathlibExt.Order.StrictTotalOrder.lt self

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.irrefl` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.irrefl` directly. -/
abbrev irrefl {α : Type*} (self : StrictTotalOrder α) (a : α) : ¬self.lt a a :=
  MathlibExt.Order.StrictTotalOrder.irrefl self a

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.trans` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.trans` directly. -/
abbrev trans {α : Type*} (self : StrictTotalOrder α) {a b c : α}
    (h1 : self.lt a b) (h2 : self.lt b c) : self.lt a c :=
  MathlibExt.Order.StrictTotalOrder.trans self h1 h2

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.total` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.total` directly. -/
abbrev total {α : Type*} (self : StrictTotalOrder α) {a b : α} (h : a ≠ b) :
    self.lt a b ∨ self.lt b a :=
  MathlibExt.Order.StrictTotalOrder.total self h

end StrictTotalOrder

/-- A profile assigns each voter a strict total order over alternatives. -/
abbrev Profile (Alt Voter : Type*) := Voter → StrictTotalOrder Alt

/-- A social welfare function maps each unrestricted profile to a social strict total order. -/
abbrev SocialWelfareFunction (Alt Voter : Type*) := Profile Alt Voter → StrictTotalOrder Alt

/-- Pareto/unanimity: if every voter strictly prefers `a` to `b`, so does society. -/
def IsPareto {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∀ (p : Profile Alt Voter) (a b : Alt), (∀ i, (p i).lt a b) → (F p).lt a b

/-- Independence of irrelevant alternatives: the social comparison of each pair `a,b`
depends only on voters' comparisons of that pair. That is, if two profiles agree on all
voters' `a`-vs-`b` comparisons, the social `a`-vs-`b` comparison agrees. -/
def IsIIA {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∀ (p₁ p₂ : Profile Alt Voter) (a b : Alt),
    (∀ i, (p₁ i).lt a b ↔ (p₂ i).lt a b) → ((F p₁).lt a b ↔ (F p₂).lt a b)

/-- `d` is a dictator for `F`: the social order always extends `d`'s strict preferences. -/
def IsDictator {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) (d : Voter) : Prop :=
  ∀ (p : Profile Alt Voter) (a b : Alt), (p d).lt a b → (F p).lt a b

/-- Dictatorship: some fixed voter whose strict preferences are always respected socially. -/
def IsDictatorial {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∃ d : Voter, IsDictator F d

/-- An arbitrary injection from alternatives into naturals. -/
private noncomputable def baseRank {Alt : Type*} [Fintype Alt] : Alt → ℕ :=
  fun w => (Fintype.equivFin Alt w).val

private lemma baseRank_injective {Alt : Type*} [Fintype Alt] :
    Function.Injective (baseRank (Alt := Alt)) := by
  intro a b h
  unfold baseRank at h
  have h2 : Fintype.equivFin Alt a = Fintype.equivFin Alt b := Fin.val_injective h
  exact (Fintype.equivFin Alt).injective h2

/-- Rank function putting `x` first, then `y`, then `z`, then everything else. -/
private noncomputable def rank3 {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z w : Alt) : ℕ :=
  if w = x then 0 else if w = y then 1 else if w = z then 2 else 3 + baseRank (Alt := Alt) w

private lemma rank3_injective {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z : Alt) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) :
    Function.Injective (rank3 (Alt := Alt) x y z) := by
  intro a b h
  have e1 : a = x ∨ a = y ∨ a = z ∨ (a ≠ x ∧ a ≠ y ∧ a ≠ z) := by
    by_cases ha1 : a = x
    · exact Or.inl ha1
    · by_cases ha2 : a = y
      · exact Or.inr (Or.inl ha2)
      · by_cases ha3 : a = z
        · exact Or.inr (Or.inr (Or.inl ha3))
        · exact Or.inr (Or.inr (Or.inr ⟨ha1, ha2, ha3⟩))
  have e2 : b = x ∨ b = y ∨ b = z ∨ (b ≠ x ∧ b ≠ y ∧ b ≠ z) := by
    by_cases hb1 : b = x
    · exact Or.inl hb1
    · by_cases hb2 : b = y
      · exact Or.inr (Or.inl hb2)
      · by_cases hb3 : b = z
        · exact Or.inr (Or.inr (Or.inl hb3))
        · exact Or.inr (Or.inr (Or.inr ⟨hb1, hb2, hb3⟩))
  unfold rank3 at h
  rcases e1 with rfl | rfl | rfl | ⟨ha1, ha2, ha3⟩ <;>
    rcases e2 with rfl | rfl | rfl | ⟨hb1, hb2, hb3⟩ <;>
    simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]
  all_goals try omega
  exact baseRank_injective (by omega)

/-- Strict total order ranking `x` above `y` above `z` above everything else. -/
private noncomputable def mkOrder3 {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z : Alt) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) : StrictTotalOrder Alt where
  lt := fun u v => rank3 (Alt := Alt) x y z u < rank3 (Alt := Alt) x y z v
  irrefl := fun a h => (lt_irrefl _) h
  trans := fun h1 h2 => Nat.lt_trans h1 h2
  total := by
    intro a b hab
    have hne : rank3 (Alt := Alt) x y z a ≠ rank3 (Alt := Alt) x y z b :=
      fun he => hab (rank3_injective x y z h1 h2 h3 he)
    exact lt_or_gt_of_ne hne

/-- `C` is decisive for the ordered pair `(a, b)`: whenever every member of `C`
ranks `a` above `b`, so does society. -/
private def decFor {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter)
    (C : Finset Voter) (a b : Alt) : Prop :=
  ∀ p : Profile Alt Voter, (∀ i ∈ C, (p i).lt a b) → (F p).lt a b
end MathlibExt.GameTheory.SocialChoice.ArrowWanted
end
