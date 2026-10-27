import Initialize.Tactic.Attr.Basic
import Macro.Order.ExprWithLimits
import Mathlib.Algebra.Order.Archimedean.Real.Basic


@[path]
private lemma main
  [Nonempty α] [Preorder β]
  {S : Set α}
  {f g : α → β}
-- given
  (h : ∀ i ∈ S, f i = g i) :
-- imply
  min⁻¹[x ∈ S] f x = min⁻¹[x ∈ S] g x := by
-- proof
  unfold «min⁻¹»
  congr 1
  funext x
  apply propext
  constructor
  ·
    rintro ⟨hx, H⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [← h x hx, ← h y hy]
    exact H y hy
  ·
    rintro ⟨hx, H⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [h x hx, h y hy]
    exact H y hy

@[path]
private lemma definition
  [Nonempty α]
  {S : Set α}
  {f : α → ℝ}
  {x₀ : α}
-- given
  (h₀ : x₀ = min⁻¹[x ∈ S] f x)
  (h₁ : ∃ x ∈ S, ∀ y ∈ S, f x ≤ f y) :
-- imply
  f x₀ = Minima S f := by
-- proof
  have hs : min⁻¹[x ∈ S] f x ∈ S ∧ ∀ y ∈ S, f (min⁻¹[x ∈ S] f x) ≤ f y := Classical.epsilon_spec h₁
  rw [← h₀] at hs
  have hl : IsLeast (f '' S) (f x₀) := by
    refine ⟨⟨x₀, hs.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hs.2 y hy
  unfold Minima
  exact hl.csInf_eq.symm


-- created on 2019-04-13
