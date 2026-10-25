import Mathlib
import Abbrev.Analysis.Section_8_1.Part2
/-!
# Analysis I, Section 8.1: Countability

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Custom notions for "equal cardinality", "countable", and "at most countable".  Note that Mathlib's
{name}`Countable` typeclass corresponds to what we call "at most countable" in this text.
- Countability of the integers and rationals.

Note that as the Chapter 3 set theory has been deprecated, we will not re-use relevant constructions from that theory here, replacing them with Mathlib counterparts instead.

-/


namespace Chapter8

theorem CountablyInfinite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  CountablyInfinite X ↔ CountablyInfinite Y := ⟨ hXY.symm.trans, hXY.trans ⟩

theorem Finite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Finite X ↔ Finite Y := by obtain ⟨ f, hf ⟩ := hXY; exact (Equiv.ofBijective f hf).finite_iff

theorem AtMostCountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  AtMostCountable X ↔ AtMostCountable Y := by
  simp [AtMostCountable, CountablyInfinite.equiv hXY, Finite.equiv hXY]

/-- Equivalence with Mathlib's {name}`Denumerable` concept (cf. Remark 8.1.2) -/
theorem CountablyInfinite.iff (X : Type) : CountablyInfinite X ↔ Nonempty (Denumerable X) := by
  simp [CountablyInfinite, EqualCard.iff]; constructor
  . intro ⟨ e ⟩; exact ⟨ Denumerable.mk' e ⟩
  intro ⟨ h ⟩; exact ⟨ h.eqv X ⟩

/-- Equivalence with Mathlib's {name}`Countable` typeclass -/
theorem CountablyInfinite.iff' (X : Type) : CountablyInfinite X ↔ Countable X ∧ Infinite X := by
  rw [iff, nonempty_denumerable_iff]

theorem CountablyInfinite.toCountable {X : Type} (hX: CountablyInfinite X) : Countable X := by
  simp_all [iff']

theorem CountablyInfinite.toInfinite {X : Type} (hX: CountablyInfinite X) : Infinite X := by
  simp_all [iff']

theorem AtMostCountable.iff (X : Type) : AtMostCountable X ↔ Countable X := by
  observe h1 : CountablyInfinite X ↔ Countable X ∧ Infinite X
  observe h2 : Finite X ∨ Infinite X
  observe h3 : Finite X → Countable X
  tauto

theorem CountablyInfinite.iff_image_inj {A:Type} (X: Set A) : CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' .univ := by
  constructor
  . intro ⟨ g, hg ⟩
    choose f hleft hright using Function.bijective_iff_has_inverse.mp hg
    refine ⟨ ⟨ Subtype.val ∘ f, ?_ ⟩, ?_ ⟩
    . intro x y hxy; apply hright.injective; simp_all [Subtype.val_inj]
    ext x; simp only [Set.mem_image, Set.mem_univ, true_and]
    constructor
    . intro hx
      use g ⟨x, hx⟩
      change (f (g ⟨x, hx⟩)).1 = x
      rw [hleft]
    rintro ⟨n, rfl⟩
    exact (f n).2
  intro ⟨ f, hf ⟩
  have := Function.leftInverse_invFun (Function.Embedding.injective f)
  use (Function.invFun f) ∘ Subtype.val; split_ands
  . rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h; grind
  intro n; use ⟨ f n, by aesop ⟩; grind

end Chapter8
