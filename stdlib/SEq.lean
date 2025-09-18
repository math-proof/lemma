import Mathlib.Tactic

/--
heterogeneous/asymptotic equality
-/
def SEq {α : Type u} {Vector : α → Sort v} {n m : α} (a : Vector n) (b : Vector m) : Prop :=
  n = m ∧ HEq a b
infix:50 " ≃ " => SEq

@[symm]
lemma SEq.symm
  {α : Type u} {Vector : α → Sort v} {n m : α} {a : Vector n} {b : Vector m}
  (h : SEq a b) :
  SEq b a :=
  ⟨h.1.symm, h.2.symm⟩

lemma SEq.comm :
  a ≃ b ↔ b ≃ a :=
  Iff.intro SEq.symm SEq.symm

lemma SEq.trans
  (h₀ : SEq a b)
  (h₁ : SEq b c) :
  SEq a c :=
  ⟨h₀.1.trans h₁.1, h₀.2.trans h₁.2⟩

@[refl, match_pattern]
lemma SEq.rfl
  {α : Type u} {Vector : α → Sort v} {n : α}
  (a : Vector n) :
  a ≃ a :=
  ⟨by rfl, HEq.rfl⟩
