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
def SEq.rfl
  {α : Type u} {Vector : α → Sort v} {n : α}
  (a : Vector n) :
  a ≃ a :=
  ⟨by rfl, HEq.rfl⟩

lemma SEq.cast.comm
  {α : Type u} {Vector : α → Sort v} {n m : α} {a : Vector n} {b : Vector m}
  (h : SEq a b) :
  a = cast (congrArg Vector h.left.symm) b :=
  match h with
  | ⟨Eq.refl _, h⟩ => h.eq

lemma SEq.cast
  {α : Type u} {Vector : α → Sort v} {n m : α} {a : Vector n} {b : Vector m}
  (h : SEq a b) :
  cast (congrArg Vector h.left) a = b :=
  match h with
  | ⟨Eq.refl _, h⟩ => h.eq

lemma Not.SEq.symm
  {α : Type u} {Vector : α → Sort v} {n m : α} {a : Vector n} {b : Vector m}
  (h : ¬SEq a b) :
  ¬SEq b a :=
  fun h' => h h'.symm

lemma Not.HEq.symm
  {α β : Sort u} {a : α} {b : β}
  (h : ¬a ≍ b) :
  ¬b ≍ a :=
  fun h' => h h'.symm
