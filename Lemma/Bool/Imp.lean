import sympy.Basic


@[main]
private lemma swap :
-- imply
  (a → p → q) ↔ (p → a → q) :=
-- proof
  ⟨fun h hp ha => h ha hp, fun h ha hp => h hp ha⟩


@[main]
private lemma fold :
-- imply
  (a ∧ b → c) ↔ (b → a → c) :=
-- proof
  ⟨fun h hb ha => h ⟨ha, hb⟩, fun h hab => h hab.2 hab.1⟩


-- created on 2026-09-27
