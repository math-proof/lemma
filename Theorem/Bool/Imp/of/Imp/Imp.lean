module

public section


public theorem Bool.Imp.of.Imp.Imp.right
  {p q r : Prop}
-- given
  (h₀ : p → q)
  (h₁ : r → p) :
-- imply
  r → q :=
-- proof
  fun h : r =>
    h₀ (h₁ h)


public theorem Bool.Imp.of.Imp.Imp
  {p q r : Prop}
-- given
  (h₀ : p → q)
  (h₁ : q → r) :
-- imply
  p → r :=
-- proof
  fun h : p =>
    h₁ (h₀ h)


-- created on 2026-11-17
