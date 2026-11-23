/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean -/
module

public import Mathlib.Tactic
public import Def.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
public import Theorem.Nat.Sequences.PolynomiallyRecursiveMCFinite

public section

namespace MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite

open MetaMathlibExt MvPolynomial

example : IsMCFinite (fun _ => 1) :=
  fun _ _ => ⟨1, 1, one_pos, one_pos, fun _ => 1, fun _ _ => by simp⟩

end MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
