/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean -/


import Mathlib.Tactic
import Def.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
import Lemma.Nat.Sequences.PolynomiallyRecursiveMCFinite


namespace MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite

open MetaMathlibExt MvPolynomial

example : IsMCFinite (fun _ => 1) :=
  fun _ _ => ⟨1, 1, one_pos, one_pos, fun _ => 1, fun _ _ => by simp⟩

end MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
