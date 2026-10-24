/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean -/


import Mathlib.Tactic
import sympy.atlas.Combinatorics.InfiniteWord.PureMorphicWord
import Lemma.Finset.InfiniteWord.PureMorphicWord

namespace MetaMathlibExt

private def probeMorphism : Bool → List Bool
  | false => [false, true]
  | true => [true]

example : morphIterate probeMorphism 0 [false] = [false] := rfl
example : morphIterate probeMorphism 1 [false] = [false, true] := rfl
example : morphIterate probeMorphism 2 [false] = [false, true, true] := rfl
example : IsNonErasing probeMorphism := by intro b; cases b <;> decide

example (n : ℕ) : (morphIterate (fun x : Fin 2 => [x, 1 - x]) n [0]).length = 2 ^ n := by
  rw [morphIterate_length_of_uniform (k := 2) (fun _ => rfl), List.length_singleton, Nat.mul_one]

private def doublingUnitMorphism (_ : Unit) : List Unit := [(), ()]

private def constantUnitWord (_ : Nat) : Unit := ()

/-- Concrete witness exercising both prolongability and omega-limit clauses. -/
example : IsPureMorphic constantUnitWord := by
  refine ⟨doublingUnitMorphism, (), ?_, ?_⟩
  · refine ⟨[()], rfl, ?_⟩
    intro n hnil
    have hlen := congrArg List.length hnil
    rw [doublingUnitIterate_length] at hlen
    simp at hlen
  · constructor
    · intro M
      exact ⟨M, by rw [doublingUnitIterate_length]; exact self_le_two_pow M⟩
    · intro n i h
      exact Subsingleton.elim _ _

#print axioms IsPureMorphic

end MetaMathlibExt
