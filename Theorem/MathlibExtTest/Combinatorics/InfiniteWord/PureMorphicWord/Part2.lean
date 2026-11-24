module
public import Mathlib.Tactic
public import Def.Combinatorics.InfiniteWord.PureMorphicWord
public import Theorem.Finset.InfiniteWord.PureMorphicWord
public import Def.MathlibExtTest.Combinatorics.InfiniteWord.PureMorphicWord.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean -/
namespace MetaMathlibExt

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
