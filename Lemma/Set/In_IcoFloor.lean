import sympy.core.relational
import Lemma.Algebra.EqFloor.is.Le.Lt
import Lemma.Set.In_Ico.of.Le.Lt
open Algebra Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α) :
-- imply
  x ∈ Ico (⌊x⌋ : α) (⌊x⌋ + 1) := by
-- proof
  denote h_d : d = ⌊x⌋
  have := Le.Lt.of.EqFloor h_d.symm
  let ⟨h₀, h₁⟩ := this
  rw [h_d] at h₀
  rw [h_d] at h₁
  apply In_Ico.of.Le.Lt h₀ h₁


-- created on 2025-03-30
-- updated on 2025-05-04
