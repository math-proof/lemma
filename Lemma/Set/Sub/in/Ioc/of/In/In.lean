import sympy.sets.sets
import Lemma.Set.Neg.In.Ioc.of.In_Ico
import Lemma.Set.Add.in.Ioc.of.In.In
import Lemma.Int.Sub.eq.Add_Neg
open Set Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c d x₀ x₁ : α}
-- given
  (h₀ : x₀ ∈ Ioc a b)
  (h₁ : x₁ ∈ Ico c d) :
-- imply
  x₀ - x₁ ∈ Ioc (a - d) (b - c) := by
-- proof
  have h₁ := Neg.In.Ioc.of.In_Ico h₁
  have h := Add.in.Ioc.of.In.In h₀ h₁
  repeat rw [Add_Neg.eq.Sub] at h
  assumption


-- created on 2025-10-01
