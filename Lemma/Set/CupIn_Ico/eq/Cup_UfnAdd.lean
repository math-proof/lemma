import sympy.sets.sets
import Lemma.Set.Eq.of.All_Imp.All_Imp
import Lemma.Set.In_Cup.is.Any_In
import Lemma.Algebra.AnyIn_Ico.of.AnyIn_Ico
open Set Algebra


@[main]
private lemma main
  [AddCommGroup ι] [PartialOrder ι] [IsOrderedAddMonoid ι]
-- given
  (d a b : ι)
  (f : ι → Set β) :
-- imply
  ⋃ n ∈ Ico a b, f n = ⋃ n ∈ Ico (a - d) (b - d), f (n + d) := by
-- proof
  apply Eq.of.All_Imp.All_Imp <;>
    intro i h <;>
    have h := Any_In.of.In_Cup.set h <;>
    apply In_Cup.of.Any_In.set
  ·
    apply AnyIn_Ico.of.AnyIn_Ico.offset h
  ·
    have h := AnyIn_Ico.of.AnyIn_Ico.offset h (-d)
    simp at h
    assumption


-- created on 2025-08-04
