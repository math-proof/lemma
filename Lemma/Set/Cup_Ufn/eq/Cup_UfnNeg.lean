import Lemma.Set.Eq.of.All_Imp.All_Imp
import Lemma.Set.In_Cup.is.Any_In
import Lemma.Int.Any_UnaryFnNeg.of.Any
open Set Int


@[main]
private lemma main
  [InvolutiveNeg α]
  {f : α → Set β} :
-- imply
  ⋃ i, f i = ⋃ i, f (-i) := by
-- proof
  apply Eq.of.All_Imp.All_Imp <;> 
  · 
    intro x h
    have h := Any_In.of.In_Cup h
    have := Any_UnaryFnNeg.of.Any h
    apply In_Cup.of.Any_In
    simp_all


-- created on 2025-08-04
