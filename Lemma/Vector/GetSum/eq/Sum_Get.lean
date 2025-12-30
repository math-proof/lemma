import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetAdd.eq.AddGetS
import sympy.vector.vector
open Vector Finset


@[main]
private lemma main
  [AddCommMonoid α]
  [DecidableEq ι]
-- given
  (s : Finset ι)
  (x : ι → List.Vector α n)
  (k : Fin n) :
-- imply
  (∑ i ∈ s, x i)[k] = ∑ i ∈ s, (x i)[k] := by
-- proof
  let f := fun v : List.Vector α n => v[k]
  have h_f0 : f 0 = 0 := by
    apply EqGet0_0
  have h_add : ∀ (a b : List.Vector α n), f (a + b) = f a + f b := by
    intro a b
    simp [f]
    apply GetAdd.eq.AddGetS
  have := UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 h_f0 h_add s x
  simp [f] at this
  assumption


@[main]
private lemma fin
  [AddCommMonoid α]
  [DecidableEq ι]
-- given
  (s : Finset ι)
  (x : ι → List.Vector α n)
  (k : Fin n) :
-- imply
  (∑ i ∈ s, x i).get k = ∑ i ∈ s, (x i).get k :=
-- proof
  main s x k


-- created on 2025-11-06
