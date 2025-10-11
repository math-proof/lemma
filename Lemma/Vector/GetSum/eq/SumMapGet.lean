import sympy.vector.vector
import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
import Lemma.Vector.EqGet0'0
open Vector Finset


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (x : List.Vector (List.Vector α n) m)
  (i : Fin n) :
-- imply
  x.sum[i.val] = (x.map (·[i])).sum := by
-- proof
  simp [Sum.eq.Sum_Get]
  let f := fun v : List.Vector α n => v[i]
  have h_f0 : f 0 = 0 := by
    apply EqGet0'0
  have h_add : ∀ (a b : List.Vector α n), f (a + b) = f a + f b := by
    intro a b
    simp [f]
    apply GetAdd.eq.AddGetS
  have := UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 (f := f) h_f0 h_add (Finset.univ : Finset (Fin m)) (fun j => x[j])
  simp [f] at this
  assumption


@[main]
private lemma fin
  [AddCommMonoid α]
-- given
  (x : List.Vector (List.Vector α n) m)
  (i : Fin n) :
-- imply
  x.sum.get i = (x.map (·.get i)).sum := by
-- proof
  apply main


-- created on 2025-10-11
