import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Sum.eq.Sum_Get
open Vector Finset


@[main, fin, val]
private lemma main
  [AddCommMonoid α]
-- given
  (x : List.Vector (List.Vector α n) m)
  (i : Fin n) :
-- imply
  x.sum[i] = (x.map (·[i])).sum := by
-- proof
  simp [Sum.eq.Sum_Get]
  let f := fun v : List.Vector α n => v[i]
  have h_f0 : f 0 = 0 := by
    apply EqGet0_0
  have h_add : ∀ (a b : List.Vector α n), f (a + b) = f a + f b := by
    intro a b
    simp [f]
    apply GetAdd.eq.AddGetS
  have := UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 h_f0 h_add (Finset.univ : Finset (Fin m)) (fun j => x[j])
  simp [f] at this
  assumption


-- created on 2025-10-11
