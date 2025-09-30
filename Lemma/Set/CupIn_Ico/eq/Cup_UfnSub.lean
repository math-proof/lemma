import sympy.functions.elementary.integers
import sympy.sets.sets
import Lemma.Set.Cup.eq.Cup_Ite
open Set


@[main]
private lemma main
  [IntegerRing ι]
-- given
  (a b c : ι)
  (f : ι → Set β)
  (h : (x : ι) → Decidable (x ∈ Ico a b)) :
-- imply
  ⋃ i ∈ Ico a b, f i = ⋃ i ∈ Ico (c - b + 1) (c - a + 1), f (c - i) := by
-- proof
  have h_iff : ∀ x, x ∈ Ico (c - b + 1) (c - a + 1) ↔ (c - x) ∈ Ico a b := by
    intro x
    sorry
  -- have h : ((x : ι) → Decidable (x ∈ Ico (c - b + 1) (c - a + 1))) := by
  -- sorry
  rw [Cup.eq.Cup_Ite _ (fun i => f (c - i))]
  sorry


-- created on 2025-08-04
-- updated on 2025-09-30
