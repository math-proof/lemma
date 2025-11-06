import Lemma.Bool.EqCast.of.SEq
import Lemma.Finset.Any_In.is.Ne_Empty
open Bool Finset


@[main]
private lemma main
  [AddCommMonoid α]
  {s : Finset ι}
  {x : ι → List.Vector α n}
  {y : ι → List.Vector α n'}
-- given
  (h_s : s ≠ ∅)
  (h : ∀ i ∈ s, x i ≃ y i) :
-- imply
  ∀ i ∈ s, cast
    (by
      let ⟨j, hj⟩ := Any_In.of.Ne_Empty h_s
      have hj := h j hj
      have h_n := hj.left
      rw [h_n]
    )
    (x i) = y i := by
-- proof
  intro i hi
  apply EqCast.of.SEq
  exact h i hi


-- created on 2025-11-06
