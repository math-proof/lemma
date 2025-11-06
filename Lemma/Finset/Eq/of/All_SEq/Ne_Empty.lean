import stdlib.SEq
import Lemma.Finset.Any_In.is.Ne_Empty
open Finset


@[main]
private lemma main
  {Vector : α → Sort v}
  {s : Finset ι}
  {x : ι → Vector n}
  {y : ι → Vector n'}
-- given
  (h_s : s ≠ ∅)
  (h : ∀ i ∈ s, x i ≃ y i) :
-- imply
  n = n' := by
-- proof
  let ⟨j, hj⟩ := Any_In.of.Ne_Empty h_s
  have hj := h j hj
  have h_n := hj.left
  rw [h_n]


-- created on 2025-11-06
