import Lemma.Finset.Any_In.is.Ne_Empty
open Finset


@[main]
private lemma main
  {s : Finset ι}
  {p : ι → Prop}

-- given
  (h_s : s ≠ ∅)
  (h : ∀ i ∈ s, p i) :
-- imply
  ∃ i ∈ s, p i := by
-- proof
  let ⟨i, hi⟩ := Any_In.of.Ne_Empty h_s
  use i
  exact ⟨hi, h i hi⟩


-- created on 2025-10-08
