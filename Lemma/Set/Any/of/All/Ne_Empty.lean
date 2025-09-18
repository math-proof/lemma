import Lemma.Set.Any_In.is.Ne_Empty
open Set


@[main]
private lemma main
  {S : Set α}
  {p : α → Prop}
-- given
  (h₀ : S ≠ ∅)
  (h₁ : ∀ e ∈ S, p e) :
-- imply
  ∃ e ∈ S, p e := by
-- proof
  let ⟨e, h_e⟩ := Any_In.of.Ne_Empty h₀
  use e
  constructor
  ·
    assumption
  ·
    apply h₁
    assumption


-- created on 2025-07-19
