import Mathlib.Data.Finset.Basic
import sympy.Basic
open Finset


@[main]
private lemma main
  {α β : Type*}
  [CommSemiring β]
  {s : Finset α}
  {f : α → β}
  {c : β} :
-- imply
  ∏ i ∈ s, (c * f i) = c ^ s.card * ∏ i ∈ s, f i := by
-- proof
  rw [prod_mul_distrib, prod_const]


-- created on 2023-06-03
