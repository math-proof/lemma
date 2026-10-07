import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Injective.of.In_Conditionset
open Finset Stirling.conditionset


@[main]
private lemma main
  {n k : ℕ}
  {e : Finset (Finset ℕ)}
-- given
  (he : e ∈ parts n k) :
-- imply
  e.card = k := by
-- proof
  obtain ⟨x, hx, rfl⟩ := he
  rw [Finset.card_image_of_injective _ (Injective.of.In_Conditionset hx), Finset.card_univ, Fintype.card_fin]


-- created on 2026-10-07
