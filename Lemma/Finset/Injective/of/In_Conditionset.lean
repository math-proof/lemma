import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Eq.of.In.In.In_Conditionset
open Finset Stirling.conditionset


@[main]
private lemma main
  {n k : ℕ}
  {x : Fin k → Finset ℕ}
-- given
  (hx : x ∈ Stirling.conditionset n k) :
-- imply
  Function.Injective x := by
-- proof
  intro i j h
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (hx.2.2 i)
  exact Eq.of.In.In.In_Conditionset hx ha (h ▸ ha)


-- created on 2026-10-07
