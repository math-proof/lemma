import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Subset_Range.of.In_Conditionset
open Finset Stirling.conditionset


@[path]
private lemma main
-- given
  (n k : ℕ) :
-- imply
  (parts n k).Finite := by
-- proof
  refine (Finset.finite_toSet ((Finset.range n).powerset.powerset)).subset ?_
  rintro e ⟨x, hx, rfl⟩
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro b hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_powerset.mpr (Subset_Range.of.In_Conditionset hx i)


-- created on 2026-10-07
