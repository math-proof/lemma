import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Subset_Range.of.In_Conditionset
open Finset Stirling.conditionset


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k).ncard =
    ((fun e : Finset (Finset ℕ) => insert ({n} : Finset ℕ) e) '' ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k)).ncard := by
-- proof
  symm
  apply Set.InjOn.ncard_image
  have hn : ∀ e ∈ (fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k, ({n} : Finset ℕ) ∉ e := by
    rintro e ⟨x, hx, rfl⟩ hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    have := Subset_Range.of.In_Conditionset hx i (hi ▸ Finset.mem_singleton_self n)
    simp at this
  intro e1 h1 e2 h2 heq
  have := congrArg (fun s => Finset.erase s ({n} : Finset ℕ)) heq
  simpa [Finset.erase_insert (hn e1 h1), Finset.erase_insert (hn e2 h2)] using this


-- created on 2026-10-07
