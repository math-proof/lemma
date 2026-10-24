import Mathlib
import sympy.Basic


/--
Atlas `mem_finsuppAntidiag_iff_degree` (SyzygiesKoszul olean broken; full proof).

[mem_finsuppAntidiag_iff_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  {n d : ℕ}
  {f : Finsupp (Fin n) ℕ} :
-- imply
  f ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag d ↔ Finsupp.degree f = d := by
-- proof
  rw [Finset.mem_finsuppAntidiag]
  simp only [Finset.subset_univ, and_true]
  have key : (Finset.univ : Finset (Fin n)).sum f = Finsupp.degree f := by
    simp [Finsupp.degree]
    exact (Finsupp.sum_fintype f (fun _ => id) (fun _ => rfl)).symm
  rw [key]


-- created on 2026-10-24
