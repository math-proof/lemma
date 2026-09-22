import sympy.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset


@[main]
private lemma main
  {ι α : Type*} [ConditionallyCompleteLinearOrder α]
  {s : Set ι} {f : ι → α} {M : α}
-- given
  (hne : s.Nonempty)
  (hfin : s.Finite)
  (hM : ⨅ x : s, f x ≤ M) :
-- imply
  ∃ x ∈ s, f x ≤ M := by
-- proof
  have hfin' : (f '' s).Finite := hfin.image f
  have hne' : (f '' s).Nonempty := hne.image f
  have hb : BddBelow (f '' s) := hfin'.bddBelow
  have heq : (⨅ x : s, f x) = sInf (f '' s) :=
    IsGLB.ciInf_set_eq (isGLB_csInf hne' hb) hne
  rw [heq] at hM
  rcases hne'.csInf_mem hfin' with ⟨x, hx, hx_eq⟩
  refine ⟨x, hx, ?_⟩
  rw [hx_eq]
  exact hM


-- created on 2019-12-01
