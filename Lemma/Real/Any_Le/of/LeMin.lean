import sympy.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset


@[path]
private lemma main
  [ConditionallyCompleteLinearOrder α]
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
  obtain ⟨x, hx, hx_eq⟩ := hne'.csInf_mem hfin'
  refine ⟨x, hx, ?_⟩
  rwa [hx_eq]


-- created on 2019-12-01
