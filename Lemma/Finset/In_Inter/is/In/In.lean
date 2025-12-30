import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [DecidableEq ι]
-- given
  (e : ι)
  (A B : Finset ι) :
-- imply
  e ∈ A ∩ B ↔ e ∈ A ∧ e ∈ B :=
-- proof
  Finset.mem_inter


-- created on 2025-12-30
