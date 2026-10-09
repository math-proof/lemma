import Mathlib
import sympy.Basic


/--
[Module_Basis_repr_apply_mem_of_mem_ideal_smul_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Basis_repr_apply_mem_of_mem_ideal_smul_top.lean)
-/
@[path]
private lemma main
  [CommRing R] [AddCommGroup N] [Module R N]
  {b : Module.Basis κ R N}
  {I : Ideal R}
  {x : N}
  {k : κ}
-- given
  (hx : x ∈ (I • ⊤ : Submodule R N)) :
-- imply
  b.repr x k ∈ I := by
-- proof
  refine Submodule.smul_induction_on hx (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]
    exact I.add_mem hx hy


-- created on 2026-10-03
