import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_CuspForm_IntegralLattice
import Lemma.Definitions.Def_CuspForm_IntegralStructure
import Lemma.Int.P2MUtil


/--
[CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two.lean)
-/
@[path]
private lemma main
  {N : ℕ} :
-- imply
  CuspForm.HasIntegralBasis N ↔ CuspForm.HasIntegralStructure N 2 := by
-- proof
  have hset : CuspForm.qIntegralSet N =
      {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2 | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)} := by
    ext f
    simp only [CuspForm.qIntegralSet, Set.mem_setOf_eq]
    refine forall_congr' fun n => ?_
    rw [Subring.mem_bot]
    exact ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩
  unfold CuspForm.HasIntegralBasis CuspForm.HasIntegralStructure CuspForm.intLattice
  rw [hset, Submodule.span_span_of_tower]


-- created on 2026-10-23
