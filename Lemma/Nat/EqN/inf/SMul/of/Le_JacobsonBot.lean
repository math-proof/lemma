import Mathlib
import sympy.Basic

open scoped Pointwise

/--
[Submodule_iInf_sup_pow_smul_top_eq_of_le_jacobson](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_iInf_sup_pow_smul_top_eq_of_le_jacobson.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  {I : Ideal R}
  {N : Submodule R M}
-- given
  (hI : I ≤ Ideal.jacobson ⊥) :
-- imply
  ⨅ n : ℕ, N ⊔ I ^ n • (⊤ : Submodule R M) = N := by
-- proof
  refine le_antisymm ?_ (le_iInf fun n => le_sup_left)
  intro x hx
  rw [Submodule.mem_iInf] at hx

  have hq : N.mkQ x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R (M ⧸ N))) := by
    rw [Submodule.mem_iInf]
    intro n
    have h1 : N.mkQ x ∈ Submodule.map N.mkQ (N ⊔ I ^ n • ⊤) := Submodule.mem_map_of_mem (hx n)
    rwa [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_mkQ] at h1
  rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hI, Submodule.mem_bot] at hq
  exact (Submodule.Quotient.mk_eq_zero N).mp hq


-- created on 2026-10-05
