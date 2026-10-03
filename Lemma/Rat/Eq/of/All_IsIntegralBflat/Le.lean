import Mathlib
import sympy.Basic


/--
[Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed.lean)
-/
@[main]
private lemma main
  [Field F]
  {Bflat B : Subring F} [IsFractionRing ↥Bflat F] [IsIntegrallyClosed ↥Bflat]
-- given
  (hle : Bflat ≤ B)
  (hint : ∀ b ∈ B, IsIntegral ↥Bflat b) :
-- imply
  B = Bflat := by
-- proof
  refine le_antisymm (fun b hb => ?_) hle
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥Bflat) (K := F)).mp (hint b hb)
  rw [← hy]
  exact y.2


-- created on 2026-10-03
