import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Gamma0HeckeOperatorHom.Main
import Lemma.Int.P2MUtil

open CongruenceSubgroup Subgroup

/--
[HeckeEis_heckeOperatorHom_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HeckeEis_heckeOperatorHom_smul.lean)
-/
@[path]
private lemma main
  [AddCommGroup A] [Monoid R] [DistribMulAction R A]
  {N ℓ : ℕ} [NeZero ℓ]
  {r : R}
  {φ : Additive ↥(Gamma0 N) →+ A} :
-- imply
  HeckeEis.heckeOperatorHom N ℓ A (r • φ) =
      r • HeckeEis.heckeOperatorHom N ℓ A φ := by
-- proof
  ext g
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  show (∑ q : ↥(Gamma0 N) ⧸ HeckeEis.heckeUpper N ℓ, (r • φ) _) =
    r • (∑ q : ↥(Gamma0 N) ⧸ HeckeEis.heckeUpper N ℓ, φ _)
  simp only [AddMonoidHom.smul_apply]
  exact Finset.smul_sum.symm


-- created on 2026-10-23
