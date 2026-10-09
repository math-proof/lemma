import Mathlib
import sympy.Basic

open Subgroup Subgroup.leftTransversals

/--
[CohCarrier_transfer_restrict_eq_pow_index](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CohCarrier_transfer_restrict_eq_pow_index.lean)
-/
@[path]
private lemma main
  [Group G] [CommGroup C]
  {K : Subgroup G} [K.FiniteIndex]
  {φ : G →* C} :
-- imply
  MonoidHom.transfer (φ.domRestrict K) = φ ^ K.index := by
-- proof
  classical
  ext g
  let := K.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_def (φ.domRestrict K) default]
  show diff (φ.domRestrict K) default (g • default) = (φ g) ^ K.index
  unfold Subgroup.leftTransversals.diff
  simp only [MonoidHom.domRestrict_apply, map_mul, map_inv,
    Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_mul_distrib,
    Finset.prod_const]
  have hreindex : (∏ q : G ⧸ K,
        φ ((default : K.LeftTransversal).2.leftQuotientEquiv (g⁻¹ • q) : G))
      = ∏ q : G ⧸ K, φ ((default : K.LeftTransversal).2.leftQuotientEquiv q : G) := by
    have := Equiv.prod_comp (MulAction.toPerm (g⁻¹ : G) : Equiv.Perm (G ⧸ K))
      (fun q => φ ((default : K.LeftTransversal).2.leftQuotientEquiv q : G))
    simpa only [MulAction.toPerm_apply] using this
  rw [hreindex, mul_comm ((φ g) ^ _) _, ← mul_assoc, inv_mul_cancel, one_mul,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ]


-- created on 2026-10-05
