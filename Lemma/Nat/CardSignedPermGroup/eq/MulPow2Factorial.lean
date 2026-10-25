import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
open SignedPerm


namespace Definitions
end Definitions
namespace SignedPerm

/--
[signedPermGroup_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean)
-/
@[path]
private lemma signedPermGroup_card
  {n : ℕ} :
-- imply
  Nat.card (SignedPermGroup n) = 2 ^ n * n.factorial := by
-- proof
  rw [Nat.card_congr (signedPermGroupEquivProd n), Nat.card_prod]
  congr 1
  · rw [Nat.card_pi]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  · rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

end SignedPerm

namespace SignedPerm

/--
[signGroupPermAction_signChangeAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean)
-/
@[path]
private lemma signGroupPermAction_signChangeAt
  {n : ℕ}
  {σ : Equiv.Perm (Fin n)}
  {j : Fin n} :
-- imply
  (signGroupPermAction n σ) (signChangeAt n j) = signChangeAt n (σ j) := by
-- proof
  ext i
  simp [signGroupPermAction, signChangeAt, Pi.mulSingle_apply, Equiv.symm_apply_eq]

end SignedPerm

namespace SignedPerm

/--
[inr_conj_inl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean)
-/
@[path]
private lemma inr_conj_inl
  {n : ℕ}
  {σ : Equiv.Perm (Fin n)}
  {ε : SignGroup n} :
-- imply
  (SemidirectProduct.inr (φ := signGroupPermAction n) σ) * (SemidirectProduct.inl ε) * (SemidirectProduct.inr (φ := signGroupPermAction n) σ)⁻¹ = SemidirectProduct.inl ((signGroupPermAction n σ) ε) := by
-- proof
  apply SemidirectProduct.ext
  · simp [mul_one, map_inv]
  · simp [mul_inv_cancel]

end SignedPerm

namespace SignedPerm

/--
[ZMod2_eq_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean)
-/
@[path]
private lemma ZMod2_eq_zero_or_one
  {x : ZMod 2} :
-- imply
  x = 0 ∨ x = 1 := by
-- proof
  fin_cases x <;> [left; right] <;> rfl

end SignedPerm

namespace SignedPerm

/--
[Multiplicative_ZMod2_cases](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean)
-/
@[path]
private lemma Multiplicative_ZMod2_cases
  {x : Multiplicative (ZMod 2)} :
-- imply
  x = 1 ∨ x = Multiplicative.ofAdd 1 := by
-- proof
  obtain h | h := ZMod2_eq_zero_or_one (Multiplicative.toAdd x)
  · left; exact Multiplicative.toAdd.injective (by simpa using h)
  · right; exact Multiplicative.toAdd.injective (by simpa using h)

end SignedPerm

namespace SignedPerm

/--
[signGroup_closure_signChangeAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean)
-/
@[path]
private lemma signGroup_closure_signChangeAt
  {n : ℕ} :
-- imply
  Subgroup.closure (Set.range (signChangeAt n)) = ⊤ := by
-- proof
  rw [eq_top_iff]; intro ε _
  rw [← Finset.univ_prod_mulSingle ε]
  apply Subgroup.prod_mem; intro j _
  obtain h | h := Multiplicative_ZMod2_cases (ε j)
  · rw [h, Pi.mulSingle_one]; exact Subgroup.one_mem _
  · rw [h]; exact Subgroup.subset_closure ⟨j, rfl⟩

end SignedPerm

namespace SignedPerm

/--
[inl_mem_of_signChangeAt_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean)
-/
@[path]
private lemma inl_mem_of_signChangeAt_mem
  {n : ℕ}
  {ε : SignGroup n}
  {S : Subgroup (SignedPermGroup n)}
-- given
  (h : ∀ j, (SemidirectProduct.inl (signChangeAt n j) : SignedPermGroup n) ∈ S) :
-- imply
  (SemidirectProduct.inl ε : SignedPermGroup n) ∈ S := by
-- proof
  have htop : S.comap (SemidirectProduct.inl (φ := signGroupPermAction n)) = ⊤ := by
    rw [eq_top_iff, ← signGroup_closure_signChangeAt n]
    exact (Subgroup.closure_le _).mpr (fun ε' ⟨j, hj⟩ => hj ▸ h j)
  have : ε ∈ S.comap (SemidirectProduct.inl (φ := signGroupPermAction n)) := by
    rw [htop]; exact Subgroup.mem_top ε
  exact this

end SignedPerm

namespace SignedPerm

/--
[inr_mem_of_adj_swaps_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean)
-/
@[path]
private lemma inr_mem_of_adj_swaps_mem
  {n : ℕ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {S : Subgroup (SignedPermGroup (n + 1))}
-- given
  (hS : ∀ i : Fin n, SemidirectProduct.inr (Equiv.swap (Fin.castSucc i) (Fin.succ i)) ∈ S) :
-- imply
  SemidirectProduct.inr σ ∈ S := by
-- proof
  have htop : S.comap (SemidirectProduct.inr (φ := signGroupPermAction (n + 1))) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_eq_top_of_mclosure_eq_top
      (Equiv.Perm.mclosure_swap_castSucc_succ n)]
    exact (Subgroup.closure_le _).mpr (fun σ' ⟨i, hi⟩ => hi ▸ hS i)
  have : σ ∈ S.comap (SemidirectProduct.inr (φ := signGroupPermAction (n + 1))) := by
    rw [htop]; exact Subgroup.mem_top σ
  exact this

end SignedPerm


-- created on 2026-10-24
