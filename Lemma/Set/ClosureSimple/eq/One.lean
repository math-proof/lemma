import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.SphericalCase
open SphericalBNPair


/--
[closure_simple_eq_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma closure_simple_eq_pair
  [Group W]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M W}
  {s : B_idx} :
-- imply
  (Subgroup.closure ({cs.simple s} : Set W) : Set W) = {1, cs.simple s} := by
-- proof
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · intro hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => simp at hx; right; exact hx
    | one => left; rfl
    | mul x y _ _ ihx ihy =>
      obtain rfl | rfl <;> rcases ihy with rfl | rfl := ihx
      · left; simp
      · right; simp
      · right; simp
      · left; have := cs.simple_sq s; rw [sq] at this; exact this
    | inv x _ ihx =>
      obtain rfl | rfl := ihx
      · left; simp
      · right
        have hsq : cs.simple s * cs.simple s = 1 := by have := cs.simple_sq s; rwa [sq] at this
        calc (cs.simple s)⁻¹ = 1 * (cs.simple s)⁻¹ := by simp
          _ = (cs.simple s * cs.simple s) * (cs.simple s)⁻¹ := by rw [hsq]
          _ = cs.simple s := by group
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_singleton _)

/--
[longest_isRightDescent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma longest_isRightDescent
  [Group W]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M W}
  {w₀ : W}
  {s : B_idx}
-- given
  (hw₀_longest : ∀ w : W, cs.length w ≤ cs.length w₀) :
-- imply
  cs.IsRightDescent w₀ s := by
-- proof
  unfold CoxeterSystem.IsRightDescent
  obtain h | h := cs.length_mul_simple w₀ s
  · exfalso; have := hw₀_longest (w₀ * cs.simple s); omega
  · omega

/--
[longest_length_mul_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma longest_length_mul_simple
  [Group W]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M W}
  {w₀ : W}
  {s : B_idx}
-- given
  (hw₀_longest : ∀ w : W, cs.length w ≤ cs.length w₀) :
-- imply
  cs.length (w₀ * cs.simple s) = cs.length w₀ - 1 := by
-- proof
  obtain h | h := cs.length_mul_simple w₀ s
  · exfalso; have := hw₀_longest (w₀ * cs.simple s); omega
  · omega

/--
[longest_isLeftDescent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma longest_isLeftDescent
  [Group W]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M W}
  {w₀ : W}
  {s : B_idx}
-- given
  (hw₀_longest : ∀ w : W, cs.length w ≤ cs.length w₀) :
-- imply
  cs.IsLeftDescent w₀ s := by
-- proof
  unfold CoxeterSystem.IsLeftDescent
  obtain h | h := cs.length_simple_mul w₀ s
  · exfalso; have := hw₀_longest (cs.simple s * w₀); omega
  · omega

/--
[longest_length_simple_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma longest_length_simple_mul
  [Group W]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M W}
  {w₀ : W}
  {s : B_idx}
-- given
  (hw₀_longest : ∀ w : W, cs.length w ≤ cs.length w₀) :
-- imply
  cs.length (cs.simple s * w₀) = cs.length w₀ - 1 := by
-- proof
  obtain h | h := cs.length_simple_mul w₀ s
  · exfalso; have := hw₀_longest (cs.simple s * w₀); omega
  · omega

/--
[longest_sq_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma longest_sq_eq_one
  [Group W]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M W}
  {w₀ : W}
-- given
  (hw₀_longest : ∀ w : W, cs.length w ≤ cs.length w₀)
  (hw₀_unique : ∀ w : W, (∀ v : W, cs.length v ≤ cs.length w) → w = w₀) :
-- imply
  w₀ ^ 2 = 1 := by
-- proof
  have hinv : cs.length w₀⁻¹ = cs.length w₀ := cs.length_inv w₀
  have hinv_longest : ∀ w : W, cs.length w ≤ cs.length w₀⁻¹ := by
    intro w; rw [hinv]; exact hw₀_longest w
  have heq : w₀⁻¹ = w₀ := hw₀_unique w₀⁻¹ hinv_longest
  rw [sq]
  calc w₀ * w₀ = w₀⁻¹ * w₀ := by rw [heq]
    _ = 1 := inv_mul_cancel w₀

/--
[conj_simple_from_parabolic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma conj_simple_from_parabolic
  [Group W]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M W}
  {w₀ : W}
-- given
  (h_parabolic : ∀ s : B_idx, ∃ s' : B_idx, Subgroup.closure ({w₀ * cs.simple s * w₀⁻¹} : Set W) = Subgroup.closure ({cs.simple s'} : Set W)) :
-- imply
  ∀ s : B_idx, ∃ s' : B_idx, w₀ * cs.simple s * w₀⁻¹ = cs.simple s' := by
-- proof
  intro s
  obtain ⟨s', hs'⟩ := h_parabolic s
  use s'
  have h_conj_in_closure : w₀ * cs.simple s * w₀⁻¹ ∈
    Subgroup.closure ({cs.simple s'} : Set W) := by
    rw [← hs']
    exact Subgroup.subset_closure (Set.mem_singleton _)
  have h_mem : (w₀ * cs.simple s * w₀⁻¹ : W) ∈ ({1, cs.simple s'} : Set W) := by
    rwa [← closure_simple_eq_pair, SetLike.mem_coe]
  obtain h | h := h_mem
  ·
    exfalso
    have : cs.simple s = 1 := by
      calc cs.simple s = w₀⁻¹ * (w₀ * cs.simple s * w₀⁻¹) * w₀ := by group
        _ = w₀⁻¹ * 1 * w₀ := by rw [h]
        _ = 1 := by group
    have : cs.length (cs.simple s) = 0 := by rw [this, cs.length_one]
    rw [cs.length_simple] at this
    exact absurd this (by omega)
  · exact h

namespace SphericalBNPair

variable [Group G] {M : CoxeterMatrix B_idx}
variable (sbp : SphericalBNPair G M)
/--
[w₀_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma w₀_sq : sbp.w₀ ^ 2 = 1 :=
  longest_sq_eq_one M.toCoxeterSystem sbp.w₀ sbp.w₀_longest sbp.w₀_unique

end SphericalBNPair

namespace SphericalBNPair

variable [Group G] {M : CoxeterMatrix B_idx}
variable (sbp : SphericalBNPair G M)
/--
[w₀_conj_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
$w_0 s w_0^{-1} = s'$. -/
lemma w₀_conj_simple : ∀ s : B_idx, ∃ s' : B_idx,
  sbp.w₀ * M.toCoxeterSystem.simple s * sbp.w₀⁻¹ = M.toCoxeterSystem.simple s' :=
  conj_simple_from_parabolic M.toCoxeterSystem sbp.w₀ sbp.w₀_conj_parabolic

end SphericalBNPair

namespace SphericalBNPair

variable [Group G] {M : CoxeterMatrix B_idx}
variable (sbp : SphericalBNPair G M)
/--
[w₀_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma w₀_mul_self : sbp.w₀ * sbp.w₀ = 1 := by
  have h := sbp.w₀_sq; rwa [sq] at h

end SphericalBNPair

namespace SphericalBNPair

variable [Group G] {M : CoxeterMatrix B_idx}
variable (sbp : SphericalBNPair G M)
/--
[w₀_inv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma w₀_inv_eq : sbp.w₀⁻¹ = sbp.w₀ :=
  mul_right_cancel (a := sbp.w₀⁻¹) (b := sbp.w₀) (c := sbp.w₀)
    (by rw [inv_mul_cancel, ← sq, sbp.w₀_sq])

end SphericalBNPair

namespace SphericalBNPair

variable [Group G] {M : CoxeterMatrix B_idx}
variable (sbp : SphericalBNPair G M)
/--
[chosen_lift_w₀_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma chosen_lift_w₀_spec :
  sbp.toBNPair.π (sbp.toBNPair.π_surj sbp.w₀).choose = sbp.w₀ :=
  (sbp.toBNPair.π_surj sbp.w₀).choose_spec

end SphericalBNPair

namespace SphericalBNPair

/--
[longestElementAutoS](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma longestElementAutoS
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M} :
-- imply
  ∀ s : B_idx, ∃ s' : B_idx, sbp.w₀ * M.toCoxeterSystem.simple s * sbp.w₀⁻¹ = M.toCoxeterSystem.simple s' :=
-- proof
  sbp.w₀_conj_simple

end SphericalBNPair

namespace SphericalBNPair

/--
[longestElementAutoSInvolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma longestElementAutoSInvolution
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M} :
-- imply
  (∀ s : B_idx, ∃ s' : B_idx, sbp.w₀ * M.toCoxeterSystem.simple s * sbp.w₀⁻¹ = M.toCoxeterSystem.simple s') ∧ ∀ (s s' : B_idx), sbp.w₀ * M.toCoxeterSystem.simple s * sbp.w₀⁻¹ = M.toCoxeterSystem.simple s' → sbp.w₀ * M.toCoxeterSystem.simple s' * sbp.w₀⁻¹ = M.toCoxeterSystem.simple s := by
-- proof
  refine ⟨sbp.longestElementAutoS, fun s s' h => ?_⟩
  have hw : sbp.w₀⁻¹ = sbp.w₀ := sbp.w₀_inv_eq
  rw [hw] at h ⊢
  have hsq : sbp.w₀ * sbp.w₀ = 1 := sbp.w₀_mul_self
  calc sbp.w₀ * M.toCoxeterSystem.simple s' * sbp.w₀
    = sbp.w₀ * (sbp.w₀ * M.toCoxeterSystem.simple s * sbp.w₀) * sbp.w₀ := by
      rw [h]
    _ = (sbp.w₀ * sbp.w₀) * M.toCoxeterSystem.simple s * (sbp.w₀ * sbp.w₀) := by
      group
    _ = 1 * M.toCoxeterSystem.simple s * 1 := by rw [hsq]
    _ = M.toCoxeterSystem.simple s := by group

end SphericalBNPair

namespace SphericalBNPair

/--
[leviComponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma leviComponent_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M} :
-- imply
  sbp.leviComponent = (sbp.toBNPair.B : Set G) ∩ ((fun s => ((sbp.toBNPair.π_surj sbp.w₀).choose : G) * s * ((sbp.toBNPair.π_surj sbp.w₀).choose : G)⁻¹) '' (sbp.toBNPair.B : Set G)) := by
-- proof
  rfl

end SphericalBNPair

namespace SphericalBNPair

/--
[leviComponentGeneral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
lemma leviComponentGeneral_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M}
  {T : Set B_idx} :
-- imply
  sbp.leviComponentGeneral T = sbp.toBNPair.standardParabolic T ∩ ((fun s => ((sbp.toBNPair.π_surj sbp.w₀).choose : G) * s * ((sbp.toBNPair.π_surj sbp.w₀).choose : G)⁻¹) '' sbp.toBNPair.standardParabolic T) := by
-- proof
  rfl

end SphericalBNPair

/--
[w](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
private lemma w_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M} :
-- imply
  sbp.w₀ ^ 2 = 1 := by
-- proof
  apply SphericalBNPair.w sbp

/--
[w](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
private lemma w_eq_2
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M} :
-- imply
  ∀ s : B_idx, ∃ s' : B_idx, sbp.w₀ * M.toCoxeterSystem.simple s * sbp.w₀⁻¹ = M.toCoxeterSystem.simple s' := by
-- proof
  apply SphericalBNPair.w sbp

/--
[w](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
private lemma w_eq_3
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M} :
-- imply
  sbp.w₀ * sbp.w₀ = 1 := by
-- proof
  apply SphericalBNPair.w sbp

/--
[w](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
private lemma w_eq_4
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M} :
-- imply
  sbp.w₀⁻¹ = sbp.w₀ := by
-- proof
  apply SphericalBNPair.w sbp

/--
[chosen_lift_w](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/SphericalCase.lean)
-/
@[path]
private lemma chosen_lift_w_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {sbp : SphericalBNPair G M} :
-- imply
  sbp.toBNPair.π (sbp.toBNPair.π_surj sbp.w₀).choose = sbp.w₀ := by
-- proof
  apply SphericalBNPair.chosen_lift_w sbp


-- created on 2026-10-23
