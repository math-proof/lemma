import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.Lemma_1_30_2


/--
[mem_invariantsSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_30_2.lean)
-/
@[path]
lemma mem_invariantsSubmodule
  {k : Type u}
  [Field k]
  {V : Type v}
  [AddCommGroup V]
  [Module k V]
  {N : Subgroup (LinearMap.GeneralLinearGroup k V)}
  {w : V} :
-- imply
  w ∈ invariantsSubmodule k V N ↔ ∀ g ∈ N, (g.val : V →ₗ[k] V) w = w := by
-- proof
  simp [invariantsSubmodule, Submodule.mem_mk, Set.mem_setOf_eq]

/--
[invariants_G_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_30_2.lean)
-/
@[path]
lemma invariants_G_invariant
  {k : Type u}
  [Field k]
  {V : Type v}
  [AddCommGroup V]
  [Module k V]
  {G N : Subgroup (LinearMap.GeneralLinearGroup k V)}
-- given
  (_hNG : N ≤ G)
  (hNormal : N.Normal) :
-- imply
  IsInvariantSubmodule k V G (invariantsSubmodule k V N) := by
-- proof
  intro g hg w hw
  simp only [invariantsSubmodule, Submodule.mem_mk] at hw ⊢
  intro n hn
  have h_conj : g⁻¹ * n * g ∈ N := hNormal.conj_mem n hn g⁻¹
  have key : (g⁻¹ * n * g).val w = w := hw _ h_conj
  have : (g⁻¹ * n * g).val w = (g⁻¹).val (n.val (g.val w)) := rfl
  rw [this] at key
  have := congr_arg g.val key
  change g.toLinearEquiv ((g.toLinearEquiv).symm (n.val (g.val w))) = g.val w at this
  rwa [g.toLinearEquiv.apply_symm_apply] at this

/--
[invariant_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_30_2.lean)
-/
@[path]
lemma invariant_of_le
  {k : Type u}
  [Field k]
  {V : Type v}
  [AddCommGroup V]
  [Module k V]
  {G N : Subgroup (LinearMap.GeneralLinearGroup k V)}
  {W : Submodule k V}
-- given
  (hNG : N ≤ G)
  (hW : IsInvariantSubmodule k V G W) :
-- imply
  IsInvariantSubmodule k V N W :=
-- proof
  fun g hg w hw => hW g (hNG hg) w hw

/--
[trivial_of_invariants_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_30_2.lean)
-/
@[path]
lemma trivial_of_invariants_eq_top
  {k : Type u}
  [Field k]
  {V : Type v}
  [AddCommGroup V]
  [Module k V]
  {N : Subgroup (LinearMap.GeneralLinearGroup k V)}
-- given
  (h : invariantsSubmodule k V N = ⊤) :
-- imply
  N = ⊥ := by
-- proof
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  ext v
  have : v ∈ invariantsSubmodule k V N := by rw [h]; trivial
  rw [mem_invariantsSubmodule] at this
  have := this g hg
  simp at this
  exact this
/-- Easy direction of Lemma 1.30.2. If `G` acts completely reducibly on `V`, then `G` is
reductive: any unipotent normal subgroup has a `G`-invariant complement to its fixed subspace,
but the complement must be trivial by Kolchin's theorem. -/


-- created on 2026-10-23
