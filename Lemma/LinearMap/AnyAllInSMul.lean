import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private lemma pi_mem_smul_top
  {B : Type u} [CommRing B]
  (J : Ideal B)
  {N : Type w} [AddCommGroup N] [Module B N]
  {r : ℕ}
  (x : Fin r → N)
  -- given
  (hx : ∀ i, x i ∈ J • (⊤ : Submodule B N)) :
  -- imply
  x ∈ J • (⊤ : Submodule B (Fin r → N)) := by
  -- proof
  classical
  have : x = ∑ i, Pi.single i (x i) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  refine Submodule.sum_mem _ fun i _ => ?_
  suffices hlin : ∀ y : N, y ∈ J • (⊤ : Submodule B N) → (Pi.single i y : Fin r → N) ∈ J • (⊤ : Submodule B (Fin r → N)) by
    apply hlin (x i) (hx i)
  intro y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  ·
    intro a ha z _
    have : (Pi.single i (a • z) : Fin r → N) = a • Pi.single i z := by
      ext j
      if h : j = i then
        subst h
        simp
      else
        simp [h]
    rw [this]
    apply Submodule.smul_mem_smul ha Submodule.mem_top
  ·
    intro z z' hz hz'
    rw [Pi.single_add]
    apply Submodule.add_mem _ hz hz'

/--
[LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul.lean)
-/
@[path]
private lemma main
  {B : Type u} [CommRing B] [IsNoetherianRing B]
  (I : Ideal B)
  {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
  {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
  -- imply
  ∃ c : ℕ, ∀ (n : ℕ) (g : M →ₗ[B] N), LinearMap.range g ≤ I ^ (n + c) • (⊤ : Submodule B N) → g ∈ I ^ n • (⊤ : Submodule B (M →ₗ[B] N)) := by
  -- proof
  classical
  obtain ⟨r, gen, hgen⟩ := Module.Finite.exists_fin (R := B) (M := M)
  let ev : (M →ₗ[B] N) →ₗ[B] (Fin r → N) :=
    { toFun := fun g i => g (gen i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro g h hgh
    refine LinearMap.ext_on_range hgen fun i => ?_
    apply congrFun hgh i
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range ev)
  refine ⟨k, fun n g hg => ?_⟩
  have h1 : ev g ∈ (I ^ (n + k) • (⊤ : Submodule B (Fin r → N))) ⊓ LinearMap.range ev := by
    refine ⟨pi_mem_smul_top (I ^ (n + k)) (fun i => g (gen i)) fun i => hg ⟨gen i, rfl⟩, ⟨g, rfl⟩⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : ev g ∈ I ^ n • LinearMap.range ev :=
    Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  obtain ⟨h, hh, hhg⟩ := h2
  rw [← hev hhg]
  apply hh


-- created on 2026-10-20
