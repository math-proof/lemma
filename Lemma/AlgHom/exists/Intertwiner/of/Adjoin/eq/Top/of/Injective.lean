import Mathlib
import sympy.Basic


/--
[AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing C₁] [CommRing C₀] [Algebra R C₁] [Algebra R C₀] [AddCommGroup M₁] [AddCommGroup M₀] [Module R M₁] [Module R M₀] [Module C₁ M₁] [Module C₀ M₀] [IsScalarTower R C₁ M₁] [IsScalarTower R C₀ M₀]
  {i : M₀ →ₗ[R] M₁}
  {G : Set C₁}
  {y : C₁ → C₀}
-- given
  (hi : Function.Injective i)
  (hfaith : ∀ y : C₀, (∀ m : M₀, y • m = 0) → y = 0)
  (hG : Algebra.adjoin R G = ⊤)
  (hy : ∀ g ∈ G, ∀ m : M₀, g • i m = i (y g • m)) :
-- imply
  ∃ res : C₁ →ₐ[R] C₀,
      (∀ (t : C₁) (m : M₀), t • i m = i (res t • m)) ∧
      (∀ g ∈ G, res g = y g) ∧
      (∀ res' : C₁ →ₐ[R] C₀, (∀ (t : C₁) (m : M₀), t • i m = i (res' t • m)) → res' = res) := by
-- proof
  classical
    have huniq : ∀ (t : C₁) (y₁ y₂ : C₀), (∀ m, t • i m = i (y₁ • m)) → (∀ m, t • i m = i (y₂ • m)) → y₁ = y₂ := by
      intro t y₁ y₂ h₁ h₂
      apply sub_eq_zero.mp
      apply hfaith _
      intro m
      apply hi
      rw [map_zero, sub_smul, map_sub, ← h₁, ← h₂, sub_self]
    let A : Subalgebra R C₁ :=
      { carrier := {t | ∃ y : C₀, ∀ m, t • i m = i (y • m)}
        mul_mem' := by
          rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
          exact ⟨ya * yb, fun m => by rw [mul_smul, hb, ha, mul_smul]⟩
        one_mem' := ⟨1, fun m => by rw [one_smul, one_smul]⟩
        add_mem' := by
          rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
          exact ⟨ya + yb, fun m => by rw [add_smul, ha, hb, add_smul, map_add]⟩
        zero_mem' := ⟨0, fun m => by rw [zero_smul, zero_smul, map_zero]⟩
        algebraMap_mem' := fun r => ⟨algebraMap R C₀ r, fun m => by
          rw [algebraMap_smul, algebraMap_smul, LinearMap.map_smul]⟩ }
    have hGA : G ⊆ A := fun g hg => ⟨y g, hy g hg⟩
    have hA : ∀ t : C₁, t ∈ A := fun t =>
      Algebra.adjoin_le hGA (hG ▸ Algebra.mem_top)
    have hall : ∀ t : C₁, ∃ y : C₀, ∀ m, t • i m = i (y • m) := fun t => hA t
    choose f hf using hall
    let res : C₁ →ₐ[R] C₀ :=
      { toFun := f
        map_one' := huniq 1 _ _ (hf 1) (fun m => by rw [one_smul, one_smul])
        map_mul' := fun a b => huniq (a * b) _ _ (hf _) (fun m => by rw [mul_smul, hf b, hf a, mul_smul])
        map_zero' := huniq 0 _ _ (hf 0) (fun m => by rw [zero_smul, zero_smul, map_zero])
        map_add' := fun a b => huniq (a + b) _ _ (hf _) (fun m => by rw [add_smul, hf a, hf b, add_smul, map_add])
        commutes' := fun r => huniq _ _ _ (hf _) (fun m => by
          rw [algebraMap_smul, algebraMap_smul, LinearMap.map_smul]) }
    refine ⟨res, fun t m => hf t m, fun g hg => huniq g _ _ (hf g) (hy g hg), fun res' hres' => ?_⟩
    ext t
    exact huniq t _ _ (hres' t) (hf t)


-- created on 2026-10-10
