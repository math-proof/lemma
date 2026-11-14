import Mathlib
import Instance.Mathlib_Algebra_IsDirectLimit
import Class.Mathlib_Algebra_IsDirectLimit
import Def.Mathlib_Algebra_IsDirectLimit

section

variable {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
  (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)

variable [DirectedSystem M f] [IsDirectLimit f g]

namespace IsDirectLimit

theorem compatibility' {i j hij} (x : M i) : g j (f i j hij x) = g i x :=
  IsDirectLimit.compatibility i j hij x

theorem is_injective {i j} {mi : M i} {mj : M j} (h : g i mi = g j mj) :
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
  IsDirectLimit.inj i j mi mj h

include f in
theorem is_surjective : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m :=
  IsDirectLimit.surj f

theorem image_preimage (p : P) :
    g (preimage_index f g p) (preimage f g p) = p :=
  (is_surjective f g p).choose_spec.choose_spec

variable {P₁ P₂ : Type*} (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)

@[simp]
theorem lift_of [IsDirectLimit f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
    (lift f g₁ g₂) (g₁ i x) = g₂ i x := by
  dsimp [lift]
  have ⟨k, hpk, hik, h_eq⟩ := is_injective f g₁ (image_preimage f g₁ (g₁ i x))
  rw [← Hg i k hik x, ← Hg (preimage_index f g₁ (g₁ i x)) k hpk, h_eq]

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid P] [Module R P] (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  [DirectedSystem M (f · · ·)] [IsDirectLimit (fun ⦃i j⦄ h => f i j h) g] [IsDirected ι (· ≤ ·)]

variable [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂) [h₁ : IsDirectLimit (f · · ·) (g₁ · ·)]

omit [IsDirected ι (· ≤ ·)] in
theorem compatibility_module {i j hij} (x : M i) : g₁ j (f i j hij x) = g₁ i x :=
  compatibility' (f · · ·) (g₁ · ·) x

@[simp]
theorem lift_of (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
    (Module.lift f g₁ g₂ Hg) (g₁ i x) = g₂ i x := by
  dsimp [lift, IsDirectLimit.lift_of]
  exact IsDirectLimit.lift_of (f · · ·) (g₁ · ·) (g₂ · ·) Hg x

theorem lift_unique (F : P₁ →ₗ[R] P₂) (x) : F x = (Module.lift f g₁ (fun i ↦ F.comp <| g₁ i)
    (fun i j hij x ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply]
      exact LinearMap.congr_arg (IsDirectLimit.compatibility (f := (f · · ·))
      (g := (g₁ · ·)) i j hij x))) x := by
  simp only [lift, IsDirectLimit.lift,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, image_preimage]

end Module

end IsDirectLimit
