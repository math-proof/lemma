import Mathlib
import Instance.Mathlib_Algebra_IsDirectLimit
import Class.Mathlib_Algebra_IsDirectLimit

section

variable {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
  (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)

variable [DirectedSystem M f] [IsDirectLimit f g]

namespace IsDirectLimit

noncomputable def preimage_index (p : P) : ι :=
  have is_surjective : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m :=
    IsDirectLimit.surj (f := f) (g := g)
  (is_surjective p).choose

noncomputable def preimage (p : P) : M (preimage_index f g p) :=
  have is_surjective : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m :=
    IsDirectLimit.surj (f := f) (g := g)
  (is_surjective p).choose_spec.choose

variable {P₁ P₂ : Type*} (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)

noncomputable def lift [IsDirectLimit f g₁] (p : P₁) : P₂ :=
  g₂ (preimage_index f g₁ p) (preimage f g₁ p)

noncomputable def Equiv [h₁ : IsDirectLimit f g₁] [h₂ : IsDirectLimit f g₂] :
    P₁ ≃ P₂ :=
  have lift_of_fwd (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x)
      {i : ι} (x : M i) :
      (lift f g₁ g₂) (g₁ i x) = g₂ i x := by
    dsimp [lift]
    have image_preimage_g₁ (p : P₁) :
        g₁ (preimage_index f g₁ p) (preimage f g₁ p) = p :=
      have is_surjective : ∀ m : P₁, ∃ j, ∃ mj : M j, g₁ j mj = m :=
        IsDirectLimit.surj (f := f) (g := g₁)
      (is_surjective p).choose_spec.choose_spec
    have is_injective_g₁ {i j : ι} {mi : M i} {mj : M j} (h : g₁ i mi = g₁ j mj) :
        ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
      IsDirectLimit.inj (f := f) (g := g₁) i j mi mj h
    have ⟨k, hpk, hik, h_eq⟩ := is_injective_g₁ (image_preimage_g₁ (g₁ i x))
    rw [← Hg i k hik x, ← Hg (preimage_index f g₁ (g₁ i x)) k hpk, h_eq]
  have lift_of_bwd (Hg : ∀ i j hij x, g₁ j (f i j hij x) = g₁ i x)
      {i : ι} (x : M i) :
      (lift f g₂ g₁) (g₂ i x) = g₁ i x := by
    dsimp [lift]
    have image_preimage_g₂ (p : P₂) :
        g₂ (preimage_index f g₂ p) (preimage f g₂ p) = p :=
      have is_surjective : ∀ m : P₂, ∃ j, ∃ mj : M j, g₂ j mj = m :=
        IsDirectLimit.surj (f := f) (g := g₂)
      (is_surjective p).choose_spec.choose_spec
    have is_injective_g₂ {i j : ι} {mi : M i} {mj : M j} (h : g₂ i mi = g₂ j mj) :
        ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
      IsDirectLimit.inj (f := f) (g := g₂) i j mi mj h
    have ⟨k, hpk, hik, h_eq⟩ := is_injective_g₂ (image_preimage_g₂ (g₂ i x))
    rw [← Hg i k hik x, ← Hg (preimage_index f g₂ (g₂ i x)) k hpk, h_eq]
  { toFun := lift f g₁ g₂
    invFun := lift f g₂ g₁
    left_inv := fun x => by
      obtain ⟨i, mi, hmi⟩ := h₁.surj x
      rw [← hmi, lift_of_fwd h₂.compatibility (x := mi),
        lift_of_bwd h₁.compatibility (x := mi)]
    right_inv := fun x => by
      obtain ⟨i, mi, hmi⟩ := h₂.surj x
      rw [← hmi, lift_of_bwd h₁.compatibility (x := mi),
        lift_of_fwd h₂.compatibility (x := mi)] }

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid P] [Module R P] (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  [DirectedSystem M (f · · ·)] [IsDirectLimit (fun ⦃i j⦄ h => f i j h) g] [IsDirected ι (· ≤ ·)]

variable [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂) [h₁ : IsDirectLimit (f · · ·) (g₁ · ·)]

noncomputable def lift
    (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) : P₁ →ₗ[R] P₂ where
  toFun := IsDirectLimit.lift (f · · ·) (g₁ · ·) (g₂ · · )
  map_add' x y := by
    have image_preimage (p : P₁) :
        g₁ (preimage_index (f · · ·) (g₁ · ·) p) (preimage (f · · ·) (g₁ · ·) p) = p :=
      have is_surjective : ∀ m : P₁, ∃ i, ∃ mi : M i, g₁ i mi = m :=
        IsDirectLimit.surj (f := (fun ⦃i j⦄ h => f i j h)) (g := (g₁ · ·))
      (is_surjective p).choose_spec.choose_spec
    have compatibility' {i j hij} (x : M i) : g₁ j (f i j hij x) = g₁ i x :=
      IsDirectLimit.compatibility (f := (f · · ·)) (g := (g₁ · ·)) i j hij x
    have is_injective {i j} {mi : M i} {mj : M j} (h : g₁ i mi = g₁ j mj) :
        ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
      IsDirectLimit.inj (f := (f · · ·)) (g := (g₁ · ·)) i j mi mj h
    obtain ⟨k, hxk, hyk⟩ :=
      IsDirected.directed (r := (· ≤ ·)) (preimage_index (f · · ·) (g₁ · ·) x)
      (preimage_index (f · · ·) (g₁ · ·) y)
    obtain ⟨k', hxyk', hkk'⟩ := IsDirected.directed (r := (· ≤ ·))
      (preimage_index (f · · ·) (g₁ · ·) (x+y)) k
    have sum_eq : g₁ k' (f (preimage_index (f · · ·) (g₁ · ·) x) k' (le_trans hxk hkk')
      (preimage (f · · ·) (g₁ · ·) x) + f (preimage_index (f · · ·) (g₁ · ·) y) k'
      (le_trans hyk hkk') (preimage (f · · ·) (g₁ · ·) y)) =
        g₁ (preimage_index (f · · ·) (g₁ · ·) (x+y)) (preimage (f · · ·) (g₁ · ·) (x+y)) := by
      simp only [LinearMap.map_add, image_preimage]
      repeat rw [compatibility', image_preimage]
    obtain ⟨k'', hk'k'', hxyk'', h'''⟩ := is_injective sum_eq
    simpa [Hg, IsDirectLimit.lift] using congr_arg (g₂ k'') h'''.symm
  map_smul' r x := by
    have image_preimage (p : P₁) :
        g₁ (preimage_index (f · · ·) (g₁ · ·) p) (preimage (f · · ·) (g₁ · ·) p) = p :=
      have is_surjective : ∀ m : P₁, ∃ i, ∃ mi : M i, g₁ i mi = m :=
        IsDirectLimit.surj (f := (fun ⦃i j⦄ h => f i j h)) (g := (g₁ · ·))
      (is_surjective p).choose_spec.choose_spec
    have is_injective {i j} {mi : M i} {mj : M j} (h : g₁ i mi = g₁ j mj) :
        ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
      IsDirectLimit.inj (f := (f · · ·)) (g := (g₁ · ·)) i j mi mj h
    have smul_eq : g₁ (preimage_index (f · · ·) (g₁ · ·) (r • x)) (preimage (f · · ·) (g₁ · ·)
      (r • x)) = g₁ (preimage_index (f · · ·) (g₁ · ·) x) (r • preimage (f · · ·) (g₁ · ·) x) := by
      simp only [image_preimage, map_smul]
    obtain ⟨k, hixk, hirxk, h_smul⟩ := is_injective smul_eq
    simpa [Hg, IsDirectLimit.lift] using congr_arg (g₂ k) h_smul

variable [h₂ : IsDirectLimit (f · · ·) (g₂ · ·)]

noncomputable def linearEquiv : P₁ ≃ₗ[R] P₂ :=
  { IsDirectLimit.Equiv (f · · ·) (g₁ · ·) (g₂ · ·) with
    map_add' := (lift f g₁ g₂ h₂.compatibility).map_add'
    map_smul' := (lift f g₁ g₂ h₂.compatibility).map_smul'}

end Module

end IsDirectLimit