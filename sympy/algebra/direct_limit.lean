import Mathlib

/-- A cocone `g` exhibits `P` as the direct limit of the transition maps `f`. -/
class IsDirectLimit {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P) [DirectedSystem M f] : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj : ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj →
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj
  compatibility : ∀ i j (hij : i ≤ j) (x : M i), g j (f i j hij x) = g i x

namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

theorem compatibility' {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] {i j : ι} (hij : i ≤ j) (x : M i) :
    g j (f i j hij x) = g i x :=
  IsDirectLimit.compatibility i j hij x

theorem is_injective {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] {i j : ι} {mi : M i} {mj : M j}
    (h : g i mi = g j mj) :
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
  IsDirectLimit.inj i j mi mj h

theorem is_surjective {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] (m : P) :
    ∃ i, ∃ mi : M i, g i mi = m :=
  IsDirectLimit.surj (f := f) (g := g) m

noncomputable def preimage_index {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] (p : P) : ι :=
  (is_surjective f g p).choose

noncomputable def preimage {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] (p : P) : M (preimage_index f g p) :=
  (is_surjective f g p).choose_spec.choose

theorem image_preimage {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] (p : P) :
    g (preimage_index f g p) (preimage f g p) = p :=
  (is_surjective f g p).choose_spec.choose_spec

variable {P₁ P₂ : Type*}

noncomputable def lift
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁] (p : P₁) : P₂ :=
  g₂ (preimage_index f g₁ p) (preimage f g₁ p)

theorem lift_of
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁]
    (Hg : ∀ i j (hij : i ≤ j) (x : M i), g₂ j (f i j hij x) = g₂ i x) {i : ι} (x : M i) :
    lift f g₁ g₂ (g₁ i x) = g₂ i x := by
  dsimp [lift]
  obtain ⟨k, hpk, hik, h_eq⟩ := is_injective f g₁ (image_preimage f g₁ (g₁ i x))
  rw [← Hg i k hik x, ← Hg (preimage_index f g₁ (g₁ i x)) k hpk, h_eq]

noncomputable def Equiv
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁] [IsDirectLimit f g₂] : P₁ ≃ P₂ where
  toFun := lift f g₁ g₂
  invFun := lift f g₂ g₁
  left_inv x := by
    obtain ⟨i, mi, hmi⟩ := IsDirectLimit.surj (f := f) (g := g₁) x
    rw [← hmi]
    have hto : lift f g₁ g₂ (g₁ i mi) = g₂ i mi :=
      lift_of f g₁ g₂ (fun i j hij y => compatibility' f g₂ hij y) mi
    rw [hto]
    apply lift_of f g₂ g₁
    intro i j hij y
    apply compatibility' f g₁ hij y
  right_inv x := by
    obtain ⟨i, mi, hmi⟩ := IsDirectLimit.surj (f := f) (g := g₂) x
    rw [← hmi]
    have hto : lift f g₂ g₁ (g₂ i mi) = g₁ i mi :=
      lift_of f g₂ g₁ (fun i j hij y => compatibility' f g₁ hij y) mi
    rw [hto]
    apply lift_of f g₁ g₂
    intro i j hij y
    apply compatibility' f g₂ hij y

theorem Equiv_apply
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁] [IsDirectLimit f g₂] (i : ι) (x : M i) :
    Equiv f g₁ g₂ (g₁ i x) = g₂ i x := by
  apply lift_of f g₁ g₂
  intro i j hij y
  apply compatibility' f g₂ hij y

theorem Equiv_symm_apply
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁] [IsDirectLimit f g₂] (i : ι) (x : M i) :
    (Equiv f g₁ g₂).symm (g₂ i x) = g₁ i x := by
  apply lift_of f g₂ g₁
  intro i j hij y
  apply compatibility' f g₁ hij y

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {P : Type*} [AddCommMonoid P] [Module R P]
  (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  (g : ∀ i, M i →ₗ[R] P)
  [DirectedSystem M (fun i j h => ⇑(f i j h))]
  [IsDirectLimit (fun i j h => ⇑(f i j h)) (fun i => ⇑(g i))]
  [IsDirected ι (· ≤ ·)]

instance [DecidableEq ι] [Nonempty ι] :
    IsDirectLimit (fun i j h => ⇑(f i j h)) (fun i => ⇑(Module.DirectLimit.of R ι M f i)) where
  surj z := Module.DirectLimit.exists_of (R := R) (ι := ι) (G := M) (f := f) z
  inj := by
    intro i j mi mj h
    apply_fun Module.DirectLimit.linearEquiv (R := R) (ι := ι) (G := M) (f := f) at h
    simp_rw [Module.DirectLimit.linearEquiv_of, Quotient.eq] at h
    exact h
  compatibility := by
    intro i j hij x
    exact Module.DirectLimit.of_f (R := R) (ι := ι) (G := M) (f := f) (hij := hij) (x := x)

end Module

end IsDirectLimit
