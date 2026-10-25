import Mathlib

set_option autoImplicit false

universe u v

namespace LinearMap

variable {B : Type u} [CommRing B] {M : Type v} {N : Type v}
  [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] {r : ℕ}

def extPushoutRel (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) : Submodule B (N × (Fin r → B)) :=
  range (LinearMap.prod δ (-(ker p).subtype))

theorem mem_extPushoutRel_iff (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) (x : N × (Fin r → B)) :
    x ∈ extPushoutRel p δ ↔ ∃ s : ↥(ker p), δ s = x.1 ∧ -(s : Fin r → B) = x.2 := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, (Prod.ext_iff.mp hs).1, (Prod.ext_iff.mp hs).2⟩
  · rintro ⟨s, h1, h2⟩
    exact ⟨s, Prod.ext h1 h2⟩

abbrev ExtPushout (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) : Type (max v u) :=
  (N × (Fin r → B)) ⧸ extPushoutRel p δ

namespace ExtPushout

variable (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N)

def mk : N × (Fin r → B) →ₗ[B] ExtPushout p δ := (extPushoutRel p δ).mkQ

theorem mk_apply (x : N × (Fin r → B)) : mk p δ x = Submodule.Quotient.mk x := rfl

theorem mk_surjective : Function.Surjective (mk p δ) := Submodule.Quotient.mk_surjective _

theorem mk_eq_zero_iff (x : N × (Fin r → B)) :
    mk p δ x = 0 ↔ ∃ s : ↥(ker p), δ s = x.1 ∧ -(s : Fin r → B) = x.2 := by
  rw [mk_apply, Submodule.Quotient.mk_eq_zero (p := extPushoutRel p δ), mem_extPushoutRel_iff]

def inl : N →ₗ[B] ExtPushout p δ := mk p δ ∘ₗ LinearMap.inl B N (Fin r → B)

def inr : (Fin r → B) →ₗ[B] ExtPushout p δ := mk p δ ∘ₗ LinearMap.inr B N (Fin r → B)

theorem inl_apply (n : N) : inl p δ n = mk p δ (n, 0) := rfl

theorem inr_apply (v : Fin r → B) : inr p δ v = mk p δ (0, v) := rfl

theorem mk_eq_inl_add_inr (n : N) (v : Fin r → B) : mk p δ (n, v) = inl p δ n + inr p δ v := by
  rw [inl_apply, inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

theorem inr_coe (s : ↥(ker p)) : inr p δ (s : Fin r → B) = inl p δ (δ s) := by
  rw [inr_apply, inl_apply, ← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  exact ⟨-s, by simp, by simp⟩

def proj : ExtPushout p δ →ₗ[B] M :=
  (extPushoutRel p δ).liftQ (p ∘ₗ LinearMap.snd B N (Fin r → B)) (by
    rintro x ⟨s, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    show p (-(s : Fin r → B)) = 0
    rw [map_neg, LinearMap.mem_ker.mp s.2, neg_zero])

theorem proj_mk (n : N) (v : Fin r → B) : proj p δ (mk p δ (n, v)) = p v := rfl

theorem proj_inl (n : N) : proj p δ (inl p δ n) = 0 := by
  rw [inl_apply, proj_mk, map_zero]

theorem proj_inr (v : Fin r → B) : proj p δ (inr p δ v) = p v := rfl

theorem proj_comp_inl : proj p δ ∘ₗ inl p δ = 0 := LinearMap.ext (proj_inl p δ)

theorem proj_comp_inr : proj p δ ∘ₗ inr p δ = p := LinearMap.ext (proj_inr p δ)

theorem inl_injective : Function.Injective (inl p δ) := by
  intro n n' h
  have h0 : inl p δ (n - n') = 0 := by rw [map_sub, h, sub_self]
  rw [inl_apply, mk_eq_zero_iff] at h0
  obtain ⟨s, h1, h2⟩ := h0
  have hs : s = 0 := by
    apply Subtype.ext
    have : -(s : Fin r → B) = 0 := h2
    simpa using this
  have h1' : δ s = n - n' := h1
  have h3 : n - n' = 0 := by rw [← h1', hs, map_zero]
  exact sub_eq_zero.mp h3

theorem proj_surjective (hp : Function.Surjective p) : Function.Surjective (proj p δ) := by
  intro m
  obtain ⟨v, rfl⟩ := hp m
  exact ⟨inr p δ v, proj_inr p δ v⟩

theorem range_inl_eq_ker_proj : range (inl p δ) = ker (proj p δ) := by
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    exact proj_inl p δ n
  · intro x hx
    obtain ⟨⟨n, v⟩, rfl⟩ := mk_surjective p δ x
    rw [LinearMap.mem_ker, proj_mk] at hx
    refine ⟨n + δ ⟨v, hx⟩, ?_⟩
    rw [map_add, ← inr_coe, mk_eq_inl_add_inr]

section lift

variable {Q : Type*} [AddCommGroup Q] [Module B Q]

def lift (f : N →ₗ[B] Q) (g : (Fin r → B) →ₗ[B] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) : ExtPushout p δ →ₗ[B] Q :=
  (extPushoutRel p δ).liftQ (f.coprod g) (by
    rintro x ⟨s, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.coprod_apply]
    show f (δ s) + g (-(s : Fin r → B)) = 0
    rw [map_neg, h, add_neg_cancel])

theorem lift_mk (f : N →ₗ[B] Q) (g : (Fin r → B) →ₗ[B] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (n : N) (v : Fin r → B) :
    lift p δ f g h (mk p δ (n, v)) = f n + g v := rfl

theorem lift_inl (f : N →ₗ[B] Q) (g : (Fin r → B) →ₗ[B] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (n : N) :
    lift p δ f g h (inl p δ n) = f n := by
  rw [inl_apply, lift_mk, map_zero, add_zero]

theorem lift_inr (f : N →ₗ[B] Q) (g : (Fin r → B) →ₗ[B] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (v : Fin r → B) :
    lift p δ f g h (inr p δ v) = g v := by
  rw [inr_apply, lift_mk, map_zero, zero_add]

theorem hom_ext {φ ψ : ExtPushout p δ →ₗ[B] Q} (h₁ : ∀ n : N, φ (inl p δ n) = ψ (inl p δ n))
    (h₂ : ∀ v : Fin r → B, φ (inr p δ v) = ψ (inr p δ v)) : φ = ψ := by
  apply LinearMap.ext
  intro x
  obtain ⟨⟨n, v⟩, rfl⟩ := mk_surjective p δ x
  rw [mk_eq_inl_add_inr, map_add, map_add, h₁, h₂]

end lift

end ExtPushout

end LinearMap
