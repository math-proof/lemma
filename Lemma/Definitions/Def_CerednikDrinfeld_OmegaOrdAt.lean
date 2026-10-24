import Lemma.Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option autoImplicit false

noncomputable section

open CerednikDrinfeld.Omega

namespace CerednikDrinfeld.Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem coord_mem_holRing : (fun z : ↥(upperHalfPlane K₀ K) => (z : K)) ∈ holRing ϖ := by
  intro n
  have h := isHolOn_ratPair (S := affinoid ϖ n) ⟨Polynomial.X, 1⟩ (fun z _ => by simp)
    ⟨algebraMap K₀ K (ϖ.ϖ⁻¹ ^ n), fun z hz => by
      have := ((mem_affinoid_iff' ϖ n z).1 hz).1
      simpa [RatPair.evalAt, map_pow, map_inv₀] using this⟩
  convert h using 1
  funext z
  simp [restrictAffinoid, RatPair.evalAt]

def coord : ↥(holRing ϖ) := ⟨fun z => (z : K), coord_mem_holRing ϖ⟩

@[simp] theorem coord_apply (z : ↥(upperHalfPlane K₀ K)) : (coord ϖ : ↥(upperHalfPlane K₀ K) → K) z = (z : K) := rfl

def coordSub (z : ↥(upperHalfPlane K₀ K)) : ↥(holRing ϖ) :=
  coord ϖ - algebraMap K ↥(holRing ϖ) (z : K)

@[simp] theorem coordSub_apply (z w : ↥(upperHalfPlane K₀ K)) :
    (coordSub ϖ z : ↥(upperHalfPlane K₀ K) → K) w = (w : K) - (z : K) := rfl

theorem coordSub_apply_self (z : ↥(upperHalfPlane K₀ K)) :
    (coordSub ϖ z : ↥(upperHalfPlane K₀ K) → K) z = 0 := sub_self _

def ordAt (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) : ℕ :=
  sSup {n : ℕ | coordSub ϖ z ^ n ∣ F}

theorem ordAt_def (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) :
    ordAt ϖ F z = sSup {n : ℕ | coordSub ϖ z ^ n ∣ F} := rfl

theorem zero_mem_setOf_pow_dvd (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) :
    (0 : ℕ) ∈ {n : ℕ | coordSub ϖ z ^ n ∣ F} := by
  simp

theorem ordAt_le_of_forall_le (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) (N : ℕ)
    (h : ∀ n : ℕ, coordSub ϖ z ^ n ∣ F → n ≤ N) : ordAt ϖ F z ≤ N :=
  csSup_le ⟨0, zero_mem_setOf_pow_dvd ϖ F z⟩ (fun n hn => h n hn)

theorem le_ordAt_of_pow_dvd (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) {n : ℕ}
    (hn : coordSub ϖ z ^ n ∣ F) (hb : BddAbove {n : ℕ | coordSub ϖ z ^ n ∣ F}) : n ≤ ordAt ϖ F z :=
  le_csSup hb hn

end CerednikDrinfeld.Omega

end
