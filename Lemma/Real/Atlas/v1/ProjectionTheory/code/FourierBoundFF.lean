import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.FourierBoundFF
open FourierBound in


namespace FourierBound

/--
[piSlope_pair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean)
-/
@[path]
lemma piSlope_pair_injective
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {θ₁ θ₂ : F}
-- given
  (hne : θ₁ ≠ θ₂) :
-- imply
  Function.Injective (fun p : F × F => (piSlope θ₁ p, piSlope θ₂ p)) := by
-- proof
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  simp only [piSlope, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hy : (θ₁ - θ₂) * (y₁ - y₂) = 0 := by linear_combination h1 - h2
  have heqy : y₁ = y₂ := by
    obtain h | h := mul_eq_zero.mp hy
    · exact absurd h (sub_ne_zero.mpr hne)
    · exact sub_eq_zero.mp h
  exact Prod.ext (by linear_combination h1 - θ₁ * heqy) heqy

end FourierBound

namespace FourierBound

/--
[piSlope_pair_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean)
-/
@[path]
lemma piSlope_pair_bijective
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {θ₁ θ₂ : F}
-- given
  (hne : θ₁ ≠ θ₂) :
-- imply
  Function.Bijective (fun p : F × F => (piSlope θ₁ p, piSlope θ₂ p)) :=
-- proof
  (Fintype.bijective_iff_injective_and_card _).mpr ⟨piSlope_pair_injective hne, rfl⟩

end FourierBound

namespace FourierBound

/--
[joint_preimage_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean)
-/
@[path]
lemma joint_preimage_card
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {θ₁ θ₂ : F}
  {A₁ A₂ : Finset F}
-- given
  (hne : θ₁ ≠ θ₂) :
-- imply
  (Finset.univ.filter (fun p : F × F => piSlope θ₁ p ∈ A₁ ∧ piSlope θ₂ p ∈ A₂)).card = A₁.card * A₂.card := by
-- proof
  set g := fun p : F × F => (piSlope θ₁ p, piSlope θ₂ p)
  have hinj : Function.Injective g := piSlope_pair_injective hne
  have hsurj : Function.Surjective g := (piSlope_pair_bijective hne).surjective
  conv_lhs =>
    rw [show (Finset.univ.filter (fun p => piSlope θ₁ p ∈ A₁ ∧ piSlope θ₂ p ∈ A₂)) =
      (A₁ ×ˢ A₂).preimage g (hinj.injOn) from by
        ext p; simp [Finset.mem_preimage, Finset.mem_product, g]]
  rw [Finset.card_preimage]
  · convert Finset.card_product A₁ A₂
    ext ⟨b₁, b₂⟩
    simp only [Finset.mem_filter, Finset.mem_product, Set.mem_range]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hsurj _⟩⟩

end FourierBound

namespace FourierBound

/--
[piSlope_fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean)
-/
@[path]
lemma piSlope_fiber_card
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {θ : F}
  {b : F} :
-- imply
  (Finset.univ.filter (fun p : F × F => piSlope θ p = b)).card = Fintype.card F := by
-- proof
  have hinj : Function.Injective (fun y : F => (b - θ * y, y)) := by
    intro a c h; exact (Prod.mk.inj h).2
  have heq : (Finset.univ.filter (fun p : F × F => piSlope θ p = b)) =
    (Finset.univ.image (fun y : F => (b - θ * y, y))) := by
    ext ⟨x, y⟩
    constructor
    · intro h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, piSlope] at h
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
      refine ⟨y, ?_, rfl⟩
      have : b - θ * y = x + θ * y - θ * y := by rw [h]
      rw [this]; ring
    · intro h
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at h
      obtain ⟨y', hx, hy'⟩ := h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, piSlope]
      rw [← hx, ← hy']; ring
  rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_univ]

end FourierBound

namespace FourierBound

/--
[fourier_numerical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean)
-/
@[path]
lemma fourier_numerical
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {Xc Dc S q : ℕ}
-- given
  (hS_le : 2 * S ≤ q)
  (hq_pos : 0 < q)
  (hDc_pos : 0 < Dc)
  (hvar : Xc * Dc * Dc * (q - S) * (q - S) ≤ S * Dc * q * q * q) :
-- imply
  Dc * Xc ≤ 4 * S * q := by
-- proof
  have hqS : q ≤ 2 * (q - S) := by omega
  have hq2 : q * q ≤ 4 * (q - S) * (q - S) := by nlinarith [Nat.mul_le_mul hqS hqS]
  have h1 : Xc * Dc * (q - S) * (q - S) ≤ S * q * q * q :=
    Nat.le_of_mul_le_mul_left (by nlinarith) hDc_pos
  have h2 : Dc * Xc * (q * q) ≤ 4 * S * q * (q * q) :=
    calc Dc * Xc * (q * q)
      _ ≤ Dc * Xc * (4 * (q - S) * (q - S)) := Nat.mul_le_mul_left _ hq2
      _ = 4 * (Xc * Dc * (q - S) * (q - S)) := by ring
      _ ≤ 4 * (S * q * q * q) := Nat.mul_le_mul_left 4 h1
      _ = 4 * S * q * (q * q) := by ring
  exact Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hq_pos hq_pos)

end FourierBound

/--
[FourierBound.preimage_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean)
-/
@[path]
lemma FourierBound.preimage_card_eq
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {θ : F}
  {A : Finset F} :
-- imply
  (Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x ∈ A)).card = Fintype.card F * A.card := by
-- proof
  have hdisj : ∀ b₁ ∈ A, ∀ b₂ ∈ A, b₁ ≠ b₂ →
    Disjoint (Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x = b₁))
      (Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x = b₂)) :=
    fun _ _ _ _ hne => Finset.disjoint_filter.mpr (fun _ _ h1 h2 => hne (h1 ▸ h2))
  have hsplit : Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x ∈ A) =
    A.biUnion (fun b => Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x = b)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    exact ⟨fun h => ⟨FourierBound.piSlope θ x, h, rfl⟩, fun ⟨b, hb, hxb⟩ => hxb ▸ hb⟩
  rw [hsplit, Finset.card_biUnion hdisj]
  simp only [FourierBound.piSlope_fiber_card, Finset.sum_const]; ring

/--
[FourierBound.variance_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean)
-/
@[path]
lemma FourierBound.variance_bound
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {X : Finset (F × F)}
  {D : Finset F}
  {M : ℕ}
-- given
  (hX : X.Nonempty)
  (hM_def : M = ∑ θ ∈ D, (X.image (piSlope θ)).card)
  (hM_le_qD : M ≤ Fintype.card F * D.card) :
-- imply
  X.card * (Fintype.card F * D.card - M) * (Fintype.card F * D.card - M) ≤ Fintype.card F * Fintype.card F * Fintype.card F * M := by
-- proof
  set q := Fintype.card F
  set f : F × F → ℕ := fun x => (D.filter (fun θ => piSlope θ x ∈ X.image (piSlope θ))).card
  set c : F → ℕ := fun θ => (X.image (piSlope θ)).card
  have hMc : M = ∑ θ ∈ D, c θ := hM_def
  have hfX : ∀ x ∈ X, f x = D.card := by
    intro x hx; simp only [f]; congr 1; ext θ; simp only [Finset.mem_filter]
    exact ⟨And.left, fun h => ⟨h, Finset.mem_image_of_mem _ hx⟩⟩
  have hSf : ∑ x : F × F, f x = q * M := by
    simp only [f, Finset.card_filter]; rw [Finset.sum_comm, hMc, Finset.mul_sum]
    congr 1; ext θ
    rw [show ∑ x : F × F, (if piSlope θ x ∈ X.image (piSlope θ) then (1:ℕ) else 0) =
      (Finset.univ.filter (fun x : F × F => piSlope θ x ∈ X.image (piSlope θ))).card from
        (Finset.card_filter _ _).symm]
    exact FourierBound.preimage_card_eq θ (X.image (piSlope θ))
  have hSf2 : ∑ x : F × F, f x ^ 2 ≤ q * M + M * M := by
    have step : ∑ x : F × F, (f x) ^ 2 =
      ∑ θ₁ ∈ D, ∑ θ₂ ∈ D, (Finset.univ.filter (fun x : F × F =>
        piSlope θ₁ x ∈ X.image (piSlope θ₁) ∧ piSlope θ₂ x ∈ X.image (piSlope θ₂))).card := by
      simp_rw [f, Finset.card_filter, sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]; congr 1; ext θ₁; rw [Finset.sum_comm]; congr 1; ext θ₂
      have h : ∀ x : F × F, (if piSlope θ₁ x ∈ X.image (piSlope θ₁) then (1:ℕ) else 0) *
        (if piSlope θ₂ x ∈ X.image (piSlope θ₂) then 1 else 0) =
        if (piSlope θ₁ x ∈ X.image (piSlope θ₁) ∧ piSlope θ₂ x ∈ X.image (piSlope θ₂)) then 1 else 0 := by
        intro x; split_ifs <;> simp_all
      simp_rw [h]
    rw [step]
    calc ∑ θ₁ ∈ D, ∑ θ₂ ∈ D, _
      _ ≤ ∑ θ₁ ∈ D, ∑ θ₂ ∈ D, (if θ₁ = θ₂ then q * c θ₁ else c θ₁ * c θ₂) := by
        apply Finset.sum_le_sum; intro θ₁ _; apply Finset.sum_le_sum; intro θ₂ _
        split_ifs with heq
        · subst heq
          have hsimp : (Finset.univ.filter (fun x : F × F =>
            piSlope θ₁ x ∈ X.image (piSlope θ₁) ∧ piSlope θ₁ x ∈ X.image (piSlope θ₁))) =
            Finset.univ.filter (fun x : F × F => piSlope θ₁ x ∈ X.image (piSlope θ₁)) := by
            ext x; simp
          rw [hsimp, FourierBound.preimage_card_eq]
        · exact le_of_eq (joint_preimage_card heq _ _)
      _ ≤ q * (∑ θ ∈ D, c θ) + (∑ θ ∈ D, c θ) * (∑ θ ∈ D, c θ) := by
        suffices h : ∀ θ₁ ∈ D, (∑ θ₂ ∈ D, if θ₁ = θ₂ then q * c θ₁ else c θ₁ * c θ₂) ≤
          q * c θ₁ + c θ₁ * (∑ θ ∈ D, c θ) by
          calc _ ≤ ∑ θ₁ ∈ D, (q * c θ₁ + c θ₁ * (∑ θ ∈ D, c θ)) := Finset.sum_le_sum h
            _ = q * (∑ θ ∈ D, c θ) + (∑ θ ∈ D, c θ) * (∑ θ ∈ D, c θ) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        intro θ₁ hθ₁
        rw [← Finset.add_sum_erase D _ hθ₁]; simp only [if_true]
        apply Nat.add_le_add_left
        have h2 : ∀ θ₂ ∈ D.erase θ₁,
          (if θ₁ = θ₂ then q * c θ₁ else c θ₁ * c θ₂) = c θ₁ * c θ₂ :=
          fun θ₂ hθ₂ => if_neg (Finset.ne_of_mem_erase hθ₂).symm
        rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
        exact Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
      _ = q * M + M * M := by rw [← hMc]
  suffices h : (X.card : ℤ) * ((q : ℤ) * D.card - M) * ((q : ℤ) * D.card - M) ≤
    (q : ℤ) * q * q * M by exact_mod_cast h
  have step1 : (X.card : ℤ) * ((q : ℤ) * D.card - M) ^ 2 ≤
    ∑ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 := by
    have heq : ∀ x ∈ X, ((q : ℤ) * (f x : ℤ) - M) ^ 2 = ((q : ℤ) * D.card - M) ^ 2 := by
      intro x hx; rw [show (f x : ℤ) = (D.card : ℤ) from by exact_mod_cast hfX x hx]
    calc (X.card : ℤ) * ((q : ℤ) * D.card - M) ^ 2
      _ = ∑ x ∈ X, ((q : ℤ) * D.card - M) ^ 2 := by simp [Finset.sum_const]
      _ = ∑ x ∈ X, ((q : ℤ) * (f x : ℤ) - M) ^ 2 := (Finset.sum_congr rfl heq).symm
      _ ≤ ∑ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
  have step2 : ∑ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 ≤ (q : ℤ) * q * q * M := by
    have expand : ∑ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 =
      (q : ℤ)^2 * (∑ x : F × F, (f x : ℤ)^2) - 2 * q * M * (∑ x : F × F, (f x : ℤ)) +
      (M : ℤ)^2 * (Fintype.card (F × F)) := by
      have h : ∀ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 =
        (q : ℤ)^2 * (f x : ℤ)^2 - 2 * q * M * (f x : ℤ) + M^2 := by intro x; ring
      simp_rw [h]; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ]; ring
    rw [expand, show (∑ x : F × F, (f x : ℤ)) = (q : ℤ) * M from by exact_mod_cast hSf,
      show (Fintype.card (F × F) : ℤ) = (q : ℤ) * q from by
        exact_mod_cast Fintype.card_prod F F]
    linarith [mul_le_mul_of_nonneg_left
      (show (∑ x : F × F, (f x : ℤ) ^ 2) ≤ (q : ℤ) * M + M * M from by
        have : (∑ x : F × F, (f x : ℤ) ^ 2) = ↑(∑ x : F × F, f x ^ 2) := by push_cast; rfl
        rw [this]; exact_mod_cast hSf2)
      (sq_nonneg (q : ℤ))]
  linarith [step1, step2, sq_abs ((q : ℤ) * ↑D.card - ↑M)]
namespace FourierBound
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

namespace FourierBound

/--
[fourier_bound_finite_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundFF.lean)
-/
@[path]
lemma fourier_bound_finite_field
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {X : Finset (F × F)}
  {D : Finset F}
  {S : ℕ}
-- given
  (hS : ∀ θ ∈ D, (X.image (piSlope θ)).card ≤ S)
  (hS_le : 2 * S ≤ Fintype.card F)
  (hX : X.Nonempty)
  (hD : D.Nonempty) :
-- imply
  D.card * X.card ≤ 4 * S * Fintype.card F := by
-- proof
  set q := Fintype.card F with hq_def
  have hq_pos : 0 < q := Fintype.card_pos
  have hDc_pos : 0 < D.card := hD.card_pos
  set M := ∑ θ ∈ D, (X.image (piSlope θ)).card
  have hM_le : M ≤ S * D.card := by
    calc M = ∑ θ ∈ D, (X.image (piSlope θ)).card := rfl
      _ ≤ ∑ _ ∈ D, S := Finset.sum_le_sum hS
      _ = S * D.card := by simp [Finset.sum_const, mul_comm]
  have hSq : S ≤ q := by omega
  have hM_le_qD : M ≤ q * D.card := by
    calc M ≤ S * D.card := hM_le
      _ ≤ q * D.card := Nat.mul_le_mul_right _ hSq
  apply fourier_numerical X.card D.card S q hS_le hq_pos hDc_pos
  have hqD_ge : D.card * (q - S) ≤ q * D.card - M := by
    have h3 : D.card * (q - S) = q * D.card - S * D.card := by
      rw [show q * D.card - S * D.card = (q - S) * D.card from
        (Nat.sub_mul q S D.card).symm]; ring
    omega
  have hvar := variance_bound X D hX M rfl hM_le_qD
  calc X.card * D.card * D.card * (q - S) * (q - S)
    _ = X.card * (D.card * (q - S)) * (D.card * (q - S)) := by ring
    _ ≤ X.card * (q * D.card - M) * (q * D.card - M) := by
      nlinarith [Nat.mul_le_mul hqD_ge hqD_ge,
        Nat.mul_le_mul_left X.card (Nat.mul_le_mul hqD_ge hqD_ge)]
    _ ≤ q * q * q * M := hvar
    _ ≤ q * q * q * (S * D.card) := Nat.mul_le_mul_left _ hM_le
    _ = S * D.card * q * q * q := by ring

end FourierBound


-- created on 2026-10-23
