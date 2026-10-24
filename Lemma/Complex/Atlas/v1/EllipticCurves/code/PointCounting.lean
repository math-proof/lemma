import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.PointCounting
open Hasse GroupExponentBound BSGSOrder QuadraticTwist Mestre


/--
[inseparable_add_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma inseparable_add_iff
  [Ring R]
  {IsInsep}
  {ax : InsepAxioms IsInsep}
  {α β : R}
-- given
  (IsInsep : R → Prop)
  (hα : IsInsep α) :
-- imply
  IsInsep (α + β) ↔ IsInsep β := by
-- proof
  constructor
  ·
    intro hαβ
    suffices h : IsInsep (-β) by
      have := ax.neg_insep (-β) h
      rwa [neg_neg] at this
    have h_neg_αβ : IsInsep (-(α + β)) := ax.neg_insep _ hαβ
    obtain ⟨γ₁, hγ₁⟩ := ax.factor _ h_neg_αβ
    obtain ⟨γ₂, hγ₂⟩ := ax.factor _ hα
    have key : -β = (γ₁ + γ₂) * ax.π := by
      have : -(α + β) + α = -β := by abel
      rw [← this, hγ₁, hγ₂, add_mul]
    rw [key]
    exact ax.mul_π_insep _
  ·
    intro hβ
    obtain ⟨γ₁, hγ₁⟩ := ax.factor _ hα
    obtain ⟨γ₂, hγ₂⟩ := ax.factor _ hβ
    have key : α + β = (γ₁ + γ₂) * ax.π := by
      rw [hγ₁, hγ₂, add_mul]
    rw [key]
    exact ax.mul_π_insep _

/--
[separable_add_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma separable_add_iff
  [Ring R]
  {IsInsep}
  {ax : InsepAxioms IsInsep}
  {α β : R}
-- given
  (IsInsep : R → Prop)
  (hα : IsInsep α) :
-- imply
  ¬ IsInsep (α + β) ↔ ¬ IsInsep β :=
-- proof
  (inseparable_add_iff ax hα).not
namespace PointCounting
variable {F : Type*} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}
/-- The predicate "$\varphi$ is an inseparable endomorphism" on the endomorphism ring of
an elliptic curve $E/F$, as a Prop-valued function on `EllipticCurve.EndomorphismRing E`. -/
end PointCounting
namespace Hasse
set_option maxHeartbeats 400000
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {W : WeierstrassCurve.Affine F}

namespace Hasse

/--
[numPoints_eq_card_sub_trace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma numPoints_eq_card_sub_trace
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {W : WeierstrassCurve.Affine F} :
-- imply
  (numPoints W : ℤ) = (Fintype.card F : ℤ) + 1 - traceFrobenius W := by
-- proof
  simp [traceFrobenius]
/-- The degree of the endomorphism $r \cdot [F] - s \cdot \mathrm{id}$ (where $[F]$ is
the Frobenius) equals the quadratic form $r^2 q - r s t + s^2$, and this degree is a
natural number. This is the key positivity input for Hasse's bound. -/
end Hasse
namespace GroupExponent

end Hasse

/--
[oneOverSqHom_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma oneOverSqHom_eq
  {n : ℕ} :
-- imply
  oneOverSqHom n = 1 / (n : ℝ) ^ 2 := by
-- proof
  unfold oneOverSqHom; simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]; split <;> simp_all

/--
[oneOverSqHom_summable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma oneOverSqHom_summable
-- imply
  Summable (fun n => ‖oneOverSqHom n‖) :=
-- proof
  hasSum_zeta_two.summable.norm.congr (fun n => by rw [oneOverSqHom_eq])

/--
[eulerProduct_zeta2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma eulerProduct_zeta2
-- imply
  HasProd (fun p : Nat.Primes => (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
-- proof
  have : ∑' (n : ℕ), oneOverSqHom n = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two.tsum_eq
    rw [show (fun n : ℕ => 1 / (n : ℝ) ^ 2) = oneOverSqHom from
      by ext; rw [oneOverSqHom_eq]] at h
    exact h
  rw [← this]
  convert EulerProduct.eulerProduct_completely_multiplicative_hasProd
    oneOverSqHom_summable using 2 with p
  rw [oneOverSqHom_eq]

/--
[eulerFactor_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma eulerFactor_ge_one
  {p : Nat.Primes} :
-- imply
  1 ≤ (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ := by
-- proof
  rw [one_le_inv_iff₀]
  have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp2 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 := by positivity
  exact ⟨by rw [sub_pos, div_lt_one hp2]; nlinarith,
    by linarith [div_nonneg one_pos.le hp2.le]⟩

/--
[partialInvProduct_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma partialInvProduct_le
  {s : Finset Nat.Primes} :
-- imply
  ∏ p ∈ s, (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 :=
-- proof
  (show Monotone (fun s : Finset Nat.Primes =>
    ∏ p ∈ s, (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹) from by
    intro s t hst; exact Finset.prod_le_prod_of_subset_of_one_le hst
      (fun p _ => le_of_lt (lt_of_lt_of_le zero_lt_one (eulerFactor_ge_one p)))
      (fun p _ _ => eulerFactor_ge_one p)
  ).ge_of_tendsto eulerProduct_zeta2 s
namespace GroupExponentBound
set_option maxHeartbeats 400000

namespace GroupExponentBound

/--
[lcm_orderOf_map_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma lcm_orderOf_map_dvd
  [Group G]
  [Group H]
  {φ : G →* H}
  {α β : G} :
-- imply
  Nat.lcm (orderOf (φ α)) (orderOf (φ β)) ∣ Nat.lcm (orderOf α) (orderOf β) :=
-- proof
  Nat.lcm_dvd
    (dvd_trans (orderOf_map_dvd φ α) (Nat.dvd_lcm_left _ _))
    (dvd_trans (orderOf_map_dvd φ β) (Nat.dvd_lcm_right _ _))

end GroupExponentBound

namespace GroupExponentBound

/--
[finite_euler_product_gt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma finite_euler_product_gt
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  6 / Real.pi ^ 2 < ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
-- proof
  classical
  have hpf : ∀ p ∈ n.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := by omega
  let f : ℕ → Nat.Primes := fun p =>
    if h : Nat.Prime p then ⟨p, h⟩ else ⟨2, by decide⟩
  have transfer : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
    ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2)⁻¹ =
    ∏ p ∈ s.image f, (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro s hs
    apply Finset.prod_nbij f
    · intro a ha; exact Finset.mem_image_of_mem f ha
    · intro a₁ ha₁ a₂ ha₂ h
      simp only [f, dif_pos (hs a₁ ha₁), dif_pos (hs a₂ ha₂)] at h
      exact Subtype.mk.inj h
    · rw [Set.SurjOn, Finset.coe_image]
    · intro a ha; simp only [f, dif_pos (hs a ha)]
  obtain ⟨q, hq, hq_ndvd⟩ : ∃ q, Nat.Prime q ∧ ¬ q ∣ n := by
    by_contra h; push_neg at h
    exact (Set.Finite.subset n.primeFactors.finite_toSet
      (fun p (hp : Nat.Prime p) => Nat.mem_primeFactors.mpr ⟨hp, h p hp, hn0⟩)).not_infinite
      Nat.infinite_setOf_prime
  have hq_notin : q ∉ n.primeFactors := by rw [Nat.mem_primeFactors]; tauto
  have hfq : 1 < (1 - 1 / (q : ℝ) ^ 2)⁻¹ := by
    rw [one_lt_inv_iff₀]
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    have hq2pos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    exact ⟨by rw [sub_pos, div_lt_one hq2pos]; nlinarith,
      by linarith [div_pos one_pos hq2pos]⟩
  have hprod_pos : 0 < ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
    apply Finset.prod_pos
    intro p hp; exact lt_of_lt_of_le zero_lt_one (eulerFactor_ge_one ⟨p, hpf p hp⟩)
  have hall : ∀ p ∈ n.primeFactors ∪ {q}, Nat.Prime p := by
    intro p hp
    obtain h | h := Finset.mem_union.mp hp
    · exact hpf p h
    · exact Finset.mem_singleton.mp h ▸ hq
  have hinv_lt : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ < Real.pi ^ 2 / 6 :=
    calc ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹
      < (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹) * (1 - 1 / (q : ℝ) ^ 2)⁻¹ :=
        lt_mul_of_one_lt_right hprod_pos hfq
      _ = ∏ p ∈ n.primeFactors ∪ {q}, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
        rw [Finset.prod_union (Finset.disjoint_singleton_right.mpr hq_notin),
          Finset.prod_singleton]
      _ ≤ Real.pi ^ 2 / 6 := by rw [transfer _ hall]; exact partialInvProduct_le _
  have hpf_pos : 0 < ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
    apply Finset.prod_pos; intro p hp
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hpf p hp).two_le
    have : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    rw [sub_pos, div_lt_one this]; nlinarith
  rw [Finset.prod_inv_distrib] at hinv_lt
  rw [inv_lt_comm₀ hpf_pos (by positivity)] at hinv_lt
  linarith [show (Real.pi ^ 2 / 6)⁻¹ = 6 / Real.pi ^ 2 from inv_div _ _]

end GroupExponentBound

namespace GroupExponentBound

/--
[exponent_ge_two_of_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma exponent_ge_two_of_nontrivial
  {G : Type*}
  [CommGroup G]
  [Fintype G]
-- given
  (hG : 1 < Fintype.card G) :
-- imply
  2 ≤ Monoid.exponent G := by
-- proof
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp hG
  exact Monoid.one_lt_exponent

end GroupExponentBound

namespace GroupExponentBound

/--
[six_div_pi_sq_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma six_div_pi_sq_lt_one
-- imply
  6 / Real.pi ^ 2 < 1 := by
-- proof
  rw [div_lt_one (by positivity : (0 : ℝ) < Real.pi ^ 2)]
  nlinarith [Real.pi_gt_three]
/-- Theorem 7.6 (full statement): for any finite abelian group $G$, the probability
that two random elements have orders with LCM equal to the group exponent strictly
exceeds $6/\pi^2$. The trivial-group case is handled separately. -/
end GroupExponentBound
namespace BSGSOrder

end GroupExponentBound

namespace BSGSOrder

/--
[nat_div_dvd_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma nat_div_dvd_div
  [AddGroup G]
  [DecidableEq G]
  {q a b : ℕ}
-- given
  (hqa : q ∣ a)
  (hab : a ∣ b) :
-- imply
  a / q ∣ b / q := by
-- proof
  obtain ⟨c, rfl⟩ := hqa
  obtain ⟨d, rfl⟩ := hab
  obtain rfl | hq := Nat.eq_zero_or_pos q
  · simp
  · rw [Nat.mul_div_cancel_left _ hq, mul_assoc, Nat.mul_div_cancel_left _ hq]
    exact dvd_mul_right c d

end BSGSOrder

namespace BSGSOrder

/--
[stripPrimeFactor_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma stripPrimeFactor_nsmul
  [AddGroup G]
  [DecidableEq G]
  {P : G}
  {p : ℕ}
  {m : ℕ}
-- given
  (hp : 1 < p)
  (hm : m • P = 0) :
-- imply
  (stripPrimeFactor P p hp m) • P = 0 := by
-- proof
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [stripPrimeFactor]
    split_ifs with h
    · exact ih _ (Nat.div_lt_self h.1 hp) h.2.2
    · exact hm

end BSGSOrder

namespace BSGSOrder

/--
[stripPrimeFactor_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma stripPrimeFactor_dvd
  [AddGroup G]
  [DecidableEq G]
  {P : G}
  {p : ℕ}
  {m : ℕ}
-- given
  (hp : 1 < p) :
-- imply
  stripPrimeFactor P p hp m ∣ m := by
-- proof
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [stripPrimeFactor]
    split_ifs with h
    · exact dvd_trans (ih _ (Nat.div_lt_self h.1 hp)) (Nat.div_dvd_of_dvd h.2.1)
    · exact dvd_refl m

end BSGSOrder

namespace BSGSOrder

/--
[stripPrimeFactor_prime_stripped](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma stripPrimeFactor_prime_stripped
  [AddGroup G]
  [DecidableEq G]
  {P : G}
  {p : ℕ}
  {m : ℕ}
-- given
  (hp : 1 < p)
  (hm_pos : 0 < m)
  (hm_ann : m • P = 0) :
-- imply
  p ∣ stripPrimeFactor P p hp m → (stripPrimeFactor P p hp m / p) • P ≠ 0 := by
-- proof
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [stripPrimeFactor]
    split_ifs with h
    · exact ih _ (Nat.div_lt_self h.1 hp)
      (Nat.div_pos (Nat.le_of_dvd hm_pos h.2.1) (by omega)) h.2.2
    · push Not at h
      exact fun hd => h hm_pos hd

end BSGSOrder

namespace BSGSOrder

/--
[computeOrder_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma computeOrder_nsmul
  [AddGroup G]
  [DecidableEq G]
  {P : G}
  {ps : List ℕ}
  {m : ℕ}
-- given
  (hm : m • P = 0) :
-- imply
  (computeOrder P ps m) • P = 0 := by
-- proof
  induction ps generalizing m with
  | nil => exact hm
  | cons p ps ih =>
    simp only [computeOrder]
    split_ifs with hp
    · exact ih _ (stripPrimeFactor_nsmul P p hp m hm)
    · exact ih _ hm

end BSGSOrder

namespace BSGSOrder

/--
[computeOrder_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma computeOrder_dvd
  [AddGroup G]
  [DecidableEq G]
  {P : G}
  {ps : List ℕ}
  {m : ℕ} :
-- imply
  computeOrder P ps m ∣ m := by
-- proof
  induction ps generalizing m with
  | nil => exact dvd_refl m
  | cons p ps ih =>
    unfold computeOrder
    split_ifs with hp
    · exact dvd_trans (ih _) (stripPrimeFactor_dvd P p hp m)
    · exact ih _

end BSGSOrder

namespace BSGSOrder

/--
[computeOrder_correct_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma computeOrder_correct_aux
  [AddGroup G]
  [DecidableEq G]
  {P : G}
  {ps : List ℕ}
  {m : ℕ}
  {q : ℕ}
-- given
  (hps : ∀ p ∈ ps, Nat.Prime p)
  (hm_pos : 0 < m)
  (hm_ann : m • P = 0)
  (hq_prime : Nat.Prime q)
  (hq_dvd : q ∣ computeOrder P ps m)
  (hq_src : q ∈ ps ∨ (m / q) • P ≠ 0) :
-- imply
  (computeOrder P ps m / q) • P ≠ 0 := by
-- proof
  induction ps generalizing m with
  | nil =>
    obtain h | h := hq_src
    · simp at h
    · exact h
  | cons p ps ih =>
    have hps_tail : ∀ r ∈ ps, Nat.Prime r := fun r hr => hps r (List.mem_cons_of_mem _ hr)
    simp only [computeOrder] at hq_dvd ⊢
    by_cases hp : 1 < p
    · simp only [hp, dite_true] at hq_dvd ⊢
      have hm'_ann := stripPrimeFactor_nsmul P p hp m hm_ann
      have hm'_dvd := stripPrimeFactor_dvd P p hp m
      have hm'_pos : 0 < stripPrimeFactor P p hp m := Nat.pos_of_ne_zero
        (fun h => by rw [h] at hm'_dvd; exact absurd (Nat.eq_zero_of_zero_dvd hm'_dvd) (by omega))
      have hsrc : q ∈ ps ∨ (stripPrimeFactor P p hp m / q) • P ≠ 0 := by
        obtain hmem | hcond := hq_src
        · rcases List.mem_cons.mp hmem with heq | htail
          · right; subst heq
            exact stripPrimeFactor_prime_stripped P q hp m hm_pos hm_ann
              (dvd_trans hq_dvd (computeOrder_dvd P ps _))
          · left; exact htail
        · right; intro h_ann; apply hcond
          exact addOrderOf_dvd_iff_nsmul_eq_zero.mp
            (dvd_trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_ann)
              (nat_div_dvd_div (dvd_trans hq_dvd (computeOrder_dvd P ps _)) hm'_dvd))
      exact ih hps_tail _ hm'_pos hm'_ann hq_dvd hsrc
    · simp only [hp, dite_false] at hq_dvd ⊢
      have hsrc : q ∈ ps ∨ (m / q) • P ≠ 0 := by
        obtain hmem | hcond := hq_src
        · rcases List.mem_cons.mp hmem with heq | htail
          · subst heq; exact absurd hq_prime.one_lt hp
          · left; exact htail
        · right; exact hcond
      exact ih hps_tail m hm_pos hm_ann hq_dvd hsrc
end BSGSOrder
namespace QuadraticTwist
universe u


namespace QuadraticTwist

variable {F : Type u} [Field F]
/--
[quadraticTwistCurve_a₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma quadraticTwistCurve_a₁ (W : WeierstrassCurve.Affine F) (s : F) :
  (quadraticTwistCurve W s).a₁ = 0 :=
  rfl

end QuadraticTwist

namespace QuadraticTwist

variable {F : Type u} [Field F]
/--
[quadraticTwistCurve_a₂](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma quadraticTwistCurve_a₂ (W : WeierstrassCurve.Affine F) (s : F) :
  (quadraticTwistCurve W s).a₂ = 0 :=
  rfl

end QuadraticTwist

namespace QuadraticTwist

variable {F : Type u} [Field F]
/--
[quadraticTwistCurve_a₃](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma quadraticTwistCurve_a₃ (W : WeierstrassCurve.Affine F) (s : F) :
  (quadraticTwistCurve W s).a₃ = 0 :=
  rfl

end QuadraticTwist

namespace QuadraticTwist

variable {F : Type u} [Field F]
/--
[quadraticTwistCurve_a₄](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma quadraticTwistCurve_a₄ (W : WeierstrassCurve.Affine F) (s : F) :
  (quadraticTwistCurve W s).a₄ = s ^ 2 * W.a₄ :=
  rfl

end QuadraticTwist

namespace QuadraticTwist

variable {F : Type u} [Field F]
/--
[quadraticTwistCurve_a₆](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma quadraticTwistCurve_a₆ (W : WeierstrassCurve.Affine F) (s : F) :
  (quadraticTwistCurve W s).a₆ = s ^ 3 * W.a₆ :=
  rfl

end QuadraticTwist

namespace QuadraticTwist

/--
[numPoints_add_twist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma numPoints_add_twist
  {F : Type u}
  [Field F]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
-- given
  (hW : Hasse.numPoints W ≤ 2 * Fintype.card F + 2) :
-- imply
  Hasse.numPoints W + twistNumPoints W = 2 * Fintype.card F + 2 := by
-- proof
  unfold twistNumPoints
  omega
end QuadraticTwist
namespace Mestre
set_option maxHeartbeats 800000

end QuadraticTwist

namespace Mestre

/--
[mestre_inequality_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma mestre_inequality_of_bounds
  {p m n M N : ℕ}
-- given
  (hp : 0 < p)
  (hm : 0 < m)
  (hn : 0 < n)
  (hM : 0 < M)
  (hN : 0 < N)
  (hbound : (m : ℤ) ^ 2 * (n : ℤ) ^ 2 ≤ 64 * (p : ℤ))
  (hMN_lt : (M : ℝ) * N < 16 * (p : ℝ))
  (hmnMN_ge : ((m : ℝ) * n) * (M * N) ≥ ((Real.sqrt p) - 1) ^ 4) :
-- imply
  16384 * (p : ℝ) ^ 3 > (Real.sqrt p - 1) ^ 8 := by
-- proof
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hmn_pos : (0 : ℝ) < (m : ℝ) * n := by positivity
  have hMN_pos : (0 : ℝ) < (M : ℝ) * N := by positivity
  have hmn_lower : (m : ℝ) * n > (Real.sqrt p - 1) ^ 4 / (16 * p) := by
    rw [gt_iff_lt, div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * p)]
    calc (Real.sqrt ↑p - 1) ^ 4
      ≤ (↑m * ↑n) * (↑M * ↑N) := hmnMN_ge
      _ < (↑m * ↑n) * (16 * ↑p) := by nlinarith
  have hbound_real : (m : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ 64 * (p : ℝ) := by
    exact_mod_cast hbound
  have hmn_sq : (m : ℝ) ^ 2 * n ^ 2 > (Real.sqrt p - 1) ^ 8 / (256 * p ^ 2) := by
    have h1 : ((m : ℝ) * n) ^ 2 = (m : ℝ) ^ 2 * n ^ 2 := by ring
    have h2 : ((Real.sqrt p - 1) ^ 4 / (16 * p)) ^ 2 =
      (Real.sqrt p - 1) ^ 8 / (256 * p ^ 2) := by ring
    rw [← h1, ← h2]
    have hq : 0 ≤ (Real.sqrt p - 1) ^ 4 / (16 * p) := by positivity
    exact sq_lt_sq' (by nlinarith) hmn_lower
  calc (Real.sqrt ↑p - 1) ^ 8
    < (m : ℝ) ^ 2 * n ^ 2 * (256 * (p : ℝ) ^ 2) := by
      rwa [gt_iff_lt, div_lt_iff₀ (by positivity : (0 : ℝ) < 256 * (p : ℝ) ^ 2)] at hmn_sq
    _ ≤ 64 * (p : ℝ) * (256 * (p : ℝ) ^ 2) := by nlinarith
    _ = 16384 * (p : ℝ) ^ 3 := by ring

end Mestre

namespace Mestre

/--
[poly_bound_132](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma poly_bound_132
  {s : ℝ}
-- given
  (hs : 132 ≤ s) :
-- imply
  (s - 1) ^ 4 ≥ 128 * s ^ 3 := by
-- proof
  nlinarith [mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ s by linarith) 3)
    (show (0 : ℝ) ≤ s - 132 by linarith),
    show (s - 1) ^ 4 - 128 * s ^ 3 =
      s ^ 3 * (s - 132) + (6 * s ^ 2 - 4 * s + 1) from by ring,
    sq_nonneg (s - 1)]

end Mestre

namespace Mestre

/--
[inequality_large_case](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma inequality_large_case
  {p : ℕ}
-- given
  (hp : 17424 ≤ p) :
-- imply
  (Real.sqrt p - 1) ^ 8 ≥ 16384 * (p : ℝ) ^ 3 := by
-- proof
  have hs : (132 : ℝ) ≤ Real.sqrt p := by
    rw [show (132 : ℝ) = Real.sqrt (17424 : ℝ) from by
      rw [show (17424 : ℝ) = 132 ^ 2 from by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 132)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hp)
  have hsq : Real.sqrt (↑p) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have h4 := poly_bound_132 (Real.sqrt p) hs
  calc (Real.sqrt p - 1) ^ 8
    = ((Real.sqrt p - 1) ^ 4) ^ 2 := by ring
    _ ≥ (128 * (Real.sqrt p) ^ 3) ^ 2 := by
      apply sq_le_sq'
      · nlinarith [sq_nonneg (Real.sqrt p - 1)]
      · exact h4
    _ = 16384 * ((Real.sqrt p) ^ 2) ^ 3 := by ring
    _ = 16384 * (p : ℝ) ^ 3 := by rw [hsq]

end Mestre

namespace Mestre

/--
[int_bound_small_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma int_bound_small_range
  {p : ℕ}
-- given
  (h0 : 17413 ≤ p)
  (h1 : p ≤ 17423) :
-- imply
  (p - 263 : ℤ) ^ 4 ≥ 16384 * (p : ℤ) ^ 3 := by
-- proof
  have hp1 : (17413 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h1
  have hp2 : (p : ℤ) ≤ 17423 := by exact_mod_cast h2
  nlinarith [sq_nonneg ((p : ℤ) - 17413), sq_nonneg ((p : ℤ) - 17423),
    sq_nonneg ((p : ℤ) - 17418)]

end Mestre

namespace Mestre

/--
[inequality_small_case](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma inequality_small_case
  {p : ℕ}
-- given
  (h0 : 17413 ≤ p)
  (h1 : p < 17424) :
-- imply
  (Real.sqrt p - 1) ^ 8 ≥ 16384 * (p : ℝ) ^ 3 := by
-- proof
  have hint := int_bound_small_range p h1 (by omega)
  have hint_real : ((p : ℝ) - 263) ^ 4 ≥ 16384 * (p : ℝ) ^ 3 := by
    have := Int.cast_le (R := ℝ).mpr hint; push_cast at this; linarith
  have hsq : Real.sqrt (↑p) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have h132 : Real.sqrt (↑p) < 132 := by
    rw [show (132 : ℝ) = Real.sqrt (17424 : ℝ) from by
      rw [show (17424 : ℝ) = 132 ^ 2 from by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 132)]]
    exact Real.sqrt_lt_sqrt (Nat.cast_nonneg p) (by exact_mod_cast h2)
  have hgt : (p : ℝ) - 263 < (Real.sqrt p - 1) ^ 2 := by
    rw [sub_sq, hsq, mul_one, one_pow]; linarith
  have h_nn : (0 : ℝ) ≤ (p : ℝ) - 263 :=
    sub_nonneg.mpr (by exact_mod_cast show 263 ≤ p by omega)
  calc (Real.sqrt ↑p - 1) ^ 8
    = ((Real.sqrt ↑p - 1) ^ 2) ^ 4 := by ring
    _ ≥ ((p : ℝ) - 263) ^ 4 := pow_le_pow_left₀ h_nn (le_of_lt hgt) 4
    _ ≥ 16384 * (p : ℝ) ^ 3 := hint_real

end Mestre

namespace Mestre

/--
[inequality_fails_large_p](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma inequality_fails_large_p
  {p : ℕ}
-- given
  (hp : 17413 ≤ p) :
-- imply
  (Real.sqrt p - 1) ^ 8 ≥ 16384 * (p : ℝ) ^ 3 := by
-- proof
  by_cases h : 17424 ≤ p
  · exact inequality_large_case p h
  · exact inequality_small_case p hp (by omega)

end Mestre

namespace Mestre

/--
[not_unique_implies_lt_width](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
lemma not_unique_implies_lt_width
  {N : ℕ}
  {p : ℕ}
-- given
  (hN_pos : 0 < N)
  (hp_prime : Nat.Prime p)
  (hp_gt4 : 4 < p)
  (h_has_multiple : ∃ k : ℕ, 0 < k ∧ (Real.sqrt p - 1) ^ 2 ≤ (k * N : ℝ) ∧ (k * N : ℝ) ≤ (Real.sqrt p + 1) ^ 2)
  (h_not_unique : ¬ HasUniqueMultipleIn N ((Real.sqrt p - 1) ^ 2) ((Real.sqrt p + 1) ^ 2)) :
-- imply
  (N : ℝ) < 4 * Real.sqrt p := by
-- proof
  unfold HasUniqueMultipleIn at h_not_unique
  obtain ⟨k₁, hk₁_pos, hk₁_lo, hk₁_hi⟩ := h_has_multiple
  have h_not_all_eq : ¬ ∀ y : ℕ,
    (0 < y ∧ (Real.sqrt ↑p - 1) ^ 2 ≤ ↑y * ↑N ∧ ↑y * ↑N ≤ (Real.sqrt ↑p + 1) ^ 2) → y = k₁ := by
    intro huniq
    exact h_not_unique ⟨k₁, ⟨hk₁_pos, hk₁_lo, hk₁_hi⟩, huniq⟩
  simp only [not_forall] at h_not_all_eq
  obtain ⟨k₂, ⟨hk₂_pos, hk₂_lo, hk₂_hi⟩, hne⟩ := h_not_all_eq
  suffices hN_le : (↑N : ℝ) ≤ 4 * Real.sqrt ↑p by
    apply lt_of_le_of_ne hN_le
    intro heq
    have hirr : Irrational (4 * Real.sqrt (↑p : ℝ)) :=
      hp_prime.irrational_sqrt.natCast_mul (show (4 : ℕ) ≠ 0 by norm_num)
    rw [← heq] at hirr
    exact hirr ⟨↑N, by push_cast; ring⟩
  obtain hlt | rfl | hlt := lt_trichotomy k₁ k₂
  ·
    have h_gap : ↑k₁ * (↑N : ℝ) + ↑N ≤ ↑k₂ * ↑N := by
      have : (↑(k₁ + 1) : ℝ) ≤ (↑k₂ : ℝ) := by exact_mod_cast (hlt : k₁ + 1 ≤ k₂)
      have := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg N)
      push_cast at this ⊢; linarith
    linarith [show (Real.sqrt ↑p + 1) ^ 2 - (Real.sqrt ↑p - 1) ^ 2 = 4 * Real.sqrt ↑p from by ring]
  · exact absurd rfl hne
  ·
    have h_gap : ↑k₂ * (↑N : ℝ) + ↑N ≤ ↑k₁ * ↑N := by
      have : (↑(k₂ + 1) : ℝ) ≤ (↑k₁ : ℝ) := by exact_mod_cast (hlt : k₂ + 1 ≤ k₁)
      have := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg N)
      push_cast at this ⊢; linarith
    linarith [show (Real.sqrt ↑p + 1) ^ 2 - (Real.sqrt ↑p - 1) ^ 2 = 4 * Real.sqrt ↑p from by ring]
/-- Bounded range case of Mestre's theorem ($229 < p < 17413$), to be discharged by a
finite computer search. Asserts that under the bound $m^2 n^2 \leq 64 p$, one of the
two annihilators $N_E, M_{E^t}$ has a unique multiple in the Hasse interval. -/

end Mestre

/--
[quadraticTwistCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
private lemma quadraticTwistCurve_a_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {s : F} :
-- imply
  (quadraticTwistCurve W s).a₁ = 0 := by
-- proof
  apply QuadraticTwist.quadraticTwistCurve_a W s

/--
[quadraticTwistCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
private lemma quadraticTwistCurve_a_eq_2
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {s : F} :
-- imply
  (quadraticTwistCurve W s).a₂ = 0 := by
-- proof
  apply QuadraticTwist.quadraticTwistCurve_a W s

/--
[quadraticTwistCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
private lemma quadraticTwistCurve_a_eq_3
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {s : F} :
-- imply
  (quadraticTwistCurve W s).a₃ = 0 := by
-- proof
  apply QuadraticTwist.quadraticTwistCurve_a W s

/--
[quadraticTwistCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
private lemma quadraticTwistCurve_a_eq_4
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {s : F} :
-- imply
  (quadraticTwistCurve W s).a₄ = s ^ 2 * W.a₄ := by
-- proof
  apply QuadraticTwist.quadraticTwistCurve_a W s

/--
[quadraticTwistCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean)
-/
@[path]
private lemma quadraticTwistCurve_a_eq_5
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {s : F} :
-- imply
  (quadraticTwistCurve W s).a₆ = s ^ 3 * W.a₆ := by
-- proof
  apply QuadraticTwist.quadraticTwistCurve_a W s


-- created on 2026-10-23
