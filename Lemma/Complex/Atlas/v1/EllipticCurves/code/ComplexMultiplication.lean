import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
open ComplexLattice
open Pointwise
open Pointwise Function
open Polynomial
open Polynomial Pointwise


namespace ComplexLattice

/--
[IdealClassGroup.mk_eq_mk_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma IdealClassGroup.mk_eq_mk_iff
  {𝒪 : Subring ℂ}
  {L₁ L₂ : ProperIdeal 𝒪} :
-- imply
  IdealClassGroup.mk 𝒪 L₁ = IdealClassGroup.mk 𝒪 L₂ ↔ IsEquivalent 𝒪 L₁.val L₂.val :=
-- proof
  Quotient.eq (r := properIdealSetoid 𝒪)

end ComplexLattice

namespace ComplexLattice

/--
[ProperIdeal.mul_equiv_snd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma ProperIdeal.mul_equiv_snd
  {𝒪 : Subring ℂ}
  {a b : ProperIdeal 𝒪} :
-- imply
  IsEquivalent 𝒪 (ProperIdeal.mul 𝒪 a b).val b.val := by
-- proof
  have hω₁_mem : a.val.ω₁ ∈ 𝒪 := a.prop.2 a.val.ω₁ a.val.ω₁_mem_lattice
  have hω₁_ne : a.val.ω₁ ≠ 0 := by
    have h0 := a.val.indep.ne_zero (0 : Fin 2)
    simp only [Matrix.cons_val_zero] at h0
    exact h0
  refine ⟨1, ⟨a.val.ω₁, hω₁_mem⟩, one_ne_zero, hω₁_ne, ?_⟩
  simp only [OneMemClass.coe_one, one_smul, Subtype.coe_mk]
  have hω₁ : (ProperIdeal.mul 𝒪 a b).val.ω₁ = a.val.ω₁ * b.val.ω₁ := rfl
  have hω₂ : (ProperIdeal.mul 𝒪 a b).val.ω₂ = a.val.ω₁ * b.val.ω₂ := rfl
  ext x
  simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul]
  constructor
  ·
    intro hx
    rw [PeriodPair.mem_lattice] at hx
    obtain ⟨m, n, hmn⟩ := hx
    rw [hω₁, hω₂] at hmn
    refine ⟨↑m * b.val.ω₁ + ↑n * b.val.ω₂, ?_, ?_⟩
    · exact PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
    · linear_combination hmn
  ·
    intro ⟨y, hy, hxy⟩
    rw [PeriodPair.mem_lattice] at hy
    obtain ⟨m, n, hmn⟩ := hy
    rw [PeriodPair.mem_lattice]
    refine ⟨m, n, ?_⟩
    rw [hω₁, hω₂]
    linear_combination hxy + a.val.ω₁ * hmn

end ComplexLattice

namespace ComplexLattice

/--
[ProperIdeal.mul_resp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma ProperIdeal.mul_resp
  {𝒪 : Subring ℂ}
  {a₁ a₂ b₁ b₂ : ProperIdeal 𝒪} :
-- imply
  (properIdealSetoid 𝒪).r a₁ a₂ → (properIdealSetoid 𝒪).r b₁ b₂ → (properIdealSetoid 𝒪).r (ProperIdeal.mul 𝒪 a₁ b₁) (ProperIdeal.mul 𝒪 a₂ b₂) := by
-- proof
  intro _ h₂
  exact ((ProperIdeal.mul_equiv_snd 𝒪 a₁ b₁).trans h₂).trans
    (ProperIdeal.mul_equiv_snd 𝒪 a₂ b₂).symm

end ComplexLattice

namespace ComplexLattice

/--
[ProperIdeal.mul_assoc_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma ProperIdeal.mul_assoc_equiv
  {𝒪 : Subring ℂ}
  {a b c : ProperIdeal 𝒪} :
-- imply
  (properIdealSetoid 𝒪).r (ProperIdeal.mul 𝒪 (ProperIdeal.mul 𝒪 a b) c) (ProperIdeal.mul 𝒪 a (ProperIdeal.mul 𝒪 b c)) := by
-- proof
  have heq : ProperIdeal.mul 𝒪 (ProperIdeal.mul 𝒪 a b) c =
    ProperIdeal.mul 𝒪 a (ProperIdeal.mul 𝒪 b c) := by
    apply Subtype.ext
    simp only [ProperIdeal.mul]
    congr 1 <;> exact mul_assoc _ _ _
  rw [heq]

end ComplexLattice

namespace ComplexLattice

/--
[endomorphismRing_commutative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma endomorphismRing_commutative
  {L : ComplexLattice} :
-- imply
  ∀ α β : ℂ, α ∈ L.endomorphismRing → β ∈ L.endomorphismRing → α * β = β * α :=
-- proof
  fun _ _ _ _ => mul_comm _ _

end ComplexLattice

namespace ComplexLattice

/--
[intCast_mem_endomorphismRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma intCast_mem_endomorphismRing
  {L : ComplexLattice}
  {n : ℤ} :
-- imply
  (n : ℂ) ∈ L.endomorphismRing := by
-- proof
  simp only [mem_endomorphismRing]
  intro z hz
  rw [show (n : ℂ) * z = ↑n * z from rfl]
  exact AddSubgroup.int_mul_mem n hz

end ComplexLattice

namespace ComplexLattice

/--
[endomorphismRing_charPoly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma endomorphismRing_charPoly
  {L : ComplexLattice}
  {τ : ℂ}
  {a b c d : ℤ}
-- given
  (hτ_mem : τ ∈ L.endomorphismRing)
  (hτ_not_int : ∀ n : ℤ, τ ≠ (n : ℂ))
  (hab : ↑a * L.ω₁ + ↑b * L.ω₂ = τ * L.ω₁)
  (hcd : ↑c * L.ω₁ + ↑d * L.ω₂ = τ * L.ω₂) :
-- imply
  τ * τ + (↑(-(a + d)) : ℂ) * τ + (↑(a * d - b * c) : ℂ) = 0 := by
-- proof
  have hω₁ : L.ω₁ ≠ 0 := by
    have h0 := L.indep.ne_zero (0 : Fin 2); simp only [Matrix.cons_val_zero] at h0; exact h0
  have hab' : τ * L.ω₁ = ↑a * L.ω₁ + ↑b * L.ω₂ := hab.symm
  have hcd' : τ * L.ω₂ = ↑c * L.ω₁ + ↑d * L.ω₂ := hcd.symm
  have h_eq : (τ * τ + (↑(-(a + d)) : ℂ) * τ + (↑(a * d - b * c) : ℂ)) * L.ω₁ = 0 := by
    have hττω : τ * τ * L.ω₁ = (↑a * ↑a + ↑b * ↑c) * L.ω₁ + (↑a * ↑b + ↑b * ↑d) * L.ω₂ := by
      calc τ * τ * L.ω₁ = τ * (τ * L.ω₁) := by ring
        _ = τ * (↑a * L.ω₁ + ↑b * L.ω₂) := by rw [hab']
        _ = ↑a * (τ * L.ω₁) + ↑b * (τ * L.ω₂) := by ring
        _ = ↑a * (↑a * L.ω₁ + ↑b * L.ω₂) + ↑b * (↑c * L.ω₁ + ↑d * L.ω₂) := by rw [hab', hcd']
        _ = (↑a * ↑a + ↑b * ↑c) * L.ω₁ + (↑a * ↑b + ↑b * ↑d) * L.ω₂ := by ring
    have expand : (τ * τ + (↑(-(a + d)) : ℂ) * τ + (↑(a * d - b * c) : ℂ)) * L.ω₁ =
      τ * τ * L.ω₁ + (↑(-(a + d)) : ℂ) * (τ * L.ω₁) + (↑(a * d - b * c) : ℂ) * L.ω₁ := by ring
    rw [expand, hττω, hab']; push_cast; ring
  obtain h' | h' := mul_eq_zero.mp h_eq
  · exact h'
  · exact absurd h' hω₁

end ComplexLattice

namespace ComplexLattice

/--
[endomorphismRing_negDisc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma endomorphismRing_negDisc
  {L : ComplexLattice}
  {τ : ℂ}
  {a b c d : ℤ}
-- given
  (hτ_mem : τ ∈ L.endomorphismRing)
  (hτ_not_int : ∀ n : ℤ, τ ≠ (n : ℂ))
  (hab : ↑a * L.ω₁ + ↑b * L.ω₂ = τ * L.ω₁)
  (hcd : ↑c * L.ω₁ + ↑d * L.ω₂ = τ * L.ω₂) :
-- imply
  -(a + d) * -(a + d) - 4 * (a * d - b * c) < 0 := by
-- proof
  have hω₁ : L.ω₁ ≠ 0 := by
    have h0 := L.indep.ne_zero (0 : Fin 2); simp only [Matrix.cons_val_zero] at h0; exact h0
  have hb_ne : (b : ℂ) ≠ 0 := by
    intro hb0
    have : (↑a : ℂ) * L.ω₁ = τ * L.ω₁ := by
      have := hab; rw [hb0, zero_mul, add_zero] at this; exact this
    exact hτ_not_int a (mul_right_cancel₀ hω₁ this.symm)
  have hτ_im : τ.im ≠ 0 := by
    intro him
    have hτ_eq : τ = (↑τ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hab' : (↑τ.re : ℂ) * L.ω₁ = (↑a : ℂ) * L.ω₁ + (↑b : ℂ) * L.ω₂ := by
      rw [← hτ_eq]; exact hab.symm
    have hlin : (τ.re - (↑a : ℝ)) • L.ω₁ + (-(↑b : ℝ)) • L.ω₂ = 0 := by
      have : (↑(τ.re - (↑a : ℝ)) : ℂ) * L.ω₁ + (↑(-(↑b : ℝ)) : ℂ) * L.ω₂ = 0 := by
        push_cast; linear_combination hab' - (↑a : ℂ) * L.ω₁ - (↑b : ℂ) * L.ω₂
      rwa [← Complex.real_smul, ← Complex.real_smul] at this
    have hpair := LinearIndependent.pair_iff.mp L.indep _ _ hlin
    exact hb_ne (by exact_mod_cast (neg_eq_zero.mp hpair.2 : (b : ℝ) = 0))
  have hchar := endomorphismRing_charPoly L τ hτ_mem hτ_not_int a b c d hab hcd
  have him := congr_arg Complex.im hchar
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.zero_im,
    Complex.intCast_im, Complex.intCast_re, Complex.ofReal_im, Complex.ofReal_re] at him
  have hre' := congr_arg Complex.re hchar
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.zero_re,
    Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re] at hre'
  have hre_val : 2 * τ.re = (↑a : ℝ) + ↑d := by
    have : τ.im * (2 * τ.re - ((↑a : ℝ) + ↑d)) = 0 := by push_cast at him ⊢; nlinarith
    obtain h | h := mul_eq_zero.mp this
    · exact absurd h hτ_im
    · linarith
  have disc_eq : ((↑a : ℝ) + ↑d) * (↑a + ↑d) - 4 * (↑a * ↑d - ↑b * ↑c) =
    -4 * (τ.im * τ.im) := by push_cast at hre' ⊢; nlinarith [hre_val]
  have him2_pos : 0 < τ.im * τ.im := mul_self_pos.mpr hτ_im
  suffices h : ((-(a + d) * -(a + d) - 4 * (a * d - b * c) : ℤ) : ℝ) < 0 by exact_mod_cast h
  push_cast; linarith

end ComplexLattice

namespace ComplexLattice

/--
[endomorphismRing_order_witness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma endomorphismRing_order_witness
  {L : ComplexLattice}
  {τ : ℂ}
-- given
  (hτ_mem : τ ∈ L.endomorphismRing)
  (hτ_not_int : ∀ n : ℤ, τ ≠ (n : ℂ)) :
-- imply
  ∃ τ' : ℂ, τ' ∈ L.endomorphismRing ∧ (∀ n : ℤ, τ' ≠ (n : ℂ)) ∧ ∃ b c : ℤ, τ' * τ' + (b : ℂ) * τ' + (c : ℂ) = 0 ∧ (b : ℤ) * b - 4 * c < 0 := by
-- proof
  have hτω₁ : τ * L.ω₁ ∈ L.lattice :=
    hτ_mem L.ω₁ (ComplexLattice.ω₁_mem L)
  have hτω₂ : τ * L.ω₂ ∈ L.lattice :=
    hτ_mem L.ω₂ (ComplexLattice.ω₂_mem L)
  rw [ComplexLattice.mem_lattice_iff] at hτω₁ hτω₂
  obtain ⟨a, b, hab⟩ := hτω₁
  obtain ⟨c, d, hcd⟩ := hτω₂
  exact ⟨τ, hτ_mem, hτ_not_int, -(a + d), a * d - b * c,
    endomorphismRing_charPoly L τ hτ_mem hτ_not_int a b c d hab hcd,
    endomorphismRing_negDisc L τ hτ_mem hτ_not_int a b c d hab hcd⟩

end ComplexLattice

namespace ComplexLattice

/--
[endomorphismRing_classification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma endomorphismRing_classification
  {L : ComplexLattice} :
-- imply
  EndomorphismRingClassification L := by
-- proof
  by_cases h : ∀ α : ℂ, α ∈ L.endomorphismRing → ∃ n : ℤ, α = (n : ℂ)
  · exact EndomorphismRingClassification.isZ h
  · push_neg at h
    obtain ⟨τ, hτ_mem, hτ_not_int⟩ := h
    have hw := endomorphismRing_order_witness L τ hτ_mem hτ_not_int
    have hIsOrder : IsImagQuadOrder L.endomorphismRing := by
      obtain ⟨τ', hτ'_mem, hτ'_not_int, b, c, hpoly, hdisc⟩ := hw
      exact ⟨τ', hτ'_mem, hτ'_not_int, b, c, hpoly, hdisc⟩
    have hEmbed : ∀ α : ℂ, α ∈ L.endomorphismRing →
      ∃ a' b' : ℤ, ↑a' * L.ω₁ + ↑b' * L.ω₂ = α * L.ω₁ := by
      intro α hα
      have hαω : α * L.ω₁ ∈ L.lattice := hα L.ω₁ (ComplexLattice.ω₁_mem L)
      rwa [ComplexLattice.mem_lattice_iff] at hαω
    exact .isOrderInImagQuadField hIsOrder hEmbed

end ComplexLattice

namespace ComplexLattice

/--
[endomorphismRing_comm_and_classification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma endomorphismRing_comm_and_classification
  {L : ComplexLattice} :
-- imply
  (∀ α β : ℂ, α ∈ L.endomorphismRing → β ∈ L.endomorphismRing → α * β = β * α) ∧ EndomorphismRingClassification L :=
-- proof
  ⟨endomorphismRing_commutative L, endomorphismRing_classification L⟩
end
namespace ComplexLattice
noncomputable section
open Pointwise Function

end ComplexLattice

namespace ComplexLattice

/--
[inducedMap_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma inducedMap_add
  {L₁ L₂ : ComplexLattice}
  {α β : ℂ}
-- given
  (hα : α ∈ latticeMulSet L₁ L₂)
  (hβ : β ∈ latticeMulSet L₁ L₂) :
-- imply
  ∀ x : torusQuot L₁, inducedMap L₁ L₂ (α + β) (latticeMulSet_add_mem L₁ L₂ hα hβ) x = inducedMap L₁ L₂ α hα x + inducedMap L₁ L₂ β hβ x := by
-- proof
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L₁.lattice.toAddSubgroup x
  change inducedMap L₁ L₂ (α + β) _ (proj L₁ z) =
    inducedMap L₁ L₂ α hα (proj L₁ z) + inducedMap L₁ L₂ β hβ (proj L₁ z)
  simp only [inducedMap_proj, add_mul, map_add]

end ComplexLattice

namespace ComplexLattice

/--
[corollary_16_2_surj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma corollary_16_2_surj
  {L₁ L₂ : ComplexLattice}
  {φ : ComplexTorusHolMap L₁ L₂}
-- given
  (hφ0 : φ.toFun 0 = 0) :
-- imply
  ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂, ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z) :=
-- proof
  theorem_16_1_existence L₁ L₂ φ hφ0

end ComplexLattice

namespace ComplexLattice

/--
[corollary_16_2_inj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma corollary_16_2_inj
  {L₁ L₂ : ComplexLattice}
  {α γ : ℂ}
-- given
  (hα : α ∈ latticeMulSet L₁ L₂)
  (hγ : γ ∈ latticeMulSet L₁ L₂)
  (heq : ∀ z : ℂ, inducedMap L₁ L₂ α hα (proj L₁ z) = inducedMap L₁ L₂ γ hγ (proj L₁ z)) :
-- imply
  α = γ :=
-- proof
  inducedMap_unique L₁ L₂ α γ hα hγ heq

end ComplexLattice

namespace ComplexLattice

/--
[corollary_16_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma corollary_16_2
  {L₁ L₂ : ComplexLattice} :
-- imply
  (∀ (φ : ComplexTorusHolMap L₁ L₂), φ.toFun 0 = 0 → ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂, ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z)) ∧ (∀ (α γ : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) (hγ : γ ∈ latticeMulSet L₁ L₂), (∀ z : ℂ, inducedMap L₁ L₂ α hα (proj L₁ z) = inducedMap L₁ L₂ γ hγ (proj L₁ z)) → α = γ) ∧ (∀ (α β : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂), ∀ x : torusQuot L₁, inducedMap L₁ L₂ (α + β) (latticeMulSet_add_mem L₁ L₂ hα hβ) x = inducedMap L₁ L₂ α hα x + inducedMap L₁ L₂ β hβ x) :=
-- proof
  ⟨fun φ hφ0 => corollary_16_2_surj L₁ L₂ φ hφ0,
    fun α γ hα hγ h => corollary_16_2_inj L₁ L₂ α γ hα hγ h,
    fun α β hα hβ => inducedMap_add L₁ L₂ α β hα hβ⟩
end
namespace ComplexLattice
noncomputable section
open Polynomial

end ComplexLattice

namespace ComplexLattice

/--
[meromorphic_comp_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma meromorphic_comp_neg
  {L : ComplexLattice}
  {f : ℂ → ℂ}
-- given
  (hf : Meromorphic f) :
-- imply
  Meromorphic (fun z => f (-z)) := by
-- proof
  intro x; exact (hf (-x)).comp_analyticAt analyticAt_id.neg

end ComplexLattice

namespace ComplexLattice

/--
[latticePeriodic_neg_of_latticePeriodic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma latticePeriodic_neg_of_latticePeriodic
  {L : ComplexLattice}
  {f : ℂ → ℂ}
-- given
  (hper : L.IsLatticePeriodic f) :
-- imply
  ∀ ω ∈ L.lattice, ∀ z : ℂ, f (-(z + ω)) = f (-z) := by
-- proof
  intro ω hω z
  rw [show -(z + ω) = -z + (-ω) from by ring]
  exact hper (-ω) (L.lattice.neg_mem hω) (-z)

end ComplexLattice

namespace ComplexLattice

/--
[even_part_isEllipticFunction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma even_part_isEllipticFunction
  {L : ComplexLattice}
  {f : ℂ → ℂ}
-- given
  (hf : L.IsEllipticFunction f) :
-- imply
  L.IsEllipticFunction (fun z => (f z + f (-z)) / 2) where meromorphic :=
-- proof
  (hf.meromorphic.add (meromorphic_comp_neg hf.meromorphic)).div
    (fun _ => analyticAt_const.meromorphicAt)
    periodic ω hω z := by
      simp only
      rw [hf.periodic ω hω z,
        latticePeriodic_neg_of_latticePeriodic L hf.periodic ω hω z]

end ComplexLattice

namespace ComplexLattice

/--
[even_part_isEvenFunction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma even_part_isEvenFunction
  {L : ComplexLattice}
  {f : ℂ → ℂ} :
-- imply
  IsEvenFunction (fun z => (f z + f (-z)) / 2) :=
-- proof
  fun z => by simp only [neg_neg]; ring

end ComplexLattice

namespace ComplexLattice

/--
[odd_quot_derivWP_isEllipticFunction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma odd_quot_derivWP_isEllipticFunction
  {L : ComplexLattice}
  {f : ℂ → ℂ}
-- given
  (hf : L.IsEllipticFunction f) :
-- imply
  L.IsEllipticFunction (fun z => (f z - f (-z)) / 2 / L.derivWeierstrassP z) where meromorphic :=
-- proof
  ((hf.meromorphic.sub (meromorphic_comp_neg hf.meromorphic)).div
    (fun _ => analyticAt_const.meromorphicAt)).div L.meromorphic_derivWeierstrassP
    periodic ω hω z := by
      simp only
      rw [hf.periodic ω hω z,
        latticePeriodic_neg_of_latticePeriodic L hf.periodic ω hω z,
        L.derivWeierstrassP_add_coe z ⟨ω, hω⟩]

end ComplexLattice

namespace ComplexLattice

/--
[odd_quot_derivWP_isEvenFunction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma odd_quot_derivWP_isEvenFunction
  {L : ComplexLattice}
  {f : ℂ → ℂ} :
-- imply
  IsEvenFunction (fun z => (f z - f (-z)) / 2 / L.derivWeierstrassP z) := by
-- proof
  intro z; simp only [neg_neg]
  rw [L.derivWeierstrassP_neg z]; field_simp; ring

end ComplexLattice

namespace ComplexLattice

/--
[odd_part_vanishes_at_derivWP_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma odd_part_vanishes_at_derivWP_zero
  {L : ComplexLattice}
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : L.IsEllipticFunction f)
  (h : L.derivWeierstrassP z = 0) :
-- imply
  f z = f (-z) := by
-- proof
  have h2z : (2 : ℂ) * z ∈ (L.lattice : Set ℂ) := by
    by_cases hz : z ∈ (L.lattice : Set ℂ)
    · have : (2 : ℂ) * z = z + z := by ring
      rw [this]; exact L.lattice.add_mem hz hz
    · exact (L.derivWeierstrassPFun_eq_zero_iff z hz).mp h
  have hkey : -z + (2 : ℂ) * z = z := by ring
  have hperiod := hf.periodic ((2 : ℂ) * z) h2z (-z)
  rwa [hkey] at hperiod

end ComplexLattice

namespace ComplexLattice

/--
[lem_16_3_i_assembly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma lem_16_3_i_assembly
  {L : ComplexLattice}
  {f : ℂ → ℂ}
  {Pe Qe Po Qo : ℂ[X]}
-- given
  (hf : L.IsEllipticFunction f)
  (hQe : ∀ z, Qe.eval (L.weierstrassP z) * ((f z + f (-z)) / 2) = Pe.eval (L.weierstrassP z))
  (hQo : ∀ z, Qo.eval (L.weierstrassP z) * ((f z - f (-z)) / 2 / L.derivWeierstrassP z) = Po.eval (L.weierstrassP z)) :
-- imply
  ∀ z, (Qe * Qo).eval (L.weierstrassP z) * f z = (Qo * Pe).eval (L.weierstrassP z) + (Qe * Po).eval (L.weierstrassP z) * L.derivWeierstrassP z := by
-- proof
  intro z
  simp only [Polynomial.eval_mul]
  have heven := hQe z
  have hodd : Qo.eval (L.weierstrassP z) * ((f z - f (-z)) / 2) =
    Po.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    by_cases hwp : L.derivWeierstrassP z = 0
    ·
      have hfz_eq := odd_part_vanishes_at_derivWP_zero L f hf z hwp
      have hO : f z - f (-z) = 0 := sub_eq_zero.mpr hfz_eq
      have hpo : Po.eval (L.weierstrassP z) = 0 := by
        have h1 := hQo z; simp only [hwp, div_zero, mul_zero] at h1; exact h1.symm
      simp only [hO, zero_div, mul_zero, hpo, zero_mul]
    ·
      have h1 := hQo z
      have key : Qo.eval (L.weierstrassP z) *
        ((f z - f (-z)) / 2 / L.derivWeierstrassP z) *
        L.derivWeierstrassP z =
        Po.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
        rw [h1]
      rwa [mul_assoc, div_mul_cancel₀ _ hwp] at key
  have hfz : f z = (f z + f (-z)) / 2 + (f z - f (-z)) / 2 := by ring
  have : Qe.eval (L.weierstrassP z) * Qo.eval (L.weierstrassP z) * f z =
    Qo.eval (L.weierstrassP z) * (Qe.eval (L.weierstrassP z) * ((f z + f (-z)) / 2)) +
    Qe.eval (L.weierstrassP z) * (Qo.eval (L.weierstrassP z) * ((f z - f (-z)) / 2)) := by
    rw [hfz]; ring
  rw [this, heven, hodd]; ring
/-- *Theorem*: the field of elliptic functions for $L$ equals $\mathbb{C}(\wp, \wp')$.
Every elliptic function $f$ can be expressed as
$f(z) = (P_1(\wp(z)) + P_2(\wp(z)) \wp'(z)) / Q(\wp(z))$ for polynomials
$P_1, P_2, Q \in \mathbb{C}[X]$ with $Q \neq 0$. -/
end
namespace ComplexLattice
noncomputable section
open Polynomial Pointwise

end ComplexLattice

namespace ComplexLattice

/--
[latticeMulSet_mul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma latticeMulSet_mul_mem
  {L : ComplexLattice}
  {α β : ℂ}
-- given
  (hα : α ∈ latticeMulSet L L)
  (hβ : β ∈ latticeMulSet L L) :
-- imply
  α * β ∈ latticeMulSet L L := by
-- proof
  intro z hz
  rw [mul_assoc]
  exact hα _ (hβ z hz)

end ComplexLattice

namespace ComplexLattice

/--
[inducedMap_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma inducedMap_mul
  {L : ComplexLattice}
  {α β : ℂ}
-- given
  (hα : α ∈ latticeMulSet L L)
  (hβ : β ∈ latticeMulSet L L) :
-- imply
  ∀ x : torusQuot L, inducedMap L L (α * β) (latticeMulSet_mul_mem L hα hβ) x = inducedMap L L α hα (inducedMap L L β hβ x) := by
-- proof
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L.lattice.toAddSubgroup x
  change inducedMap L L (α * β) _ (proj L z) =
    inducedMap L L α hα (inducedMap L L β hβ (proj L z))
  simp only [inducedMap_proj, mul_assoc]

end ComplexLattice

namespace ComplexLattice

/--
[corollary_16_5_ring_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
lemma corollary_16_5_ring_iso
  {L : ComplexLattice} :
-- imply
  (∀ (φ : ComplexTorusHolMap L L), φ.toFun 0 = 0 → ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L L, ∀ z : ℂ, φ.toFun (proj L z) = inducedMap L L α hα (proj L z)) ∧ (∀ (α γ : ℂ) (hα : α ∈ latticeMulSet L L) (hγ : γ ∈ latticeMulSet L L), (∀ z : ℂ, inducedMap L L α hα (proj L z) = inducedMap L L γ hγ (proj L z)) → α = γ) ∧ (∀ (α β : ℂ) (hα : α ∈ latticeMulSet L L) (hβ : β ∈ latticeMulSet L L), ∀ x : torusQuot L, inducedMap L L (α + β) (latticeMulSet_add_mem L L hα hβ) x = inducedMap L L α hα x + inducedMap L L β hβ x) ∧ (∀ (α β : ℂ) (hα : α ∈ latticeMulSet L L) (hβ : β ∈ latticeMulSet L L), ∀ x : torusQuot L, inducedMap L L (α * β) (latticeMulSet_mul_mem L hα hβ) x = inducedMap L L α hα (inducedMap L L β hβ x)) := by
-- proof
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (corollary_16_2 L L).1
  · exact (corollary_16_2 L L).2.1
  · exact (corollary_16_2 L L).2.2
  · exact fun α β hα hβ => inducedMap_mul L α β hα hβ
/-- The *Rosati involution* on $\mathrm{End}(\mathbb{C}/L)$: for any
endomorphism multiplier $\alpha$, the complex conjugate
$\overline{\alpha}$ is also an endomorphism multiplier. -/
end


/--
[mem_endomorphismRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma mem_endomorphismRing_eq
  {L : ComplexLattice}
  {α : ℂ} :
-- imply
  α ∈ L.endomorphismRing ↔ ∀ z ∈ L.toAddSubgroup, α * z ∈ L.toAddSubgroup := by
-- proof
  apply ComplexLattice.mem_endomorphismRing

/--
[IsEquivalent.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma refl_eq
  {𝒪 : Subring ℂ}
  {L : ComplexLattice} :
-- imply
  IsEquivalent 𝒪 L L := by
-- proof
  apply ComplexLattice.IsEquivalent.refl 𝒪 L

/--
[IsEquivalent.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma symm_eq
  {𝒪 : Subring ℂ}
  {L₁ L₂ : ComplexLattice}
-- given
  (h : IsEquivalent 𝒪 L₁ L₂) :
-- imply
  IsEquivalent 𝒪 L₂ L₁ := by
-- proof
  apply ComplexLattice.IsEquivalent.symm h

/--
[IsEquivalent.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma trans_eq
  {𝒪 : Subring ℂ}
  {L₁ L₂ L₃ : ComplexLattice}
-- given
  (h₁₂ : IsEquivalent 𝒪 L₁ L₂)
  (h₂₃ : IsEquivalent 𝒪 L₂ L₃) :
-- imply
  IsEquivalent 𝒪 L₁ L₃ := by
-- proof
  apply ComplexLattice.IsEquivalent.trans h₁₂ h₂₃

/--
[isEquivalent_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma isEquivalent_equivalence_eq
  {𝒪 : Subring ℂ} :
-- imply
  Equivalence (IsEquivalent 𝒪) := by
-- proof
  apply ComplexLattice.isEquivalent_equivalence 𝒪

/--
[IsEquivalent.isHomothetic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma isHomothetic_eq
  {𝒪 : Subring ℂ}
  {L₁ L₂ : ComplexLattice}
-- given
  (h : IsEquivalent 𝒪 L₁ L₂) :
-- imply
  IsHomothetic L₁ L₂ := by
-- proof
  apply ComplexLattice.IsEquivalent.isHomothetic h

/--
[lattice_subset_of_isImagQuadOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma lattice_subset_of_isImagQuadOrder_eq
  {𝒪 : Subring ℂ}
  {L : ProperIdeal 𝒪}
  {z : ℂ}
-- given
  (h𝒪 : IsImagQuadOrder 𝒪)
  (hz : z ∈ L.val.toAddSubgroup) :
-- imply
  z ∈ 𝒪 := by
-- proof
  apply ComplexLattice.lattice_subset_of_isImagQuadOrder 𝒪 h𝒪 L z hz

/--
[omega1_mem_of_isImagQuadOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma omega1_mem_of_isImagQuadOrder_eq
  {𝒪 : Subring ℂ}
  {L : ProperIdeal 𝒪}
-- given
  (h𝒪 : IsImagQuadOrder 𝒪) :
-- imply
  L.val.ω₁ ∈ 𝒪 := by
-- proof
  apply ComplexLattice.omega1_mem_of_isImagQuadOrder 𝒪 h𝒪 L

/--
[lambda_omega1_mem_of_isImagQuadOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma lambda_omega1_mem_of_isImagQuadOrder_eq
  {𝒪 : Subring ℂ}
  {L₁ L₂ : ProperIdeal 𝒪}
  {c : ℂ}
-- given
  (h𝒪 : IsImagQuadOrder 𝒪)
  (hc : c ≠ 0)
  (hL : (L₂.val.lattice : Set ℂ) = c • (L₁.val.lattice : Set ℂ)) :
-- imply
  c * L₁.val.ω₁ ∈ 𝒪 := by
-- proof
  apply ComplexLattice.lambda_omega1_mem_of_isImagQuadOrder 𝒪 h𝒪 L₁ L₂ c hc hL

/--
[isEquivalent_of_isHomothetic_properIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma isEquivalent_of_isHomothetic_properIdeal_eq
  {𝒪 : Subring ℂ}
  {L₁ L₂ : ProperIdeal 𝒪}
-- given
  (h𝒪 : IsImagQuadOrder 𝒪)
  (h : IsHomothetic L₁.val L₂.val) :
-- imply
  IsEquivalent 𝒪 L₁.val L₂.val := by
-- proof
  apply ComplexLattice.isEquivalent_of_isHomothetic_properIdeal 𝒪 h𝒪 L₁ L₂ h

/--
[isEquivalent_iff_isHomothetic_properIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma isEquivalent_iff_isHomothetic_properIdeal_eq
  {𝒪 : Subring ℂ}
  {L₁ L₂ : ProperIdeal 𝒪}
-- given
  (h𝒪 : IsImagQuadOrder 𝒪) :
-- imply
  IsEquivalent 𝒪 L₁.val L₂.val ↔ IsHomothetic L₁.val L₂.val := by
-- proof
  apply ComplexLattice.isEquivalent_iff_isHomothetic_properIdeal 𝒪 h𝒪 L₁ L₂

/--
[latticeMulSet_zero_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma latticeMulSet_zero_mem_eq
  {L₁ L₂ : ComplexLattice} :
-- imply
  (0 : ℂ) ∈ latticeMulSet L₁ L₂ := by
-- proof
  apply ComplexLattice.latticeMulSet_zero_mem L₁ L₂

/--
[latticeMulSet_add_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma latticeMulSet_add_mem_eq
  {L₁ L₂ : ComplexLattice}
  {α β : ℂ}
-- given
  (hα : α ∈ latticeMulSet L₁ L₂)
  (hβ : β ∈ latticeMulSet L₁ L₂) :
-- imply
  α + β ∈ latticeMulSet L₁ L₂ := by
-- proof
  apply ComplexLattice.latticeMulSet_add_mem L₁ L₂ hα hβ

/--
[latticeMulSet_neg_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean)
-/
@[path]
private lemma latticeMulSet_neg_mem_eq
  {L₁ L₂ : ComplexLattice}
  {α : ℂ}
-- given
  (hα : α ∈ latticeMulSet L₁ L₂) :
-- imply
  -α ∈ latticeMulSet L₁ L₂ := by
-- proof
  apply ComplexLattice.latticeMulSet_neg_mem L₁ L₂ hα


-- created on 2026-10-23
