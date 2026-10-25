import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part7
open nonZeroDivisors Module FieldNormTrace QuadraticOrder ImaginaryQuadraticDiscriminant FractionalOIdeal NormTrace PrincipalIdealNorm IdealNormMultiplicativity FractionalIdealNorm ComplexLattice ImagQuadDiscriminant ProperIdealInvertible IdealClassGroup IdealTorsion CMTorsorAction CMIdealIsogeny
open FractionalIdeal
open NormTrace
open NormTrace NumberField
open scoped NumberField
open scoped Pointwise
open Module
open Pointwise
open FractionalIdeal nonZeroDivisors
open QuadraticOrder ImaginaryQuadraticDiscriminant
open nonZeroDivisors FractionalIdeal
open ProperIdealInvertible
open ComplexLattice
open IdealTorsion NormTrace
open CMTorsorAction NormTrace


namespace FieldNormTrace

/--
[norm_eq_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma norm_eq_sq
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  α.norm = α.re ^ 2 - D * α.im ^ 2 := by
-- proof
  simp only [Zsqrtd.norm_def, sq]; ring

end FieldNormTrace

namespace FieldNormTrace

/--
[norm_eq_mul_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma norm_eq_mul_conj
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  (α.norm : ℤ√D) = α * star α :=
-- proof
  Zsqrtd.norm_eq_mul_conj α

end FieldNormTrace

namespace FieldNormTrace

/--
[trace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma trace_eq
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  α + star α = ↑(2 * α.re) := by
-- proof
  ext <;> simp [Zsqrtd.re_star, Zsqrtd.im_star, two_mul]

end FieldNormTrace

namespace FieldNormTrace

/--
[trace_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma trace_re
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  (α + star α).re = 2 * α.re := by
-- proof
  simp [Zsqrtd.re_add, Zsqrtd.re_star, two_mul]

end FieldNormTrace

namespace FieldNormTrace

/--
[trace_im](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma trace_im
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  (α + star α).im = 0 := by
-- proof
  simp [Zsqrtd.im_add, Zsqrtd.im_star]

end FieldNormTrace

namespace FieldNormTrace

/--
[conj_eq_trace_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma conj_eq_trace_sub
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  star α = ↑(2 * α.re) - α := by
-- proof
  ext <;> simp [Zsqrtd.re_star, Zsqrtd.im_star, two_mul]

end FieldNormTrace

namespace FieldNormTrace

/--
[mul_star_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma mul_star_re
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  (α * star α).re = α.re ^ 2 - D * α.im ^ 2 := by
-- proof
  simp [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star, sq]; ring

end FieldNormTrace

namespace FieldNormTrace

/--
[mul_star_im](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma mul_star_im
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  (α * star α).im = 0 := by
-- proof
  simp [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring

end FieldNormTrace

namespace FieldNormTrace

/--
[norm_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma norm_mul
  {D : ℤ}
  {α β : ℤ√D} :
-- imply
  (α * β).norm = α.norm * β.norm :=
-- proof
  Zsqrtd.norm_mul α β

end FieldNormTrace

namespace FieldNormTrace

/--
[norm_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma norm_conj
  {D : ℤ}
  {α : ℤ√D} :
-- imply
  (star α).norm = α.norm :=
-- proof
  Zsqrtd.norm_conj α

end FieldNormTrace

namespace FieldNormTrace

/--
[norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma norm_nonneg
  {D : ℤ}
  {α : ℤ√D}
-- given
  (hD : D ≤ 0) :
-- imply
  0 ≤ α.norm :=
-- proof
  Zsqrtd.norm_nonneg hD α
end FieldNormTrace


namespace QuadraticOrder

/--
[disc_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma disc_def
  {t n : ℤ} :
-- imply
  disc t n = t ^ 2 - 4 * n :=
-- proof
  rfl

end QuadraticOrder

namespace QuadraticOrder

/--
[traceZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma traceZ_eq
  {d : ℤ}
  {τ : ℤ√d} :
-- imply
  traceZ τ = 2 * τ.re :=
-- proof
  rfl

end QuadraticOrder

namespace QuadraticOrder

/--
[discZsqrtd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma discZsqrtd_eq
  {d : ℤ}
  {τ : ℤ√d} :
-- imply
  discZsqrtd τ = 4 * d * τ.im ^ 2 := by
-- proof
  simp only [discZsqrtd, disc, traceZ, Zsqrtd.norm_def]
  ring

end QuadraticOrder

namespace QuadraticOrder

/--
[discZsqrtd_eq_sq_sub_conj_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma discZsqrtd_eq_sq_sub_conj_re
  {d : ℤ}
  {τ : ℤ√d} :
-- imply
  discZsqrtd τ = ((τ - star τ) * (τ - star τ)).re := by
-- proof
  simp only [discZsqrtd, disc, traceZ, Zsqrtd.norm_def,
    Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_mul]
  ring

end QuadraticOrder

namespace QuadraticOrder

/--
[sq_sub_conj_im_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma sq_sub_conj_im_eq_zero
  {d : ℤ}
  {τ : ℤ√d} :
-- imply
  ((τ - star τ) * (τ - star τ)).im = 0 := by
-- proof
  simp only [Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.im_sub, Zsqrtd.re_sub, Zsqrtd.im_mul]
  ring

end QuadraticOrder

namespace QuadraticOrder

/--
[discZsqrtd_eq_trace_sq_sub_four_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma discZsqrtd_eq_trace_sq_sub_four_norm
  {d : ℤ}
  {τ : ℤ√d} :
-- imply
  discZsqrtd τ = (traceZ τ) ^ 2 - 4 * (Zsqrtd.norm τ) := by
-- proof
  simp only [discZsqrtd, disc]

end QuadraticOrder

namespace QuadraticOrder

/--
[discZsqrtd_sqrtd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma discZsqrtd_sqrtd
  {d : ℤ}
  {τ : ℤ√d} :
-- imply
  discZsqrtd (⟨0, 1⟩ : ℤ√d) = 4 * d := by
-- proof
  simp [discZsqrtd_eq]
end QuadraticOrder


namespace ImaginaryQuadraticDiscriminant

/--
[discriminant_decomposition_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma discriminant_decomposition_exists
  {D : ℤ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D) :
-- imply
  ∃ D_K : ℤ, ∃ u : ℤ, u ≥ 1 ∧ IsFundamentalImaginaryQuadraticDiscriminant D_K ∧ D = u ^ 2 * D_K := by
-- proof
  suffices h : ∀ n : ℕ, ∀ D : ℤ, (-D).toNat = n → IsImaginaryQuadraticDiscriminant D →
    ∃ D_K : ℤ, ∃ u : ℤ, u ≥ 1 ∧ IsFundamentalImaginaryQuadraticDiscriminant D_K ∧
      D = u ^ 2 * D_K from
    h _ D rfl hD
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro D hn hD
    by_cases hfund : IsFundamentalImaginaryQuadraticDiscriminant D
    · exact ⟨D, 1, le_refl 1, hfund, by ring⟩
    · unfold IsFundamentalImaginaryQuadraticDiscriminant at hfund
      push Not at hfund
      obtain ⟨u, D', hu, hD', heq⟩ := hfund hD
      have hD'neg : D' < 0 := hD'.1
      have hDneg : D < 0 := hD.1
      have hlt : (-D').toNat < n := by
        rw [← hn]
        have hu2ge : u ^ 2 ≥ 4 := by nlinarith
        have key : -D' < -D := by nlinarith
        omega
      obtain ⟨D_K, v, hv, hfundK, heq'⟩ := ih _ hlt D' rfl hD'
      refine ⟨D_K, u * v, ?_, hfundK, ?_⟩
      · nlinarith
      · rw [heq, heq']; ring
/-- Uniqueness of the decomposition `D = u² · D_K`: the conductor `u` and fundamental
discriminant `D_K` are uniquely determined by `D`. -/
end ImaginaryQuadraticDiscriminant
open nonZeroDivisors


namespace FractionalOIdeal

/--
[mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma mul_eq
  [CommRing R]
  [IsDomain R]
  [Field K]
  {l l' : K}
  {a a' : Ideal R} :
-- imply
  (spanSingleton R⁰ l * (a : FractionalIdeal R⁰ K)) * (spanSingleton R⁰ l' * (a' : FractionalIdeal R⁰ K)) = spanSingleton R⁰ (l * l') * ((a * a' : Ideal R) : FractionalIdeal R⁰ K) := by
-- proof
  rw [coeIdeal_mul, ← spanSingleton_mul_spanSingleton]
  ring
end FractionalOIdeal


namespace NormTrace

/--
[idealNorm_eq_card_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_eq_card_quotient
  [CommRing 𝒪]
  {𝔞 : Ideal 𝒪} :
-- imply
  idealNorm 𝔞 = Nat.card (𝒪 ⧸ 𝔞) :=
-- proof
  Submodule.cardQuot_apply 𝔞

end NormTrace

namespace NormTrace

/--
[idealNorm_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_top
  [CommRing 𝒪] :
-- imply
  idealNorm (⊤ : Ideal 𝒪) = 1 :=
-- proof
  Submodule.cardQuot_top 𝒪 𝒪

end NormTrace

namespace NormTrace

/--
[idealNorm_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_bot
  [CommRing 𝒪]
  [Infinite 𝒪] :
-- imply
  idealNorm (⊥ : Ideal 𝒪) = 0 :=
-- proof
  Submodule.cardQuot_bot 𝒪 𝒪

end NormTrace

namespace NormTrace

/--
[idealNorm_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_pos
  [CommRing 𝒪]
  [CommRing 𝒪]
  [IsDomain 𝒪]
  [Module.Free ℤ 𝒪]
  [Module.Finite ℤ 𝒪]
  {𝔞 : Ideal 𝒪}
-- given
  (h : 𝔞 ≠ ⊥) :
-- imply
  0 < idealNorm 𝔞 := by
-- proof
  rw [idealNorm, Submodule.cardQuot_apply, Nat.pos_iff_ne_zero, Nat.card_ne_zero]
  exact ⟨⟨Ideal.Quotient.mk 𝔞 0⟩, Ideal.finiteQuotientOfFreeOfNeBot 𝔞 h⟩

end NormTrace

namespace NormTrace

/--
[idealNorm_eq_absNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_eq_absNorm
  [CommRing 𝒪]
  [CommRing 𝒪]
  [Nontrivial 𝒪]
  [IsDedekindDomain 𝒪]
  [Module.Free ℤ 𝒪]
  {𝔞 : Ideal 𝒪} :
-- imply
  Ideal.absNorm 𝔞 = idealNorm 𝔞 :=
-- proof
  Ideal.absNorm_apply 𝔞
end NormTrace
namespace PrincipalIdealNorm
open NormTrace
variable {𝒪 : Type*} [CommRing 𝒪] [IsDedekindDomain 𝒪]
  [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪]


namespace PrincipalIdealNorm

/--
[idealNorm_span_singleton_eq_natAbs_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_span_singleton_eq_natAbs_norm
  [CommRing 𝒪]
  [IsDedekindDomain 𝒪]
  {α : 𝒪} :
-- imply
  idealNorm (Ideal.span {α}) = (Algebra.norm ℤ α).natAbs := by
-- proof
  rw [idealNorm, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]

end PrincipalIdealNorm

namespace PrincipalIdealNorm

/--
[idealNorm_span_singleton_eq_abs_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_span_singleton_eq_abs_norm
  [CommRing 𝒪]
  [IsDedekindDomain 𝒪]
  {α : 𝒪} :
-- imply
  (idealNorm (Ideal.span {α}) : ℤ) = := by
-- proof
  rw [idealNorm_span_singleton_eq_natAbs_norm]
  simp
end PrincipalIdealNorm
namespace PrincipalIdealNorm
open NormTrace NumberField
open scoped NumberField

end PrincipalIdealNorm

namespace PrincipalIdealNorm

/--
[idealNorm_principal_ringOfIntegers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_principal_ringOfIntegers
  {K : Type*}
  [Field K]
  [NumberField K]
  {α : 𝓞 K} :
-- imply
  Ideal.absNorm (Ideal.span {α}) = (Algebra.norm ℤ α).natAbs :=
-- proof
  Ideal.absNorm_span_singleton α
end PrincipalIdealNorm
namespace IdealNormMultiplicativity
open NormTrace
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
  [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪]


namespace IdealNormMultiplicativity

/--
[mem_span_singleton_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma mem_span_singleton_mul
  [CommRing 𝒪]
  [IsDomain 𝒪]
  {α : 𝒪}
  {𝔞 : Ideal 𝒪}
  {z : 𝒪}
-- given
  (hz : z ∈ Ideal.span {α} * 𝔞) :
-- imply
  ∃ w ∈ 𝔞, z = α * w := by
-- proof
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨r, rfl⟩ := ha
    exact ⟨r * b, 𝔞.mul_mem_left r hb, by ring⟩
  · rintro _ _ ⟨wx, hwx_mem, rfl⟩ ⟨wy, hwy_mem, rfl⟩
    exact ⟨wx + wy, 𝔞.add_mem hwx_mem hwy_mem, by ring⟩

end IdealNormMultiplicativity

namespace IdealNormMultiplicativity

/--
[idealNorm_mul_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_mul_principal
  [CommRing 𝒪]
  [IsDomain 𝒪]
  {α : 𝒪}
  {𝔞 : Ideal 𝒪} :
-- imply
  idealNorm (Ideal.span {α} * 𝔞) = idealNorm (Ideal.span {α}) * idealNorm 𝔞 := by
-- proof
  by_cases hα : α = 0
  · subst hα
    haveI : Infinite 𝒪 := Module.Free.infinite ℤ 𝒪
    have h0 : Ideal.span {(0 : 𝒪)} = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
    rw [h0, Ideal.bot_mul, idealNorm_bot, zero_mul]
  have hle : (Ideal.span {α} * 𝔞 : Ideal 𝒪) ≤ Ideal.span {α} :=
    (Ideal.mul_mono_right le_top).trans (Ideal.mul_top _).le
  have htower := Submodule.card_quotient_mul_card_quotient
    (Ideal.span {α} : Submodule 𝒪 𝒪) (↑(Ideal.span {α} * 𝔞)) hle
  simp only [idealNorm, Submodule.cardQuot_apply]
  rw [← htower, mul_comm]
  congr 1
  set P := Submodule.map (↑(Ideal.span {α} * 𝔞) : Submodule 𝒪 𝒪).mkQ
    (↑(Ideal.span {α}) : Submodule 𝒪 𝒪)
  have hmem : ∀ x : 𝒪, α * x ∈ (Ideal.span {α} : Submodule 𝒪 𝒪) :=
    fun x => Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self α)
  symm; apply Nat.card_congr
  let f : 𝒪 → P := fun x => ⟨Submodule.Quotient.mk (α * x), ⟨α * x, hmem x, rfl⟩⟩
  have hf : ∀ a b : 𝒪, a - b ∈ (𝔞 : Submodule 𝒪 𝒪) → f a = f b := by
    intro a b hab
    apply Subtype.ext
    show Submodule.Quotient.mk (α * a) = Submodule.Quotient.mk (α * b)
    rw [Submodule.Quotient.eq]
    show α * a - α * b ∈ (↑(Ideal.span {α} * 𝔞) : Submodule 𝒪 𝒪)
    rw [show α * a - α * b = α * (a - b) from by ring]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self α) hab
  let F : 𝒪 ⧸ (𝔞 : Submodule 𝒪 𝒪) → P :=
    Quotient.lift f (fun a b h => hf a b ((Submodule.quotientRel_def (p := 𝔞)).mp h))
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  ·
    intro a b hab
    induction a using Quotient.inductionOn with | _ a => ?_
    induction b using Quotient.inductionOn with | _ b => ?_
    show Quotient.mk _ a = Quotient.mk _ b
    rw [Quotient.eq]
    show (𝔞 : Submodule 𝒪 𝒪).quotientRel a b
    rw [Submodule.quotientRel_def]
    change f a = f b at hab
    have h2 := congr_arg Subtype.val hab
    simp only [f] at h2
    rw [Submodule.Quotient.eq] at h2
    change α * a - α * b ∈ (Ideal.span {α} * 𝔞 : Ideal 𝒪) at h2
    rw [show α * a - α * b = α * (a - b) from by ring] at h2
    obtain ⟨w, hw_mem, hw_eq⟩ := mem_span_singleton_mul h2
    exact (mul_left_cancel₀ hα hw_eq).symm ▸ hw_mem
  ·
    rintro ⟨q, hq⟩
    obtain ⟨y, hy_mem, hy_eq⟩ := hq
    have hy_mem' : y ∈ Ideal.span {α} := hy_mem
    rw [Ideal.mem_span_singleton'] at hy_mem'
    obtain ⟨c, rfl⟩ := hy_mem'
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    show f c = ⟨q, _⟩
    apply Subtype.ext
    show Submodule.Quotient.mk (α * c) = q
    rwa [show α * c = c * α from mul_comm α c]

end IdealNormMultiplicativity

namespace IdealNormMultiplicativity

/--
[idealNorm_smul_eq_natAbs_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealNorm_smul_eq_natAbs_mul
  [CommRing 𝒪]
  [IsDomain 𝒪]
  [IsDedekindDomain 𝒪]
  {α : 𝒪}
  {𝔞 : Ideal 𝒪} :
-- imply
  idealNorm (Ideal.span {α} * 𝔞) = (Algebra.norm ℤ α).natAbs * idealNorm 𝔞 := by
-- proof
  rw [idealNorm_mul_principal]
  congr 1
  simp only [idealNorm, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
end IdealNormMultiplicativity
open scoped Pointwise
namespace FractionalIdealNorm
variable {𝒪 : Type*} [CommRing 𝒪] [IsDedekindDomain 𝒪] [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪]
variable {K : Type*} [CommRing K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
open nonZeroDivisors

end IdealNormMultiplicativity

namespace FractionalIdealNorm

/--
[fractionalIdealNorm_eq_absNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma fractionalIdealNorm_eq_absNorm
  [CommRing 𝒪]
  [IsDedekindDomain 𝒪]
  [Module.Free ℤ 𝒪]
  [Module.Finite ℤ 𝒪]
  [CommRing K]
  [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]
  {𝔟 : FractionalIdeal 𝒪⁰ K} :
-- imply
  fractionalIdealNorm 𝔟 = FractionalIdeal.absNorm 𝔟 :=
-- proof
  (FractionalIdeal.absNorm_eq 𝔟).symm

end FractionalIdealNorm

namespace FractionalIdealNorm

/--
[fractionalIdealNorm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma fractionalIdealNorm_eq
  [CommRing 𝒪]
  [IsDedekindDomain 𝒪]
  [Module.Free ℤ 𝒪]
  [Module.Finite ℤ 𝒪]
  [CommRing K]
  [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]
  {𝔟 : FractionalIdeal 𝒪⁰ K} :
-- imply
  fractionalIdealNorm 𝔟 = (Ideal.absNorm 𝔟.num : ℚ) / :=
-- proof
  rfl
end FractionalIdealNorm
open Module
noncomputable section


/--
[nsmul_mem_of_card_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma nsmul_mem_of_card_quotient
  [AddCommGroup M]
  [Module ℤ M]
  {N : Submodule ℤ M}
  {x : M} :
-- imply
  (Nat.card (M ⧸ N)) • x ∈ N := by
-- proof
  rw [← Submodule.Quotient.mk_eq_zero]
  show N.mkQ ((Nat.card (M ⧸ N)) • x) = 0
  rwa [map_nsmul]

/--
[zsmul_mem_of_card_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma zsmul_mem_of_card_quotient
  [AddCommGroup M]
  [Module ℤ M]
  {N : Submodule ℤ M}
  {x : M} :
-- imply
  (Nat.card (M ⧸ N) : ℤ) • x ∈ N := by
-- proof
  rw [natCast_zsmul]
  exact nsmul_mem_of_card_quotient N x

/--
[nsmul_top_eq_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma nsmul_top_eq_pi
  {n : ℤ} :
-- imply
  Submodule.map (n • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ))) ⊤ = Submodule.pi Set.univ (fun _ : Fin 2 => Submodule.span ℤ {n}) := by
-- proof
  ext x
  simp only [Submodule.mem_map, Submodule.mem_top, true_and, LinearMap.smul_apply,
    LinearMap.id_apply, Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact Submodule.mem_span_singleton.mpr ⟨y i, mul_comm (y i) n⟩
  · intro h
    choose c hc using fun i => Submodule.mem_span_singleton.mp (h i)
    refine ⟨c, funext fun i => ?_⟩
    show n * c i = x i
    rw [mul_comm]; exact hc i

/--
[nat_card_int_quotient_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma nat_card_int_quotient_span
  {n : ℕ} :
-- imply
  Nat.card (ℤ ⧸ Submodule.span ℤ {(n : ℤ)}) = n := by
-- proof
  change Nat.card (ℤ ⧸ Ideal.span {(n : ℤ)}) = n
  rw [Nat.card_congr (Int.quotientSpanEquivZMod (n : ℤ)).toEquiv]
  simp [Int.natAbs_natCast, Nat.card_zmod]

/--
[nat_card_quotient_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma nat_card_quotient_nsmul
  {n : ℕ} :
-- imply
  Nat.card ((Fin 2 → ℤ) ⧸ (Submodule.map ((n : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] _)) ⊤)) = n ^ 2 := by
-- proof
  rw [nsmul_top_eq_pi]
  rw [Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi]
  simp only [nat_card_int_quotient_span, Finset.prod_const, Finset.card_fin]

/--
[nsmul_le_of_card_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma nsmul_le_of_card_quotient
  {N : Submodule ℤ (Fin 2 → ℤ)}
  {n : ℕ}
-- given
  (hindex : Nat.card ((Fin 2 → ℤ) ⧸ N) = n) :
-- imply
  Submodule.map ((n : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] _)) ⊤ ≤ N := by
-- proof
  intro x hx
  obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
  show (n : ℤ) • y ∈ N
  rw [← hindex]
  exact zsmul_mem_of_card_quotient N y

/--
[sublattice_index_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma sublattice_index_nsmul
  {N : Submodule ℤ (Fin 2 → ℤ)}
  {n : ℕ}
-- given
  (hn : 0 < n)
  (hindex : Nat.card ((Fin 2 → ℤ) ⧸ N) = n) :
-- imply
  Nat.card ↥(Submodule.map (Submodule.map ((n : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] _)) ⊤).mkQ N) = n := by
-- proof
  set nM := Submodule.map ((n : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] _)) ⊤
  have hle : nM ≤ N := nsmul_le_of_card_quotient N n hindex
  have htower := Submodule.card_quotient_mul_card_quotient N nM hle
  rw [hindex, nat_card_quotient_nsmul] at htower
  have hn' : n ≠ 0 := by omega
  have : Nat.card ↥(Submodule.map nM.mkQ N) * n = n * n := by rw [htower]; ring
  exact mul_right_cancel₀ hn' this
end
namespace ComplexLattice
open Pointwise

namespace ComplexLattice

/--
[endomorphismRing_eq_of_homothetic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma endomorphismRing_eq_of_homothetic
  {L L' : ComplexLattice}
-- given
  (h : IsHomothetic L L') :
-- imply
  L'.endomorphismRing = L.endomorphismRing := by
-- proof
  obtain ⟨c, hc, hcL⟩ := h
  ext α
  simp only [Subring.mem_mk, endomorphismRing]
  constructor
  ·
    intro hα z hz
    have hcz : c * z ∈ L'.lattice.toAddSubgroup := by
      show c • z ∈ (L'.lattice : Set ℂ)
      rw [hcL]
      exact Set.smul_mem_smul_set hz
    have hacv := hα (c * z) hcz
    rw [show α * (c * z) = c * (α * z) from by ring] at hacv
    change c • (α * z) ∈ (L'.lattice : Set ℂ) at hacv
    rw [hcL, Set.mem_smul_set_iff_inv_smul_mem₀ hc] at hacv
    simpa only [smul_eq_mul, inv_mul_cancel_left₀ hc] using hacv
  ·
    intro hα z hz
    have hz' : z ∈ (L'.lattice : Set ℂ) := hz
    rw [hcL, Set.mem_smul_set] at hz'
    obtain ⟨w, hw, rfl⟩ := hz'
    show α * (c • w) ∈ (L'.lattice : Set ℂ)
    rw [hcL]
    simp only [smul_eq_mul]
    rw [show α * (c * w) = c * (α * w) from by ring]
    exact Set.smul_mem_smul_set (hα w hw)

end ComplexLattice

namespace ComplexLattice

/--
[IsProperIdeal.of_homothetic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma IsProperIdeal.of_homothetic
  {𝒪 : Subring ℂ}
  {L L' : ComplexLattice}
-- given
  (hL : IsProperIdeal 𝒪 L)
  (hom : IsHomothetic L L') :
-- imply
  IsProperIdeal 𝒪 L' := by
-- proof
  unfold IsProperIdeal at *
  rw [endomorphismRing_eq_of_homothetic hom, hL]

end ComplexLattice

namespace ComplexLattice

/--
[isProperIdeal_iff_of_homothetic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma isProperIdeal_iff_of_homothetic
  {𝒪 : Subring ℂ}
  {L L' : ComplexLattice}
-- given
  (hom : IsHomothetic L L') :
-- imply
  IsProperIdeal 𝒪 L ↔ IsProperIdeal 𝒪 L' :=
-- proof
  ⟨fun h => h.of_homothetic hom, fun h => h.of_homothetic hom.symm⟩
end ComplexLattice
namespace FractionalOIdeal
variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]
open FractionalIdeal nonZeroDivisors
end FractionalOIdeal
namespace ImagQuadDiscriminant
open QuadraticOrder ImaginaryQuadraticDiscriminant

end ComplexLattice

namespace ImagQuadDiscriminant

/--
[sq_mod_four_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma sq_mod_four_iff
  {t : ℤ} :
-- imply
  (t % 2 = 0 ∧ t ^ 2 % 4 = 0) ∨ (t % 2 = 1 ∧ t ^ 2 % 4 = 1) := by
-- proof
  obtain h | h := (show t % 2 = 0 ∨ t % 2 = 1 by omega)
  · left; exact ⟨h, by
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h; subst hk; ring_nf; omega⟩
  · right; refine ⟨h, ?_⟩
    have ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (show (t - 1) % 2 = 0 by omega)
    have : t = 2 * k + 1 := by omega
    subst this; ring_nf; omega

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[mod_two_eq_of_sq_mod_four_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma mod_two_eq_of_sq_mod_four_eq
  {t₁ t₂ : ℤ}
-- given
  (h : t₁ ^ 2 % 4 = t₂ ^ 2 % 4) :
-- imply
  t₁ % 2 = t₂ % 2 := by
-- proof
  obtain ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;> := sq_mod_four_iff t₁
  obtain ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;> := sq_mod_four_iff t₂
  omega

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[trace_parity_eq_of_disc_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma trace_parity_eq_of_disc_eq
  {t₁ n₁ t₂ n₂ : ℤ}
-- given
  (heq : t₁ ^ 2 - 4 * n₁ = t₂ ^ 2 - 4 * n₂) :
-- imply
  t₁ % 2 = t₂ % 2 :=
-- proof
  mod_two_eq_of_sq_mod_four_eq (by omega)

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma existence
  {D : ℤ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D) :
-- imply
  ∃ 𝒪 : ImaginaryQuadraticOrder, 𝒪.discriminant = D := by
-- proof
  obtain ⟨hlt, hmod⟩ := hD
  obtain h0 | h1 := hmod
  ·
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
    exact ⟨⟨0, -k, by omega, Or.inl (by omega)⟩, by
      simp [ImaginaryQuadraticOrder.discriminant]; omega⟩
  ·
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (show (1 - D) % 4 = 0 by omega)
    exact ⟨⟨1, k, by omega, Or.inr (by omega)⟩, by
      simp [ImaginaryQuadraticOrder.discriminant]; omega⟩

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma uniqueness
  {𝒪₁ 𝒪₂ : ImaginaryQuadraticOrder}
-- given
  (hD : 𝒪₁.discriminant = 𝒪₂.discriminant) :
-- imply
  𝒪₁.SameOrder 𝒪₂ :=
-- proof
  ⟨hD, trace_parity_eq_of_disc_eq (by
    simp only [ImaginaryQuadraticOrder.discriminant] at hD; exact hD)⟩

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[orderFromDecomposition_disc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma orderFromDecomposition_disc
  {D : ℤ}
  {dec : ImaginaryQuadraticDiscriminantDecomposition D} :
-- imply
  (orderFromDecomposition dec).discriminant = D := by
-- proof
  simp only [orderFromDecomposition, ImaginaryQuadraticOrder.discriminant]
  obtain h0 | h1 := dec.hD_K.1.2
  · simp only [h0, ↑reduceIte]
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
    have hk_eq : dec.D_K / 4 = k := by omega
    rw [hk_eq]
    nlinarith [dec.hD, hk]
  · have h0f : ¬(dec.D_K % 4 = 0) := by omega
    simp only [h0f, ↑reduceIte]
    obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (dec.D_K - 1) % 4 = 0 by omega)
    have hm_eq : (dec.D_K - 1) / 4 = m := by omega
    rw [hm_eq]
    nlinarith [dec.hD]

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[maximalOrder_disc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma maximalOrder_disc
  {D_K : ℤ}
-- given
  (hfund : IsFundamentalImaginaryQuadraticDiscriminant D_K) :
-- imply
  (maximalOrder D_K hfund).discriminant = D_K := by
-- proof
  simp only [maximalOrder, ImaginaryQuadraticOrder.discriminant]
  obtain h0 | h1 := hfund.1.2
  · simp only [h0, ↑reduceIte]
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
    have : D_K / 4 = k := by omega
    rw [this]; nlinarith [hk]
  · have h0f : ¬(D_K % 4 = 0) := by omega
    simp only [h0f, ↑reduceIte]
    obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (D_K - 1) % 4 = 0 by omega)
    have : (D_K - 1) / 4 = m := by omega
    rw [this]; nlinarith

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[conductor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma conductor_eq
  {D : ℤ}
  {dec : ImaginaryQuadraticDiscriminantDecomposition D} :
-- imply
  (orderFromDecomposition dec).discriminant = dec.u ^ 2 * (maximalOrder dec.D_K dec.hD_K).discriminant := by
-- proof
  rwa [orderFromDecomposition_disc, maximalOrder_disc]

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[exists_unique_order](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma exists_unique_order
  {D : ℤ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D) :
-- imply
  ∃ (u D_K : ℤ), u ≥ 1 ∧ IsFundamentalImaginaryQuadraticDiscriminant D_K ∧ D = u ^ 2 * D_K ∧ ∃ (𝒪_K : ImaginaryQuadraticOrder), 𝒪_K.discriminant = D_K ∧ ∃ (𝒪 : ImaginaryQuadraticOrder), 𝒪.discriminant = D ∧ 𝒪.discriminant = u ^ 2 * 𝒪_K.discriminant ∧ (∀ 𝒪' : ImaginaryQuadraticOrder, 𝒪'.discriminant = D → 𝒪.SameOrder 𝒪') := by
-- proof
  obtain ⟨D_K, u, hu, hfund, hdecomp⟩ := discriminant_decomposition_exists D hD
  let dec : ImaginaryQuadraticDiscriminantDecomposition D := ⟨u, D_K, hu, hfund, hdecomp⟩
  refine ⟨u, D_K, hu, hfund, hdecomp, maximalOrder D_K hfund, maximalOrder_disc D_K hfund,
    orderFromDecomposition dec, orderFromDecomposition_disc dec, ?_, fun 𝒪' h𝒪' =>
      uniqueness _ 𝒪' ((orderFromDecomposition_disc dec).trans h𝒪'.symm)⟩
  rwa [orderFromDecomposition_disc dec, maximalOrder_disc]

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[conductor_is_lattice_index](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma conductor_is_lattice_index
  {D : ℤ}
  {dec : ImaginaryQuadraticDiscriminantDecomposition D} :
-- imply
  (orderFromDecomposition dec).IsSuborderOfIndex (maximalOrder dec.D_K dec.hD_K) dec.u := by
-- proof
  refine ⟨dec.hu, by rw [orderFromDecomposition_disc, maximalOrder_disc]; exact dec.hD, ?_⟩
  simp only [orderFromDecomposition, maximalOrder]
  obtain h0 | h1 := dec.hD_K.1.2
  ·
    simp only [h0, ↑reduceIte]
    exact ⟨0, by ring⟩
  ·
    have h0f : ¬(dec.D_K % 4 = 0) := by omega
    simp only [h0f, ↑reduceIte]
    exact ⟨0, by ring⟩

end ImagQuadDiscriminant

namespace ImagQuadDiscriminant

/--
[exists_unique_order_conductor_index](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma exists_unique_order_conductor_index
  {D : ℤ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D) :
-- imply
  ∃ (u D_K : ℤ) (𝒪_K 𝒪 : ImaginaryQuadraticOrder), u ≥ 1 ∧ IsFundamentalImaginaryQuadraticDiscriminant D_K ∧ 𝒪_K.discriminant = D_K ∧ 𝒪.discriminant = D ∧ 𝒪.IsSuborderOfIndex 𝒪_K u ∧ (∀ 𝒪' : ImaginaryQuadraticOrder, 𝒪'.discriminant = D → 𝒪.SameOrder 𝒪') := by
-- proof
  obtain ⟨D_K, u, hu, hfund, hdecomp⟩ := discriminant_decomposition_exists D hD
  let dec : ImaginaryQuadraticDiscriminantDecomposition D := ⟨u, D_K, hu, hfund, hdecomp⟩
  refine ⟨u, D_K, maximalOrder D_K hfund, orderFromDecomposition dec,
    hu, hfund, maximalOrder_disc D_K hfund, orderFromDecomposition_disc dec,
    conductor_is_lattice_index dec, fun 𝒪' h𝒪' =>
      uniqueness _ 𝒪' ((orderFromDecomposition_disc dec).trans h𝒪'.symm)⟩
end ImagQuadDiscriminant
namespace ProperIdealInvertible
open FractionalIdeal
section General
variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]


namespace ProperIdealInvertible

/--
[algebraMap_range_subset_idealOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma algebraMap_range_subset_idealOrder
  [CommRing R]
  [IsDomain R]
  [Field K]
  {I : FractionalIdeal R⁰ K} :
-- imply
  Set.range (algebraMap R K) ⊆ idealOrder I := by
-- proof
  rintro x ⟨r, rfl⟩ y hy
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact Submodule.smul_mem _ r hy

end ProperIdealInvertible

namespace ProperIdealInvertible

/--
[isProper_iff_order_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma isProper_iff_order_subset
  [CommRing R]
  [IsDomain R]
  [Field K]
  {I : FractionalIdeal R⁰ K} :
-- imply
  IsProper I ↔ idealOrder I ⊆ Set.range (algebraMap R K) :=
-- proof
  ⟨fun h => h ▸ le_refl _, fun h => le_antisymm h (algebraMap_range_subset_idealOrder I)⟩
set_option linter.unusedSectionVars false in

end ProperIdealInvertible

namespace ProperIdealInvertible

/--
[idealOrder_mul_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealOrder_mul_unit
  [CommRing R]
  [IsDomain R]
  [Field K]
  {u : (FractionalIdeal R⁰ K)ˣ}
  {I : FractionalIdeal R⁰ K} :
-- imply
  idealOrder ((u : FractionalIdeal R⁰ K) * I) = idealOrder I := by
-- proof
  ext x
  simp only [idealOrder, Set.mem_setOf_eq]
  rw [show (∀ y ∈ ((↑u * I : FractionalIdeal R⁰ K) : Submodule R K),
    x * y ∈ ((↑u * I : FractionalIdeal R⁰ K) : Submodule R K)) ↔
    spanSingleton R⁰ x * (↑u * I) ≤ ↑u * I
    from spanSingleton_mul_le_iff.symm]
  rw [show (∀ y ∈ (I : Submodule R K), x * y ∈ (I : Submodule R K)) ↔
    spanSingleton R⁰ x * I ≤ I
    from spanSingleton_mul_le_iff.symm]
  constructor
  · intro h
    have hcomm : spanSingleton R⁰ x * (↑u * I) = ↑u * (spanSingleton R⁰ x * I) := by ring
    rw [hcomm] at h
    have h1 : ↑u⁻¹ * (↑u * (spanSingleton R⁰ x * I)) ≤ ↑u⁻¹ * (↑u * I) :=
      mul_le_mul_of_nonneg_left h (FractionalIdeal.zero_le _)
    simp only [← mul_assoc] at h1
    have h2 : (↑u⁻¹ : FractionalIdeal R⁰ K) * ↑u = 1 := by exact_mod_cast u.inv_mul
    rwa [h2, one_mul, one_mul] at h1
  · intro h
    have hcomm : spanSingleton R⁰ x * (↑u * I) = ↑u * (spanSingleton R⁰ x * I) := by ring
    rw [hcomm]
    exact mul_le_mul_of_nonneg_left h (FractionalIdeal.zero_le _)
set_option linter.unusedSectionVars false in

end ProperIdealInvertible

namespace ProperIdealInvertible

/--
[isProper_mul_unit_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma isProper_mul_unit_iff
  [CommRing R]
  [IsDomain R]
  [Field K]
  {u : (FractionalIdeal R⁰ K)ˣ}
  {I : FractionalIdeal R⁰ K} :
-- imply
  IsProper ((u : FractionalIdeal R⁰ K) * I) ↔ IsProper I := by
-- proof
  unfold IsProper
  rw [idealOrder_mul_unit]

end ProperIdealInvertible

namespace ProperIdealInvertible

/--
[isProper_of_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma isProper_of_isUnit
  [CommRing R]
  [IsDomain R]
  [Field K]
  {I : FractionalIdeal R⁰ K}
-- given
  (hI : IsUnit I) :
-- imply
  IsProper I := by
-- proof
  rw [isProper_iff_order_subset]
  intro x hx
  obtain ⟨u, rfl⟩ := hI
  have h1 : spanSingleton R⁰ x * ↑u ≤ ↑u := by
    rw [FractionalIdeal.mul_le]
    intro a ha b hb
    rw [FractionalIdeal.mem_spanSingleton] at ha
    obtain ⟨c, rfl⟩ := ha
    exact (Algebra.smul_mul_assoc c x b) ▸ Submodule.smul_mem _ c (hx b hb)
  have h2 : spanSingleton R⁰ x * ↑u * ↑u⁻¹ ≤ ↑u * ↑u⁻¹ :=
    mul_le_mul_of_nonneg_right h1 (FractionalIdeal.zero_le _)
  rw [mul_assoc, u.mul_inv, mul_one] at h2
  rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff] at h2
  exact h2.elim (fun r hr => ⟨r, hr⟩)
end General
section Quadratic

end ProperIdealInvertible

namespace ProperIdealInvertible

/--
[mem_conjIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma mem_conjIdeal
  {d : ℤ}
  {I : Ideal (ℤ√d)}
  {x : ℤ√d}
-- given
  (hx : x ∈ I) :
-- imply
  star x ∈ conjIdeal I :=
-- proof
  Ideal.mem_map_of_mem _ hx

end ProperIdealInvertible

namespace ProperIdealInvertible

/--
[conjIdeal_conjIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma conjIdeal_conjIdeal
  {d : ℤ}
  {I : Ideal (ℤ√d)} :
-- imply
  conjIdeal (conjIdeal I) = I := by
-- proof
  simp only [conjIdeal, Ideal.map_map]
  have : (starRingEnd (ℤ√d)).comp (starRingEnd (ℤ√d)) = RingHom.id _ := by ext <;> simp
  rw [this, Ideal.map_id]

end ProperIdealInvertible

namespace ProperIdealInvertible

/--
[isUnit_coeIdeal_of_mul_eq_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma isUnit_coeIdeal_of_mul_eq_span
  {d : ℤ}
  [IsDomain (ℤ√d)]
  {K' : Type*}
  [Field K']
  [Algebra (ℤ√d) K']
  [IsFractionRing (ℤ√d) K']
  {J J' : Ideal (ℤ√d)}
  {n : ℤ√d}
-- given
  (hn : n ≠ 0)
  (h : J * J' = Ideal.span {n}) :
-- imply
  IsUnit ((J : FractionalIdeal (ℤ√d)⁰ K')) := by
-- proof
  have h1 : (J : FractionalIdeal (ℤ√d)⁰ K') * ↑J' =
    spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n) := by
    rw [← coeIdeal_mul, h, coeIdeal_span_singleton]
  have hn' : (algebraMap (ℤ√d) K') n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (ℤ√d) K')).mpr hn
  set inv := spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n)⁻¹ *
    (↑J' : FractionalIdeal (ℤ√d)⁰ K')
  have h2 : (J : FractionalIdeal (ℤ√d)⁰ K') * inv = 1 := by
    calc (J : FractionalIdeal (ℤ√d)⁰ K') * inv
      = (↑J : FractionalIdeal (ℤ√d)⁰ K') * ↑J' *
        spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n)⁻¹ := by ring
      _ = spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n) *
        spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n)⁻¹ := by rw [h1]
      _ = 1 := by
        rw [spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hn', spanSingleton_one]
  have h3 : inv * (J : FractionalIdeal (ℤ√d)⁰ K') = 1 := by rw [mul_comm]; exact h2
  exact ⟨⟨↑J, inv, h2, h3⟩, rfl⟩

end ProperIdealInvertible

namespace IdealClassGroup

/--
[isProper_of_isUnit_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma isProper_of_isUnit_quadratic
  {d : ℤ}
  [CommRing R]
  [IsDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I : FractionalIdeal R⁰ K}
-- given
  (hI : IsUnit I) :
-- imply
  IsProper I :=
-- proof
  isProper_of_isUnit I hI

end IdealClassGroup

namespace IdealClassGroup

/--
[cl_is_commGroup_imagQuad](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma cl_is_commGroup_imagQuad
  {𝒪 : Subring ℂ}
  [IsDomain 𝒪]
-- given
  (h𝒪 : IsImagQuadOrder 𝒪) :
-- imply
  Nonempty (CommGroup (ComplexLattice.IdealClassGroup 𝒪)) :=
-- proof
  ⟨IdealClassGroup.commGroup 𝒪⟩

end IdealClassGroup

namespace IdealTorsion

/--
[mem_idealTorsion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma mem_idealTorsion_iff
  [CommRing 𝒪]
  [AddCommGroup E]
  [Module 𝒪 E]
  {𝔞 : Ideal 𝒪}
  {P : E} :
-- imply
  P ∈ idealTorsion 𝔞 ↔ ∀ α ∈ 𝔞, α • P = 0 :=
-- proof
  Iff.rfl

end IdealTorsion

namespace IdealTorsion

/--
[idealTorsion_eq_torsionBySet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma idealTorsion_eq_torsionBySet
  [CommRing 𝒪]
  [AddCommGroup E]
  [Module 𝒪 E]
  {𝔞 : Ideal 𝒪} :
-- imply
  idealTorsion (E := E) 𝔞 = Submodule.torsionBySet 𝒪 E (𝔞 : Set 𝒪) := by
-- proof
  ext P
  simp only [mem_idealTorsion_iff, Submodule.mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall]

end IdealTorsion

namespace CMTorsorAction

/--
[CMIsogenyData.toLinearMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma CMIsogenyData.toLinearMap_surjective
  [CommRing 𝒪]
  {𝔟 𝔞 : Ideal 𝒪}
  {φ : CMIsogenyData 𝒪 𝔟 𝔞} :
-- imply
  Function.Surjective φ.toLinearMap := by
-- proof
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

end CMTorsorAction

namespace CMTorsorAction

/--
[CMIsogenyData.ker_toLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma CMIsogenyData.ker_toLinearMap
  [CommRing 𝒪]
  {𝔟 𝔞 : Ideal 𝒪}
  {φ : CMIsogenyData 𝒪 𝔟 𝔞} :
-- imply
  LinearMap.ker φ.toLinearMap = Submodule.map (𝔟 : Submodule 𝒪 𝒪).mkQ (φ.targetIdeal : Submodule 𝒪 𝒪) := by
-- proof
  unfold CMIsogenyData.toLinearMap
  rw [Submodule.ker_mapQ]
  simp only [Submodule.comap_id]

end CMTorsorAction

namespace CMTorsorAction

/--
[degIsogeny_eq_idealNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma degIsogeny_eq_idealNorm
  [CommRing 𝒪]
  {𝔟 𝔞 : Ideal 𝒪}
  [IsDedekindDomain 𝒪]
  [Module.Free ℤ 𝒪]
  [Module.Finite ℤ 𝒪]
  {φ : CMIsogenyData 𝒪 𝔟 𝔞}
-- given
  (h𝔠_ne : φ.targetIdeal ≠ ⊥) :
-- imply
  degIsogeny φ = idealNorm 𝔞 := by
-- proof
  unfold degIsogeny idealNorm
  rw [φ.ker_toLinearMap]
  have h3 := Submodule.card_quotient_mul_card_quotient
    (φ.targetIdeal : Submodule 𝒪 𝒪) (𝔟 : Submodule 𝒪 𝒪) φ.le_target
  have hcm := cardQuot_mul 𝔞 φ.targetIdeal
  rw [φ.ideal_mul_target_eq] at hcm
  simp only [Submodule.cardQuot_apply] at hcm
  rw [hcm] at h3
  have hfin : Finite (𝒪 ⧸ φ.targetIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot φ.targetIdeal h𝔠_ne
  have h𝔠_pos : 0 < Nat.card (𝒪 ⧸ (φ.targetIdeal : Submodule 𝒪 𝒪)) := by
    rw [Nat.card_pos_iff]
    exact ⟨inferInstance, inferInstance⟩
  exact mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp h𝔠_pos) h3
end CMTorsorAction
namespace CMIdealIsogeny
open CMTorsorAction NormTrace


namespace CMIdealIsogeny

/--
[isogeny_degree_eq_idealNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean)
-/
@[path]
lemma isogeny_degree_eq_idealNorm
  [CommRing 𝒪]
  {𝔟 𝔞 : Ideal 𝒪}
  [IsDedekindDomain 𝒪]
  [Module.Free ℤ 𝒪]
  [Module.Finite ℤ 𝒪]
  {φ : CMIsogenyData 𝒪 𝔟 𝔞}
-- given
  (h𝔠_ne : φ.targetIdeal ≠ ⊥) :
-- imply
  degIsogeny φ = idealNorm 𝔞 :=
-- proof
  degIsogeny_eq_idealNorm φ h𝔠_ne
/-- Any two CM elliptic curves with the same endomorphism ring `𝒪` are linked by a CM
ideal isogeny: for any two ideals `𝔟₁, 𝔟₂` there exists an ideal `𝔞` and a
`CMIsogenyData 𝒪 𝔟₁ 𝔞` whose target equals `𝔟₂`. -/

end CMIdealIsogeny


-- created on 2026-10-23
