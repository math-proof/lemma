import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Norm.Basic

open scoped Polynomial.Bivariate WithZero nonZeroDivisors
open Polynomial

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

namespace CoordinateRing

lemma algebraNorm_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) : Algebra.norm K[X] f ≠ 0 :=
  (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis W)).mpr hf

open scoped Classical in

noncomputable def valuationInftyDef (f : W.CoordinateRing) : ℤᵐ⁰ :=
  if f = 0 then 0 else WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ)

lemma degree_norm_add_le (f g : W.CoordinateRing) :
    (Algebra.norm K[X] (f + g)).degree ≤
      max (Algebra.norm K[X] f).degree (Algebra.norm K[X] g).degree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  obtain ⟨p', q', rfl⟩ := exists_smul_basis_eq g
  have : p • (1 : W.CoordinateRing) + q • mk W Y + (p' • 1 + q' • mk W Y) =
      (p + p') • 1 + (q + q') • mk W Y := by
    rw [add_smul, add_smul]; abel
  rw [this, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  refine max_le ?_ ?_
  · rcases le_max_iff.mp (degree_add_le p p') with h | h
    · exact le_max_of_le_left (le_max_of_le_left (nsmul_le_nsmul_right h 2))
    · exact le_max_of_le_right (le_max_of_le_left (nsmul_le_nsmul_right h 2))
  · rcases le_max_iff.mp (degree_add_le q q') with h | h
    · exact le_max_of_le_left (le_max_of_le_right
        (add_le_add_left (nsmul_le_nsmul_right h 2) 3))
    · exact le_max_of_le_right (le_max_of_le_right
        (add_le_add_left (nsmul_le_nsmul_right h 2) 3))

noncomputable def valuationInftyInt : Valuation W.CoordinateRing ℤᵐ⁰ where
  toFun := valuationInftyDef W
  map_zero' := if_pos rfl
  map_one' := by
    simp [valuationInftyDef]
  map_mul' f g := by
    classical
    by_cases hf : f = 0
    · simp [valuationInftyDef, hf]
    by_cases hg : g = 0
    · simp [valuationInftyDef, hg]
    simp only [valuationInftyDef, if_neg hf, if_neg hg, if_neg (mul_ne_zero hf hg), map_mul,
      natDegree_mul (algebraNorm_ne_zero W hf) (algebraNorm_ne_zero W hg), Nat.cast_add, WithZero.exp_add]
  map_add_le_max' f g := by
    classical
    by_cases hfg : f + g = 0
    · simp [valuationInftyDef, hfg]
    by_cases hf : f = 0
    · simp [valuationInftyDef, hf]
    by_cases hg : g = 0
    · simp [valuationInftyDef, hg]
    simp only [valuationInftyDef, if_neg hf, if_neg hg, if_neg hfg, le_max_iff,
      WithZero.exp_le_exp, Nat.cast_le]
    have h := degree_norm_add_le W f g
    rw [degree_eq_natDegree (algebraNorm_ne_zero W hfg), degree_eq_natDegree (algebraNorm_ne_zero W hf),
      degree_eq_natDegree (algebraNorm_ne_zero W hg)] at h
    rcases le_max_iff.mp h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)

lemma valuationInftyInt_apply (f : W.CoordinateRing) :
    valuationInftyInt W f = valuationInftyDef W f := rfl

lemma nonZeroDivisors_le_supp_primeCompl :
    W.CoordinateRing⁰ ≤ (valuationInftyInt W).supp.primeCompl := fun _ hs => by
  simp [valuationInftyInt_apply, valuationInftyDef, nonZeroDivisors.ne_zero hs]

end CoordinateRing

noncomputable def valuationInfty : Valuation W.FunctionField ℤᵐ⁰ :=
  (CoordinateRing.valuationInftyInt W).extendToLocalization
    (CoordinateRing.nonZeroDivisors_le_supp_primeCompl W) W.FunctionField

lemma valuationInfty_algebraMap (f : W.CoordinateRing) :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField f) =
      CoordinateRing.valuationInftyDef W f :=
  Valuation.extendToLocalization_apply_map_apply ..

lemma valuationInfty_algebraMap_of_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField f) =
      WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ) := by
  rw [valuationInfty_algebraMap, CoordinateRing.valuationInftyDef, if_neg hf]

namespace CoordinateRing

lemma natDegree_norm_smul_basis_of_eq_zero (p : K[X]) :
    (Algebra.norm K[X] (p • (1 : W.CoordinateRing) + (0 : K[X]) • mk W Y)).natDegree =
      2 * p.natDegree := by
  by_cases hp : p = 0
  · subst hp
    have : (0 : K[X]) • (1 : W.CoordinateRing) + (0 : K[X]) • mk W Y = 0 := by simp
    rw [this, (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).mpr rfl,
      natDegree_zero]
  · have h := degree_norm_smul_basis (W' := W) p 0
    rw [degree_zero, degree_eq_natDegree hp, two_nsmul, two_nsmul, WithBot.bot_add,
      WithBot.bot_add, max_bot_right] at h
    apply natDegree_eq_of_degree_eq_some
    rw [h, two_mul]
    rfl

lemma natDegree_norm_smul_basis_of_ne_zero (p q : K[X]) (hq : q ≠ 0) :
    (Algebra.norm K[X] (p • (1 : W.CoordinateRing) + q • mk W Y)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  have h := degree_norm_smul_basis (W' := W) p q
  apply natDegree_eq_of_degree_eq_some
  rw [h, degree_eq_natDegree hq]
  by_cases hp : p = 0
  · subst hp
    rw [degree_zero, two_nsmul, WithBot.bot_add, max_bot_left, natDegree_zero, mul_zero,
      Nat.zero_max, two_nsmul, two_mul]
    rfl
  · rw [degree_eq_natDegree hp, two_nsmul, two_nsmul, two_mul, two_mul]
    rfl

lemma natDegree_norm_mk_C (p : K[X]) :
    (Algebra.norm K[X] (mk W (C p))).natDegree = 2 * p.natDegree := by
  rw [← natDegree_norm_smul_basis_of_eq_zero W p, CoordinateRing.smul, zero_smul, add_zero,
    mul_one]

lemma natDegree_norm_mk_Y : (Algebra.norm K[X] (mk W Y)).natDegree = 3 := by
  have := natDegree_norm_smul_basis_of_ne_zero W 0 1 one_ne_zero
  rw [zero_smul, one_smul, zero_add] at this
  rw [this]
  norm_num

lemma mk_Y_ne_zero : mk W Y ≠ 0 := by
  simpa [YClass] using YClass_ne_zero (W' := W) 0

lemma mk_Y_mul_mk_Y_add :
    mk W Y * (mk W Y + mk W (C (C W.a₁ * X + C W.a₃))) =
      mk W (C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) := by
  have h : mk W (Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y) =
      mk W (C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) :=
    AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [WeierstrassCurve.Affine.polynomial]; ring1⟩
  rw [map_add, map_mul, map_pow] at h
  rw [← h]
  ring

end CoordinateRing

lemma valuationInfty_X :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))) =
      WithZero.exp 2 := by
  rw [valuationInfty_algebraMap_of_ne_zero W (CoordinateRing.XClass_ne_zero (W' := W) 0 ∘ ?_),
    CoordinateRing.natDegree_norm_mk_C, natDegree_X]
  · rfl
  · intro h; simpa [CoordinateRing.XClass] using h

lemma valuationInfty_Y :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) =
      WithZero.exp 3 := by
  rw [valuationInfty_algebraMap_of_ne_zero W (CoordinateRing.mk_Y_ne_zero W),
    CoordinateRing.natDegree_norm_mk_Y]
  rfl

lemma valuationInfty_surjective : Function.Surjective (valuationInfty W) := by
  intro γ
  rcases eq_or_ne γ 0 with rfl | hγ
  · exact ⟨0, map_zero _⟩
  · refine ⟨(algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) /
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))) ^ WithZero.log γ, ?_⟩
    rw [map_zpow₀, map_div₀, valuationInfty_Y, valuationInfty_X, ← WithZero.exp_sub,
      ← WithZero.exp_zsmul, smul_eq_mul]
    norm_num
    exact WithZero.exp_log hγ

instance valuationInfty_isNontrivial : (valuationInfty W).IsNontrivial :=
  ⟨algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)), by
    rw [valuationInfty_X]; exact ⟨WithZero.exp_ne_zero, by decide⟩⟩

instance : IsDiscreteValuationRing (valuationInfty W).valuationSubring := inferInstance

end WeierstrassCurve.Affine
