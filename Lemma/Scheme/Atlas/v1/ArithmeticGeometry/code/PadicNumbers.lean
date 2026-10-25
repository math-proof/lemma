import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part9
open PadicInt in InverseLimit InverseLimit.NatInverseSystem DiscreteValuation PadicIntegers
open Finset PadicInt
open PadicInt Classical


namespace InverseLimit.NatInverseSystem

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma ext
  {S : NatInverseSystem}
  {a b : S.InverseLimit}
-- given
  (h : ∀ n, S.proj n a = S.proj n b) :
-- imply
  a = b :=
-- proof
  Subtype.ext (funext h)

end InverseLimit.NatInverseSystem

namespace InverseLimit.NatInverseSystem

/--
[proj_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma proj_lift
  {S : NatInverseSystem}
  {n : ℕ}
  {x : X}
-- given
  (g : ∀ n, X → S.obj n)
  (hg : ∀ n x, S.map n (g (n + 1) x) = g n x) :
-- imply
  S.proj n (S.lift g hg x) = g n x :=
-- proof
  rfl

end InverseLimit.NatInverseSystem

namespace InverseLimit.NatInverseSystem

/--
[lift_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma lift_unique
  {S : NatInverseSystem}
  {φ : X → S.InverseLimit}
-- given
  (g : ∀ n, X → S.obj n)
  (hg : ∀ n x, S.map n (g (n + 1) x) = g n x)
  (hφ : ∀ n x, S.proj n (φ x) = g n x) :
-- imply
  φ = S.lift g hg :=
-- proof
  funext fun x => S.ext fun n => (hφ n x).trans (S.proj_lift g hg n x).symm

end InverseLimit.NatInverseSystem

namespace DiscreteValuation

/--
[coe_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma coe_mk
  [CommRing R]
  {v : DiscreteValuation R}
  {f : R → WithTop ℤ}
  (h1 h2 h3) :
-- imply
  ((⟨f, h1, h2, h3⟩ : DiscreteValuation R) : R → WithTop ℤ) = f :=
-- proof
  rfl

end DiscreteValuation

namespace DiscreteValuation

/--
[val_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma val_zero
  [CommRing R]
  {v : DiscreteValuation R} :
-- imply
  v 0 = ⊤ :=
-- proof
  (v.val_eq_top_iff 0).mpr rfl
end DiscreteValuation
namespace PadicIntegers
noncomputable section
open PadicInt


namespace PadicInt

/--
[padicDigit_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicDigit_mul_pow
  {p : ℕ}
  [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : ℕ} :
-- imply
  padicDigit a n * p ^ n = a.appr (n + 1) - a.appr n := by
-- proof
  unfold padicDigit
  exact Nat.div_mul_cancel (dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n))

end PadicInt

namespace PadicInt

/--
[appr_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma appr_succ_eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : ℕ} :
-- imply
  a.appr (n + 1) = a.appr n + padicDigit a n * p ^ n := by
-- proof
  have hle : a.appr n ≤ a.appr (n + 1) := appr_mono a (Nat.le_succ n)
  have hd := padicDigit_mul_pow a n
  omega

end PadicInt

namespace PadicInt

/--
[appr_eq_sum_padicDigit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma appr_eq_sum_padicDigit
  {p : ℕ}
  [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : ℕ} :
-- imply
  a.appr n = ∑ k ∈ range n, padicDigit a k * p ^ k := by
-- proof
  induction n with
  | zero => simp [appr]
  | succ n ih =>
    rw [sum_range_succ, ← ih, appr_succ_eq]

end PadicInt

namespace PadicInt

/--
[digitPartialSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma digitPartialSum_nonneg
  {p : ℕ}
  [hp : Fact p.Prime]
  {b : ℕ → Fin p}
  {n : ℕ} :
-- imply
  0 ≤ digitPartialSum b n := by
-- proof
  apply Finset.sum_nonneg; intro k _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

end PadicInt

namespace PadicInt

/--
[digitPartialSum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma digitPartialSum_lt
  {p : ℕ}
  [hp : Fact p.Prime]
  {b : ℕ → Fin p}
  {n : ℕ} :
-- imply
  digitPartialSum b n < (p : ℤ) ^ n := by
-- proof
  induction n with
  | zero => simp [digitPartialSum]
  | succ n ih =>
    unfold digitPartialSum at ih ⊢; rw [Finset.sum_range_succ]
    have hb : ((b n).val : ℤ) ≤ p - 1 := by have := (b n).isLt; omega
    calc ∑ k ∈ Finset.range n, ((b k).val : ℤ) * (p : ℤ) ^ k + (b n).val * (p : ℤ) ^ n
      _ < (p : ℤ) ^ n + (p - 1) * (p : ℤ) ^ n := by
        have := mul_le_mul_of_nonneg_right hb (pow_nonneg (Nat.cast_nonneg p) n); linarith
      _ = (p : ℤ) ^ (n + 1) := by ring
set_option maxHeartbeats 800000 in

end PadicInt

namespace PadicInt

/--
[padicExpansion_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicExpansion_surjective
  {p : ℕ}
  [hp : Fact p.Prime]
  {b : ℕ → Fin p} :
-- imply
  ∃ (x : ℤ_[p]), ∀ n, padicExpansion x n = b n := by
-- proof
  set S := digitPartialSum b with hS_def
  have h_dvd : ∀ n, (p : ℤ) ^ n ∣ S (n + 1) - S n := by
    intro n; simp only [hS_def, digitPartialSum, Finset.sum_range_succ, add_sub_cancel_left]
    exact dvd_mul_left _ _
  set x : ℤ_[p] := PadicInt.ofIntSeq S
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub S p h_dvd)
  use x
  have h_appr_eq : ∀ n, (x.appr n : ℤ) = S n := by
    intro n
    have h_zmod := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub S p h_dvd n
    have h_dvd_diff : (p ^ n : ℤ) ∣ (x.appr n : ℤ) - S n := by
      have h_eq : (↑(x.appr n) : ZMod (p ^ n)) = (↑(S n) : ZMod (p ^ n)) := by
        change PadicInt.toZModPow n x = _; exact h_zmod
      have : ((↑(x.appr n) - S n : ℤ) : ZMod (p ^ n)) = 0 := by
        push_cast; exact sub_eq_zero.mpr h_eq
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at this
    have h_appr_lt : (x.appr n : ℤ) < (p : ℤ) ^ n := by exact_mod_cast appr_lt x n
    have h_S_lt : S n < (p : ℤ) ^ n := hS_def ▸ digitPartialSum_lt b n
    have h_S_nn : (0 : ℤ) ≤ S n := hS_def ▸ digitPartialSum_nonneg b n
    have hp_pos : (0 : ℤ) < (p : ℤ) ^ n :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))
    obtain ⟨c, hc⟩ := h_dvd_diff
    have : -1 < c := by nlinarith [Nat.cast_nonneg (α := ℤ) (x.appr n)]
    have : c < 1 := by nlinarith
    rw [show c = 0 by omega, mul_zero] at hc; linarith
  intro n
  apply Fin.ext; show padicDigit x n = (b n).val
  have hle : x.appr n ≤ x.appr (n + 1) := by
    have : (x.appr n : ℤ) ≤ x.appr (n + 1) := by
      rw [h_appr_eq n, h_appr_eq (n + 1), hS_def, digitPartialSum, digitPartialSum,
        Finset.sum_range_succ]
      linarith [mul_nonneg (show (0 : ℤ) ≤ (b n).val from Nat.cast_nonneg _)
        (show (0 : ℤ) ≤ (p : ℤ) ^ n from pow_nonneg (Nat.cast_nonneg _) _)]
    exact_mod_cast this
  suffices h : x.appr (n + 1) - x.appr n = (b n).val * p ^ n by
    unfold padicDigit; rw [h]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))
  zify [hle]
  rw [h_appr_eq (n + 1), h_appr_eq n, hS_def, digitPartialSum, digitPartialSum,
    Finset.sum_range_succ, add_sub_cancel_left]

end PadicInt

namespace PadicInt

/--
[padicExpansion_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicExpansion_injective
  {p : ℕ}
  [hp : Fact p.Prime] :
-- imply
  Function.Injective (padicExpansion (p := p)) := by
-- proof
  intro x y h
  have hd : ∀ n, padicDigit x n = padicDigit y n := by
    intro n; exact congr_arg Fin.val (congr_fun h n)
  have ha : ∀ n, x.appr n = y.appr n := by
    intro n
    rw [appr_eq_sum_padicDigit x n, appr_eq_sum_padicDigit y n]
    congr 1; ext k; congr 1; exact hd k
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  have hx := appr_spec n x
  rw [ha n] at hx
  have h_sub : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    have := Ideal.sub_mem _ hx (appr_spec n y); rwa [sub_sub_sub_cancel_right] at this
  rw [← ker_toZModPow] at h_sub
  rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at h_sub

end PadicInt

namespace PadicInt

/--
[padicExpansion_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicExpansion_bijective
  {p : ℕ}
  [hp : Fact p.Prime] :
-- imply
  Function.Bijective (padicExpansion (p := p)) :=
-- proof
  ⟨padicExpansion_injective, fun b =>
    let ⟨x, hx⟩ := padicExpansion_surjective b
    ⟨x, funext hx⟩⟩
end PadicInt
open PadicInt
section DVRDefinition


/--
[IsDiscreteValuationRing.isPrincipalIdealRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma IsDiscreteValuationRing.isPrincipalIdealRing
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R] :
-- imply
  IsPrincipalIdealRing R :=
-- proof
  inferInstance

/--
[IsDiscreteValuationRing.isLocalRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma IsDiscreteValuationRing.isLocalRing
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R] :
-- imply
  IsLocalRing R :=
-- proof
  inferInstance
end DVRDefinition
section PadicIntDVR
variable (p : ℕ) [Fact (Nat.Prime p)]

/--
[PadicInt.isDiscreteValuationRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma PadicInt.isDiscreteValuationRing
  {p : ℕ}
  [Fact (Nat.Prime p)] :
-- imply
  IsDiscreteValuationRing ℤ_[p] :=
-- proof
  inferInstance
end PadicIntDVR
section Theorem48
open PadicInt
variable {p : ℕ} [hp : Fact p.Prime]

/--
[PadicInt.exact_mul_pow_p_toZModPow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma PadicInt.exact_mul_pow_p_toZModPow
  {p : ℕ}
  [hp : Fact p.Prime]
  {m : ℕ} :
-- imply
  Set.range (fun (a : ℤ_[p]) => (p : ℤ_[p]) ^ m * a) = ↑(RingHom.ker (toZModPow m : ℤ_[p] →+* ZMod (p ^ m))) := by
-- proof
  rw [ker_toZModPow]
  ext x
  simp only [Set.mem_range, SetLike.mem_coe, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩

/--
[padicValuationDef_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicValuationDef_zero
  {p : ℕ}
  [hp : Fact (Nat.Prime p)] :
-- imply
  padicValuationDef (0 : ℤ_[p]) = ⊤ := by
-- proof
  simp [padicValuationDef]

/--
[padicValuationDef_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicValuationDef_of_ne_zero
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a : ℤ_[p]}
-- given
  (ha : a ≠ 0) :
-- imply
  padicValuationDef a = ↑(PadicInt.valuation a) := by
-- proof
  simp [padicValuationDef, ha]

/--
[padicValuationDef_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicValuationDef_ne_top
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a : ℤ_[p]}
-- given
  (ha : a ≠ 0) :
-- imply
  padicValuationDef a ≠ ⊤ := by
-- proof
  simp [ha]

/--
[padicValuationDef_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicValuationDef_mul
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a b : ℤ_[p]}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  padicValuationDef (a * b) = padicValuationDef a + padicValuationDef b := by
-- proof
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [padicValuationDef_of_ne_zero ha, padicValuationDef_of_ne_zero hb,
    padicValuationDef_of_ne_zero hab, PadicInt.valuation_mul ha hb, Nat.cast_add]

/--
[padicValuationDef_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma padicValuationDef_add
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a b : ℤ_[p]} :
-- imply
  min (padicValuationDef a) (padicValuationDef b) ≤ padicValuationDef (a + b) := by
-- proof
  by_cases hab : a + b = 0
  · simp [hab]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp only [padicValuationDef_of_ne_zero ha, padicValuationDef_of_ne_zero hb,
    padicValuationDef_of_ne_zero hab]
  calc min (↑(a.valuation) : WithTop ℕ) ↑(b.valuation)
    = ↑(min a.valuation b.valuation) := by norm_cast
    _ ≤ ↑((a + b).valuation) := WithTop.coe_le_coe.mpr (PadicInt.le_valuation_add hab)
end
section Corollary4_13
variable (p : ℕ) [Fact (Nat.Prime p)]

/--
[PadicInt.isDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma PadicInt.isDomain
  {p : ℕ}
  [Fact (Nat.Prime p)] :
-- imply
  IsDomain ℤ_[p] :=
-- proof
  inferInstance
end Corollary4_13
section Theorem4_15
noncomputable section
open PadicInt Classical
variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/--
[unit_valuation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma unit_valuation_zero
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {u : ℤ_[p]ˣ} :
-- imply
  PadicInt.valuation (u : ℤ_[p]) = 0 := by
-- proof
  have hu_ne : (u : ℤ_[p]) ≠ 0 := u.ne_zero
  have huinv_ne : (↑u⁻¹ : ℤ_[p]) ≠ 0 := (u⁻¹).ne_zero
  have h1 : (u : ℤ_[p]) * (↑u⁻¹ : ℤ_[p]) = 1 := by exact_mod_cast u.mul_inv
  have hval : PadicInt.valuation (u : ℤ_[p]) + PadicInt.valuation (↑u⁻¹ : ℤ_[p]) = 0 := by
    rw [← PadicInt.valuation_mul hu_ne huinv_ne, h1, PadicInt.valuation_one]
  omega

/--
[thm_4_15_units_valuation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma thm_4_15_units_valuation
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a : ℤ_[p]}
-- given
  (ha : a ≠ 0) :
-- imply
  IsUnit a ↔ PadicInt.valuation a = 0 := by
-- proof
  constructor
  · intro ⟨u, hu⟩
    rw [← hu]
    exact unit_valuation_zero u
  · intro h
    rw [PadicInt.isUnit_iff, PadicInt.norm_eq_zpow_neg_valuation ha, h]
    simp

/--
[thm_4_15_unique_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma thm_4_15_unique_factorization
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a : ℤ_[p]}
-- given
  (ha : a ≠ 0) :
-- imply
  ∃! nu : ℕ × (ℤ_[p])ˣ, a = (p : ℤ_[p]) ^ nu.1 * ↑nu.2 := by
-- proof
  refine ⟨⟨a.valuation, PadicInt.unitCoeff ha⟩, ?_, ?_⟩
  ·
    simp only
    rw [mul_comm]
    exact PadicInt.unitCoeff_spec ha
  ·
    rintro ⟨m, u⟩ hmu
    simp only at hmu
    have hu_ne : (u : ℤ_[p]) ≠ 0 := u.ne_zero
    have hu_val : PadicInt.valuation (u : ℤ_[p]) = 0 := unit_valuation_zero u
    have hp_ne : (p : ℤ_[p]) ≠ 0 := NeZero.ne _
    have hm_eq : m = a.valuation := by
      have : a.valuation = m := by
        rw [hmu, PadicInt.valuation_p_pow_mul m (u : ℤ_[p]) hu_ne, hu_val, add_zero]
      omega
    have hu_eq : u = PadicInt.unitCoeff ha := by
      ext
      have hspec := PadicInt.unitCoeff_spec ha
      have key : (p : ℤ_[p]) ^ m * (u : ℤ_[p]) =
        (p : ℤ_[p]) ^ m * ↑(PadicInt.unitCoeff ha) := by
        calc (p : ℤ_[p]) ^ m * (u : ℤ_[p])
          = a := hmu.symm
          _ = ↑(PadicInt.unitCoeff ha) * (p : ℤ_[p]) ^ a.valuation := hspec
          _ = ↑(PadicInt.unitCoeff ha) * (p : ℤ_[p]) ^ m := by rw [← hm_eq]
          _ = (p : ℤ_[p]) ^ m * ↑(PadicInt.unitCoeff ha) := by ring
      exact mul_left_cancel₀ (pow_ne_zero _ hp_ne) key
    exact Prod.ext hm_eq hu_eq
end
end Theorem4_15
section Theorem4_16
noncomputable section
open PadicInt Classical
variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/--
[thm_4_16_nonzero_ideal_span_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma thm_4_16_nonzero_ideal_span_pow
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {I : Ideal ℤ_[p]}
-- given
  (hI : I ≠ ⊥) :
-- imply
  ∃ m : ℕ, I = Ideal.span {(p : ℤ_[p]) ^ m} :=
-- proof
  ideal_eq_span_pow_p hI
end
end Theorem4_16
section Corollary4_17
variable (p : ℕ) [Fact (Nat.Prime p)]

/--
[PadicInt.isPrincipalIdealRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma PadicInt.isPrincipalIdealRing
  {p : ℕ}
  [Fact (Nat.Prime p)] :
-- imply
  IsPrincipalIdealRing ℤ_[p] :=
-- proof
  inferInstance

/--
[PadicInt.isLocalRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
lemma PadicInt.isLocalRing
  {p : ℕ}
  [Fact (Nat.Prime p)] :
-- imply
  IsLocalRing ℤ_[p] :=
-- proof
  inferInstance
end Corollary4_17

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
private lemma ext_eq_2
  [CommRing R]
  {v : DiscreteValuation R}
  {v w : DiscreteValuation R}
-- given
  (h : ∀ x, v x = w x) :
-- imply
  v = w := by
-- proof
  apply DiscreteValuation.ext v h

/--
[invLimProj_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
private lemma invLimProj_compat_eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {m n : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (invLimProj p n) = invLimProj p m := by
-- proof
  apply PadicIntegers.invLimProj_compat p m n h

/--
[padicDigit_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
private lemma padicDigit_lt_eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : ℕ} :
-- imply
  padicDigit a n < p := by
-- proof
  apply PadicInt.padicDigit_lt a n

/--
[PadicInt.toZModPow_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean)
-/
@[path]
private lemma toZModPow_surjective_eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {m : ℕ} :
-- imply
  Function.Surjective (toZModPow m : ℤ_[p] →+* ZMod (p ^ m)) := by
-- proof
  apply PadicInt.toZModPow_surjective m


-- created on 2026-10-23
