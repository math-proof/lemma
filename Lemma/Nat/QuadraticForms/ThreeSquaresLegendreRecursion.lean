import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part23
open MetaMathlibExt


namespace MetaMathlibExt

/--
[r3leg_coord_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_coord_mem (n : ℕ) (a b c : ℤ)
  (h : a ^ 2 + b ^ 2 + c ^ 2 = (n : ℤ)) :
  a ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  rw [Finset.mem_Icc]
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have ha : a ^ 2 ≤ (n : ℤ) := by omega
  have hpos := Int.le_self_sq a
  have hneg := Int.le_self_sq (-a)
  rw [show (-a) ^ 2 = a ^ 2 by ring] at hneg
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_mem_rep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_mem_rep {n : ℕ} {x : r3legIntVec} :
  x ∈ r3legRep n ↔ r3legQ x = (n : ℤ) := by
  rw [r3legRep, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_product, Finset.mem_product]
    have h₁ := r3leg_coord_mem n x.1.1 x.1.2 x.2 h
    have h₂ := r3leg_coord_mem n x.1.2 x.1.1 x.2 (by
      dsimp [r3legQ] at h ⊢
      linear_combination h)
    have h₃ := r3leg_coord_mem n x.2 x.1.1 x.1.2 (by
      dsimp [r3legQ] at h ⊢
      linear_combination h)
    exact ⟨⟨h₁, h₂⟩, h₃⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_rep_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_rep_card (n : ℕ) :
  (r3legRep n).card = Nat.threeSquareRepresentationCount n := by
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_mem_imageRep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_mem_imageRep {p n : ℕ} {π : Quaternion ℤ} {y : r3legIntVec} :
  y ∈ r3legImageRep p n π ↔
    r3legQ y = (p ^ 2 * n : ℕ) ∧
    r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star π) y) := by
  classical
  rw [r3legImageRep, Finset.mem_filter, r3leg_mem_rep]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_sqrtPairs_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_sqrtPairs_card {p : ℕ} [Fact (Nat.Prime p)]
  (hp3 : 3 ≤ p) (Δ : ZMod p) :
  (Fintype.card (r3legSqrtPairs p Δ) : ℤ) =
    1 + ((p : ℤ) - 1) * (1 + quadraticChar (ZMod p) Δ) := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hsqrt : (Fintype.card (r3legSqrts p Δ) : ℤ) =
    quadraticChar (ZMod p) Δ + 1 := by
    let s := {x : ZMod p | x ^ 2 = Δ}.toFinset
    let e : r3legSqrts p Δ ≃ ↥s := Equiv.subtypeEquiv (Equiv.refl _) (by
      intro x
      simp [s])
    have hc := Fintype.card_congr e
    rw [Fintype.card_coe] at hc
    rw [hc]
    simpa [s] using quadraticChar_card_sqrts hchar Δ
  have hu : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [Fintype.card_units, ZMod.card]
  have hcard := Fintype.card_congr (r3leg_sqrtPairEquiv Δ)
  rw [Fintype.card_option, Fintype.card_prod, hu] at hcard
  have hcard' : (Fintype.card (r3legSqrtPairs p Δ) : ℤ) =
    ((p - 1 : ℕ) : ℤ) * Fintype.card (r3legSqrts p Δ) + 1 := by
    exact_mod_cast hcard
  have hsub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  rw [hsub, hsqrt] at hcard'
  linear_combination hcard'

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_binary_card_of_left_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_binary_card_of_left_ne_zero {p : ℕ} [Fact (Nat.Prime p)]
  (hp3 : 3 ≤ p) (a b d : ZMod p) (ha : a ≠ 0) :
  (Fintype.card (r3legBinaryZeros p a b d) : ℤ) =
    1 + ((p : ℤ) - 1) *
      (1 + quadraticChar (ZMod p) (b ^ 2 - a * d)) := by
  rw [Fintype.card_congr (r3leg_binarySqrtEquiv a b d ha)]
  exact r3leg_sqrtPairs_card hp3 _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_zeroProd_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_zeroProd_card {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
  (Fintype.card (r3legZeroProd p) : ℤ) = 2 * (p : ℤ) - 1 := by
  have hcard := Fintype.card_congr (r3leg_zeroProdEquiv (p := p))
  rw [Fintype.card_sum, ZMod.card, Fintype.card_units, ZMod.card] at hcard
  have hcard' : (Fintype.card (r3legZeroProd p) : ℤ) =
    (p : ℤ) + ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hcard
  have hsub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  rw [hsub] at hcard'
  linear_combination hcard'

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_twoSq_card_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_twoSq_card_eq_one {p : ℕ} [Fact (Nat.Prime p)]
  (c : ZMod p) (hc : c ≠ 0) :
  Fintype.card (r3legTwoSq p c) = Fintype.card (r3legTwoSq p 1) := by
  symm
  exact Fintype.card_congr (r3leg_twoSqEquivOne c hc)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_sum_twoSq_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_sum_twoSq_comp {p : ℕ} [Fact (Nat.Prime p)]
  (g : ZMod p → ZMod p) (hg : ∀ t, g t = 0 ↔ t = 0) :
  (∑ t : ZMod p, Fintype.card (r3legTwoSq p (g t))) =
    Fintype.card (r3legTwoSq p 0) +
      (p - 1) * Fintype.card (r3legTwoSq p 1) := by
  classical
  let f := fun t : ZMod p => Fintype.card (r3legTwoSq p (g t))
  have hzero : g 0 = 0 := (hg 0).mpr rfl
  have herase :
    (∑ t ∈ (Finset.univ.erase (0 : ZMod p)), f t) =
      (p - 1) * Fintype.card (r3legTwoSq p 1) := by
    calc
      (∑ t ∈ (Finset.univ.erase (0 : ZMod p)), f t) =
        ∑ _t ∈ (Finset.univ.erase (0 : ZMod p)),
          Fintype.card (r3legTwoSq p 1) := by
        apply Finset.sum_congr rfl
        intro t ht
        apply r3leg_twoSq_card_eq_one
        intro hgt
        have ht0 := (hg t).mp hgt
        exact (Finset.mem_erase.mp ht).1 ht0
      _ = (Finset.univ.erase (0 : ZMod p)).card *
        Fintype.card (r3legTwoSq p 1) := by simp
      _ = (p - 1) * Fintype.card (r3legTwoSq p 1) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : ZMod p))
  rw [herase] at hsplit
  dsimp [f] at hsplit ⊢
  rw [hzero] at hsplit
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_cone_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_cone_card {p : ℕ} [Fact (Nat.Prime p)] :
  Fintype.card (r3legCone p) = p ^ 2 := by
  have hcone := Fintype.card_congr (r3leg_coneSigmaEquiv (p := p))
  rw [Fintype.card_sigma,
    r3leg_sum_twoSq_comp (fun t : ZMod p => -t ^ 2) (by
      intro t
      constructor
      · intro h
        have : t ^ 2 = 0 := by simpa using congrArg Neg.neg h
        exact sq_eq_zero_iff.mp this
      · rintro rfl
        simp)] at hcone
  have hpairs := Fintype.card_congr (r3leg_twoSqSigmaEquiv (p := p))
  rw [Fintype.card_sigma,
    r3leg_sum_twoSq_comp (fun t : ZMod p => t) (fun t => Iff.rfl),
    Fintype.card_prod, ZMod.card] at hpairs
  rw [pow_two]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_iso_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_iso_card {p : ℕ} [Fact (Nat.Prime p)] :
  Fintype.card (r3legIso p) = p ^ 2 - 1 := by
  rw [Fintype.card_congr (r3leg_isoConeEquiv (p := p)),
    Fintype.card_subtype_compl, r3leg_cone_card]
  have hzero :
    Fintype.card {w : r3legCone p // (w.1 : r3legModVec p) = 0} = 1 := by
    let z : r3legCone p := ⟨(0 : r3legModVec p), by simp [r3legQ]⟩
    calc
      Fintype.card {w : r3legCone p // (w.1 : r3legModVec p) = 0} =
        Fintype.card {w : r3legCone p // w = z} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun w => by
          simp [z, Subtype.ext_iff])
      _ = 1 := Fintype.card_subtype_eq z
  rw [hzero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_smul_right_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_smul_right_injective {p : ℕ} [Fact (Nat.Prime p)]
  (v : r3legModVec p) (hv : v ≠ 0) :
  Function.Injective (fun c : ZMod p => c • v) := by
  intro a b hab
  obtain ⟨⟨x, y⟩, z⟩ := v
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · have hz : z ≠ 0 := by
      intro hz
      apply hv
      simp [hx, hy, hz]
      have h := congrArg (fun w : r3legModVec p => w.2) hab
      exact mul_right_cancel₀ hz (by simpa using h)
    · have h := congrArg (fun w : r3legModVec p => w.1.2) hab
      exact mul_right_cancel₀ hy (by simpa using h)
  · have h := congrArg (fun w : r3legModVec p => w.1.1) hab
    exact mul_right_cancel₀ hx (by simpa using h)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_primitiveUnitMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_primitiveUnitMap_injective {p n : ℕ} [Fact (Nat.Prime p)]
  (hp3 : 3 ≤ p) (y : r3legIntVec) (hyq : r3legQ y = (p ^ 2 * n : ℕ))
  (hyne : r3legRed p y ≠ 0) :
  Function.Injective (r3leg_primitiveUnitMap hp3 y hyq hyne) := by
  intro u v huv
  apply Units.ext
  apply r3leg_smul_right_injective (r3legRed p y) hyne
  have h := congrArg
    (fun w : {w : r3legIso p // r3legInc hp3 w y} => (w.1.1 : r3legModVec p)) huv
  exact h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_repType_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_repType_card (n : ℕ) :
  Fintype.card (r3legRepType n) = Nat.threeSquareRepresentationCount n := by
  rw [Fintype.card_coe, r3leg_rep_card]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_zeroRed_rep_card_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_zeroRed_rep_card_of_dvd {p n : ℕ} [Fact (Nat.Prime p)]
  (hdiv : p ^ 2 ∣ n) :
  Fintype.card {x : r3legRepType n // r3legRed p (x : r3legIntVec) = 0} =
    Nat.threeSquareRepresentationCount (n / p ^ 2) := by
  have hmul : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hdiv
  have hcard := Fintype.card_congr (r3leg_scaleRepEquiv (p := p) (n / p ^ 2))
  rwa [hmul, r3leg_repType_card] at hcard

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_zeroRed_scaled_filter_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_zeroRed_scaled_filter_card {p n : ℕ} [Fact (Nat.Prime p)] :
  (Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
    r3legRed p (y : r3legIntVec) = 0)).card =
    Nat.threeSquareRepresentationCount n := by
  rw [← Fintype.card_subtype]
  calc
    Fintype.card
      {y : r3legRepType (p ^ 2 * n) // r3legRed p (y : r3legIntVec) = 0} =
      Fintype.card (r3legRepType n) :=
      (Fintype.card_congr (r3leg_scaleRepEquiv (p := p) n)).symm
    _ = Nat.threeSquareRepresentationCount n := r3leg_repType_card n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_nonzeroRed_scaled_filter_card_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_nonzeroRed_scaled_filter_card_add {p n : ℕ}
  [Fact (Nat.Prime p)] :
  (Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
    r3legRed p (y : r3legIntVec) ≠ 0)).card +
    Nat.threeSquareRepresentationCount n =
    Nat.threeSquareRepresentationCount (p ^ 2 * n) := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun y : r3legRepType (p ^ 2 * n) => r3legRed p (y : r3legIntVec) = 0)
  rw [r3leg_zeroRed_scaled_filter_card, Finset.card_univ, r3leg_repType_card] at h
  simpa only [ne_eq, add_comm] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_zeroRed_inc_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_zeroRed_inc_sum {p n : ℕ} [Fact (Nat.Prime p)]
  (hp3 : 3 ≤ p) :
  (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
    r3legRed p (y : r3legIntVec) = 0),
    (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)) =
    ∑ x : r3legRepType n,
      (Fintype.card
        {w : r3legIso p // r3legInc hp3 w (r3legScale p (x : r3legIntVec))} : ℤ) := by
  let e := r3leg_scaleRepEquiv (p := p) n
  calc
    (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
      r3legRed p (y : r3legIntVec) = 0),
      (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)) =
        ∑ y : {y : r3legRepType (p ^ 2 * n) //
          r3legRed p (y : r3legIntVec) = 0},
          (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ) := by
      apply Finset.sum_subtype
      intro y
      simp
    _ = ∑ x : r3legRepType n,
      (Fintype.card
        {w : r3legIso p // r3legInc hp3 w (r3legScale p (x : r3legIntVec))} : ℤ) := by
      symm
      apply Fintype.sum_equiv e
      intro x
      rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_legendre_mul_correction_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_legendre_mul_correction_eq_zero {p n : ℕ}
  [Fact (Nat.Prime p)] :
  legendreSym p (-(n : ℤ)) *
    (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) = 0 := by
  split_ifs with hdiv
  · have hpdiv : p ∣ n := dvd_trans (⟨p, by simp [pow_two]⟩ : p ∣ p ^ 2) hdiv
    have hnzero : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpdiv
    have hleg : legendreSym p (-(n : ℤ)) = 0 := by
      apply (legendreSym.eq_zero_iff p (-(n : ℤ))).mpr
      push_cast
      rw [hnzero, neg_zero]
    rw [hleg, zero_mul]
  · simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_g_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_g_eq_sum {p k : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
  r3legG p k = ∑ i ∈ Finset.range k, (p : ℤ) ^ i := by
  apply Int.ediv_eq_of_eq_mul_left
  · have : (1 : ℤ) < p := by exact_mod_cast (show 1 < p by omega)
    omega
  · exact (geom_sum_mul (p : ℤ) k).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_g_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_g_zero {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
  r3legG p 0 = 0 := by
  rw [r3leg_g_eq_sum hp3]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_g_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_g_one {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
  r3legG p 1 = 1 := by
  rw [r3leg_g_eq_sum hp3]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_g_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_g_two {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
  r3legG p 2 = (p : ℤ) + 1 := by
  rw [r3leg_g_eq_sum hp3]
  norm_num [Finset.sum_range_succ]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_g_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_g_succ {p k : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
  r3legG p (k + 1) = r3legG p k + (p : ℤ) ^ k := by
  rw [r3leg_g_eq_sum hp3, r3leg_g_eq_sum hp3, Finset.sum_range_succ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[r3leg_g_rec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3leg_g_rec {p k : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
  r3legG p (k + 2) = ((p : ℤ) + 1) * r3legG p (k + 1) -
    (p : ℤ) * r3legG p k := by
  rw [show k + 2 = (k + 1) + 1 by omega, r3leg_g_succ hp3,
    r3leg_g_succ hp3, pow_succ]
  ring

end MetaMathlibExt

/--
[r3_legendre_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean)
-/
@[path]
private lemma r3_legendre_recursion_eq
  {p n α : ℕ} [Fact (Nat.Prime p)]
-- given
  (hp3 : 3 ≤ p)
  (hn : 1 ≤ n) :
-- imply
  (Nat.threeSquareRepresentationCount (p ^ (2 * α) * n) : ℤ) =
    (((((p : ℤ) ^ (α + 1) - 1) / ((p : ℤ) - 1)) -
    legendreSym p (-(n : ℤ)) *
    (((p : ℤ) ^ α - 1) / ((p : ℤ) - 1))) *
    Nat.threeSquareRepresentationCount n -
    (p : ℤ) * (((p : ℤ) ^ α - 1) / ((p : ℤ) - 1)) *
    (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) := by
-- proof
  apply MetaMathlibExt.r3_legendre_recursion hp3 hn


-- created on 2026-10-20
-- updated on 2026-10-26
