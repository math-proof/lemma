import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part9
open PowerSeries
open scoped PowerSeries.WithPiTopology
open MetaMathlibExt


namespace MetaMathlibExt

/--
[opc_supportedMod_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_supportedMod_mul {R : Type*} [CommRing R] (p : ℕ)
  (r s : ZMod p) (F G : R⟦X⟧) (hF : opcSupportedMod R p r F)
  (hG : opcSupportedMod R p s G) :
  opcSupportedMod R p (r + s) (F * G) := by
  intro n hn
  rw [PowerSeries.coeff_mul] at hn
  obtain ⟨ij, hij, hterm⟩ : ∃ ij ∈ Finset.antidiagonal n,
    PowerSeries.coeff ij.1 F * PowerSeries.coeff ij.2 G ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (Finset.sum_eq_zero h)
  have h1 : PowerSeries.coeff ij.1 F ≠ 0 := left_ne_zero_of_mul hterm
  have h2 : PowerSeries.coeff ij.2 G ≠ 0 := right_ne_zero_of_mul hterm
  have e1 := hF _ h1
  have e2 := hG _ h2
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  conv_lhs => rw [← hsum]
  push_cast
  rw [e1, e2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_supportedMod_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_supportedMod_add {R : Type*} [CommRing R] (p : ℕ)
  (r : ZMod p) (F G : R⟦X⟧) (hF : opcSupportedMod R p r F)
  (hG : opcSupportedMod R p r G) : opcSupportedMod R p r (F + G) := by
  intro n hn
  have hFG : PowerSeries.coeff n (F + G)
    = PowerSeries.coeff n F + PowerSeries.coeff n G := map_add _ _ _
  rw [hFG] at hn
  by_cases h1 : PowerSeries.coeff n F = 0
  · rw [h1, zero_add] at hn
    exact hG n hn
  · exact hF n h1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_supportedMod_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_supportedMod_nsmul {R : Type*} [CommRing R] (p : ℕ)
  (r : ZMod p) (F : R⟦X⟧) (k : ℕ) (hF : opcSupportedMod R p r F) :
  opcSupportedMod R p r (k • F) := by
  intro n hn
  have hFG : PowerSeries.coeff n (k • F) = k • PowerSeries.coeff n F :=
    map_nsmul _ _ _
  rw [hFG] at hn
  exact hF n (fun h => hn (by rw [h, nsmul_zero]))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_supportedMod_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_supportedMod_map {R S : Type*} [CommRing R] [CommRing S]
  (f : R →+* S) (p : ℕ) (r : ZMod p) (F : R⟦X⟧)
  (hF : opcSupportedMod R p r F) : opcSupportedMod S p r (PowerSeries.map f F) := by
  intro n hn
  rw [PowerSeries.coeff_map] at hn
  exact hF n (fun h => hn (by rw [h, map_zero]))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_supportedMod_expand](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_supportedMod_expand {R : Type*} [CommRing R] (p : ℕ)
  (hp : p ≠ 0) (G : R⟦X⟧) : opcSupportedMod R p 0 (PowerSeries.expand p hp G) := by
  have : NeZero p := ⟨hp⟩
  intro n hn
  rw [PowerSeries.coeff_expand] at hn
  by_contra hcon
  have hdvd : p ∣ n := by
    by_contra hnd
    simp [hnd] at hn
  exact hcon ((ZMod.natCast_eq_zero_iff n p).mpr hdvd)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_supportedMod_coeff_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_supportedMod_coeff_eq_zero {R : Type*} [CommRing R]
  (p : ℕ) [NeZero p] (r : ZMod p) (F : R⟦X⟧) (hF : opcSupportedMod R p r F)
  (hr : r ≠ 0) (m : ℕ) : PowerSeries.coeff (p * m) F = 0 := by
  by_contra hne
  exact hr ((hF _ hne).symm.trans
    ((ZMod.natCast_eq_zero_iff (p * m) p).mpr (dvd_mul_right p m)))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_card_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_card_subset (t : Finset ℕ) :
  Nat.card {s : Finset ℕ // s ⊆ t} = 2 ^ t.card := by
  have hfin : Finite ↥(t.powerset) := Finite.of_fintype _
  rw [← Nat.card_congr (opcSubsetPowerset t), Nat.card_eq_finsetCard,
    Finset.card_powerset]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_overpartition_card_eq_coeff_genFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_overpartition_card_eq_coeff_genFun (m : ℕ) :
  ((Nat.card (opcOver m) : ℕ) : ℤ)
    = (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))).coeff m := by
  have hfin : ∀ π : m.Partition,
    Finite {s : Finset ℕ // s ⊆ π.parts.toFinset} :=
    fun π => Finite.of_equiv _ (opcSubsetPowerset _)
  rw [Nat.Partition.coeff_genFun, Nat.card_congr (opcOverSigma m), Nat.card_sigma,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [opc_card_subset π.parts.toFinset, Nat.cast_pow, Nat.cast_two]
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Finset.prod_const]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_coeff_weight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_coeff_weight {α : Type*} (w : α → ℕ) (k : ℕ) :
  PowerSeries.coeff k (opcWeight w) = ((Nat.card {a // w a = k} : ℕ) : ℤ) :=
  PowerSeries.coeff_mk _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_weight_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_weight_mul {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
  (h₁ : ∀ k, Finite {a // w₁ a = k}) (h₂ : ∀ k, Finite {a // w₂ a = k}) :
  opcWeight (fun p : α × β => w₁ p.1 + w₂ p.2)
    = opcWeight w₁ * opcWeight w₂ := by
  apply PowerSeries.ext
  intro N
  have : ∀ ij : ↥(Finset.HasAntidiagonal.antidiagonal N),
    Fintype {a : α // w₁ a = ij.1.1} := by
    intro ij
    have hfin := h₁ ij.1.1
    exact Fintype.ofFinite _
  have : ∀ ij : ↥(Finset.HasAntidiagonal.antidiagonal N),
    Fintype {b : β // w₂ b = ij.1.2} := by
    intro ij
    have hfin := h₂ ij.1.2
    exact Fintype.ofFinite _
  rw [PowerSeries.coeff_mul]
  simp_rw [opc_coeff_weight]
  rw [Nat.card_congr (opcProdEquiv w₁ w₂ N), Nat.card_sigma, Nat.cast_sum]
  simp_rw [Nat.card_prod, Nat.cast_mul]
  rw [← Finset.sum_coe_sort (s := Finset.HasAntidiagonal.antidiagonal N)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_weight_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_weight_add {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
  (h₁ : ∀ k, Finite {a // w₁ a = k}) (h₂ : ∀ k, Finite {a // w₂ a = k}) :
  opcWeight (Sum.elim w₁ w₂) = opcWeight w₁ + opcWeight w₂ := by
  apply PowerSeries.ext
  intro N
  have hF1 : Finite {a : α // w₁ a = N} := h₁ N
  have hF2 : Finite {b : β // w₂ b = N} := h₂ N
  rw [opc_coeff_weight, map_add, opc_coeff_weight, opc_coeff_weight,
    Nat.card_congr (opcSumEquiv w₁ w₂ N), Nat.card_sum, Nat.cast_add]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_weight_congr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_weight_congr {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
  (e : α ≃ β) (h : ∀ a, w₂ (e a) = w₁ a) :
  opcWeight w₁ = opcWeight w₂ := by
  apply PowerSeries.ext
  intro k
  simp_rw [opc_coeff_weight]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquiv e (fun a => by rw [h a])

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_finite_intFiber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_finite_intFiber (k : ℕ) :
  Finite {x : ℤ // x.natAbs ^ 2 = k} := by
  have hbound : ∀ x : {x : ℤ // x.natAbs ^ 2 = k},
    x.val ∈ Finset.Icc (-((k : ℤ) + 1)) ((k : ℤ) + 1) := by
    intro x
    have hle : x.val.natAbs ≤ x.val.natAbs ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    have hle2 : x.val.natAbs ≤ k := hle.trans_eq x.property
    have habs : |x.val| ≤ ((k : ℤ) + 1) := by
      have h3 : ((x.val.natAbs : ℕ) : ℤ) ≤ ((k : ℤ) + 1) := by
        exact_mod_cast Nat.le_succ_of_le hle2
      rwa [Int.natCast_natAbs] at h3
    rw [Finset.mem_Icc]
    exact abs_le.mp habs
  exact Finite.of_injective
    (fun x : {x : ℤ // x.natAbs ^ 2 = k} =>
      (⟨x.val, hbound x⟩ : ↥(Finset.Icc (-((k : ℤ) + 1)) ((k : ℤ) + 1))))
    (fun a b h => Subtype.ext (by simpa using h))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_finite_thetaOnFiber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_finite_thetaOnFiber (P : ℤ → Prop) (k : ℕ) :
  Finite {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = k} := by
  have := opc_finite_intFiber k
  exact Finite.of_injective
    (fun x : {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = k} =>
      (⟨x.val.val, x.property⟩ : {x : ℤ // x.natAbs ^ 2 = k}))
    (fun a b h => Subtype.ext (Subtype.ext (by simpa using h)))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_finite_prodFiber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_finite_prodFiber {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
  (h₁ : ∀ k, Finite {a // w₁ a = k}) (h₂ : ∀ k, Finite {a // w₂ a = k})
  (k : ℕ) : Finite {p : α × β // w₁ p.1 + w₂ p.2 = k} := by
  have : ∀ ij : ↥(Finset.HasAntidiagonal.antidiagonal k),
    Fintype {a : α // w₁ a = ij.1.1} := by
    intro ij
    have hfin := h₁ ij.1.1
    exact Fintype.ofFinite _
  have : ∀ ij : ↥(Finset.HasAntidiagonal.antidiagonal k),
    Fintype {b : β // w₂ b = ij.1.2} := by
    intro ij
    have hfin := h₂ ij.1.2
    exact Fintype.ofFinite _
  exact Finite.of_equiv _ (opcProdEquiv w₁ w₂ k).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_natAbs_weight_iff_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_natAbs_weight_iff_sq (t : ℤ × ℤ × ℤ) (n : ℕ) :
  (t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2) = n) ↔
  (t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = (n : ℤ)) := by
  constructor
  · intro h
    have h' : (((t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2) : ℕ)) : ℤ)
      = ((n : ℕ) : ℤ) := by rw [h]
    simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq] at h'
    rwa [← add_assoc] at h'
  · intro h
    have h' : (((t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2) : ℕ)) : ℤ)
      = ((n : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq, ← add_assoc]
      exact h
    exact_mod_cast h'

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_coeff_theta_cube](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_coeff_theta_cube (n : ℕ) :
  PowerSeries.coeff n (opcTheta ^ 3)
    = ((Nat.card {x : ℤ × ℤ × ℤ //
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) := by
  have hfin : ∀ k, Finite {x : {x : ℤ // True} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfin2 : ∀ k, Finite {p : {x : ℤ // True} × {x : ℤ // True} //
    p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_prodFiber _ _ hfin hfin k
  have e1 : opcTheta * opcTheta
    = opcWeight (fun p : {x : ℤ // True} × {x : ℤ // True} =>
      p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2) :=
    (opc_weight_mul _ _ hfin hfin).symm
  have e2 : (opcWeight (fun p : {x : ℤ // True} × {x : ℤ // True} =>
    p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2)) * opcTheta
    = opcWeight (fun p : ({x : ℤ // True} × {x : ℤ // True}) × {x : ℤ // True} =>
      (p.1.1.val.natAbs ^ 2 + p.1.2.val.natAbs ^ 2) + p.2.val.natAbs ^ 2) :=
    (opc_weight_mul _ _ hfin2 hfin).symm
  have e3 : opcWeight (fun p : ({x : ℤ // True} × {x : ℤ // True}) × {x : ℤ // True} =>
    (p.1.1.val.natAbs ^ 2 + p.1.2.val.natAbs ^ 2) + p.2.val.natAbs ^ 2)
    = opcWeight (fun t : ℤ × ℤ × ℤ =>
      t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2)) :=
    opc_weight_congr _ _ opcReassoc (fun p => (add_assoc _ _ _).symm)
  have e4 : ∀ k, ((Nat.card {t : ℤ × ℤ × ℤ //
    t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2) = k} : ℕ) : ℤ)
    = ((Nat.card {x : ℤ × ℤ × ℤ //
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (k : ℤ)} : ℕ) : ℤ) := by
    intro k
    apply congrArg
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun t => opc_natAbs_weight_iff_sq t k)
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, e1, e2, e3,
    opc_coeff_weight]
  exact e4 n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_genFun_two_mul_pentagonalSeries_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_genFun_two_mul_pentagonalSeries_sq :
  Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ)) * (PowerSeries.pentagonalSeries ℤ) ^ 2
    = PowerSeries.expand 2 two_ne_zero (PowerSeries.pentagonalSeries ℤ) := by
  have hP : HasProd
    (fun i : ℕ ↦ 1 + ∑' j : ℕ, (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧))
    (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))) :=
    Nat.Partition.hasProd_genFun (fun _ _ ↦ (2 : ℤ))
  have hE : HasProd (fun n : ℕ ↦ (1 - X ^ (n + 1) : ℤ⟦X⟧))
    (PowerSeries.pentagonalSeries ℤ) :=
    PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ
  have hPE := (hP.mul hE).mul hE
  have hfactor : ∀ i : ℕ, (1 + ∑' j : ℕ, (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧))
    * (1 - (X ^ (i + 1) : ℤ⟦X⟧)) * (1 - (X ^ (i + 1) : ℤ⟦X⟧))
    = 1 - (X ^ (2 * (i + 1)) : ℤ⟦X⟧) := by
    intro i
    have hconst : (X ^ (i + 1) : ℤ⟦X⟧).constantCoeff = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_X_pow]
      simp
    have hS : (∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j) * (1 - X ^ (i + 1)) = 1 :=
      PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
        hconst
    have hsumY : Summable (fun j : ℕ => (X ^ (i + 1) : ℤ⟦X⟧) ^ j) :=
      PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hconst
    have hterm : ∀ j : ℕ, (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧)
      = (PowerSeries.C 2 * X ^ (i + 1)) * (X ^ (i + 1) : ℤ⟦X⟧) ^ j := by
      intro j
      have e1 : (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧)
        = PowerSeries.C 2 * X ^ ((i + 1) * (j + 1)) :=
        PowerSeries.smul_eq_C_mul _ _
      rw [e1, pow_mul, pow_succ', mul_assoc]
    have hA : (∑' j : ℕ, (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧))
      = (PowerSeries.C 2 * X ^ (i + 1))
        * (∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j) := by
      rw [tsum_congr hterm]
      exact hsumY.tsum_mul_left _
    have hC2 : (PowerSeries.C (2 : ℤ) : ℤ⟦X⟧) = 2 := by simp
    have hY2 : (X ^ (2 * (i + 1) : ℕ) : ℤ⟦X⟧) = (X ^ (i + 1) : ℤ⟦X⟧) ^ 2 := by
      rw [show 2 * (i + 1) = (i + 1) * 2 from by ring, pow_mul]
    have h1 : (1 + (2 : ℤ⟦X⟧) * X ^ (i + 1)
      * (∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j)) * (1 - X ^ (i + 1))
      = 1 + X ^ (i + 1) := by
      have e : (1 + (2 : ℤ⟦X⟧) * X ^ (i + 1)
        * (∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j)) * (1 - X ^ (i + 1))
        = (1 - X ^ (i + 1)) + (2 : ℤ⟦X⟧) * X ^ (i + 1)
          * ((∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j) * (1 - X ^ (i + 1))) := by
        ring
      rw [e, hS]
      ring
    rw [hA, hC2, h1, hY2]
    ring
  have hPE' : HasProd (fun n : ℕ ↦ (1 - X ^ (2 * (n + 1)) : ℤ⟦X⟧))
    ((Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ)) * PowerSeries.pentagonalSeries ℤ)
      * PowerSeries.pentagonalSeries ℤ) :=
    hPE.congr_fun (fun i => (hfactor i).symm)
  have hprod : ∀ s : Finset ℕ, (∏ n ∈ s, (1 - X ^ (2 * (n + 1)) : ℤ⟦X⟧))
    = PowerSeries.expand 2 two_ne_zero
      (∏ n ∈ s, (1 - X ^ (n + 1) : ℤ⟦X⟧)) := by
    intro s
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro n _
    rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
  have hexp : HasProd (fun n : ℕ ↦ (1 - X ^ (2 * (n + 1)) : ℤ⟦X⟧))
    (PowerSeries.expand 2 two_ne_zero (PowerSeries.pentagonalSeries ℤ)) := by
    rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    apply tendsto_nhds_of_eventually_eq
    by_cases hd : 2 ∣ d
    · obtain ⟨m, rfl⟩ := hd
      have e1 : ∀ s : Finset ℕ, (∏ n ∈ s, (1 - X ^ (2 * (n + 1)) : ℤ⟦X⟧)).coeff
        (2 * m) = (∏ n ∈ s, (1 - X ^ (n + 1) : ℤ⟦X⟧)).coeff m := by
        intro s
        rw [hprod s, PowerSeries.coeff_expand_mul]
      have e2 : (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.pentagonalSeries ℤ)).coeff (2 * m)
        = (PowerSeries.pentagonalSeries ℤ).coeff m :=
        PowerSeries.coeff_expand_mul _ _ _ _
      simp only [e1, e2]
      exact PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq _ _
    · apply Filter.Eventually.of_forall
      intro s
      rw [hprod s, PowerSeries.coeff_expand_of_not_dvd _ _ _ hd,
        PowerSeries.coeff_expand_of_not_dvd _ _ _ hd]
  have hunique := HasProd.unique hPE' hexp
  rw [pow_two, ← hunique]
  exact (mul_assoc _ _ _).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_support_thetaOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_support_thetaOn (P : ℤ → Prop) (r : ZMod 5)
  (hP : ∀ x : ℤ, P x → ((x ^ 2 : ℤ) : ZMod 5) = r) :
  opcSupportedMod ℤ 5 r (opcThetaOn P) := by
  intro m hm
  have hcoeff : PowerSeries.coeff m (opcThetaOn P)
    = ((Nat.card {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = m} : ℕ) : ℤ) :=
    opc_coeff_weight (fun x : {x : ℤ // P x} => x.val.natAbs ^ 2) m
  rw [hcoeff] at hm
  have hfin := opc_finite_thetaOnFiber P m
  have hFT : Fintype {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = m} :=
    Fintype.ofFinite _
  have hpos : 0 < Nat.card {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = m} :=
    Nat.pos_of_ne_zero (by exact_mod_cast hm)
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff] at hpos
  obtain ⟨⟨x, hxP⟩, hx⟩ := hpos
  have hmx : x ^ 2 = (((m : ℕ)) : ℤ) := by
    have hx' : (((x.natAbs ^ 2 : ℕ)) : ℤ) = (((m : ℕ)) : ℤ) := by rw [hx]
    rwa [Nat.cast_pow, Int.natAbs_sq] at hx'
  have hr := hP x hxP
  rw [hmx] at hr
  rwa [Int.cast_natCast] at hr

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_finite_sumFiber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_finite_sumFiber {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
  (h₁ : ∀ k, Finite {a // w₁ a = k}) (h₂ : ∀ k, Finite {a // w₂ a = k})
  (k : ℕ) : Finite {x : α ⊕ β // Sum.elim w₁ w₂ x = k} := by
  have hf1 := h₁ k
  have hf2 := h₂ k
  have hF1 : Fintype {a : α // w₁ a = k} := Fintype.ofFinite _
  have hF2 : Fintype {b : β // w₂ b = k} := Fintype.ofFinite _
  have hFS : Fintype ({a : α // w₁ a = k} ⊕ {b : β // w₂ b = k}) := inferInstance
  have hFinS : Finite ({a : α // w₁ a = k} ⊕ {b : β // w₂ b = k}) :=
    Finite.of_fintype _
  exact @Finite.of_equiv _ _ hFinS (opcSumEquiv w₁ w₂ k).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_theta_eq_dissection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_theta_eq_dissection : opcTheta = opcA + opcB + opcC := by
  have hfinA : ∀ k, Finite
    {x : {x : ℤ // x % 5 = 0} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinB : ∀ k, Finite
    {x : {x : ℤ // x % 5 = 1 ∨ x % 5 = 4} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinC : ∀ k, Finite
    {x : {x : ℤ // x % 5 = 2 ∨ x % 5 = 3} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinAB : ∀ k, Finite {x : ({x : ℤ // x % 5 = 0}
    ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4}) //
    Sum.elim (fun x : {x : ℤ // x % 5 = 0} => x.val.natAbs ^ 2)
      (fun x : {x : ℤ // x % 5 = 1 ∨ x % 5 = 4} => x.val.natAbs ^ 2) x = k} :=
    fun k => opc_finite_sumFiber _ _ hfinA hfinB k
  change opcWeight (fun x : {x : ℤ // True} => x.val.natAbs ^ 2)
    = opcWeight (fun x : {x : ℤ // x % 5 = 0} => x.val.natAbs ^ 2)
    + opcWeight (fun x : {x : ℤ // x % 5 = 1 ∨ x % 5 = 4} => x.val.natAbs ^ 2)
    + opcWeight (fun x : {x : ℤ // x % 5 = 2 ∨ x % 5 = 3} => x.val.natAbs ^ 2)
  rw [← opc_weight_add _ _ hfinA hfinB, ← opc_weight_add _ _ hfinAB hfinC]
  symm
  exact opc_weight_congr _ _ opcSplit (fun p => by
    match p with
    | .inl (.inl ⟨x, _⟩) => rfl
    | .inl (.inr ⟨x, _⟩) => rfl
    | .inr ⟨x, _⟩ => rfl)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_coeff_mul_thetaOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_coeff_mul_thetaOn (P Q : ℤ → Prop) (N : ℕ) :
  PowerSeries.coeff N (opcThetaOn P * opcThetaOn Q)
    = ((Nat.card (opcSq P Q N) : ℕ) : ℤ) := by
  have hfinP : ∀ k, Finite {x : {x : ℤ // P x} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinQ : ∀ k, Finite {x : {x : ℤ // Q x} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have e : opcThetaOn P * opcThetaOn Q
    = opcWeight (fun p : {x : ℤ // P x} × {x : ℤ // Q x} =>
      p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2) :=
    (opc_weight_mul _ _ hfinP hfinQ).symm
  rw [e]
  simp only [opc_coeff_weight]
  rw [Nat.card_congr (opcFiberSqEquiv P Q N)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_dvd_of_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_dvd_of_sq (x y : ℤ) (N : ℕ)
  (h0 : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0)
  (heq : x ^ 2 + y ^ 2 = (((N : ℕ)) : ℤ)) : (5 : ℕ) ∣ N := by
  have e1 : (((((N : ℕ))) : ℤ) : ZMod 5) = ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) := by
    rw [← heq]
  have e : (((N : ℕ)) : ZMod 5) = 0 := e1.trans h0
  exact (ZMod.natCast_eq_zero_iff N 5).mp e

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_card_sq_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_card_sq_eq_zero (P Q : ℤ → Prop) (N : ℕ)
  (hPQ : ∀ x y : ℤ, P x → Q y → ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0)
  (hd : ¬ (5 : ℕ) ∣ N) : Nat.card (opcSq P Q N) = 0 := by
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun t => by
    obtain ⟨⟨x, y⟩, hP, hQ, heq⟩ := t
    exact hd (opc_dvd_of_sq x y N (hPQ x y hP hQ) heq)⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_finite_sqFiber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_finite_sqFiber (P Q : ℤ → Prop) (N : ℕ) :
  Finite (opcSq P Q N) := by
  have hfinP : ∀ k, Finite {x : {x : ℤ // P x} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinQ : ∀ k, Finite {x : {x : ℤ // Q x} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfin : Finite {p : {x : ℤ // P x} × {x : ℤ // Q x} //
    p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2 = N} :=
    opc_finite_prodFiber _ _ hfinP hfinQ N
  exact @Finite.of_equiv _ _ hfin (opcFiberSqEquiv P Q N)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_card_split](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_card_split (M : ℕ) : Nat.card (opcT M)
  = Nat.card (opcSq (fun x => x % 5 = 0) (fun x => x % 5 = 0) (5 * M))
    + Nat.card (opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
      (fun x => x % 5 = 2 ∨ x % 5 = 3) (5 * M)) := by
  have hfin : Finite (opcSq (fun _ => True) (fun _ => True) M) :=
    opc_finite_sqFiber _ _ M
  have hT : Finite (opcT M) := Finite.of_equiv _ (opcPhi M)
  have hdiv : Finite {t : opcT M // (5 : ℤ) ∣ t.val.2} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hndiv : Finite {t : opcT M // ¬ (5 : ℤ) ∣ t.val.2} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have eT := Equiv.sumCompl (fun t : opcT M => (5 : ℤ) ∣ t.val.2)
  rw [← Nat.card_congr eT, Nat.card_sum, Nat.card_congr (opcPart1 M),
    Nat.card_congr (opcPart2 M)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_five_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_five_ne_zero : (5 : ℕ) ≠ 0 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_tsum_sq_mul_eulerFunction_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_tsum_sq_mul_eulerFunction_sq (q : ℂ) (hq : ‖q‖ < 1) :
  (∑' n : ℤ, q ^ (n * n).toNat) * eulerFunction (q ^ 2)
    = eulerFunction (-q) ^ 2 := by
  have hJ := MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product
    1 q one_ne_zero hq
  obtain ⟨hs, hm, heq⟩ := hJ
  have hgeo : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hq
  have hVnorm : Summable fun n : ℕ => ‖q ^ (2 * n + 1)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeo
    intro n
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt hq) (by omega)
  have hUnorm : Summable fun n : ℕ => ‖q ^ (2 * n + 2)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeo
    intro n
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt hq) (by omega)
  have mV : Multipliable fun n : ℕ => (1 + q ^ (2 * n + 1)) :=
    multipliable_one_add_of_summable hVnorm
  have mU : Multipliable fun n : ℕ => (1 - q ^ (2 * n + 2)) := by
    have hUneg : Summable fun n : ℕ => ‖-(q ^ (2 * n + 2))‖ :=
      (summable_congr (fun n : ℕ => norm_neg _)).mpr hUnorm
    have h := multipliable_one_add_of_summable
      (f := fun n : ℕ => (-(q ^ (2 * n + 2)))) hUneg
    have eU : ∀ n : ℕ, (1 + (-(q ^ (2 * n + 2)))) = (1 - q ^ (2 * n + 2)) :=
      fun n => by ring
    exact (multipliable_congr eU).mp h
  have mA : Multipliable fun n : ℕ =>
    ((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
      * (1 + q ^ (2 * n + 1))) :=
    (mU.mul mV).mul mV
  have eEven : ∀ k : ℕ, (1 + q ^ (2 * k + 1)) = (1 - (-q) ^ (2 * k + 1)) :=
    fun k => by rw [Odd.neg_pow ⟨k, rfl⟩ _, sub_neg_eq_add]
  have mEven : Multipliable fun k : ℕ => (1 - (-q) ^ (2 * k + 1)) :=
    (multipliable_congr eEven).mp mV
  have eOdd : ∀ k : ℕ, (1 - q ^ (2 * k + 2)) = (1 - (-q) ^ (2 * k + 1 + 1)) :=
    fun k => by
      rw [show (2 * k + 1) + 1 = 2 * k + 2 from by ring,
        Even.neg_pow ⟨k + 1, by ring⟩ _]
  have mOdd : Multipliable fun k : ℕ => (1 - (-q) ^ (2 * k + 1 + 1)) :=
    (multipliable_congr eOdd).mp mU
  have htsum : (∑' n : ℤ, q ^ (n * n).toNat)
    = ∏' n : ℕ, ((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
      * (1 + q ^ (2 * n + 1))) := by
    have e1 : (∑' n : ℤ, q ^ (n * n).toNat)
      = ∑' n : ℤ, (1 : ℂ) ^ n * q ^ (n * n).toNat :=
      tsum_congr fun n => by simp
    have e2 : (∏' n : ℕ, (1 - q ^ (2 * n + 2))
      * (1 + (1 : ℂ) * q ^ (2 * n + 1))
      * (1 + (1 : ℂ)⁻¹ * q ^ (2 * n + 1)))
      = ∏' n : ℕ, ((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
        * (1 + q ^ (2 * n + 1))) :=
      tprod_congr fun n => by simp
    rwa [e1, heq]
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have hmq : ‖-q‖ < 1 := by rwa [norm_neg]
  have eE2 : eulerFunction (q ^ 2)
    = ∏' n : ℕ, (1 - q ^ (2 * n + 2)) := by
    rw [eulerFunction_eq_tprod hq2]
    apply tprod_congr
    intro n
    have e : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [← pow_mul, e]
  have hsplit := tprod_even_mul_odd
    (f := fun m : ℕ => (1 - (-q) ^ (m + 1))) mEven mOdd
  have eEm : eulerFunction (-q)
    = (∏' n : ℕ, (1 + q ^ (2 * n + 1)))
      * (∏' n : ℕ, (1 - q ^ (2 * n + 2))) := by
    rw [eulerFunction_eq_tprod hmq, hsplit.symm]
    congr 1
    · exact tprod_congr (fun k : ℕ => by
      rw [Odd.neg_pow ⟨k, rfl⟩ _, sub_neg_eq_add])
    · exact tprod_congr (fun k : ℕ => by
      rw [show (2 * k + 1) + 1 = 2 * k + 2 from by ring,
        Even.neg_pow ⟨k + 1, by ring⟩ _])
  have mVU := mV.mul mU
  calc (∑' n : ℤ, q ^ (n * n).toNat) * eulerFunction (q ^ 2)
    = (∏' n : ℕ, ((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
      * (1 + q ^ (2 * n + 1))))
      * (∏' n : ℕ, (1 - q ^ (2 * n + 2))) := by rw [htsum, eE2]
    _ = ∏' n : ℕ, (((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
      * (1 + q ^ (2 * n + 1))) * (1 - q ^ (2 * n + 2))) :=
      (Multipliable.tprod_mul mA mU).symm
    _ = ∏' n : ℕ, (((1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 2)))
      * ((1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 2)))) :=
      tprod_congr (fun n : ℕ => by ring)
    _ = (∏' n : ℕ, ((1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 2))))
      * (∏' n : ℕ, ((1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 2)))) :=
      Multipliable.tprod_mul mVU mVU
    _ = ((∏' n : ℕ, (1 + q ^ (2 * n + 1)))
      * (∏' n : ℕ, (1 - q ^ (2 * n + 2))))
      * ((∏' n : ℕ, (1 + q ^ (2 * n + 1)))
        * (∏' n : ℕ, (1 - q ^ (2 * n + 2)))) := by
      rw [Multipliable.tprod_mul mV mU]
    _ = eulerFunction (-q) ^ 2 := by
      have e : (∏' n : ℕ, (1 + q ^ (2 * n + 1)))
        * (∏' n : ℕ, (1 - q ^ (2 * n + 2))) = eulerFunction (-q) :=
        eEm.symm
      rw [e]
      exact (pow_two _).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_hasSum_mul_of_abs_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_hasSum_mul_of_abs_summable (F G : ℤ⟦X⟧) (q : ℂ)
  (hF : Summable fun n : ℕ => ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖)
  (hG : Summable fun n : ℕ => ‖(((((G.coeff n : ℤ))) : ℂ)) * q ^ n‖) :
  HasSum (fun n : ℕ => ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n)
    ((∑' n : ℕ, (((((F.coeff n : ℤ))) : ℂ)) * q ^ n)
      * (∑' n : ℕ, (((((G.coeff n : ℤ))) : ℂ)) * q ^ n))
    ∧ Summable fun n : ℕ => ‖((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n‖ := by
  have hterm : ∀ n : ℕ, (∑ kl ∈ Finset.antidiagonal n,
    (((((F.coeff kl.1 : ℤ))) : ℂ)) * q ^ kl.1
      * ((((((G.coeff kl.2 : ℤ))) : ℂ)) * q ^ kl.2))
    = ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun kl hkl => ?_)
    obtain ⟨i, k⟩ := kl
    have hmem : i + k = n := Finset.mem_antidiagonal.mp hkl
    have hpair : (((((F.coeff i : ℤ))) : ℂ)) * q ^ i
      * ((((((G.coeff k : ℤ))) : ℂ)) * q ^ k)
      = (((((F.coeff i * G.coeff k : ℤ))) : ℂ)) * q ^ (i + k) := by
      rw [Int.cast_mul, pow_add]
      ring
    rwa [← hmem]
  have hnorm := summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG
  have htsum := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG
  have hHas : HasSum (fun n : ℕ => ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n)
    ((∑' n : ℕ, (((((F.coeff n : ℤ))) : ℂ)) * q ^ n)
      * (∑' n : ℕ, (((((G.coeff n : ℤ))) : ℂ)) * q ^ n)) := by
    have h2 := hnorm.of_norm.hasSum.congr_fun (fun n => (hterm n).symm)
    rwa [← htsum] at h2
  exact ⟨hHas, hHas.summable.norm⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_summable_norm_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_summable_norm_series (F : ℤ⟦X⟧) (C : ℝ) (q : ℂ)
  (hq : ‖q‖ < 1) (hC : ∀ n : ℕ, ‖(((((F.coeff n : ℤ))) : ℂ))‖ ≤ C) :
  Summable fun n : ℕ => ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖ := by
  have hgeo : Summable fun n : ℕ => C * ‖q‖ ^ n :=
    (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left C
  have h1 : Summable fun n : ℕ => ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeo
    intro n
    have e1 : ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖
      = ‖(((((F.coeff n : ℤ))) : ℂ))‖ * ‖q‖ ^ n := by
      rw [norm_mul, norm_pow]
    rw [e1]
    exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg _) n)
  exact h1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_sq_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_sq_toNat (x : ℤ) : (x * x).toNat = x.natAbs ^ 2 := by
  have hnn : 0 ≤ x * x := mul_self_nonneg x
  have h : (((x * x).toNat : ℕ) : ℤ) = (((x.natAbs ^ 2 : ℕ)) : ℤ) := by
    rw [Int.toNat_of_nonneg hnn, Nat.cast_pow, Int.natAbs_sq, ← pow_two]
  exact_mod_cast h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_summable_sq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_summable_sq_pow (q : ℂ) (hq : ‖q‖ < 1) :
  Summable fun x : ℤ => q ^ (x * x).toNat := by
  have hgeo : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hq
  have hside : Summable fun x : ℤ => ‖q‖ ^ x.natAbs := by
    apply Summable.of_nat_of_neg
    · simpa using hgeo
    · simpa using hgeo
  refine Summable.of_norm_bounded hside ?_
  intro x
  rw [opc_sq_toNat, norm_pow]
  have hle : x.natAbs ≤ x.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
  exact pow_le_pow_of_le_one (norm_nonneg _) hq.le hle

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_theta_coeff_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_theta_coeff_eq_card (m : ℕ) :
  opcTheta.coeff m = ((Nat.card {x : ℤ // x.natAbs ^ 2 = m} : ℕ) : ℤ) := by
  unfold opcTheta opcThetaOn opcWeight
  rw [PowerSeries.coeff_mk]
  exact congrArg _ (Nat.card_congr (opcThetaFiber m))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_fiber_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_fiber_hasSum (q : ℂ) (m : ℕ) :
  HasSum (fun x : {x : ℤ // x.natAbs ^ 2 = m} => q ^ (x.val * x.val).toNat)
    (((((opcTheta.coeff m : ℤ)) : ℂ)) * q ^ m) := by
  have hfin := opc_finite_intFiber m
  have hFT : Fintype {x : ℤ // x.natAbs ^ 2 = m} := Fintype.ofFinite _
  have hterm : ∀ x : {x : ℤ // x.natAbs ^ 2 = m},
    q ^ (x.val * x.val).toNat = q ^ m := by
    intro x
    congr 1
    rwa [opc_sq_toNat]
  have hsum : (∑ x : {x : ℤ // x.natAbs ^ 2 = m}, q ^ (x.val * x.val).toNat)
    = (((((opcTheta.coeff m : ℤ)) : ℂ)) * q ^ m) := by
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [opc_theta_coeff_eq_card, Nat.card_eq_fintype_card, Int.cast_natCast]
  rw [← hsum]
  exact hasSum_fintype _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_eval_thetaSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_eval_thetaSeries (q : ℂ) (hq : ‖q‖ < 1) :
  (∑' n : ℕ, (((((opcTheta.coeff n : ℤ))) : ℂ)) * q ^ n)
    = ∑' n : ℤ, q ^ (n * n).toNat := by
  have hbase := (opc_summable_sq_pow q hq).hasSum
  have hsig := (Equiv.hasSum_iff opcSigmaTheta).mpr hbase
  have hmain : HasSum (fun n : ℕ => (((((opcTheta.coeff n : ℤ))) : ℂ)) * q ^ n)
    (∑' n : ℤ, q ^ (n * n).toNat) :=
    HasSum.sigma hsig (fun m => opc_fiber_hasSum q m)
  exact hmain.tsum_eq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_coeff_pent_complex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_coeff_pent_complex_eq (n : ℕ) :
  (PowerSeries.pentagonalSeries ℂ).coeff n
    = ((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ) := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    have h1 : (PowerSeries.pentagonalSeries ℂ).coeff (pentagonal k)
      = (-1 : ℂ) ^ k.natAbs := by
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    have h2 : ((((PowerSeries.pentagonalSeries ℤ).coeff (pentagonal k) : ℤ)) : ℂ)
      = (-1 : ℂ) ^ k.natAbs := by
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [h1, h2]
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hn,
    PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, Int.cast_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_norm_pentCoeff_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_norm_pentCoeff_le_one (n : ℕ) :
  ‖(((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ))‖ ≤ 1 := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow,
      Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow]
    simp
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, Int.cast_zero, norm_zero]
    exact zero_le_one

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_eval_expand_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_eval_expand_two (q : ℂ) (hq : ‖q‖ < 1) :
  (∑' n : ℕ, ((((((PowerSeries.expand 2 two_ne_zero
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ))) : ℂ)) * q ^ n)
    = eulerFunction (q ^ 2) := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have heuler := hasSum_eulerFunction_pentagonalSeries hq2
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    dsimp only at h
    omega
  have hsupp : Function.support (fun n : ℕ => (((((PowerSeries.expand 2
    two_ne_zero (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ))) : ℂ) * q ^ n)
    ⊆ Set.range (fun k : ℕ => 2 * k) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hd : 2 ∣ n
    · obtain ⟨k, hk⟩ := hd
      exact ⟨k, hk.symm⟩
    · exfalso
      apply hn
      rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd, Int.cast_zero, zero_mul]
  have hterm : ∀ k : ℕ, (((((PowerSeries.expand 2 two_ne_zero
    (PowerSeries.pentagonalSeries ℤ)).coeff (2 * k) : ℤ))) : ℂ) * q ^ (2 * k)
      = (PowerSeries.pentagonalSeries ℂ).coeff k * (q ^ 2) ^ k := by
    intro k
    rw [PowerSeries.coeff_expand_mul, ← opc_coeff_pent_complex_eq, pow_mul]
  rwa [← hinj.tsum_eq hsupp, tsum_congr hterm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_eval_rescale_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_eval_rescale_neg (q : ℂ) (hq : ‖q‖ < 1) :
  (∑' n : ℕ, ((((((PowerSeries.rescale (-1 : ℤ)
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ))) : ℂ)) * q ^ n)
    = eulerFunction (-q) := by
  have hmq : ‖-q‖ < 1 := by rwa [norm_neg]
  have heuler := hasSum_eulerFunction_pentagonalSeries hmq
  have hterm : ∀ n : ℕ, (((((PowerSeries.rescale (-1 : ℤ)
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ))) : ℂ) * q ^ n
      = (PowerSeries.pentagonalSeries ℂ).coeff n * (-q) ^ n := by
    intro n
    rw [PowerSeries.coeff_rescale, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, ← opc_coeff_pent_complex_eq]
    ring
  rwa [tsum_congr hterm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_coeff_eq_zero_of_tsum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private theorem opc_coeff_eq_zero_of_tsum_eq_zero (c : ℕ → ℂ) (r : ℝ)
  (hr : 0 < r) (hs : Summable fun n : ℕ => ‖c n‖ * r ^ n)
  (hz : ∀ q : ℂ, ‖q‖ < r → (∑' n : ℕ, c n * q ^ n) = 0) :
  ∀ n : ℕ, c n = 0 := by
  have hnorm : ∀ n : ℕ,
    ‖FormalMultilinearSeries.ofScalars ℂ c n‖ = ‖c n‖ :=
    fun n => FormalMultilinearSeries.ofScalars_norm ℂ c n
  set rnn : NNReal := ⟨r, hr.le⟩
  have hrr : (rnn : ℝ) = r := rfl
  have hs' : Summable fun n : ℕ =>
    ‖FormalMultilinearSeries.ofScalars ℂ c n‖ * (rnn : ℝ) ^ n := by
    rw [hrr]
    simp_rw [hnorm]
    exact hs
  have hle : ((rnn : ENNReal)) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    FormalMultilinearSeries.le_radius_of_summable_norm _ hs'
  have hpos : (0 : ENNReal) < ((rnn : ENNReal)) := by
    have h0 : (0 : NNReal) < rnn := hr
    exact_mod_cast h0
  have hrad : 0 < (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    lt_of_lt_of_le hpos hle
  have hAt : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ c).sum
    (FormalMultilinearSeries.ofScalars ℂ c) 0 :=
    (FormalMultilinearSeries.hasFPowerSeriesOnBall _ hrad).hasFPowerSeriesAt
  have hval : ∀ q : ℂ, (FormalMultilinearSeries.ofScalars ℂ c).sum q
    = ∑' n : ℕ, c n * q ^ n := by
    intro q
    have e := FormalMultilinearSeries.ofScalars_sum_eq c q
    simp only [smul_eq_mul] at e
    exact e
  have hev : (FormalMultilinearSeries.ofScalars ℂ c).sum =ᶠ[nhds (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with q hq
    have hqr : ‖q‖ < r := by
      have hmem : dist q 0 < r := hq
      rwa [dist_zero_right] at hmem
    rw [hval q]
    exact hz q hqr
  have hpeq : FormalMultilinearSeries.ofScalars ℂ c = 0 :=
    hAt.eq_zero_of_eventually hev
  intro n
  have h0n : FormalMultilinearSeries.ofScalars ℂ c n = 0 := by
    rw [hpeq]
    rfl
  exact (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) n).mp h0n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_theta_coeff_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_theta_coeff_bound (m : ℕ) :
  ‖(((((opcTheta.coeff m : ℤ))) : ℂ))‖ ≤ 2 := by
  have hcard2 : Nat.card {x : ℤ // x.natAbs ^ 2 = m} ≤ 2 := by
    by_cases hne : Nonempty {x : ℤ // x.natAbs ^ 2 = m}
    · obtain ⟨a₀⟩ := hne
      have hmem : ∀ x : {x : ℤ // x.natAbs ^ 2 = m},
        x.val = a₀.val ∨ x.val = -a₀.val := by
        intro x
        have e1 : x.val.natAbs ^ 2 = a₀.val.natAbs ^ 2 := by
          rw [x.property, a₀.property]
        have e2 : x.val ^ 2 = a₀.val ^ 2 := by
          have hx : ((((x.val.natAbs ^ 2 : ℕ))) : ℤ) = x.val ^ 2 := by
            rw [Nat.cast_pow, Int.natAbs_sq]
          have ha : ((((a₀.val.natAbs ^ 2 : ℕ))) : ℤ) = a₀.val ^ 2 := by
            rw [Nat.cast_pow, Int.natAbs_sq]
          have e1c : ((((x.val.natAbs ^ 2 : ℕ))) : ℤ)
            = ((((a₀.val.natAbs ^ 2 : ℕ))) : ℤ) := by rw [e1]
          rwa [hx, ha] at e1c
        exact (sq_eq_sq_iff_eq_or_eq_neg (a := x.val) (b := a₀.val)).mp e2
      classical
      have hinj : Function.Injective (fun x : {x : ℤ // x.natAbs ^ 2 = m} =>
        if x.val = a₀.val then (0 : Fin 2) else 1) := by
        intro x y hxy
        by_cases hx : x.val = a₀.val <;> by_cases hy : y.val = a₀.val
        · exact Subtype.ext (by rw [hx, hy])
        · simp [hx, hy] at hxy
        · simp [hx, hy] at hxy
        · have hx' := (hmem x).resolve_left hx
          have hy' := (hmem y).resolve_left hy
          exact Subtype.ext (by rw [hx', hy'])
      have hfinT := opc_finite_intFiber m
      have hFT : Fintype {x : ℤ // x.natAbs ^ 2 = m} := Fintype.ofFinite _
      calc Nat.card {x : ℤ // x.natAbs ^ 2 = m}
        = Fintype.card {x : ℤ // x.natAbs ^ 2 = m} :=
          Nat.card_eq_fintype_card
        _ ≤ Fintype.card (Fin 2) := Fintype.card_le_of_injective _ hinj
        _ = 2 := Fintype.card_fin 2
    · have h0 : Nat.card {x : ℤ // x.natAbs ^ 2 = m} = 0 :=
      Nat.card_eq_zero.mpr (Or.inl ⟨fun t => hne ⟨t⟩⟩)
      omega
  rw [opc_theta_coeff_eq_card, Int.cast_natCast, Complex.norm_natCast]
  exact_mod_cast hcard2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_norm_expand_coeff_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_norm_expand_coeff_le_one (n : ℕ) :
  ‖(((PowerSeries.expand 2 two_ne_zero
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℂ))‖ ≤ 1 := by
  by_cases hd : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hd
    rw [PowerSeries.coeff_expand_mul]
    exact opc_norm_pentCoeff_le_one k
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd, Int.cast_zero, norm_zero]
    exact zero_le_one

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_norm_rescale_coeff_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_norm_rescale_coeff_le_one (n : ℕ) :
  ‖(((PowerSeries.rescale (-1 : ℤ)
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℂ))‖ ≤ 1 := by
  rw [PowerSeries.coeff_rescale, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact opc_norm_pentCoeff_le_one n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_gauss_diff_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_gauss_diff_summable :
  Summable fun n : ℕ => ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
    - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
      * PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
    * (1 / 2 : ℝ) ^ n := by
  have hq0 : ‖(((1 / 2 : ℝ)) : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_real]
    norm_num
  have hq0lt : ‖(((1 / 2 : ℝ)) : ℂ)‖ < 1 := by rw [hq0]; norm_num
  have hTh := opc_summable_norm_series opcTheta 2 _ hq0lt
    (fun n => opc_theta_coeff_bound n)
  have hExp := opc_summable_norm_series _ 1 _ hq0lt
    (fun n => opc_norm_expand_coeff_le_one n)
  have hRe := opc_summable_norm_series _ 1 _ hq0lt
    (fun n => opc_norm_rescale_coeff_le_one n)
  obtain ⟨hLHS, hLHSn⟩ := opc_hasSum_mul_of_abs_summable _ _ _ hTh hExp
  obtain ⟨hRHS, hRHSn⟩ := opc_hasSum_mul_of_abs_summable _ _ _ hRe hRe
  have hsum := hLHSn.add hRHSn
  have hq0n : ∀ n : ℕ, ‖(((1 / 2 : ℝ)) : ℂ) ^ n‖ = (1 / 2 : ℝ) ^ n := by
    intro n
    rw [norm_pow, hq0]
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (by norm_num) _)) ?_ hsum
  intro n
  have hle : ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
    - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
      * PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
    ≤ ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
      + ‖((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
      * PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖ :=
    norm_sub_le _ _
  calc ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
    - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
    * PowerSeries.rescale (-1 : ℤ)
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
    * (1 / 2 : ℝ) ^ n
    ≤ (‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
      + ‖((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
      * PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖)
      * (1 / 2 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right hle (pow_nonneg (by norm_num) _)
    _ = ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
      * ‖(((1 / 2 : ℝ)) : ℂ) ^ n‖
      + ‖((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
      * PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
      * ‖(((1 / 2 : ℝ)) : ℂ) ^ n‖ := by
      rw [hq0n n]
      ring
    _ = ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
      * (((1 / 2 : ℝ)) : ℂ) ^ n‖
      + ‖((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
      * PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
      * (((1 / 2 : ℝ)) : ℂ) ^ n‖ := by
      rw [norm_mul, norm_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_gauss_diff_tsum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_gauss_diff_tsum_eq_zero (q : ℂ) (hq : ‖q‖ < 1 / 2) :
  (∑' n : ℕ, (((((opcTheta * PowerSeries.expand 2 two_ne_zero
    (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
    - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
      * PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)) * q ^ n) = 0 := by
  have hq1 : ‖q‖ < 1 := lt_trans hq (by norm_num)
  have hTh := opc_summable_norm_series opcTheta 2 q hq1
    (fun n => opc_theta_coeff_bound n)
  have hExp := opc_summable_norm_series _ 1 q hq1
    (fun n => opc_norm_expand_coeff_le_one n)
  have hRe := opc_summable_norm_series _ 1 q hq1
    (fun n => opc_norm_rescale_coeff_le_one n)
  obtain ⟨hLHS, -⟩ := opc_hasSum_mul_of_abs_summable _ _ q hTh hExp
  obtain ⟨hRHS, -⟩ := opc_hasSum_mul_of_abs_summable _ _ q hRe hRe
  have h := hLHS.sub hRHS
  rw [opc_eval_thetaSeries q hq1, opc_eval_expand_two q hq1,
    opc_eval_rescale_neg q hq1] at h
  have hN4 := opc_tsum_sq_mul_eulerFunction_sq q hq1
  have h0 : (∑' n : ℤ, q ^ (n * n).toNat) * eulerFunction (q ^ 2)
    - eulerFunction (-q) * eulerFunction (-q) = 0 := by
    linear_combination hN4
  rw [h0] at h
  have h2 := h.congr_fun (fun n => sub_mul _ _ _)
  exact h2.tsum_eq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_theta_mul_expand_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_theta_mul_expand_two :
  opcTheta * PowerSeries.expand 2 two_ne_zero (PowerSeries.pentagonalSeries ℤ)
    = (PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)) ^ 2 := by
  have hpow : (PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)) ^ 2
    = (PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ))
      * (PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)) :=
    pow_two _
  rw [hpow]
  apply PowerSeries.ext
  intro n
  apply Int.cast_injective (α := ℂ)
  have hcz := opc_coeff_eq_zero_of_tsum_eq_zero
    (fun n : ℕ => ((((opcTheta * PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
      - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
        * PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ))
    (1 / 2 : ℝ) (by norm_num) opc_gauss_diff_summable
    (fun q hq => opc_gauss_diff_tsum_eq_zero q hq)
  have h0 := hcz n
  exact sub_eq_zero.mp h0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_pent_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_pent_coeff_zero :
  (PowerSeries.pentagonalSeries ℤ).coeff 0 = 1 := by
  have h0 : pentagonal (0 : ℤ) = 0 := by
    rw [pentagonal_def]
    norm_num
  have h1 : Int.negOnePow (0 : ℤ) = 1 := by decide
  have h := PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℤ) (0 : ℤ)
  rwa [h0, h1] at h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_rescale_expand_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_rescale_expand_two :
  PowerSeries.rescale (-1 : ℤ)
    (PowerSeries.expand 2 two_ne_zero (PowerSeries.pentagonalSeries ℤ))
    = PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_rescale]
  by_cases hd : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hd
    have h1 : (-1 : ℤ) ^ (2 * k) = 1 := Even.neg_one_pow ⟨k, by ring⟩
    rw [h1, one_mul]
  · have h0 : (PowerSeries.expand 2 two_ne_zero
    (PowerSeries.pentagonalSeries ℤ)).coeff n = 0 :=
    PowerSeries.coeff_expand_of_not_dvd _ _ _ hd
    rw [h0, mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[opc_theta_mul_rescale_genFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma opc_theta_mul_rescale_genFun :
  opcTheta * PowerSeries.rescale (-1 : ℤ)
    (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))) = 1 := by
  have hmap := congrArg (PowerSeries.rescale (-1 : ℤ))
    opc_genFun_two_mul_pentagonalSeries_sq
  rw [map_mul, map_pow, opc_rescale_expand_two] at hmap
  have hmul := congrArg (opcTheta * ·) hmap
  rw [← mul_assoc, opc_theta_mul_expand_two] at hmul
  have hbase : PowerSeries.rescale (-1 : ℤ)
    (PowerSeries.pentagonalSeries ℤ) ≠ 0 := by
    intro hcon
    have h0 : (PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff 0 = 0 := by
      rw [hcon]
      simp
    rw [PowerSeries.coeff_rescale, pow_zero, one_mul,
      opc_pent_coeff_zero] at h0
    exact one_ne_zero h0
  have hC : (PowerSeries.rescale (-1 : ℤ)
    (PowerSeries.pentagonalSeries ℤ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hbase
  have hmul2 : (opcTheta * PowerSeries.rescale (-1 : ℤ)
    (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))))
    * (PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)) ^ 2
    = 1 * (PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)) ^ 2 := by
    rwa [one_mul]
  exact mul_right_cancel₀ hC hmul2

end MetaMathlibExt

namespace Nat.Overpartition

/--
[natCard_eq_card_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
lemma natCard_eq_card_subtype
  {m : ℕ} :
-- imply
  Nat.card (Nat.Overpartition m) =
    Nat.card { p : Multiset ℕ × Finset ℕ //
      (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = m ∧ ∀ a ∈ p.2, a ∈ p.1 } := by
-- proof
  apply Nat.card_congr
  exact
    { toFun := fun O =>
      ⟨(O.toPartition.parts, O.overlines), fun a ha => O.toPartition.parts_pos ha,
        O.toPartition.parts_sum,
        fun a ha => Multiset.mem_toFinset.mp (O.overlines_subset ha)⟩
      invFun := fun p =>
        { toPartition :=
          { parts := p.val.1
            parts_pos := fun {a} ha => p.property.1 a ha
            parts_sum := p.property.2.1 }
          overlines := p.val.2
          overlines_subset := fun a ha =>
            Multiset.mem_toFinset.mpr (p.property.2.2 a ha) }
      left_inv := fun O => by
        obtain ⟨P, S, hsub⟩ := O
        obtain ⟨M, hpos, hsum⟩ := P
        apply Nat.Overpartition.ext
        · apply Nat.Partition.ext
          rfl
        · rfl
      right_inv := fun p => by
        obtain ⟨⟨M, S⟩, hpos, hsum, hsub⟩ := p
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · rfl }

end Nat.Overpartition

namespace Nat

/--
[threeSquareRepresentationCount_eq_natCard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
lemma threeSquareRepresentationCount_eq_natCard
  {n : ℕ} :
-- imply
  Nat.threeSquareRepresentationCount n =
    Nat.card { x : ℤ × ℤ × ℤ //
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ) } := by
-- proof
  have single : ∀ w y z : ℤ, w ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ) →
    w ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro w y z h
    rw [Finset.mem_Icc]
    have hby : 0 ≤ y ^ 2 := sq_nonneg y
    have hbz : 0 ≤ z ^ 2 := sq_nonneg z
    have hle : w ^ 2 ≤ (n : ℤ) := by omega
    have h1 : w ≤ w ^ 2 := Int.le_self_sq w
    have h2 : -w ≤ (-w) ^ 2 := Int.le_self_sq (-w)
    have hneg : (-w) ^ 2 = w ^ 2 := by ring
    rw [hneg] at h2
    constructor <;> omega
  have hbound : ∀ p : (ℤ × ℤ) × ℤ,
    p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ) →
    p.1.1 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) ∧
      p.1.2 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) ∧
      p.2 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro p h
    refine ⟨single p.1.1 p.1.2 p.2 h, ?_, ?_⟩
    · have h' : p.1.2 ^ 2 + p.1.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
      linear_combination h
      exact single p.1.2 p.1.1 p.2 h'
    · have h'' : p.2 ^ 2 + p.1.1 ^ 2 + p.1.2 ^ 2 = (n : ℤ) := by
      linear_combination h
      exact single p.2 p.1.1 p.1.2 h''
  have eAssoc : { x : ℤ × ℤ × ℤ //
    x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ) } ≃
    { p : (ℤ × ℤ) × ℤ //
      p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ) } :=
    (Equiv.subtypeEquiv (Equiv.prodAssoc ℤ ℤ ℤ) (fun p => Iff.rfl)).symm
  have eFilter : { p : (ℤ × ℤ) × ℤ //
    p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ) } ≃
    ↥(Finset.filter
      (fun p : (ℤ × ℤ) × ℤ =>
        p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ))
      (Finset.product
        (Finset.product
          (Finset.Icc (-(n : ℤ)) (n : ℤ))
          (Finset.Icc (-(n : ℤ)) (n : ℤ)))
        (Finset.Icc (-(n : ℤ)) (n : ℤ)))) := by
    apply Equiv.subtypeEquiv (Equiv.refl _)
    intro p
    simp only [Equiv.refl_apply]
    constructor
    · intro h
      rw [Finset.mem_filter]
      obtain ⟨ha, hb, hc⟩ := hbound p h
      refine ⟨?_, h⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩
    · intro h
      exact (Finset.mem_filter.mp h).2
  unfold threeSquareRepresentationCount
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (eFilter.symm.trans eAssoc.symm)
end Nat


namespace MetaMathlibExt

/--
[overpartition_card_mul_five_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
lemma overpartition_card_mul_five_modEq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  Int.ModEq 5 (Nat.card (Nat.Overpartition (5 * n)))
    (((-1 : ℤ) ^ n) * Nat.threeSquareRepresentationCount n) := by
-- proof
  rw [Nat.Overpartition.natCard_eq_card_subtype,
    Nat.threeSquareRepresentationCount_eq_natCard]
  exact overpartition_mul_five_mod_five n hn

end MetaMathlibExt

/--
[overpartition_mul_five_mod_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma overpartition_mul_five_mod_five_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  Int.ModEq 5
    (Nat.card {
    p : Multiset ℕ × Finset ℕ //
    (∀ a ∈ p.1, 0 < a) ∧
    p.1.sum = 5 * n ∧
    ∀ a ∈ p.2, a ∈ p.1
    })
    (((-1 : ℤ) ^ n) * Nat.card {
    x : ℤ × ℤ × ℤ //
    x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = n
    }) := by
-- proof
  apply MetaMathlibExt.overpartition_mul_five_mod_five n hn


-- created on 2026-10-20
-- updated on 2026-10-26
