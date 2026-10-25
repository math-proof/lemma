import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.Perfect
import Class.AlgebraicCurve_DivisorClassGroup
import Instance.JacJ1_ChartAlgebra

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain IntermediateField

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

def aevalAdjoin (s : L) : K[X] →ₐ[K] Algebra.adjoin K ({s} : Set L) :=
  (aeval (R := K) s).codRestrict (Algebra.adjoin K ({s} : Set L))
    (fun p => by simp [Algebra.adjoin_singleton_eq_range_aeval])

theorem aevalAdjoin_surjective (s : L) : Function.Surjective (aevalAdjoin K s) := by
  rintro ⟨x, hx⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, rfl⟩ := hx
  exact ⟨p, rfl⟩

def chartRing (S : Set L) : Subalgebra K L where
  carrier := {x | IsIntegral (Algebra.adjoin K S) x}
  mul_mem' ha hb := ha.mul hb
  one_mem' := isIntegral_one
  add_mem' ha hb := ha.add hb
  zero_mem' := isIntegral_zero
  algebraMap_mem' a := by
    have : IsIntegral (Algebra.adjoin K S)
        (algebraMap (Algebra.adjoin K S) L (algebraMap K (Algebra.adjoin K S) a)) :=
      isIntegral_algebraMap
    simpa [← IsScalarTower.algebraMap_apply] using this

theorem mem_chartRing_iff {S : Set L} {x : L} :
    x ∈ chartRing K S ↔ IsIntegral (Algebra.adjoin K S) x := Iff.rfl

theorem adjoin_le_chartRing (S : Set L) : Algebra.adjoin K S ≤ chartRing K S := by
  intro x hx
  rw [mem_chartRing_iff]
  have : IsIntegral (Algebra.adjoin K S) (algebraMap (Algebra.adjoin K S) L ⟨x, hx⟩) :=
    isIntegral_algebraMap
  exact this

theorem subset_chartRing (S : Set L) : S ⊆ (chartRing K S : Set L) := fun _ hx =>
  adjoin_le_chartRing K S (Algebra.subset_adjoin hx)

theorem chartRing_mono {S S' : Set L} (h : S ⊆ S') : chartRing K S ≤ chartRing K S' := by
  intro x hx
  rw [mem_chartRing_iff] at hx ⊢
  have := hx.map_of_comp_eq (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom
    (RingHom.id L) (by ext a; rfl)
  simpa using this

abbrev chartIncl {S S' : Set L} (h : S ⊆ S') : chartRing K S →ₐ[K] chartRing K S' :=
  Subalgebra.inclusion (chartRing_mono K h)

theorem coe_chartIncl {S S' : Set L} (h : S ⊆ S') (x : chartRing K S) :
    (chartIncl K h x : L) = x :=

  Subalgebra.coe_inclusion _ x

theorem chartIncl_injective {S S' : Set L} (h : S ⊆ S') :
    Function.Injective (chartIncl K h) :=
  Subalgebra.inclusion_injective _


section OneGenerator

variable (s : L) [FiniteDimensional K⟮s⟯ L] [CharZero K]

open scoped IntermediateField.algebraAdjoinAdjoin in


end OneGenerator

section Valuation

variable {K}

theorem adjoin_le_valuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) {S : Set L} (hS : S ⊆ O) {y : L}
    (hy : y ∈ Algebra.adjoin K S) : y ∈ O := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact hS hy
  | algebraMap a => exact hK a
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

def _root_.ValuationSubring.toSubalgebraOfBase (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) : Subalgebra K L :=
  { O.toSubring with algebraMap_mem' := hK }

theorem _root_.ValuationSubring.mem_toSubalgebraOfBase_iff (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) {x : L} : x ∈ O.toSubalgebraOfBase hK ↔ x ∈ O :=
  Iff.rfl

theorem _root_.ValuationSubring.integers_toSubalgebraOfBase (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) : O.valuation.Integers (O.toSubalgebraOfBase hK) where
  hom_inj := Subtype.val_injective
  map_le_one a := (O.valuation_le_one_iff _).mpr a.2
  exists_of_le_one r hr := ⟨⟨r, O.mem_of_valuation_le_one r hr⟩, rfl⟩

theorem chartRing_le_valuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) {S : Set L} (hS : S ⊆ O) {x : L}
    (hx : x ∈ chartRing K S) : x ∈ O := by
  have hle : Algebra.adjoin K S ≤ O.toSubalgebraOfBase hK :=
    fun y hy => adjoin_le_valuationSubring O hK hS hy
  have hxO : IsIntegral (O.toSubalgebraOfBase hK) x := by
    have := ((mem_chartRing_iff K).mp hx).map_of_comp_eq (Subalgebra.inclusion hle).toRingHom
      (RingHom.id L) (by ext a; rfl)
    simpa using this
  exact O.mem_of_valuation_le_one x
    ((O.integers_toSubalgebraOfBase hK).isIntegral_iff_v_le_one.mp hxO)

variable (K)
variable (s : L)

def centre (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) :
    Ideal (chartRing K ({s} : Set L)) where
  carrier := {a | O.valuation a < 1}
  add_mem' {a b} ha hb := lt_of_le_of_lt (O.valuation.map_add a b) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c a ha := by
    have hc : O.valuation c ≤ 1 := (O.valuation_le_one_iff _).mpr
      (chartRing_le_valuationSubring O hK (Set.singleton_subset_iff.mpr hs) c.2)
    show O.valuation ((c : L) * a) < 1
    rw [map_mul]
    exact mul_lt_of_le_one_of_lt hc ha

theorem mem_centre_iff (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (a : chartRing K ({s} : Set L)) :
    a ∈ centre K s O hK hs ↔ O.valuation a < 1 := Iff.rfl

theorem valuation_coe_le_one (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (a : chartRing K ({s} : Set L)) : O.valuation a ≤ 1 :=
  (O.valuation_le_one_iff _).mpr
    (chartRing_le_valuationSubring O hK (Set.singleton_subset_iff.mpr hs) a.2)

theorem valuation_eq_one_of_not_mem_centre (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) {a : chartRing K ({s} : Set L)}
    (ha : a ∉ centre K s O hK hs) : O.valuation a = 1 :=
  le_antisymm (valuation_coe_le_one K s O hK hs a) (not_lt.mp ha)


def chartPlaces (s : L) : Set (Place K L) := {v | s ∈ v.toValuationSubring}

theorem mem_chartPlaces_iff {s : L} {v : Place K L} :
    v ∈ chartPlaces K s ↔ s ∈ v.toValuationSubring := Iff.rfl

theorem mem_chartPlaces_or_mem_chartPlaces_inv (v : Place K L) (t : L) :
    v ∈ chartPlaces K t ∨ v ∈ chartPlaces K t⁻¹ :=
  v.toValuationSubring.mem_or_inv_mem t

variable [FiniteDimensional K⟮s⟯ L] [CharZero K]

omit [CharZero K] in

theorem centre_ne_bot (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) : centre K s O hK hs ≠ ⊥ := by
  intro hbot
  apply hO
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := chartRing K ({s} : Set L)) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbc : b ∉ centre K s O hK hs := by rw [hbot]; simpa using hb0
  apply O.mem_of_valuation_le_one
  rw [map_div₀, show O.valuation (algebraMap _ L b) = 1 from
    valuation_eq_one_of_not_mem_centre K s O hK hs hbc, div_one]
  exact valuation_coe_le_one K s O hK hs a

def primeOfValuationSubring (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) : HeightOneSpectrum (chartRing K ({s} : Set L)) :=
  ⟨centre K s O hK hs, inferInstance, centre_ne_bot K s O hK hs hO⟩

theorem valuationSubringAtPrime_le (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime L (primeOfValuationSubring K s O hK hs hO) ≤ O := by
  intro x hx
  have hx' : ∃ (a b : chartRing K ({s} : Set L)) (_ : b ∈ (centre K s O hK hs).primeCompl),
      x = algebraMap _ L a * (algebraMap _ L b)⁻¹ := hx
  obtain ⟨a, b, hb, rfl⟩ := hx'
  apply O.mem_of_valuation_le_one
  rw [map_mul, map_inv₀, show O.valuation (algebraMap _ L b) = 1 from
    valuation_eq_one_of_not_mem_centre K s O hK hs hb, inv_one, mul_one]
  exact valuation_coe_le_one K s O hK hs a

theorem valuationSubringAtPrime_primeOfValuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime L (primeOfValuationSubring K s O hK hs hO) = O :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le K s O hK hs hO) hO

theorem exists_ofHeightOneSpectrum_eq (v : Place K L) (hs : s ∈ v.toValuationSubring) :
    ∃ 𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L)),
      Place.ofHeightOneSpectrum (K := K) 𝔭 = v := by
  refine ⟨primeOfValuationSubring K s v.toValuationSubring v.algebraMap_mem' hs v.ne_top', ?_⟩
  apply Place.ext
  rw [Place.ofHeightOneSpectrum_toValuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact valuationSubringAtPrime_primeOfValuationSubring K s _ _ hs _

theorem mem_ofHeightOneSpectrum (𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L))) :
    s ∈ (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring := by
  rw [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
  exact 𝔭.valuation_le_one (K := L)
    (⟨s, subset_chartRing K ({s} : Set L) (Set.mem_singleton s)⟩ : chartRing K ({s} : Set L))

theorem ofHeightOneSpectrum_injective :
    Function.Injective
      (Place.ofHeightOneSpectrum (K := K) (F := L) (R := chartRing K ({s} : Set L))) := by
  intro 𝔭 𝔮 h
  have hv := congrArg Place.toValuationSubring h
  simp only [Place.ofHeightOneSpectrum_toValuationSubring] at hv
  have hequiv := (Valuation.isEquiv_iff_valuationSubring _ _).mpr hv
  ext a
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
  exact hequiv.lt_one_iff_lt_one

def primeEquivChartPlaces : HeightOneSpectrum (chartRing K ({s} : Set L)) ≃ chartPlaces K s :=
  Equiv.ofBijective
    (fun 𝔭 => ⟨Place.ofHeightOneSpectrum (K := K) 𝔭, mem_ofHeightOneSpectrum K s 𝔭⟩)
    ⟨fun 𝔭 𝔮 h => ofHeightOneSpectrum_injective K s (congrArg Subtype.val h),
     fun v => by
      obtain ⟨𝔭, h𝔭⟩ := exists_ofHeightOneSpectrum_eq K s v.1 v.2
      exact ⟨𝔭, Subtype.ext h𝔭⟩⟩

@[simp] theorem coe_primeEquivChartPlaces (𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L))) :
    (primeEquivChartPlaces K s 𝔭 : Place K L) = Place.ofHeightOneSpectrum (K := K) 𝔭 :=
  rfl

end Valuation

section InvertGenerator

variable {K}

theorem exists_pow_mul_mem_adjoin {S : Set L} {s : L} (hs : s ∈ S) (hs0 : s ≠ 0) {x : L}
    (hx : x ∈ Algebra.adjoin K (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ Algebra.adjoin K S := by
  have hsA : s ∈ Algebra.adjoin K S := Algebra.subset_adjoin hs
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hs0]; exact one_mem _⟩
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap a => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ a⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y + z) = s ^ n * (s ^ m * y) + s ^ m * (s ^ n * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hsA n) hm) (mul_mem (pow_mem hsA m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y * z) = (s ^ m * y) * (s ^ n * z) := by ring
    rw [this]
    exact mul_mem hm hn

theorem exists_pow_mul_mem_chartRing {S : Set L} {s : L} (hs : s ∈ S) (hs0 : s ≠ 0) {x : L}
    (hx : x ∈ chartRing K (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ chartRing K S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartRing_iff K).mp hx

  have hcoeff : ∀ i, ∃ n : ℕ, s ^ n * (p.coeff i : L) ∈ Algebra.adjoin K S :=
    fun i => exists_pow_mul_mem_adjoin hs hs0 (p.coeff i).2
  choose n hn using hcoeff
  set N : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hN
  have hnN : ∀ i ≤ p.natDegree, n i ≤ N := fun i hi =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

  set q : L[X] := (p.map (algebraMap (Algebra.adjoin K (insert s⁻¹ S)) L)).scaleRoots (s ^ N)
    with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (s ^ N * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]

  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin K S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · have hle : n i ≤ N * (p.natDegree - i) := by
        calc n i ≤ N := hnN i hi.le
          _ = N * 1 := (mul_one N).symm
          _ ≤ N * (p.natDegree - i) := Nat.mul_le_mul_left N (Nat.one_le_iff_ne_zero.mpr (by omega))
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have : (s ^ N) ^ (p.natDegree - i) = s ^ k * s ^ n i := by
        rw [← pow_mul, hk, pow_add, mul_comm]
      rw [this, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : L) * (s ^ k * s ^ n i) = s ^ k * (s ^ n i * (p.coeff i : L)) by ring]
      exact mul_mem (pow_mem (Algebra.subset_adjoin hs) k) (hn i)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _

  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin K S) L) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨N, (mem_chartRing_iff K).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

end InvertGenerator

end CurveModel

end AlgebraicCurve

end
