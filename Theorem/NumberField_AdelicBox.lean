module

public import Instance.NumberField_AdelicHaar
public import Def.NumberField_AdelicBox

public noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct

namespace NumberField.AdelicBox

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

variable (v : HeightOneSpectrum R)


public theorem algebraMap_mem_adicCompletionIntegers (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

public theorem valued_algebraMap (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

public theorem ball_mem_nhds (x t : v.adicCompletion K) (ht : t ≠ 0) :
    {z : v.adicCompletion K | Valued.v (z - x) < Valued.v t} ∈ nhds x := by
  have ht' : Valued.v.restrict t ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff, Valuation.zero_iff]
  refine Valued.mem_nhds.mpr ⟨Units.mk0 _ ht', fun z hz => ?_⟩
  rw [Units.val_mk0] at hz
  exact Valued.v.restrict_lt_iff.mp hz

public theorem exists_valued_sub_algebraMap_lt (x t : v.adicCompletion K) (ht : t ≠ 0) :
    ∃ c : K, Valued.v (x - algebraMap K (v.adicCompletion K) c) < Valued.v t := by
  obtain ⟨_, hz, c, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) x) _ (ball_mem_nhds R K v x t ht)
  exact ⟨c, by rwa [Set.mem_setOf_eq, Valuation.map_sub_swap] at hz⟩

public theorem exists_valued_algebraMap_sub_lt (x : v.adicCompletionIntegers K)
    (t : v.adicCompletion K) (ht : t ≠ 0) :
    ∃ a : R, Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a) -
      (x : v.adicCompletion K)) < Valued.v t := by
  set γ : (WithZero (Multiplicative ℤ))ˣ := Units.mk0 (Valued.v t) ((Valuation.ne_zero_iff _).mpr ht)
    with hγ

  have hn : {z : v.adicCompletion K | Valued.v (z - x) < Valued.v t} ∩
      {z : v.adicCompletion K | Valued.v (z - x) < Valued.v (1 : v.adicCompletion K)} ∈
        nhds (x : v.adicCompletion K) :=
    Filter.inter_mem (ball_mem_nhds R K v _ t ht) (ball_mem_nhds R K v _ 1 one_ne_zero)
  obtain ⟨_, ⟨hzγ, hz1⟩, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) (x : v.adicCompletion K)) _ hn
  have hyγ : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < γ := by
    rw [hγ, Units.val_mk0]; exact hzγ
  have hz1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < 1 := by
    have := hz1; rwa [Set.mem_setOf_eq, Valuation.map_one] at this
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < 1 := hz1

  have hyint : v.valuation K y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have h : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) (x : v.adicCompletion K)
      rw [sub_add_cancel] at this
      exact this.trans (max_le hy1.le hx1)
    rwa [show algebraMap K (v.adicCompletion K) y = (y : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint γ
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a) -
      algebraMap K (v.adicCompletion K) y) < γ := by
    rw [← map_sub, show algebraMap K (v.adicCompletion K) (algebraMap R K a - y) =
        ((algebraMap R K a - y : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
    (algebraMap K (v.adicCompletion K) (algebraMap R K a) - algebraMap K (v.adicCompletion K) y)
    (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K))
  rw [sub_add_sub_cancel] at this
  rw [hγ, Units.val_mk0] at ha' hyγ
  exact lt_of_le_of_lt this (max_lt ha' hyγ)

public theorem exists_mul_mem_adicCompletionIntegers (x : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * x ∈ v.adicCompletionIntegers K := by
  obtain ⟨c, hc⟩ := exists_valued_sub_algebraMap_lt R K v x 1 one_ne_zero
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  refine ⟨s, hs0, ?_⟩
  have hid : algebraMap K (v.adicCompletion K) (algebraMap R K s) * x =
      algebraMap K (v.adicCompletion K) (algebraMap R K s) *
        (x - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K s)) +
      algebraMap K (v.adicCompletion K) (algebraMap R K a) := by
    have : algebraMap R K s * (algebraMap R K a / algebraMap R K s) = algebraMap R K a := by
      field_simp
    rw [mul_sub, ← map_mul, this]
    ring
  rw [hid, HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [Valuation.map_mul]
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K s)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp
        (algebraMap_mem_adicCompletionIntegers R K v s)
    have h2 : Valued.v (x - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K s))
        ≤ 1 := by
      have := hc.le; rwa [Valuation.map_one] at this
    exact mul_le_one' h1 h2
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp
      (algebraMap_mem_adicCompletionIntegers R K v a)

omit v in

public theorem algebraMap_mul_apply (r : R) (y : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (algebraMap R (FiniteAdeleRing R K) r * y) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) * y v := rfl

omit v in

public theorem algebraMap_add_apply (k : K) (y : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (algebraMap K (FiniteAdeleRing R K) k + y) v = algebraMap K (v.adicCompletion K) k + y v := rfl

omit v in

public theorem exists_mul_mem_integralFiniteAdeles (y : FiniteAdeleRing R K) :
    ∃ s : R, s ≠ 0 ∧ algebraMap R (FiniteAdeleRing R K) s * y ∈ integralFiniteAdeles R K := by
  classical
  have hS : {v : HeightOneSpectrum R | y v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp
      (show Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
        from y).eventually
  choose s hs0 hs using fun v => exists_mul_mem_adicCompletionIntegers R K v (y v)
  refine ⟨∏ w ∈ hS.toFinset, s w, Finset.prod_ne_zero_iff.mpr fun w _ => hs0 w, fun v => ?_⟩
  rw [algebraMap_mul_apply]
  by_cases hv : v ∈ hS.toFinset
  · rw [← Finset.prod_erase_mul _ _ hv, map_mul, map_mul, mul_assoc]
    exact mul_mem (algebraMap_mem_adicCompletionIntegers R K v _) (hs v)
  · have hyv : y v ∈ v.adicCompletionIntegers K := by
      simpa [Set.Finite.mem_toFinset] using hv
    exact mul_mem (algebraMap_mem_adicCompletionIntegers R K v _) hyv

omit v in

public theorem exists_forall_valued_sub_le {z : FiniteAdeleRing R K} (hz : z ∈ integralFiniteAdeles R K)
    {s : R} (hs : s ≠ 0) :
    ∃ a : R, ∀ v : HeightOneSpectrum R,
      Valued.v (z v - algebraMap K (v.adicCompletion K) (algebraMap R K a)) ≤
        Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K s)) := by
  classical

  have hI : (Ideal.span {s} : Ideal R) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hs
  set T := (Ideal.finite_factors hI).toFinset with hT
  let e : HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal R)).factors
  have hvs : ∀ v : HeightOneSpectrum R,
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K s)) ≠ 0 := fun v => by
    rw [valued_algebraMap]; exact v.intValuation_ne_zero s hs
  have hS : ∀ v : HeightOneSpectrum R,
      algebraMap K (v.adicCompletion K) (algebraMap R K s) ≠ 0 := fun v =>
    (Valuation.ne_zero_iff _).mp (hvs v)

  choose a ha using fun v : HeightOneSpectrum R =>
    exists_valued_algebraMap_sub_lt R K v ⟨z v, hz v⟩ _ (hS v)

  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum R => v.asIdeal) e (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a v.1)
  refine ⟨b, fun v => ?_⟩
  have hzb : z v - algebraMap K (v.adicCompletion K) (algebraMap R K b) =
      (z v - algebraMap K (v.adicCompletion K) (algebraMap R K (a v))) +
      (algebraMap K (v.adicCompletion K) (algebraMap R K (a v)) -
        algebraMap K (v.adicCompletion K) (algebraMap R K b)) := by ring
  rw [hzb]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · have := ha v
    rw [Valuation.map_sub_swap] at this
    exact this.le
  · rw [← map_sub, ← map_sub, valued_algebraMap, valued_algebraMap]
    by_cases hv : v ∈ T
    ·
      rw [v.intValuation_if_neg hs, Valuation.map_sub_swap]
      exact (v.intValuation_le_pow_iff_mem _ _).mpr (hb v hv)
    ·
      have hsv : s ∉ v.asIdeal := by
        intro h
        apply hv
        rw [hT, Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.mpr h
      rw [(HeightOneSpectrum.intValuation_eq_one_iff).mpr hsv]
      exact v.intValuation_le_one _

omit v in

public theorem exists_algebraMap_add_mem_integralFiniteAdeles (y : FiniteAdeleRing R K) :
    ∃ k : K, algebraMap K (FiniteAdeleRing R K) k + y ∈ integralFiniteAdeles R K := by
  obtain ⟨s, hs, hsy⟩ := exists_mul_mem_integralFiniteAdeles R K y
  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le R K hsy hs
  refine ⟨-(algebraMap R K a / algebraMap R K s), fun v => ?_⟩
  have hsK : algebraMap R K s ≠ 0 := fun h => hs ((injective_iff_map_eq_zero _).mp
    (IsFractionRing.injective R K) s h)
  set S := algebraMap K (v.adicCompletion K) (algebraMap R K s) with hSdef
  set A := algebraMap K (v.adicCompletion K) (algebraMap R K a) with hAdef
  have hS : S ≠ 0 := by rw [hSdef]; exact (map_ne_zero _).mpr hsK
  have hvS : Valued.v S ≠ 0 := (Valuation.ne_zero_iff _).mpr hS
  rw [algebraMap_add_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
  have hid : algebraMap K (v.adicCompletion K) (-(algebraMap R K a / algebraMap R K s)) + y v =
      S⁻¹ * (S * y v - A) := by
    rw [map_neg, map_div₀, ← hSdef, ← hAdef]
    field_simp
    ring
  rw [hid, Valuation.map_mul, map_inv₀]
  have h := ha v
  rw [algebraMap_mul_apply, ← hSdef, ← hAdef] at h
  calc (Valued.v S)⁻¹ * Valued.v (S * y v - A)
      ≤ (Valued.v S)⁻¹ * Valued.v S := by gcongr
    _ = 1 := inv_mul_cancel₀ hvS

end Finite

end NumberField.AdelicBox
