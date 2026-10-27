import Initialize.Tactic.Attr.Basic
import Mathlib

open IsDedekindDomain NumberField

/--
[AdelicDock_isCompact_localLevelOne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_isCompact_localLevelOne.lean)

`AdelicLevel.idealBound` from FLT Def_NumberField_AdelicLevel.lean (IdealBound).
-/
noncomputable def AdelicLevel.idealBound (R : Type*) [CommRing R] [IsDedekindDomain R]
    (N : Ideal R) (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ) :=
  open scoped Classical in
  if N = ⊥ then 0
  else WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ))

structure AdelicDock.IsLocalLevelOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (N : Ideal R)
  (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Prop where
  integral : ∀ i j, m i j ∈ v.adicCompletionIntegers K
  lowerLeft : Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v
  lowerRight : Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v

namespace AdelicLevel

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem idealBound_bot (v : HeightOneSpectrum R) : idealBound R (⊥ : Ideal R) v = 0 := by
  classical
  simp [idealBound]

theorem idealBound_of_ne_bot {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v =
      WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ)) := by
  classical
  simp [idealBound, hN]

end AdelicLevel

namespace AdelicDock

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] {v : HeightOneSpectrum R} {N : Ideal R}

theorem IsLocalLevelOne.one : IsLocalLevelOne R K v N (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) where
  integral i j := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  lowerLeft := by
    rw [Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le
  lowerRight := by
    rw [Matrix.one_apply_eq, sub_self, map_zero]
    exact zero_le

variable {m m' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}

theorem IsLocalLevelOne.mul (hm : IsLocalLevelOne R K v N m) (hm2 : IsLocalLevelOne R K v N m') :
    IsLocalLevelOne R K v N (m * m') where
  integral i j := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem (mul_mem (hm.integral i 0) (hm2.integral 0 j))
      (mul_mem (hm.integral i 1) (hm2.integral 1 j))
  lowerLeft := by
    have h : (m * m') 1 0 = m 1 0 * m' 0 0 + m 1 1 * m' 1 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h]
    apply (Valuation.map_add Valued.v _ _).trans
    apply max_le
    · rw [map_mul]
      calc
        Valued.v (m 1 0) * Valued.v (m' 0 0)
            ≤ AdelicLevel.idealBound R N v * 1 :=
          mul_le_mul' hm.lowerLeft ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm2.integral 0 0))
        _ = AdelicLevel.idealBound R N v := mul_one _
    · rw [map_mul]
      calc
        Valued.v (m 1 1) * Valued.v (m' 1 0)
            ≤ 1 * AdelicLevel.idealBound R N v :=
          mul_le_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm.integral 1 1)) hm2.lowerLeft
        _ = AdelicLevel.idealBound R N v := one_mul _
  lowerRight := by
    have h : (m * m') 1 1 - 1 =
        m 1 0 * m' 0 1 + ((m 1 1 - 1) * m' 1 1 + (m' 1 1 - 1)) := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h]
    apply (Valuation.map_add Valued.v _ _).trans
    apply max_le
    · rw [map_mul]
      calc
        Valued.v (m 1 0) * Valued.v (m' 0 1)
            ≤ AdelicLevel.idealBound R N v * 1 :=
          mul_le_mul' hm.lowerLeft ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm2.integral 0 1))
        _ = AdelicLevel.idealBound R N v := mul_one _
    · apply (Valuation.map_add Valued.v _ _).trans
      apply max_le
      · rw [map_mul]
        calc
          Valued.v (m 1 1 - 1) * Valued.v (m' 1 1)
              ≤ AdelicLevel.idealBound R N v * 1 :=
            mul_le_mul' hm.lowerRight ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm2.integral 1 1))
          _ = AdelicLevel.idealBound R N v := mul_one _
      · exact hm2.lowerRight

end AdelicDock

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (N : Ideal R)

noncomputable def AdelicDock.localLevelOne :
    Subgroup (GL (Fin 2) (v.adicCompletion K)) where
  carrier := {g | AdelicDock.IsLocalLevelOne R K v N (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∧
    AdelicDock.IsLocalLevelOne R K v N
      ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' {a b} ha hb :=
    ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
     by rw [mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' {a} ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem AdelicDock.mem_localLevelOne_iff
    (k : GL (Fin 2) (v.adicCompletion K)) :
    k ∈ AdelicDock.localLevelOne R K v N ↔
      AdelicDock.IsLocalLevelOne R K v N k ∧
      AdelicDock.IsLocalLevelOne R K v N
        ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
  Iff.rfl

namespace AdelicLevel

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem setOf_valued_le_eq_preimage (t : v.adicCompletion K) (ht : t ≠ 0) :
    {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} =
      (fun y => y * t⁻¹) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
  rw [mul_inv_le_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ht)), one_mul]

theorem isClosed_setOf_valued_le (t : v.adicCompletion K) (ht : t ≠ 0) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} := by
  rw [setOf_valued_le_eq_preimage v t ht]
  exact (Valued.isClosed_valuationSubring (v.adicCompletion K)).preimage
    (continuous_id.mul continuous_const)

theorem valued_algebraMap (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

theorem exists_valued_eq_exp_neg (n : ℕ) :
    ∃ t : v.adicCompletion K, t ≠ 0 ∧ Valued.v t = WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  refine ⟨(algebraMap K (v.adicCompletion K) (algebraMap R K π)) ^ n, ?_, ?_⟩
  · refine pow_ne_zero _ fun h => ?_
    have := valued_algebraMap (K := K) v π
    rw [h, map_zero, hπ] at this
    exact WithZero.exp_ne_zero this.symm
  · rw [map_pow, valued_algebraMap, hπ]
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

theorem isClosed_setOf_valued_le_idealBound (N : Ideal R) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ AdelicLevel.idealBound R N v} := by
  by_cases hN : N = ⊥
  · have : {y : v.adicCompletion K | Valued.v y ≤ AdelicLevel.idealBound R N v} = {0} := by
      ext y; simp [hN, idealBound_bot]
    rw [this]; exact isClosed_singleton
  · obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := K) v
      ((Associates.mk v.asIdeal).count (Associates.mk N).factors)
    rw [idealBound_of_ne_bot hN, ← hvt]
    exact isClosed_setOf_valued_le v t ht

end AdelicLevel

/- Compactness of v.adicCompletionIntegers (FLT Def_NumberField_AdelicHaar Local). -/
namespace HeightOneSpectrum.AdicCompletionIntegersCompact

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem exists_valued_algebraMap_sub_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((algebraMap R (v.adicCompletion K) a) - (x : v.adicCompletion K)) < 1 := by
  have hn : {z : v.adicCompletion K | Valued.v (z - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
    have hz' : Valued.v.restrict (z - (x : v.adicCompletion K)) < 1 := by
      rw [← Units.val_one]; exact hz
    exact (Valuation.restrict_lt_one_iff _).mp hz'
  obtain ⟨_, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) (x : v.adicCompletion K)) _ hn
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < 1 := hz
  have hyint : v.valuation K y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have h : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) (x : v.adicCompletion K)
      rw [sub_add_cancel] at this
      exact this.trans (max_le hy1.le hx1)
    rwa [show algebraMap K (v.adicCompletion K) y = (y : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v ((algebraMap R (v.adicCompletion K) a) -
      algebraMap K (v.adicCompletion K) y) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K) a, ← map_sub,
      show algebraMap K (v.adicCompletion K) (algebraMap R K a - y) =
        ((algebraMap R K a - y : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha.trans_eq Units.val_one
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
    ((algebraMap R (v.adicCompletion K) a) - algebraMap K (v.adicCompletion K) y)
    (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K))
  rw [sub_add_sub_cancel] at this
  exact lt_of_le_of_lt this (max_lt ha' hy1)

theorem mem_maximalIdeal_iff_valued_lt_one (d : v.adicCompletionIntegers K) :
    d ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      Valued.v (d : v.adicCompletion K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hd : Valued.v (d : v.adicCompletion K) ≤ 1 := d.2
  exact ⟨fun h => lt_of_le_of_ne hd h, fun h => ne_of_lt h⟩

theorem residue_algebraMap_surjective :
    Function.Surjective (fun a : R =>
      IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) a)) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_valued_algebraMap_sub_lt_one R K v x
  refine ⟨a, ?_⟩
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, mem_maximalIdeal_iff_valued_lt_one]
  simpa [HeightOneSpectrum.algebraMap_adicCompletion] using ha

theorem residue_algebraMap_eq_zero_of_mem {a : R} (ha : a ∈ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
      (algebraMap R (v.adicCompletionIntegers K) a) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_valued_lt_one]
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mpr ha

variable [Module.Free ℤ R] [Module.Finite ℤ R]

instance : Ring.HasFiniteQuotients R := Ring.HasFiniteQuotients.of_module_finite ℤ R

instance : Infinite R := Module.Free.infinite ℤ R

instance finite_residueField_adicCompletionIntegers :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  have : Finite (R ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let f : R ⧸ v.asIdeal → IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    Ideal.Quotient.lift v.asIdeal
      ((IsLocalRing.residue (v.adicCompletionIntegers K)).comp
        (algebraMap R (v.adicCompletionIntegers K)))
      (fun a ha => residue_algebraMap_eq_zero_of_mem R K v ha)
  refine Finite.of_surjective f fun z => ?_
  obtain ⟨a, ha⟩ := residue_algebraMap_surjective R K v z
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

instance : Finite (R ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

open scoped Valued

instance properSpace_adicCompletion : ProperSpace (v.adicCompletion K) := by
  have : IsDiscreteValuationRing 𝒪[v.adicCompletion K] :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have : Finite 𝓀[v.adicCompletion K] :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  exact (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := v.adicCompletion K)).mpr ⟨inferInstance, inferInstance, inferInstance⟩

instance compactSpace_adicCompletionIntegers : CompactSpace (v.adicCompletionIntegers K) := by
  have h : CompactSpace 𝒪[v.adicCompletion K] :=
    (Valued.integer.properSpace_iff_compactSpace_integer (K := v.adicCompletion K)).mp inferInstance
  exact h

end HeightOneSpectrum.AdicCompletionIntegersCompact

@[instance] theorem HeightOneSpectrum.compactSpace_adicCompletionIntegers
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)
  [Module.Free ℤ R] [Module.Finite ℤ R] : CompactSpace (v.adicCompletionIntegers K) :=
  HeightOneSpectrum.AdicCompletionIntegersCompact.compactSpace_adicCompletionIntegers R K v

@[path]
private lemma main
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Module.Free ℤ R] [Module.Finite ℤ R] (v : HeightOneSpectrum R) (N : Ideal R) :
-- imply
  IsCompact (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
-- proof
  classical
  set C : Set (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    {m | AdelicDock.IsLocalLevelOne R K v N m} with hC_def

  have : CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have hO : IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    isCompact_iff_compactSpace.mpr inferInstance
  have hpi : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO

  have hCcl : IsClosed C := by
    have h1 : IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) |
        ∀ i j, m i j ∈ v.adicCompletionIntegers K} := by
      have : {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | ∀ i j, m i j ∈ v.adicCompletionIntegers K} =
        ⋂ i, ⋂ j, (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m i j) ⁻¹'
          (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
        ext m; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        (Valued.isClosed_valuationSubring (v.adicCompletion K)).preimage (continuous_id.matrix_elem i j)
    have h2 : IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) |
        Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v} :=
      (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := K) v N).preimage (continuous_id.matrix_elem 1 0)
    have h3 : IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) |
        Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v} :=
      (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := K) v N).preimage
        ((continuous_id.matrix_elem 1 1).sub continuous_const)
    have hCeq : C = ({m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | ∀ i j, m i j ∈ v.adicCompletionIntegers K}
        ∩ {m | Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v})
        ∩ {m | Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v} := by
      ext m
      simp only [hC_def, Set.mem_ofPred_eq, Set.mem_inter_iff]
      exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
    rw [hCeq]
    exact (h1.inter h2).inter h3
  have hC : IsCompact C :=
    hpi.of_isClosed_subset hCcl fun m hm i _ j _ => hm.integral i j

  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) =
    (Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹' (C ×ˢ (MulOpposite.op '' C)) := by
    ext g
    rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff]
    simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image, hC_def, Set.mem_ofPred_eq]
    constructor
    ·
      rintro ⟨h1, h2⟩
      exact ⟨h1, _, h2, rfl⟩
    ·
      rintro ⟨h1, m, hm, hm'⟩
      refine ⟨h1, ?_⟩
      have : m = ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
        MulOpposite.op_injective hm'
      rwa [← this]
  rwa [heq]

-- created on 2026-10-09
