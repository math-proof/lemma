import Lemma.Definitions.Def_ModularCurve_X0
import Lemma.Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open HahnSeries IntermediateField
open scoped Matrix

namespace ModularCurve

variable (q : ℕ) [Fact q.Prime]

def zetaQ : CyclotomicField q ℚ :=
  haveI : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) := CyclotomicField.isCyclotomicExtension q ℚ
  IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ)

theorem isPrimitiveRoot_zetaQ : IsPrimitiveRoot (zetaQ q) q := by
  haveI : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) := CyclotomicField.isCyclotomicExtension q ℚ
  exact IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)

theorem zetaQ_pow : zetaQ q ^ q = 1 := (isPrimitiveRoot_zetaQ q).pow_eq_one

def jLevel : LaurentSeries (CyclotomicField q ℚ) :=
  qExpand (CyclotomicField q ℚ) q (coeffMap (algebraMap ℚ (CyclotomicField q ℚ)) jq)

def jLevelN (d : ℕ) [NeZero d] : LaurentSeries (CyclotomicField q ℚ) :=
  qExpand (CyclotomicField q ℚ) d (jLevel q)

theorem jLevelN_one : jLevelN q 1 = jLevel q := qExpand_one_apply _

def zetaSubring : Subalgebra ℤ (CyclotomicField q ℚ) := Algebra.adjoin ℤ {zetaQ q}

theorem zetaQ_mem_zetaSubring : zetaQ q ∈ zetaSubring q := Algebra.subset_adjoin rfl

theorem multipliable_one_sub_C_mul_X_pow {R : Type} [CommRing R] [TopologicalSpace R] (c : R) (m : ℕ → ℕ)
    (hm : ∀ n, n < m n) : Multipliable fun n => (1 : PowerSeries R) - PowerSeries.C c * PowerSeries.X ^ m n := by
  nontriviality R
  simp_rw [sub_eq_add_neg]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro k hk
  rw [PowerSeries.order_neg, ← PowerSeries.smul_eq_C_mul]
  calc ((n : ℕ) : ℕ∞) < (m k : ℕ) := by exact_mod_cast hk.trans_lt (hm k)
    _ = PowerSeries.order ((PowerSeries.X : PowerSeries R) ^ m k) := (PowerSeries.order_X_pow _).symm
    _ ≤ PowerSeries.order (c • (PowerSeries.X : PowerSeries R) ^ m k) := PowerSeries.le_order_smul

def siegelExponent (a : Fin 2 → ZMod q) : ℤ := 6 * ((a 0).val : ℤ) ^ 2 - 6 * q * (a 0).val + (q : ℤ) ^ 2

def siegelConstExponent (a : Fin 2 → ZMod q) : ℕ := 6 * (a 0).val * (a 1).val

def siegelSeriesInt (a : Fin 2 → ZMod q) : PowerSeries (zetaSubring q) :=
  letI : TopologicalSpace (zetaSubring q) := ⊥
  (1 - PowerSeries.C (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (a 1).val) * PowerSeries.X ^ (a 0).val) *
    ((∏' n : ℕ, (1 - PowerSeries.C (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (a 1).val) *
        PowerSeries.X ^ (q * (n + 1) + (a 0).val))) *
      ∏' n : ℕ, (1 - PowerSeries.C (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (q - (a 1).val)) *
        PowerSeries.X ^ (q * (n + 1) - (a 0).val)))

theorem multipliable_siegelFactor_left (a : Fin 2 → ZMod q) :
    letI : TopologicalSpace (zetaSubring q) := ⊥
    Multipliable fun n : ℕ => (1 - PowerSeries.C (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (a 1).val) *
      PowerSeries.X ^ (q * (n + 1) + (a 0).val) : PowerSeries (zetaSubring q)) := by
  letI : TopologicalSpace (zetaSubring q) := ⊥
  refine multipliable_one_sub_C_mul_X_pow _ _ fun n => ?_
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  nlinarith

theorem multipliable_siegelFactor_right (a : Fin 2 → ZMod q) :
    letI : TopologicalSpace (zetaSubring q) := ⊥
    Multipliable fun n : ℕ => (1 - PowerSeries.C (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (q - (a 1).val)) *
      PowerSeries.X ^ (q * (n + 1) - (a 0).val) : PowerSeries (zetaSubring q)) := by
  letI : TopologicalSpace (zetaSubring q) := ⊥
  refine multipliable_one_sub_C_mul_X_pow _ _ fun n => ?_
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have ha : (a 0).val < q := (a 0).val_lt
  have : q * (n + 1) - (a 0).val ≥ q * n + 1 := by
    have : q * (n + 1) = q * n + q := by ring
    omega
  nlinarith

def siegelSeries (a : Fin 2 → ZMod q) : PowerSeries (CyclotomicField q ℚ) :=
  (siegelSeriesInt q a).map (algebraMap (zetaSubring q) (CyclotomicField q ℚ))

theorem coeff_siegelSeries_mem (a : Fin 2 → ZMod q) (n : ℕ) :
    PowerSeries.coeff n (siegelSeries q a) ∈ zetaSubring q := by
  rw [siegelSeries, PowerSeries.coeff_map]
  exact Subtype.property _

def siegelPower (a : Fin 2 → ZMod q) : LaurentSeries (CyclotomicField q ℚ) :=
  single (siegelExponent q a) (zetaQ q ^ siegelConstExponent q a) *
    ofPowerSeries ℤ (CyclotomicField q ℚ) (siegelSeries q a ^ (12 * q))

variable (M' : ℕ)

def levelGenerators : Set (LaurentSeries (CyclotomicField q ℚ)) :=
  {C (zetaQ q)} ∪ {x | ∃ d : ℕ, ∃ _ : NeZero d, d ∣ M' ∧ x = jLevelN q d} ∪
    {x | ∃ d : ℕ, ∃ _ : NeZero d, ∃ a : Fin 2 → ZMod q,
      d ∣ M' ∧ a ≠ 0 ∧ x = qExpand (CyclotomicField q ℚ) d (siegelPower q a)}

theorem zeta_mem_levelGenerators : C (zetaQ q) ∈ levelGenerators q M' :=
  Or.inl (Or.inl rfl)

variable {M'} in
theorem jLevelN_mem_levelGenerators {d : ℕ} [NeZero d] (hd : d ∣ M') : jLevelN q d ∈ levelGenerators q M' :=
  Or.inl (Or.inr ⟨d, ‹_›, hd, rfl⟩)

variable {M'} in
theorem siegelPower_mem_levelGenerators {d : ℕ} [NeZero d] (hd : d ∣ M') {a : Fin 2 → ZMod q} (ha : a ≠ 0) :
    qExpand (CyclotomicField q ℚ) d (siegelPower q a) ∈ levelGenerators q M' :=
  Or.inr ⟨d, ‹_›, a, hd, ha, rfl⟩

def levelFunctionField : IntermediateField ℚ (LaurentSeries (CyclotomicField q ℚ)) :=
  IntermediateField.adjoin ℚ (levelGenerators q M')

theorem zeta_mem_levelFunctionField : C (zetaQ q) ∈ levelFunctionField q M' :=
  subset_adjoin ℚ _ (zeta_mem_levelGenerators q M')

variable {M'} in
theorem jLevelN_mem_levelFunctionField {d : ℕ} [NeZero d] (hd : d ∣ M') :
    jLevelN q d ∈ levelFunctionField q M' :=
  subset_adjoin ℚ _ (jLevelN_mem_levelGenerators q hd)

variable {M'} in
theorem siegelPower_mem_levelFunctionField {d : ℕ} [NeZero d] (hd : d ∣ M') {a : Fin 2 → ZMod q}
    (ha : a ≠ 0) : qExpand (CyclotomicField q ℚ) d (siegelPower q a) ∈ levelFunctionField q M' :=
  subset_adjoin ℚ _ (siegelPower_mem_levelGenerators q hd ha)

theorem levelFunctionField_le {M'' : ℕ} (h : M' ∣ M'') :
    levelFunctionField q M' ≤ levelFunctionField q M'' := by
  rw [levelFunctionField, adjoin_le_iff]
  rintro x ((rfl | ⟨d, hne, hd, rfl⟩) | ⟨d, hne, a, hd, ha, rfl⟩)
  · exact zeta_mem_levelFunctionField q M''
  · exact jLevelN_mem_levelFunctionField q (hd.trans h)
  · exact siegelPower_mem_levelFunctionField q (hd.trans h) ha

theorem levelFunctionField_map_mem (ℓ : ℕ) [NeZero ℓ] {x : LaurentSeries (CyclotomicField q ℚ)}
    (hx : x ∈ levelFunctionField q M') :
    qExpand (CyclotomicField q ℚ) ℓ x ∈ levelFunctionField q (M' * ℓ) := by
  have hC : ∀ c : ℚ, qExpand (CyclotomicField q ℚ) ℓ (algebraMap ℚ _ c) ∈ levelFunctionField q (M' * ℓ) := by
    intro c
    have h : algebraMap ℚ (LaurentSeries (CyclotomicField q ℚ)) =
        (C : CyclotomicField q ℚ →+* LaurentSeries (CyclotomicField q ℚ)).comp
          (algebraMap ℚ (CyclotomicField q ℚ)) := Subsingleton.elim _ _
    rw [h, RingHom.comp_apply, qExpand_C, ← RingHom.comp_apply, ← h]
    exact IntermediateField.algebraMap_mem _ c
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with ((rfl | ⟨d, hne, hd, rfl⟩) | ⟨d, hne, a, hd, ha, rfl⟩)
    · rw [qExpand_C]; exact zeta_mem_levelFunctionField q _
    · haveI : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne d)⟩
      rw [jLevelN, qExpand_qExpand]
      exact jLevelN_mem_levelFunctionField q
        ((mul_dvd_mul_left ℓ hd).trans (dvd_of_eq (mul_comm ℓ M')))
    · haveI : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne d)⟩
      rw [qExpand_qExpand]
      exact siegelPower_mem_levelFunctionField q
        ((mul_dvd_mul_left ℓ hd).trans (dvd_of_eq (mul_comm ℓ M'))) ha
  | algebraMap c => exact hC c
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

variable {q} in

def diagD (d : ℕ) (hd : d.Coprime q) : GL (Fin 2) (ZMod q) where
  val := Matrix.diagonal ![((ZMod.unitOfCoprime d hd : (ZMod q)ˣ) : ZMod q), 1]
  inv := Matrix.diagonal ![(((ZMod.unitOfCoprime d hd)⁻¹ : (ZMod q)ˣ) : ZMod q), 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · exact (ZMod.unitOfCoprime d hd).mul_inv
    · exact mul_one 1
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · exact (ZMod.unitOfCoprime d hd).inv_mul
    · exact mul_one 1

variable {q} in
theorem coe_diagD (d : ℕ) (hd : d.Coprime q) :
    (diagD d hd : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      Matrix.diagonal ![((ZMod.unitOfCoprime d hd : (ZMod q)ˣ) : ZMod q), 1] := rfl

variable {M'} in
theorem coprime_of_dvd_level {d : ℕ} (hd : d ∣ M') (hqM' : ¬ q ∣ M') : d.Coprime q :=
  (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h => hqM' (h.trans hd)))

def levelComponentField (L : Type) [Field L] [Algebra ℚ L] (ι : CyclotomicField q ℚ →ₐ[ℚ] L) :
    IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (⇑(coeffMap (ι : CyclotomicField q ℚ →+* L)) ''
    (levelFunctionField q M' : Set (LaurentSeries (CyclotomicField q ℚ))))

end ModularCurve

end
