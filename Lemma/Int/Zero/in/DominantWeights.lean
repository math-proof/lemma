import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.KostantTheorem
open MeasureTheory Filter


/--
[KostantSetupData.zero_mem_dominantWeights](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma KostantSetupData.zero_mem_dominantWeights
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  (0 : ksd.P) ∈ ksd.dominantWeights := by
-- proof
  rw [ksd.dominantWeights_spec]
  intro i
  rw [ksd.pairingCoroot_zero i]

/--
[singleFactorCoeff_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma singleFactorCoeff_eq_mul
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  {α : P'}
  {n : ℕ} :
-- imply
  singleFactorCoeff α n = groupRingOneMinusExp α * geomFactorCoeff α n := by
-- proof
  let a : AddMonoidAlgebra ℤ P' := AddMonoidAlgebra.single (0 : P') 1
  let b : AddMonoidAlgebra ℤ P' := AddMonoidAlgebra.single α 1
  let c : AddMonoidAlgebra ℤ P' := AddMonoidAlgebra.single (n • α) 1
  have ha : groupRingOneMinusExp α = a - b := rfl
  have hc : geomFactorCoeff α n = c := rfl
  rw [ha, hc, sub_mul]
  have hac : a * c = AddMonoidAlgebra.single (n • α) (1 : ℤ) := by
    simp [a, c, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  have hbc : b * c = AddMonoidAlgebra.single ((n + 1) • α) (1 : ℤ) := by
    simp [b, c, AddMonoidAlgebra.single_mul_single, mul_one, add_comm α (n • α), succ_nsmul]
  rw [hac, hbc]
  rfl

/--
[singleFactorPS_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma singleFactorPS_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  {α : P'} :
-- imply
  singleFactorPS α = PowerSeries.C (groupRingOneMinusExp α) * geomFactorPS α := by
-- proof
  apply PowerSeries.ext; intro n
  simp only [singleFactorPS, geomFactorPS, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul]
  exact singleFactorCoeff_eq_mul α n

/--
[fullProductPS_eq_C_numeratorProd_mul_geomProductPS](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma fullProductPS_eq_C_numeratorProd_mul_geomProductPS
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  {S : Finset P'} :
-- imply
  fullProductPS S = PowerSeries.C (numeratorProd S) * geomProductPS S := by
-- proof
  simp only [fullProductPS, geomProductPS, numeratorProd]
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro α _
  exact singleFactorPS_eq α

/--
[KostantSetupData.equation12_geom_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma KostantSetupData.equation12_geom_form
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  ∀ (wt : ksd.P) (_ : wt ∈ ksd.dominantWeights), (Fintype.card ksd.W : ℤ) • gradedHilbertSeries (ksd.gradedHomDim wt) = (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) * powerSeriesCT (geomProductPS ksd.roots * PowerSeries.C (numeratorProd ksd.roots * ksd.weylCharacter wt)) :=
-- proof
  fun wt hwt => ksd.equation12_geom_form_field wt hwt

/--
[KostantSetupData.equation12_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma KostantSetupData.equation12_spec
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  ∀ (wt : ksd.P) (_ : wt ∈ ksd.dominantWeights), (Fintype.card ksd.W : ℤ) • gradedHilbertSeries (ksd.gradedHomDim wt) = (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) * (concreteCT_fullRoots_char ksd.roots (ksd.weylCharacter wt)) := by
-- proof
  intro wt hwt
  rw [ksd.equation12_geom_form wt hwt]
  congr 1
  simp only [concreteCT_fullRoots_char]
  congr 1
  rw [fullProductPS_eq_C_numeratorProd_mul_geomProductPS, map_mul]
  ring

/--
[KostantSetupData.equation12_hilbert_series](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma KostantSetupData.equation12_hilbert_series
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  ∀ (wt : ksd.P) (_ : wt ∈ ksd.dominantWeights), (Fintype.card ksd.W : ℤ) • gradedHilbertSeries (ksd.gradedHomDim wt) = (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) * (concreteCT_fullRoots_char ksd.roots (ksd.weylCharacter wt)) :=
-- proof
  ksd.equation12_spec

/--
[KostantSetupData.isDominant_iff_mem_dominantWeights](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma KostantSetupData.isDominant_iff_mem_dominantWeights
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {μ : ksd.P} :
-- imply
  ksd.isDominant μ ↔ μ ∈ ksd.dominantWeights := by
-- proof
  unfold isDominant
  rw [ksd.dominantWeights_spec]
  rfl

/--
[singleFactorPS_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma singleFactorPS_eq_mul
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {α : P'} :
-- imply
  singleFactorPS α = (PowerSeries.C (groupRingOneMinusExp α) : PowerSeries (AddMonoidAlgebra ℤ P')) * geomFactorPS α := by
-- proof
  ext n
  simp only [singleFactorPS, geomFactorPS, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul]
  exact congr_fun (congr_arg _ (singleFactorCoeff_eq_mul α n)) _

/--
[fullProductPS_eq_numerator_mul_geom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma fullProductPS_eq_numerator_mul_geom
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {S : Finset P'} :
-- imply
  fullProductPS S = (PowerSeries.C (numeratorProd S) : PowerSeries (AddMonoidAlgebra ℤ P')) * geomProductPS S := by
-- proof
  unfold fullProductPS geomProductPS numeratorProd
  induction S using Finset.induction with
  | empty => simp [Finset.prod_empty, map_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [singleFactorPS_eq_mul, ih]
    simp only [map_mul]
    ring

/--
[kostant_cst_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma kostant_cst_free
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Module.Free ksd.invariantSubalgebra (SymmetricAlgebra R 𝔤) := by
-- proof
  haveI : Module.Free ksd.invariantSubalgebra
    (TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace) :=
    Algebra.TensorProduct.instFree R ksd.invariantSubalgebra ksd.harmonicSubspace
  exact Module.Free.of_equiv (kostant_cst_tensor ksd)
set_option synthInstance.maxHeartbeats 80000 in

/--
[kostant_Sg_free_over_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma kostant_Sg_free_over_invariants
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Module.Free ksd.invariantSubalgebra (SymmetricAlgebra R 𝔤) :=
-- proof
  kostant_cst_free ksd
set_option synthInstance.maxHeartbeats 80000

/--
[nontrivial_of_irreducible_module](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma nontrivial_of_irreducible_module
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {V : Type*}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  [LieModule.IsIrreducible R 𝔤 V] :
-- imply
  Nontrivial R := by
-- proof
  haveI : Nontrivial V := LieModule.nontrivial_of_isIrreducible R 𝔤 V
  by_contra hr
  rw [not_nontrivial_iff_subsingleton] at hr
  haveI := hr; haveI : Subsingleton V := Module.subsingleton R V
  exact not_subsingleton V (by infer_instance)

/--
[powerSeries_zsmul_left_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma powerSeries_zsmul_left_cancel
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {n : ℤ}
  {a b : PowerSeries ℤ}
-- given
  (hn : n ≠ 0)
  (h : n • a = n • b) :
-- imply
  a = b := by
-- proof
  ext m
  have := congr_arg (PowerSeries.coeff (R := ℤ) m) h
  simp only [map_zsmul] at this
  exact mul_left_cancel₀ hn this

/--
[weylGroup_card_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma weylGroup_card_ne_zero
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  (Fintype.card ksd.W : ℤ) ≠ 0 := by
-- proof
  exact_mod_cast Fintype.card_ne_zero

/--
[concreteCT_fullRoots_char_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma concreteCT_fullRoots_char_one
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {roots : Finset ksd.P} :
-- imply
  concreteCT_fullRoots_char roots (Finsupp.single (0 : ksd.P) 1) = concreteCT_fullRoots roots := by
-- proof
  unfold concreteCT_fullRoots_char concreteCT_fullRoots
  simp [AddMonoidAlgebra.one_def.symm, map_one, mul_one]

/--
[concreteCT_posRoots_lambda_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma concreteCT_posRoots_lambda_zero
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {roots posRoots : Finset ksd.P} :
-- imply
  concreteCT_posRoots_lambda roots posRoots (0 : ksd.P) = concreteCT_posRoots roots posRoots := by
-- proof
  unfold concreteCT_posRoots_lambda concreteCT_posRoots groupRingExp
  simp [AddMonoidAlgebra.one_def.symm, one_mul]

/--
[pbwHarmonicFreeUEA](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma pbwHarmonicFreeUEA
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Module.Free R ksd.harmonicSubspaceUEA :=
-- proof
  Module.Free.of_equiv' inferInstance ksd.pbwHarmonicEquiv

/--
[pbw_harmonicFree_UEA](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma pbw_harmonicFree_UEA
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Module.Free R ksd.harmonicSubspaceUEA :=
-- proof
  pbwHarmonicFreeUEA ksd

/--
[pbw_free_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma pbw_free_lift
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) (UniversalEnvelopingAlgebra R 𝔤) := by
-- proof
  haveI : Module.Free R ksd.harmonicSubspaceUEA := pbwHarmonicFreeUEA ksd
  haveI : Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA) :=
    Algebra.TensorProduct.instFree R
      (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA
  exact Module.Free.of_equiv (pbwTensorEquivUEA ksd)

/--
[kostant_Ug_free_over_center_of_setupData](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma kostant_Ug_free_over_center_of_setupData
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) (UniversalEnvelopingAlgebra R 𝔤) :=
-- proof
  pbw_free_lift ksd

/--
[kostant_Ug_free_over_center](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma kostant_Ug_free_over_center
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) (UniversalEnvelopingAlgebra R 𝔤) :=
-- proof
  pbw_free_lift ksd

/--
[theorem_13_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma theorem_13_5
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Nonempty (↑(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) ≃ₐ[R] MvPolynomial (Fin ksd.rank) R) ∧ Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) (UniversalEnvelopingAlgebra R 𝔤) :=
-- proof
  ⟨⟨kostant_center_is_polynomial ksd⟩, kostant_Ug_free_over_center ksd⟩
open MeasureTheory Filter

/--
[KostantFq_denom_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma KostantFq_denom_ne_zero
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {q : ℝ}
  {z : ℂ}
-- given
  (hq : 0 ≤ q)
  (hq1 : q < 1)
  (hz : ‖z‖ = 1) :
-- imply
  (1 : ℂ) - (q : ℂ) * z ≠ 0 := by
-- proof
  intro h
  have h0 : ‖(1 : ℂ) - (q : ℂ) * z‖ = 0 := by rw [h, norm_zero]
  have hqz : ‖(q : ℂ) * z‖ = q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq, hz, mul_one]
  linarith [show ‖(1 : ℂ) - (q : ℂ) * z‖ ≥ 1 - q from
    calc ‖(1 : ℂ) - (q : ℂ) * z‖ ≥ ‖(1 : ℂ)‖ - ‖(q : ℂ) * z‖ := norm_sub_norm_le _ _
      _ = 1 - q := by rw [hqz, norm_one]]

/--
[KostantFq_normSq_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma KostantFq_normSq_bound
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {q : ℝ}
  {z : ℂ}
-- given
  (hq : 0 ≤ q)
  (hz : ‖z‖ = 1) :
-- imply
  Complex.normSq (1 - z) ≤ 4 * Complex.normSq (1 - (q : ℂ) * z) := by
-- proof
  have hz' : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  have hns1 : Complex.normSq (1 - z) = 2 - 2 * z.re := by
    rw [Complex.normSq_sub, Complex.normSq_one, hz']
    simp only [one_mul, Complex.conj_re]; ring
  have hns2 : Complex.normSq (1 - (q : ℂ) * z) = 1 - 2 * q * z.re + q ^ 2 := by
    rw [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
      Complex.normSq_ofReal, hz']
    simp only [one_mul, mul_one, map_mul, Complex.conj_ofReal, Complex.conj_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hns1, hns2]
  have hre_sq : z.re * z.re ≤ 1 := by
    have : z.re * z.re + z.im * z.im = 1 := by rw [← Complex.normSq_apply]; exact hz'
    linarith [mul_self_nonneg z.im]
  nlinarith [sq_nonneg (1 - q), mul_self_nonneg (1 + z.re), mul_self_nonneg (1 - z.re)]

/--
[KostantFq_single_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma KostantFq_single_tendsto_one
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {z : ℂ}
-- given
  (hz1 : z ≠ 1) :
-- imply
  Tendsto (fun q : ℝ => (1 - z) / (1 - (q : ℂ) * z)) (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 1) := by
-- proof
  have h1z : (1 : ℂ) - z ≠ 0 := by rw [Ne, sub_eq_zero]; exact Ne.symm hz1
  have h1z' : (1 : ℂ) - (1 : ℂ) * z ≠ 0 := by rwa [one_mul]
  suffices h : Tendsto (fun q : ℝ => (1 - z) / (1 - (q : ℂ) * z))
    (nhds 1) (nhds ((1 - z) / (1 - (1 : ℂ) * z))) by
    have hval : (1 - z) / (1 - (1 : ℂ) * z) = 1 := by rw [one_mul]; exact div_self h1z
    rw [hval] at h; exact h.mono_left nhdsWithin_le_nhds
  apply Tendsto.div tendsto_const_nhds
  · apply Tendsto.const_sub
    apply Tendsto.mul_const
    exact Complex.continuous_ofReal.continuousAt.tendsto
  · exact h1z'

/--
[tendsto_norm_sq_sub_zero_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma tendsto_norm_sq_sub_zero_complex
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  {l : Filter α}
  {f : α → ℂ}
  {a : ℂ}
-- given
  (hf : Tendsto f l (nhds a)) :
-- imply
  Tendsto (fun x => ‖f x - a‖ ^ 2) l (nhds 0) := by
-- proof
  have h1 : Tendsto (fun x => f x - a) l (nhds 0) := by
    rw [show (0 : ℂ) = a - a from by ring]; exact Tendsto.sub hf tendsto_const_nhds
  have h2 : Tendsto (fun x => ‖f x - a‖) l (nhds 0) := by
    rw [show (0 : ℝ) = ‖(0 : ℂ)‖ from by simp]; exact Tendsto.norm h1
  simpa using h2.pow 2

/--
[kostant_lemma_13_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma kostant_lemma_13_2
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _}
  [MeasurableSpace T]
  {μ : Measure T}
  [IsFiniteMeasure μ]
  {posRoots : Finset ι}
  {φ : ι → T → ℂ}
-- given
  (hφ_norm : ∀ α ∈ posRoots, ∀ x, ‖φ α x‖ = 1)
  (hφ_meas : ∀ α ∈ posRoots, Measurable (φ α))
  (hφ_ne_one : ∀ α ∈ posRoots, μ {x | φ α x = 1} = 0) :
-- imply
  Tendsto (fun q : ℝ => ∫ x, ‖KostantFqProd posRoots φ q x - 1‖^2 ∂μ) (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 0) := by
-- proof
  suffices h : Tendsto (fun q : ℝ => ∫ x, ‖KostantFqProd posRoots φ q x - 1‖ ^ 2 ∂μ)
    (nhdsWithin 1 (Set.Ioo 0 1)) (nhds (∫ _ : T, (0 : ℝ) ∂μ)) by
    simp only [integral_zero] at h; exact h
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => ((2 : ℝ) ^ posRoots.card + 1) ^ 2)
  · apply eventually_of_mem self_mem_nhdsWithin
    intro q _
    exact ((Finset.measurable_prod posRoots fun α hα =>
      (measurable_const.sub (hφ_meas α hα)).div
        (measurable_const.sub (measurable_const.mul (hφ_meas α hα)))).sub
      measurable_const).norm.pow_const _ |>.aestronglyMeasurable
  · apply eventually_of_mem self_mem_nhdsWithin
    intro q hq
    apply Eventually.of_forall; intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hq0 := hq.1; have hq1 := hq.2
    have hpn : ‖KostantFqProd posRoots φ q x‖ ≤ 2 ^ posRoots.card := by
      unfold KostantFqProd
      rw [show ‖∏ α ∈ posRoots, KostantFqSingleFactor q (φ α x)‖ =
        ∏ α ∈ posRoots, ‖KostantFqSingleFactor q (φ α x)‖ from by
        change (normHom : ℂ →*₀ ℝ) _ = _; exact map_prod normHom _ posRoots]
      calc ∏ α ∈ posRoots, ‖KostantFqSingleFactor q (φ α x)‖
        ≤ ∏ _ ∈ posRoots, (2 : ℝ) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => by
            unfold KostantFqSingleFactor; rw [norm_div]
            rw [div_le_iff₀ (norm_pos_iff.mpr
              (KostantFq_denom_ne_zero q (φ i x) (le_of_lt hq0) hq1 (hφ_norm i hi x)))]
            nlinarith [KostantFq_normSq_bound q (φ i x) (le_of_lt hq0) (hφ_norm i hi x),
              sq_nonneg (‖(1 : ℂ) - φ i x‖ - 2 * ‖(1 : ℂ) - (q : ℂ) * φ i x‖),
              norm_nonneg ((1 : ℂ) - φ i x), norm_nonneg ((1 : ℂ) - (q : ℂ) * φ i x),
              Complex.normSq_eq_norm_sq (1 - φ i x),
              Complex.normSq_eq_norm_sq (1 - (q : ℂ) * φ i x)]
        _ = 2 ^ posRoots.card := by rw [Finset.prod_const, Finset.card_def]
    have h_sub : ‖KostantFqProd posRoots φ q x - 1‖ ≤ 2 ^ posRoots.card + 1 := by
      linarith [norm_sub_le (KostantFqProd posRoots φ q x) 1, norm_one (α := ℂ)]
    exact pow_le_pow_left₀ (norm_nonneg _) h_sub 2
  · exact integrable_const _
  ·
    have hae : ∀ᵐ x ∂μ, ∀ α ∈ posRoots, φ α x ≠ 1 := by
      rw [ae_iff]
      apply measure_mono_null (show {a | ¬∀ α ∈ posRoots, φ α a ≠ 1} ⊆
        ⋃ α ∈ (posRoots : Set ι), {x | φ α x = 1} from by
        intro x hx; push Not at hx
        exact let ⟨α, hα, heq⟩ := hx; Set.mem_biUnion hα heq)
      exact (measure_biUnion_null_iff posRoots.countable_toSet).mpr
        fun α hα => hφ_ne_one α hα
    filter_upwards [hae] with t ht
    apply tendsto_norm_sq_sub_zero_complex
    show Tendsto (fun q => ∏ α ∈ posRoots, KostantFqSingleFactor q (φ α t))
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 1)
    rw [show (1 : ℂ) = ∏ _ ∈ posRoots, (1 : ℂ) from by simp]
    exact @tendsto_finset_prod ι ℝ ℂ _ _ _
      (fun α (q : ℝ) => KostantFqSingleFactor q (φ α t)) _ _
      posRoots (fun α hα => KostantFq_single_tendsto_one (φ α t) (ht α hα))

/--
[kostant_cst_mulMap_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma kostant_cst_mulMap_bijective_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Function.Bijective (kostant_cst_mulMap ksd) := by
-- proof
  apply kostant_cst_mulMap_bijective R 𝔤 ksd

/--
[pbw_mulMap_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean)
-/
@[path]
private lemma pbw_mulMap_bijective_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [DecidableEq P']
  [AddCommGroup P']
  [LieAlgebra.IsSemisimple R 𝔤]
  {ksd : @KostantSetupData R _ 𝔤 _ _ _} :
-- imply
  Function.Bijective (pbw_mulMap ksd) := by
-- proof
  apply pbw_mulMap_bijective R 𝔤 ksd


-- created on 2026-10-23
-- updated on 2026-10-24
