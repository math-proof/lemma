import Mathlib
import Lemma.Definitions.Def_ModularCurve_NodeDescent
import Lemma.Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open CharPReduction

variable (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))

instance charZero_laurentSeries_algClosure : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
  charZero_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := AlgebraicClosure ℚ))

instance charZero_fieldOver : CharZero (fieldOver N K) :=
  (fieldOver N K).subtype.charZero

theorem constSeries_mem_fieldOver (c : K) :
    constSeries K.toSubalgebra.toSubring c ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inl ⟨c, rfl⟩)

instance algebraFieldOver : Algebra K (fieldOver N K) :=
  RingHom.toAlgebra
    { toFun := fun c => ⟨constSeries K.toSubalgebra.toSubring c, constSeries_mem_fieldOver N K c⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }

theorem algebraMap_fieldOver_coe (c : K) :
    ((algebraMap K (fieldOver N K) c : fieldOver N K) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) :=
  rfl

theorem coeffEmb_jq_eq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem coeffEmb_qExpand_eq (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N x) = qExpand (AlgebraicClosure ℚ) N (coeffEmb (AlgebraicClosure ℚ) x) := by
  ext m
  simp only [coeffEmb_coeff]
  by_cases h : (N : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem fieldOver_le_modularFunctionFieldBar :
    (fieldOver N K).toSubring ≤ (modularFunctionFieldBar N).toSubring := by
  change Subfield.closure _ ≤ (modularFunctionFieldBar N).toSubfield
  rw [Subfield.closure_le]
  rintro x (⟨c, rfl⟩ | rfl | rfl)
  · exact (modularFunctionFieldBar N).algebraMap_mem (c : AlgebraicClosure ℚ)
  · change jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar N
    rw [← coeffEmb_jq_eq]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))
  · change jqNModC (AlgebraicClosure ℚ) N ∈ modularFunctionFieldBar N
    rw [jqNModC, ← coeffEmb_jq_eq, ← coeffEmb_qExpand_eq]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))

instance algebraFieldOverBar : Algebra (fieldOver N K) (modularFunctionFieldBar N) :=
  (Subring.inclusion (fieldOver_le_modularFunctionFieldBar N K)).toAlgebra

theorem algebraMap_fieldOver_bar_coe (x : fieldOver N K) :
    ((algebraMap (fieldOver N K) (modularFunctionFieldBar N) x : modularFunctionFieldBar N)
      : LaurentSeries (AlgebraicClosure ℚ)) = x :=
  rfl

instance isScalarTower_fieldOver_bar_laurent :
    IsScalarTower (fieldOver N K) (modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IsScalarTower.of_algebraMap_eq (R := fieldOver N K) (S := modularFunctionFieldBar N)
    (A := LaurentSeries (AlgebraicClosure ℚ)) (fun _ => rfl)

instance isScalarTower_K_fieldOver_bar :
    IsScalarTower K (fieldOver N K) (modularFunctionFieldBar N) :=
  IsScalarTower.of_algebraMap_eq (R := K) (S := fieldOver N K) (A := modularFunctionFieldBar N)
    (fun _ => Subtype.ext rfl)

section PrimeLevel

variable (q : ℕ) [Fact q.Prime]

theorem coeffEmb_mem_fieldOver_of_mem_full {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull (1 * q)) :
    coeffEmb (AlgebraicClosure ℚ) x ∈ fieldOver (1 * q) K := by
  have hq : q.Prime := Fact.out

  change x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions (1 * q)) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨d, hd, hdvd, rfl⟩
      · rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single]
        rw [← algebraMap_laurentSeries_eq_single]
        exact Subfield.subset_closure (Or.inl ⟨⟨algebraMap ℚ (AlgebraicClosure ℚ) c,
          IntermediateField.algebraMap_mem K c⟩, rfl⟩)
      · haveI := hd
        rw [coeffEmb_qExpand_eq, coeffEmb_jq_eq]
        have hdvd' : d ∣ q := by simpa using hdvd
        rcases (Nat.dvd_prime hq).mp hdvd' with rfl | hdq
        · rw [qExpand_one_apply]
          exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
        · have : qExpand (AlgebraicClosure ℚ) d (jqModC (AlgebraicClosure ℚ))
              = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
            rw [jqNModC]; exact qExpand_congr (by rw [hdq, one_mul]) _
          rw [this]
          exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem isIntegral_fieldOver_algebraMap_laurent (c : AlgebraicClosure ℚ) :
    IsIntegral (fieldOver (1 * q) K)
      (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) := by
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;>
      first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  obtain ⟨p, hp, hpc⟩ := (halg.isAlgebraic c).isIntegral
  refine ⟨p.map (algebraMap ℚ (fieldOver (1 * q) K)), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map,
    RingHom.ext_rat ((algebraMap ↥(fieldOver (1 * q) K) (LaurentSeries (AlgebraicClosure ℚ))).comp
        (algebraMap ℚ ↥(fieldOver (1 * q) K)))
      ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp
        (algebraMap ℚ (AlgebraicClosure ℚ))),
    ← Polynomial.hom_eval₂, hpc, map_zero]

instance algebra_isIntegral_fieldOver_bar :
    Algebra.IsIntegral (fieldOver (1 * q) K) (modularFunctionFieldBar (1 * q)) := by
  refine ⟨fun x => ?_⟩
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(fieldOver (1 * q) K)
      ↥(modularFunctionFieldBar (1 * q)) (LaurentSeries (AlgebraicClosure ℚ))) Subtype.val_injective]
  change IsIntegral (fieldOver (1 * q) K) (x : LaurentSeries (AlgebraicClosure ℚ))
  suffices h : ∀ y ∈ Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
        ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (modularFunctionFieldFull (1 * q) : Set (LaurentSeries ℚ))),
      IsIntegral (fieldOver (1 * q) K) y from h _ (mem_laurentBaseChange_iff.mp x.2)
  intro y hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact isIntegral_fieldOver_algebraMap_laurent K q c
      · exact isIntegral_algebraMap (R := ↥(fieldOver (1 * q) K))
          (x := ⟨_, coeffEmb_mem_fieldOver_of_mem_full K q hz⟩)
  | one => exact isIntegral_one
  | add y z _ _ hy hz => exact hy.add hz
  | neg y _ hy => exact hy.neg
  | inv y _ hy => exact hy.inv
  | mul y z _ _ hy hz => exact hy.mul hz

end PrimeLevel

end NodeLocalized
end ModularCurve

end
