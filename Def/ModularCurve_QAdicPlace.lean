module

public import Theorem.HahnSeries.X0
public import Def.AlgebraicCurve_DivisorClassGroup

@[expose] public section

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve Valuation

namespace ModularCurve

variable (L : Type*) [Field L]


section QSeriesBar

variable (F : IntermediateField L (LaurentSeries L))

def qSeriesBar (f : F) : LaurentSeries L := (f : LaurentSeries L)

variable {L F}

end QSeriesBar

section QAdicPlaceBar

variable (F : IntermediateField L (LaurentSeries L))

def qIntegersBar : ValuationSubring F where
  carrier := {f : F | 0 ≤ (qSeriesBar L F f).order}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, qSeriesBar_zero, HahnSeries.order_zero, le_refl]
  one_mem' := by
    simp only [Set.mem_setOf_eq, qSeriesBar_one]
    rw [HahnSeries.order_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rcases eq_or_ne (a + b) 0 with h0 | h0
    · simp only [h0, qSeriesBar_zero, HahnSeries.order_zero, le_refl]
    · have h := HahnSeries.min_order_le_order_add (x := qSeriesBar L F a)
        (y := qSeriesBar L F b) (by rw [← qSeriesBar_add]; exact qSeriesBar_ne_zero h0)
      rw [qSeriesBar_add]
      exact le_trans (le_min ha hb) h
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rcases eq_or_ne a 0 with rfl | ha0
    · simp only [zero_mul, qSeriesBar_zero, HahnSeries.order_zero, le_refl]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp only [mul_zero, qSeriesBar_zero, HahnSeries.order_zero, le_refl]
    rw [order_qSeriesBar_mul ha0 hb0]
    omega
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [qSeriesBar_neg, HahnSeries.order_neg]
    exact ha
  mem_or_inv_mem' := by
    intro f
    simp only [Set.mem_setOf_eq]
    rcases eq_or_ne f 0 with rfl | hf0
    · left
      simp only [qSeriesBar_zero, HahnSeries.order_zero, le_refl]
    rcases lt_or_ge (qSeriesBar L F f).order 0 with h | h
    · right
      rw [qSeriesBar_inv, order_inv_of_ne_zero_bar (qSeriesBar_ne_zero hf0)]
      omega
    · exact Or.inl h

variable {F}


section Witness

variable {L} {j : F} (hj : (qSeriesBar L F j).order = -1)
include hj

def uniformizerBar : qIntegersBar L F :=
  ⟨j⁻¹, inv_mem_qIntegersBar_of_order_eq_neg_one hj⟩

end Witness

variable (F) in

def qInftyPlaceBar (h : ∃ j : F, (qSeriesBar L F j).order = -1) : Place L F where
  toValuationSubring := qIntegersBar L F
  algebraMap_mem' := fun a => by
    rw [mem_qIntegersBar_iff, qSeriesBar_algebraMap]
    rcases eq_or_ne a 0 with rfl | ha
    · simp only [HahnSeries.single_eq_zero, HahnSeries.order_zero, le_refl]
    · rw [HahnSeries.order_single ha]
  ne_top' := qIntegersBar_ne_top h.choose_spec
  isPrincipalIdealRing' := qIntegersBar_isPrincipalIdealRing h.choose_spec

end QAdicPlaceBar

section RationalTwin

variable (F : IntermediateField ℚ (LaurentSeries ℚ))

def qInftyPlaceRat (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) : Place ℚ F where
  toValuationSubring := qIntegersBar ℚ F
  algebraMap_mem' a := by
    have h' := @Place.algebraMap_mem' ℚ F _ _ (SubalgebraClass.toAlgebra F) (qInftyPlaceBar ℚ F h) a
    have hi : (DivisionRing.toRatAlgebra : Algebra ℚ F) = SubalgebraClass.toAlgebra F := Subsingleton.elim _ _
    rw [hi]
    exact h'
  ne_top' := qIntegersBar_ne_top h.choose_spec
  isPrincipalIdealRing' := qIntegersBar_isPrincipalIdealRing h.choose_spec

variable (N : ℕ) [NeZero N]

def cuspInfty : Place ℚ (modularFunctionField N) :=
  qInftyPlaceRat _ ⟨⟨jq, jq_mem N⟩, order_jq⟩

def cuspInftyFull : Place ℚ (modularFunctionFieldFull N) :=
  qInftyPlaceRat _ ⟨⟨jq, jq_mem_full N⟩, order_jq⟩

end RationalTwin

section IsCusp

variable {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E]

def IsCusp (j : E) (v : Place K E) : Prop :=
  j ∉ v.toValuationSubring

end IsCusp

end ModularCurve

end

end
