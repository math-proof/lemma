module

public import Mathlib
public import Def.ModularCurve_QAdicPlace
public import Theorem.HahnSeries.JqCoeff

@[expose] public section

set_option autoImplicit false

noncomputable section

open HahnSeries AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000

namespace ModularCurve

variable (K : Type*) [Field K]


section QAdicPlaceMod

variable (F : IntermediateField K (LaurentSeries K))

variable {F} in

def jModElt (hF : jqModC K ∈ F) : F := ⟨jqModC K, hF⟩

variable {F} in
variable {F} in
variable {F} in

variable {F} in
variable {F} in

def jModInvElt (hF : jqModC K ∈ F) : F := (jModElt K hF)⁻¹

variable {F} in
variable {F} in
variable {F} in

variable {F} in
variable {F} in

def uniformizerMod (hF : jqModC K ∈ F) : qIntegersBar K F :=
  ⟨jModInvElt K hF, jModInvElt_mem_qIntegersBar K hF⟩

variable {F} in
variable {F} in
variable {F} in

variable {F} in

variable {F} in

def qInftyPlaceMod (hF : jqModC K ∈ F) : Place K F where
  toValuationSubring := qIntegersBar K F
  algebraMap_mem' := fun a => by
    rw [mem_qIntegersBar_iff, qSeriesBar_algebraMap]
    rcases eq_or_ne a 0 with rfl | ha
    · simp only [HahnSeries.single_eq_zero, HahnSeries.order_zero, le_refl]
    · rw [HahnSeries.order_single ha]
  ne_top' := qIntegersBar_ne_top_of_jqModC_mem K hF
  isPrincipalIdealRing' := qIntegersBar_isPrincipalIdealRing_of_jqModC_mem K hF


end QAdicPlaceMod

section LevelN

variable (N : ℕ) [NeZero N]

def cuspInftyGeom : Place K (modularFunctionFieldC K N) :=
  qInftyPlaceMod K (jqModC_mem K N)

end LevelN


end ModularCurve

end

end
