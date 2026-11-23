module

public import Theorem.ValuationSubring.FinitePlaceLift
public import Structure.AlgebraicCurve_SemistableCharts

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]


namespace ComponentChart

variable {A F Fbar}


@[simp] public theorem ofConstantReduction_integers (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).integers = R.integers := rfl


@[simp] public theorem ofConstantReduction_dom (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).dom = Set.univ := rfl


@[simp] public theorem ofConstantReduction_nodes (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).nodes = ∅ := rfl


@[simp] public theorem ofConstantReduction_placeMap (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).placeMap = R.placeMap := rfl

end ComponentChart


namespace Annulus

variable {A F}

variable {Fbar}


public theorem maximalIdeal_top_eq_bot' : maximalIdeal ↥(⊤ : ValuationSubring L) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [Ideal.mem_bot]
  by_contra hne
  apply hx
  have hxv : (x : L) ≠ 0 := fun h => hne (Subtype.ext h)
  exact ⟨⟨x, ⟨(x : L)⁻¹, ValuationSubring.mem_top _⟩,
    Subtype.ext (mul_inv_cancel₀ hxv), Subtype.ext (inv_mul_cancel₀ hxv)⟩, rfl⟩


public theorem dom_ofTop : (ofTop L F).dom = ∅ := rfl


public theorem dom_eq_empty_of_top (An : Annulus (⊤ : ValuationSubring L) F) : An.dom = ∅ := by
  ext P
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hP
  obtain ⟨-, -, ⟨h, hm⟩, hne, -⟩ := An.mem_dom P hP
  rw [maximalIdeal_top_eq_bot', Ideal.mem_bot] at hm
  exact hne (congrArg Subtype.val hm)

end DegenerateMember

end Annulus

namespace ComponentChart

section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]

attribute [local instance] ConstantReduction.ofTopAlgebra


public theorem ofTop_dom : (ofTop L F).dom = Set.univ := rfl


public theorem ofTop_nodes : (ofTop L F).nodes = ∅ := rfl


public theorem not_isAttached_ofTop (An : Annulus (⊤ : ValuationSubring L) F)
    (x : Place (ResidueField ↥(⊤ : ValuationSubring L)) F) : ¬ An.IsAttached (ofTop L F) x :=
  fun h => Finset.notMem_empty _ h.1

end DegenerateMember

end ComponentChart

end AlgebraicCurve

end
