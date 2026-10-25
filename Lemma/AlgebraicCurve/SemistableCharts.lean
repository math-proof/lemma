import Lemma.ModularCurve.FinitePlaceLift
import Structure.AlgebraicCurve_SemistableCharts

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]


namespace ComponentChart

variable {A F Fbar}

def ofConstantReduction (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    ComponentChart A F Fbar where
  integers := R.integers
  residue := R.residue
  dom := Set.univ
  nodes := ∅
  placeMap := R.placeMap
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem
  placeMap_not_mem_nodes := fun _ _ h => (Finset.notMem_empty _ h).elim
  pointwise := fun P _ hP f hf hfib => hR P hP f hf (fun w hw => hfib w (Set.mem_univ w) hw)
  mapDomain_placeMap := fun f hf D hD _ Q _ =>
    R.mapDomain_placeMap f hf D (fun P => hD P (Set.mem_univ P)) Q

@[simp] theorem ofConstantReduction_integers (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).integers = R.integers := rfl

@[simp] theorem ofConstantReduction_dom (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).dom = Set.univ := rfl

@[simp] theorem ofConstantReduction_nodes (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).nodes = ∅ := rfl

@[simp] theorem ofConstantReduction_placeMap (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).placeMap = R.placeMap := rfl

end ComponentChart


namespace Annulus

variable {A F}

variable {Fbar}

def IsAttached (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) :
    Prop :=
  x ∈ C.nodes ∧ ∃ hz : An.param ∈ C.integers, x.ord (C.residue ⟨An.param, hz⟩) = 1 ∧
    ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)

section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]

theorem maximalIdeal_top_eq_bot' : maximalIdeal ↥(⊤ : ValuationSubring L) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [Ideal.mem_bot]
  by_contra hne
  apply hx
  have hxv : (x : L) ≠ 0 := fun h => hne (Subtype.ext h)
  exact ⟨⟨x, ⟨(x : L)⁻¹, ValuationSubring.mem_top _⟩,
    Subtype.ext (mul_inv_cancel₀ hxv), Subtype.ext (inv_mul_cancel₀ hxv)⟩, rfl⟩

def ofTop : Annulus (⊤ : ValuationSubring L) F where
  dom := ∅
  param := 1
  modulus := 0
  modulus_mem := Ideal.zero_mem _
  mem_dom := fun _ h => (Set.notMem_empty _ h).elim
  existsUnique_evalAt_eq := fun c hc hc0 _ => by
    rw [maximalIdeal_top_eq_bot', Ideal.mem_bot] at hc
    exact absurd (congrArg Subtype.val hc) hc0
  ord_param_sub := fun _ h => (Set.notMem_empty _ h).elim
  unit_principle := fun _ _ _ => ⟨0, 1, one_ne_zero, fun _ h => (Set.notMem_empty _ h).elim⟩

theorem dom_ofTop : (ofTop L F).dom = ∅ := rfl

theorem dom_eq_empty_of_top (An : Annulus (⊤ : ValuationSubring L) F) : An.dom = ∅ := by
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

def ofTop : ComponentChart (⊤ : ValuationSubring L) F F :=
  ofConstantReduction (ConstantReduction.ofTop L F) (ConstantReduction.isPointwise_ofTop L F)

theorem ofTop_dom : (ofTop L F).dom = Set.univ := rfl

theorem ofTop_nodes : (ofTop L F).nodes = ∅ := rfl

theorem not_isAttached_ofTop (An : Annulus (⊤ : ValuationSubring L) F)
    (x : Place (ResidueField ↥(⊤ : ValuationSubring L)) F) : ¬ An.IsAttached (ofTop L F) x :=
  fun h => Finset.notMem_empty _ h.1

end DegenerateMember

end ComponentChart

end AlgebraicCurve

end
