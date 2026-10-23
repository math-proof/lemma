import Lemma.Definitions.Def_ModularCurve_FinitePlaceLift

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

structure ComponentChart where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  dom : Set (Place L F)

  nodes : Finset (Place (ResidueField A) Fbar)

  placeMap : Place L F → Place (ResidueField A) Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

  placeMap_not_mem_nodes : ∀ P ∈ dom, placeMap P ∉ nodes

  pointwise : ∀ P ∈ dom, P.IsRational → ∀ (f : F) (hf : f ∈ integers),
    (∀ w ∈ dom, placeMap w = placeMap P → f ∈ w.toValuationSubring) →
      ∃ (hm : (residue ⟨f, hf⟩ : Fbar) ∈ (placeMap P).toValuationSubring) (h : P.evalAt f ∈ A),
        algebraMap (ResidueField A) (placeMap P).ResidueField (IsLocalRing.residue A ⟨P.evalAt f, h⟩)
          = IsLocalRing.residue (placeMap P).toValuationSubring ⟨residue ⟨f, hf⟩, hm⟩

  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P ∈ dom, D P = P.ord (f : F)) → (∀ P, P ∉ dom → D P = 0) →
      ∀ Q, Q ∉ nodes → Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

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

structure Annulus where

  dom : Set (Place L F)

  param : F

  modulus : A

  modulus_mem : modulus ∈ maximalIdeal A

  mem_dom : ∀ P ∈ dom, P.IsRational ∧ param ∈ P.toValuationSubring ∧
    (∃ h : P.evalAt param ∈ A, (⟨P.evalAt param, h⟩ : A) ∈ maximalIdeal A) ∧ P.evalAt param ≠ 0 ∧
    ∃ m ∈ maximalIdeal A, (modulus : L) = P.evalAt param * m

  existsUnique_evalAt_eq : ∀ c : A, c ∈ maximalIdeal A → (c : L) ≠ 0 →
    (∃ m ∈ maximalIdeal A, (modulus : L) = c * m) → ∃! P : Place L F, P ∈ dom ∧ P.evalAt param = c

  ord_param_sub : ∀ P ∈ dom, P.ord (param - algebraMap L F (P.evalAt param)) = 1

  unit_principle : ∀ f : F, f ≠ 0 → (∀ P ∈ dom, P.ord f = 0) →
    ∃ (m : ℤ) (c : L), c ≠ 0 ∧
      ∀ P ∈ dom, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A)

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
