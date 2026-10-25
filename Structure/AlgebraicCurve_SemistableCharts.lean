import Structure.ModularCurve_FinitePlaceLift

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


section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]


end DegenerateMember

end Annulus

namespace ComponentChart

section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]


end DegenerateMember

end ComponentChart

end AlgebraicCurve

end
