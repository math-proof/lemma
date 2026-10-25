import Mathlib
import Instance.AlgebraicCurve_DivisorClassGroup
import Lemma.AlgebraicCurve.Repartitions

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

structure ConstantReduction where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  placeMap : Place L F → Place (ResidueField A) Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

  deg_placeMap : ∀ P, (placeMap P).deg = P.deg

  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

namespace ConstantReduction

variable {A F Fbar}

set_option linter.unusedVariables false in


variable (R : ConstantReduction A F Fbar)


end ConstantReduction

end AlgebraicCurve

end
