import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.Monogenic
open IsLocalRing
open IsDiscreteValuationRing


/--
[exists_generator_with_residue_minpoly_uniformizer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
private lemma exists_generator_with_residue_minpoly_uniformizer_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
-- imply
  ∃ (α : B) (F : Polynomial A),
    Algebra.adjoin A ({α} : Set B) = ⊤ ∧
    Algebra.adjoin (ResidueField A)
    ({residue B α} : Set (ResidueField B)) = ⊤ ∧
    F.Monic ∧
    F.map (residue A) =
    minpoly (ResidueField A) (residue B α) ∧
    IsUnit (Polynomial.aeval α F.derivative) ∧
    maximalIdeal B = Ideal.span {Polynomial.aeval α F} := by
-- proof
  apply IsDiscreteValuationRing.exists_generator_with_residue_minpoly_uniformizer

/--
[exists_adjoin_eq_top_of_separable_residueField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
private lemma exists_adjoin_eq_top_of_separable_residueField_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
-- imply
  ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ := by
-- proof
  apply IsDiscreteValuationRing.exists_adjoin_eq_top_of_separable_residueField

/--
[adjoin_eq_top_of_lift_of_map_maximalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
private lemma adjoin_eq_top_of_lift_of_map_maximalIdeal_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  {β : B}
-- given
  (hunram : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (hβ : Algebra.adjoin (ResidueField A) ({residue B β} : Set _) = ⊤) :
-- imply
  Algebra.adjoin A ({β} : Set B) = ⊤ := by
-- proof
  apply IsDiscreteValuationRing.adjoin_eq_top_of_lift_of_map_maximalIdeal hunram hβ

/--
[etale_of_isSeparable_residueField_of_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
private lemma etale_of_isSeparable_residueField_of_finrank_eq_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
-- given
  (hfin : Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B)) :
-- imply
  Algebra.Etale A B := by
-- proof
  apply IsDiscreteValuationRing.etale_of_isSeparable_residueField_of_finrank_eq hfin


-- created on 2026-10-20
