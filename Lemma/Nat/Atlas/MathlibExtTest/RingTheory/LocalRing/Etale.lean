import Mathlib
import sympy.Basic
open Polynomial


/--
[test_formallyUnramified_of_isUnit_aeval_derivative_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/Etale.lean)
-/
@[path]
lemma test_formallyUnramified_of_isUnit_aeval_derivative_adjoin_eq_top
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  {x : S}
  {P : R[X]}
-- given
  (h0 : aeval x P = 0)
  (hu : IsUnit (aeval x P.derivative))
  (htop : Algebra.adjoin R ({x} : Set S) = ⊤) :
-- imply
  Algebra.FormallyUnramified R S :=
-- proof
  Algebra.FormallyUnramified.of_isUnit_aeval_derivative_of_adjoin_eq_top x P h0 hu htop

/--
[test_etale_forward_exists_adjoin_eq_top_separable_minpoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/Etale.lean)
-/
@[path]
lemma test_etale_forward_exists_adjoin_eq_top_separable_minpoly
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [IsLocalRing R]
  [IsLocalRing S]
  [Module.Finite R S]
  [FaithfulSMul R S]
  [Module.Flat R S]
  [Algebra.FinitePresentation R S]
-- given
  (h : Algebra.Etale R S) :
-- imply
  ∃ x : S, Algebra.adjoin R ({x} : Set S) = ⊤ ∧ ((minpoly R x).map (IsLocalRing.residue R)).Separable :=
-- proof
  (Algebra.etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly).mp h

/--
[test_etale_reverse_exists_adjoin_eq_top_separable_minpoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/Etale.lean)
-/
@[path]
lemma test_etale_reverse_exists_adjoin_eq_top_separable_minpoly
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [IsLocalRing R]
  [IsLocalRing S]
  [Module.Finite R S]
  [FaithfulSMul R S]
  [Module.Flat R S]
  [Algebra.FinitePresentation R S]
-- given
  (h : ∃ x : S, Algebra.adjoin R ({x} : Set S) = ⊤ ∧ ((minpoly R x).map (IsLocalRing.residue R)).Separable) :
-- imply
  Algebra.Etale R S :=
-- proof
  (Algebra.etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly).mpr h

/--
[test_etale_iff_dedekind_finite_torsionFree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/Etale.lean)
-/
@[path]
lemma test_etale_iff_dedekind_finite_torsionFree
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [IsLocalRing R]
  [IsLocalRing S]
  [IsDedekindDomain R]
  [Module.Finite R S]
  [FaithfulSMul R S]
  [Module.IsTorsionFree R S] :
-- imply
  Algebra.Etale R S ↔ ∃ x : S, Algebra.adjoin R ({x} : Set S) = ⊤ ∧ ((minpoly R x).map (IsLocalRing.residue R)).Separable := by
-- proof
  let _ : Module.Flat R S := inferInstance
  let _ : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  let _ : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finitePresentation R S
  exact Algebra.etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly


-- created on 2026-10-23
