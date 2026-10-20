import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.LocalRing.Etale
open Polynomial
open Algebra.FormallyUnramified
open Algebra


/--
[of_isUnit_aeval_derivative_of_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/Etale.lean)
-/
@[path]
private lemma of_isUnit_aeval_derivative_of_adjoin_eq_top_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {x : S}
  {P : R[X]}
-- given
  (hP : aeval x P = 0)
  (hP' : IsUnit (aeval x P.derivative))
  (hx : Algebra.adjoin R {x} = ⊤) :
-- imply
  Algebra.FormallyUnramified R S := by
-- proof
  apply Algebra.FormallyUnramified.of_isUnit_aeval_derivative_of_adjoin_eq_top x P hP hP' hx

/--
[etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/Etale.lean)
-/
@[path]
private lemma etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly_eq
  [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S] [Module.Finite R S] [FaithfulSMul R S] [Module.Flat R S] [Algebra.FinitePresentation R S] :
-- imply
  Algebra.Etale R S ↔
      ∃ x : S, Algebra.adjoin R ({x} : Set S) = ⊤ ∧
        ((minpoly R x).map (IsLocalRing.residue R)).Separable := by
-- proof
  apply Algebra.etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly


-- created on 2026-10-20
