import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.MonomialDisorder
open Finset StatMech StatMech.Ising


/--
[sum_reverseInteractionCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MonomialDisorder.lean)
-/
@[path]
private lemma sum_reverseInteractionCoupling_eq
  [Fintype V]
  [DecidableEq V]
  {D : Finset P}
-- given
  (K : P -> Real)
  (f : P -> Real) :
-- imply
  (∑ p : P, reverseInteractionCoupling K D p * f p) = (∑ p : P, K p * f p) - 2 * ∑ p ∈ D, K p * f p := by
-- proof
  apply StatMech.Ising.sum_reverseInteractionCoupling K D f

/--
[isSpinMonomial_finsetProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MonomialDisorder.lean)
-/
@[path]
private lemma isSpinMonomial_finsetProd_eq
  [Fintype V]
  [DecidableEq V]
  {S : Finset P}
-- given
  (fac : P -> ConfigSpace V -> Real)
  (hfac : forall p, IsSpinMonomial (fac p)) :
-- imply
  IsSpinMonomial (fun sigma => ∏ p ∈ S, fac p sigma) := by
-- proof
  apply StatMech.Ising.isSpinMonomial_finsetProd fac hfac S

/--
[monomialInteractionPartition_eq_powerset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MonomialDisorder.lean)
-/
@[path]
private lemma monomialInteractionPartition_eq_powerset_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (K : P -> Real)
  (fac : P -> ConfigSpace V -> Real)
  (hpm : forall p sigma, fac p sigma = 1 ∨ fac p sigma = -1) :
-- imply
  monomialInteractionPartition K fac = ∑ S ∈ (Finset.univ : Finset P).powerset, (∏ p ∈ S, Real.cosh (K p)) * (∏ p ∈ (Finset.univ : Finset P) \ S, Real.sinh (K p)) * ∑ sigma : ConfigSpace V, ∏ p ∈ (Finset.univ : Finset P) \ S, fac p sigma := by
-- proof
  apply StatMech.Ising.monomialInteractionPartition_eq_powerset K fac hpm

/--
[monomialInteractionPartition_reverse_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MonomialDisorder.lean)
-/
@[path]
private lemma monomialInteractionPartition_reverse_le_eq
  [Fintype V]
  [DecidableEq V]
  {D : Finset P}
-- given
  (K : P -> Real)
  (fac : P -> ConfigSpace V -> Real)
  (hK : forall p, 0 <= K p)
  (hfac : forall p, IsSpinMonomial (fac p))
  (hpm : forall p sigma, fac p sigma = 1 ∨ fac p sigma = -1) :
-- imply
  monomialInteractionPartition (reverseInteractionCoupling K D) fac <= monomialInteractionPartition K fac := by
-- proof
  apply StatMech.Ising.monomialInteractionPartition_reverse_le K fac hK hfac hpm D


-- created on 2026-10-23
