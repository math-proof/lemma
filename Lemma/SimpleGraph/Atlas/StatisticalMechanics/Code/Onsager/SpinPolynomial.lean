import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part4
open StatMech StatMech.Onsager


/--
[eval_ons_sectorPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma eval_ons_sectorPoly_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
-- given
  (h : Fin 2 × Fin 2) :
-- imply
  eval x (ons_sectorPoly L h) = ons_sectorWeight L x h := by
-- proof
  apply StatMech.Onsager.eval_ons_sectorPoly L x h

/--
[eval_ons_spinPoly00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma eval_ons_spinPoly00_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  eval x (ons_spinPoly00 L) = ons_spin00 L x := by
-- proof
  apply StatMech.Onsager.eval_ons_spinPoly00 L x

/--
[eval_ons_spinPoly10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma eval_ons_spinPoly10_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  eval x (ons_spinPoly10 L) = ons_spin10 L x := by
-- proof
  apply StatMech.Onsager.eval_ons_spinPoly10 L x

/--
[eval_ons_spinPoly01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma eval_ons_spinPoly01_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  eval x (ons_spinPoly01 L) = ons_spin01 L x := by
-- proof
  apply StatMech.Onsager.eval_ons_spinPoly01 L x

/--
[eval_ons_spinPoly11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma eval_ons_spinPoly11_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  eval x (ons_spinPoly11 L) = ons_spin11 L x := by
-- proof
  apply StatMech.Onsager.eval_ons_spinPoly11 L x

/--
[ons_spinDet_eq_spinDetX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma ons_spinDet_eq_spinDetX_eq
  {L : ℕ}
  {beta : ℝ}
  {a b : Fin 2} :
-- imply
  ons_spinDet L beta a b = ons_spinDetX L (Real.tanh beta) a b := by
-- proof
  apply StatMech.Onsager.ons_spinDet_eq_spinDetX L beta a b

/--
[eval_ons_spinDetPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma eval_ons_spinDetPoly_eq
  {L : ℕ}
  {x : ℝ}
  {a b : Fin 2} :
-- imply
  eval x (ons_spinDetPoly L a b) = ons_spinDetX L x a b := by
-- proof
  apply StatMech.Onsager.eval_ons_spinDetPoly L x a b

/--
[ons_spinKacWardAt_all_of_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma ons_spinKacWardAt_all_of_small_eq
  {L : ℕ}
  [Fact (2 < L)]
  {epsilon : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hsmall : ∀ x ∈ Set.Ioo (0 : ℝ) epsilon, ons_spinKacWardAt L x) :
-- imply
  ∀ x : ℝ, ons_spinKacWardAt L x := by
-- proof
  apply StatMech.Onsager.ons_spinKacWardAt_all_of_small L hepsilon hsmall

/--
[ons_spinKacWardIdentities_of_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean)
-/
@[path]
private lemma ons_spinKacWardIdentities_of_small_eq
  {epsilon : ℕ → ℝ}
  {beta : ℝ}
-- given
  (hepsilon : ∀ L, 0 < epsilon L)
  (hsmall : ∀ (L : ℕ) (hL : 2 < L), letI : Fact (2 < L) := ⟨hL⟩ ∀ x ∈ Set.Ioo (0 : ℝ) (epsilon L), ons_spinKacWardAt L x) :
-- imply
  ons_spinKacWardIdentities beta := by
-- proof
  apply StatMech.Onsager.ons_spinKacWardIdentities_of_small epsilon hepsilon hsmall beta


-- created on 2026-10-23
