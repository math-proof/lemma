import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwEvenPolynomial_eq_one_of_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma kwEvenPolynomial_eq_one_of_isAcyclic_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hG : G.IsAcyclic)
  (x : Sym2 V -> ℂ) :
-- imply
  kwEvenPolynomial G x = 1 := by
-- proof
  apply StatMech.FrontierA.kwEvenPolynomial_eq_one_of_isAcyclic G hG x

/--
[kwStarGraph_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma kwStarGraph_isAcyclic_eq
  {ι : Type} :
-- imply
  (kwStarGraph ι).IsAcyclic := by
-- proof
  apply StatMech.FrontierA.kwStarGraph_isAcyclic ι

/--
[kwStarDart_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma kwStarDart_adj_eq
  {d : kwStarDart ι} :
-- imply
  (kwStarGraph ι).Adj (kwStarDartTail d) (kwStarDartHead d) := by
-- proof
  apply StatMech.FrontierA.kwStarDart_adj d

/--
[kwStarTransition_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma kwStarTransition_support_eq
  [Fintype ι]
  [DecidableEq ι]
  {x : Sym2 (Unit ⊕ ι) -> ℂ}
  {phase : kwStarDart ι -> kwStarDart ι -> ℂ}
  {d1 d2 : kwStarDart ι}
-- given
  (h : kwStarTransition x phase d2 d1 ≠ 0) :
-- imply
  kwStarDartHead d1 = kwStarDartTail d2 ∧ kwStarDartHead d2 ≠ kwStarDartTail d1 := by
-- proof
  apply StatMech.FrontierA.kwStarTransition_support h

/--
[kwStarTransition_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma kwStarTransition_sq_eq
  [Fintype ι]
  [DecidableEq ι]
-- given
  (x : Sym2 (Unit ⊕ ι) -> ℂ)
  (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
-- imply
  kwStarTransition x phase ^ 2 = 0 := by
-- proof
  apply StatMech.FrontierA.kwStarTransition_sq x phase

/--
[kwStarTransition_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma kwStarTransition_isNilpotent_eq
  [Fintype ι]
  [DecidableEq ι]
-- given
  (x : Sym2 (Unit ⊕ ι) -> ℂ)
  (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
-- imply
  IsNilpotent (kwStarTransition x phase) := by
-- proof
  apply StatMech.FrontierA.kwStarTransition_isNilpotent x phase

/--
[det_one_sub_eq_one_of_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma det_one_sub_eq_one_of_isNilpotent_eq
  [Fintype ι]
  [DecidableEq ι]
  {M : Matrix ι ι ℂ}
-- given
  (hM : IsNilpotent M) :
-- imply
  (1 - M).det = 1 := by
-- proof
  apply StatMech.FrontierA.det_one_sub_eq_one_of_isNilpotent M hM

/--
[kwStarTransition_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma kwStarTransition_det_eq
  [Fintype ι]
  [DecidableEq ι]
-- given
  (x : Sym2 (Unit ⊕ ι) -> ℂ)
  (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
-- imply
  (1 - kwStarTransition x phase).det = 1 := by
-- proof
  apply StatMech.FrontierA.kwStarTransition_det x phase

/--
[kacWard_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean)
-/
@[path]
private lemma kacWard_star_eq
  {ι : Type}
  [Fintype ι]
  [DecidableEq ι]
-- given
  (x : Sym2 (Unit ⊕ ι) -> ℂ)
  (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
-- imply
  (1 - kwStarTransition x phase).det = (kwEvenPolynomial (kwStarGraph ι) x) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_star x phase


-- created on 2026-10-23
