import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive
open StatMech StatMech.Universality


/--
[fkIsingSquare_caseTwo_westSouth_contour_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean)
-/
@[path]
private lemma fkIsingSquare_caseTwo_westSouth_contour_algebra_eq
  {m cW cS oW oE oS oN : Complex}
-- given
  (hcS : cS = isingLambda⁻¹ * cW)
  (hoN : oN = isingLambda * oW)
  (hoS : oS = isingLambda * oE)
  (hW : oW = cW)
  (hS : oS = cS) :
-- imply
  ((Real.sqrt 2 : Complex) * m * cW + m * oW) - m * oE = Complex.I * (((Real.sqrt 2 : Complex) * m * cS + m * oS) - m * oN) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_caseTwo_westSouth_contour_algebra m cW cS oW oE oS oN hcS hoN hoS hW hS

/--
[fkIsingSquare_caseTwo_eastNorth_contour_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean)
-/
@[path]
private lemma fkIsingSquare_caseTwo_eastNorth_contour_algebra_eq
  {m cE cN oW oE oS oN : Complex}
-- given
  (hcN : cN = isingLambda⁻¹ * cE)
  (hoN : oN = isingLambda * oW)
  (hoS : oS = isingLambda * oE)
  (hE : oE = cE)
  (hN : oN = cN) :
-- imply
  (m * oW) - ((Real.sqrt 2 : Complex) * m * cE + m * oE) = Complex.I * ((m * oS) - ((Real.sqrt 2 : Complex) * m * cN + m * oN)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_caseTwo_eastNorth_contour_algebra m cE cN oW oE oS oN hcN hoN hoS hE hN

/--
[fkIsingSquare_no_visit_pointwise_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean)
-/
@[path]
private lemma fkIsingSquare_no_visit_pointwise_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hclosed : ∀ side, ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e side)
  (hopen : ∀ side, ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e side) :
-- imply
  let D := fkIsingSquareDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareMedialCarrier n := .dart (e, .west) let E : FKIsingSquareMedialCarrier n := .dart (e, .east) let S : FKIsingSquareMedialCarrier n := .dart (e, .south) let N : FKIsingSquareMedialCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_no_visit_pointwise_contour_balance n hn omega e hclosed hopen

/--
[fkIsingSquare_one_visit_west_pointwise_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean)
-/
@[path]
private lemma fkIsingSquare_one_visit_west_pointwise_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hopen : ∀ side, fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e side)
  (hseparated : ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head)
  (hphaseW : (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .west)) = (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .west)))
  (hphaseS : (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south))) :
-- imply
  let D := fkIsingSquareDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareMedialCarrier n := .dart (e, .west) let E : FKIsingSquareMedialCarrier n := .dart (e, .east) let S : FKIsingSquareMedialCarrier n := .dart (e, .south) let N : FKIsingSquareMedialCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_one_visit_west_pointwise_contour_balance n hn omega e hwest heast hopen hseparated hphaseW hphaseS

/--
[fkIsingSquare_one_visit_east_pointwise_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean)
-/
@[path]
private lemma fkIsingSquare_one_visit_east_pointwise_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hopen : ∀ side, fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e side)
  (hseparated : ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head)
  (hphaseE : (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .east)) = (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .east)))
  (hphaseN : (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north))) :
-- imply
  let D := fkIsingSquareDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareMedialCarrier n := .dart (e, .west) let E : FKIsingSquareMedialCarrier n := .dart (e, .east) let S : FKIsingSquareMedialCarrier n := .dart (e, .south) let N : FKIsingSquareMedialCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_one_visit_east_pointwise_contour_balance n hn omega e hwest heast hopen hseparated hphaseE hphaseN

/--
[fkIsingSquare_fermionicObservable_contour_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean)
-/
@[path]
private lemma fkIsingSquare_fermionicObservable_contour_relation_eq
  {n : Nat}
  {geometry : FKIsingSquareSwitchingGeometry n hn}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  let D := fkIsingSquareDobrushinDomain n hn let edges := fkIsingSquareLocalCarrierDarts n e D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) = Complex.I * (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_fermionicObservable_contour_relation n hn geometry e


-- created on 2026-10-23
