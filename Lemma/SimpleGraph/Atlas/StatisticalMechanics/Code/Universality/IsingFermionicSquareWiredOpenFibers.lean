import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOpenFibers
open Finset SimpleGraph StatMech StatMech.Universality


/--
[fkIsingSquareWired_one_visit_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOpenFibers.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_separated_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hone : (fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) ∨ (¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)) :
-- imply
  ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_separated n hn omega e hone

/--
[fkIsingSquareWired_one_visit_gadget_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOpenFibers.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_gadget_separated_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hone : (fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) ∨ (¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)) :
-- imply
  ¬ (fkIsingSquareLiftPhysicalGraph n (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega)) ⊔ fkIsingSquareWiredExteriorGadget n).Reachable (.physical (fkIsingSquareOrientedEdge n e).tail) (.physical (fkIsingSquareOrientedEdge n e).head) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_gadget_separated n hn omega e hone

/--
[fkIsingSquareWired_one_visit_west_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOpenFibers.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e side)
  (hphaseW : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .west)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .west)))
  (hphaseS : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south))) :
-- imply
  let D := fkIsingSquareWiredDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_contour_balance n hn omega e hwest heast hopen hphaseW hphaseS

/--
[fkIsingSquareWired_one_visit_east_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOpenFibers.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e side)
  (hphaseE : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .east)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .east)))
  (hphaseN : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north))) :
-- imply
  let D := fkIsingSquareWiredDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_contour_balance n hn omega e hwest heast hopen hphaseE hphaseN


-- created on 2026-10-23
