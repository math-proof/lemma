import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareSwitching
open Finset Complex StatMech StatMech.Universality


/--
[fkIsingSquare_closed_west_south_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean)
-/
@[path]
private lemma fkIsingSquare_closed_west_south_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west) :
-- imply
  (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south)) = isingLambda⁻¹ * (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_west_south_phase n hn omega e h

/--
[fkIsingSquare_closed_east_north_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean)
-/
@[path]
private lemma fkIsingSquare_closed_east_north_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north)) = isingLambda⁻¹ * (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_east_north_phase n hn omega e h

/--
[fkIsingSquare_open_west_north_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean)
-/
@[path]
private lemma fkIsingSquare_open_west_north_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west) :
-- imply
  (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = isingLambda * (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_west_north_phase n hn omega e h

/--
[fkIsingSquare_open_east_south_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean)
-/
@[path]
private lemma fkIsingSquare_open_east_south_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east) :
-- imply
  (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = isingLambda * (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_east_south_phase n hn omega e h

/--
[FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean)
-/
@[path]
private lemma windingPhase_eq_of_winding_eq_add_four_pi_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {omega omega' : ConfigSpace (Sym2 P.V)}
  {e e' : M}
-- given
  (h : D.winding omega' e' = D.winding omega e + 4 * Real.pi) :
-- imply
  D.windingPhase omega' e' = D.windingPhase omega e := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi D omega omega' e e' h

/--
[fkIsingSquare_double_visit_terminal_side_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_terminal_side_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∧ (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north))) ∨ (((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧ (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south))) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_terminal_side_phase n hn omega e hwest heast

/--
[fkIsingSquare_caseThree_westNorth_balance_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean)
-/
@[path]
private lemma fkIsingSquare_caseThree_westNorth_balance_algebra_eq
  {m cW cE cS cN oW oN : Complex}
-- given
  (hcS : cS = isingLambda⁻¹ * cW)
  (hcN : cN = isingLambda⁻¹ * cE)
  (hoN : oN = isingLambda * oW)
  (hterminal : oN = cN)
  (hsource : oW = cW) :
-- imply
  (m * cW + (Real.sqrt 2 : Complex) * m * oW) + m * cE = m * cS + (m * cN + (Real.sqrt 2 : Complex) * m * oN) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_caseThree_westNorth_balance_algebra m cW cE cS cN oW oN hcS hcN hoN hterminal hsource

/--
[fkIsingSquare_caseThree_eastSouth_balance_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean)
-/
@[path]
private lemma fkIsingSquare_caseThree_eastSouth_balance_algebra_eq
  {m cW cE cS cN oE oS : Complex}
-- given
  (hcS : cS = isingLambda⁻¹ * cW)
  (hcN : cN = isingLambda⁻¹ * cE)
  (hoS : oS = isingLambda * oE)
  (hterminal : oS = cS)
  (hsource : oE = cE) :
-- imply
  m * cW + (m * cE + (Real.sqrt 2 : Complex) * m * oE) = (m * cS + (Real.sqrt 2 : Complex) * m * oS) + m * cN := by
-- proof
  apply StatMech.Universality.fkIsingSquare_caseThree_eastSouth_balance_algebra m cW cE cS cN oE oS hcS hcN hoS hterminal hsource


-- created on 2026-10-23
