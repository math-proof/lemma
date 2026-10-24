import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredSwitching
open Finset Complex StatMech StatMech.Universality StatMech.Universality.LegacyWiredSwitching


/--
[fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc_eq
  {n : Nat}
  {i : FKIsingSquareWiredBoundaryDartIndex n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n (fkIsingSquareWiredBoundaryDart n hn i)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i

/--
[fkIsingSquareWiredBondMate_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_primalLabel_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (openSub (fkSquareBoxPlanar n).G omega ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartEndpoint n (fkIsingSquareWiredBondMate n hn d)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_primalLabel_reachable n hn omega d

/--
[fkIsingSquareWiredLoopGraph_adj_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_adj_primalLabel_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
-- imply
  (openSub (fkSquareBoxPlanar n).G omega ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable (fkIsingSquareWiredCarrierPrimalLabel n hn x) (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_adj_primalLabel_reachable n hn omega hxy

/--
[fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Reachable x y) :
-- imply
  (openSub (fkSquareBoxPlanar n).G omega ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable (fkIsingSquareWiredCarrierPrimalLabel n hn x) (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable n hn omega hxy

/--
[fkIsingSquareWired_double_visit_closed_endpoints_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_closed_endpoints_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_closed_endpoints_reachable n hn omega e hwest heast

/--
[fkIsingSquareWiredCompletedLoopGraph_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_reachable_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x y ↔ (fkIsingSquareWiredLoopGraph n hn omega).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_reachable_iff n hn omega x y

/--
[fkIsingSquareWired_one_visit_completedLoop_componentCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_completedLoop_componentCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hone : (fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) ∨ (¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)) :
-- imply
  Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (setOpen e.1 omega)).ConnectedComponent + 1 = Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)).ConnectedComponent := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_completedLoop_componentCount n hn omega e hone

/--
[fkIsingSquareWired_double_visit_clusterCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_clusterCount_eq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  numClustersBC (fkSquareBoxPlanar n).G (fkIsingSquareWiredDobrushinDomain n hn).wiring (setOpen e.1 omega) = numClustersBC (fkSquareBoxPlanar n).G (fkIsingSquareWiredDobrushinDomain n hn).wiring (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_clusterCount_eq n hn omega e hwest heast

/--
[fkIsingSquareWired_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).criticalMass (setOpen e.1 omega) = Real.sqrt 2 * (fkIsingSquareWiredDobrushinDomain n hn).criticalMass (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_separated_of_eulerDefect_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_separated_of_eulerDefect_eq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hone : (fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) ∨ (¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east))
  (heuler : fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) = fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega)) :
-- imply
  ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_separated_of_eulerDefect_eq n hn omega e hone heuler

/--
[fkIsingSquareWired_closed_west_south_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_west_south_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south)) = isingLambda⁻¹ * (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.LegacyWiredSwitching.fkIsingSquareWired_closed_west_south_phase n hn omega e h

/--
[fkIsingSquareWired_closed_east_north_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_east_north_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north)) = isingLambda⁻¹ * (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.LegacyWiredSwitching.fkIsingSquareWired_closed_east_north_phase n hn omega e h

/--
[fkIsingSquareWired_open_west_north_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_west_north_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .west) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = isingLambda * (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.LegacyWiredSwitching.fkIsingSquareWired_open_west_north_phase n hn omega e h

/--
[fkIsingSquareWired_open_east_south_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_east_south_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = isingLambda * (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.LegacyWiredSwitching.fkIsingSquareWired_open_east_south_phase n hn omega e h

/--
[fkIsingSquareWired_no_visit_pointwise_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_no_visit_pointwise_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hclosed : ∀ side, ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e side)
  (hopen : ∀ side, ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e side) :
-- imply
  let D := fkIsingSquareWiredDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.LegacyWiredSwitching.fkIsingSquareWired_no_visit_pointwise_contour_balance n hn omega e hclosed hopen

/--
[fkIsingSquareWired_one_visit_west_pointwise_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_pointwise_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e side)
  (hseparated : ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head)
  (hphaseW : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .west)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .west)))
  (hphaseS : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south))) :
-- imply
  let D := fkIsingSquareWiredDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.LegacyWiredSwitching.fkIsingSquareWired_one_visit_west_pointwise_contour_balance n hn omega e hwest heast hopen hseparated hphaseW hphaseS

/--
[fkIsingSquareWired_one_visit_east_pointwise_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_pointwise_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e side)
  (hseparated : ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head)
  (hphaseE : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .east)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .east)))
  (hphaseN : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north))) :
-- imply
  let D := fkIsingSquareWiredDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.LegacyWiredSwitching.fkIsingSquareWired_one_visit_east_pointwise_contour_balance n hn omega e hwest heast hopen hseparated hphaseE hphaseN


-- created on 2026-10-23
