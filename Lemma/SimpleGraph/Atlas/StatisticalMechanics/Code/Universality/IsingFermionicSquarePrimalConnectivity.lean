import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity
open SimpleGraph StatMech StatMech.Universality


/--
[fkIsingSquare_openWiredExteriorGadget_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_openWiredExteriorGadget_reachable_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : (fkSquareBoxPlanar n).V} :
-- imply
  (fkIsingSquareLiftPhysicalGraph n (openSub (fkSquareBoxPlanar n).G omega) ⊔ fkIsingSquareWiredExteriorGadget n).Reachable (.physical x) (.physical y) ↔ (openSub (fkSquareBoxPlanar n).G omega ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquare_openWiredExteriorGadget_reachable_iff n omega x y

/--
[fkIsingSquare_caseThree_westNorth_contour_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_caseThree_westNorth_contour_algebra_eq
  {m cW cE cS cN oW oN : Complex}
-- given
  (hcS : cS = isingLambda⁻¹ * cW)
  (hcN : cN = isingLambda⁻¹ * cE)
  (hoN : oN = isingLambda * oW)
  (hterminal : oN = cN)
  (hsource : oW = cW) :
-- imply
  (m * cW + (Real.sqrt 2 : Complex) * m * oW) - m * cE = Complex.I * (m * cS - (m * cN + (Real.sqrt 2 : Complex) * m * oN)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_caseThree_westNorth_contour_algebra m cW cE cS cN oW oN hcS hcN hoN hterminal hsource

/--
[fkIsingSquare_caseThree_eastSouth_contour_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_caseThree_eastSouth_contour_algebra_eq
  {m cW cE cS cN oE oS : Complex}
-- given
  (hcS : cS = isingLambda⁻¹ * cW)
  (hcN : cN = isingLambda⁻¹ * cE)
  (hoS : oS = isingLambda * oE)
  (hterminal : oS = cS)
  (hsource : oE = cE) :
-- imply
  m * cW - (m * cE + (Real.sqrt 2 : Complex) * m * oE) = Complex.I * ((m * cS + (Real.sqrt 2 : Complex) * m * oS) - m * cN) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_caseThree_eastSouth_contour_algebra m cW cE cS cN oE oS hcS hcN hoS hterminal hsource

/--
[fkIsingSquareCarrierPrimalLabel_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquareCarrierPrimalLabel_source_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCarrierPrimalLabel n hn .source = fkIsingSquareMarkedA n := by
-- proof
  apply StatMech.Universality.fkIsingSquareCarrierPrimalLabel_source n hn

/--
[fkIsingSquareCarrierPrimalLabel_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquareCarrierPrimalLabel_terminal_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCarrierPrimalLabel n hn .terminal = fkIsingSquareMarkedB n := by
-- proof
  apply StatMech.Universality.fkIsingSquareCarrierPrimalLabel_terminal n hn

/--
[fkIsingSquareCarrierPrimalLabel_sourceAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquareCarrierPrimalLabel_sourceAttachment_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCarrierPrimalLabel n hn (fkIsingSquareSourceAttachment n hn) = fkIsingSquareMarkedA n := by
-- proof
  apply StatMech.Universality.fkIsingSquareCarrierPrimalLabel_sourceAttachment n hn

/--
[fkIsingSquareCarrierPrimalLabel_terminalAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquareCarrierPrimalLabel_terminalAttachment_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCarrierPrimalLabel n hn (fkIsingSquareTerminalAttachment n hn) = fkIsingSquareMarkedB n := by
-- proof
  apply StatMech.Universality.fkIsingSquareCarrierPrimalLabel_terminalAttachment n hn

/--
[fkIsingSquare_localMate_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_localMate_primalLabel_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (openSub (fkSquareBoxPlanar n).G omega ⊔ (fkIsingSquareDobrushinDomain n hn).wiring).Reachable (fkIsingSquareCarrierPrimalLabel n hn (.dart d)) (fkIsingSquareCarrierPrimalLabel n hn (.dart (FKIsingMedialDart.localMate omega d))) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_localMate_primalLabel_reachable n hn omega d

/--
[fkIsingSquare_cutBondMate_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_cutBondMate_primalLabel_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (openSub (fkSquareBoxPlanar n).G omega ⊔ (fkIsingSquareDobrushinDomain n hn).wiring).Reachable (fkIsingSquareCarrierPrimalLabel n hn x) (fkIsingSquareCarrierPrimalLabel n hn (fkIsingSquareCutBondMate n hn x)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_cutBondMate_primalLabel_reachable n hn omega x

/--
[fkIsingSquareLoopGraph_adj_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_adj_primalLabel_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareLoopGraph n hn omega).Adj x y) :
-- imply
  (openSub (fkSquareBoxPlanar n).G omega ⊔ (fkIsingSquareDobrushinDomain n hn).wiring).Reachable (fkIsingSquareCarrierPrimalLabel n hn x) (fkIsingSquareCarrierPrimalLabel n hn y) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_adj_primalLabel_reachable n hn omega hxy

/--
[fkIsingSquareLoopGraph_reachable_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_reachable_primalLabel_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareLoopGraph n hn omega).Reachable x y) :
-- imply
  (openSub (fkSquareBoxPlanar n).G omega ⊔ (fkIsingSquareDobrushinDomain n hn).wiring).Reachable (fkIsingSquareCarrierPrimalLabel n hn x) (fkIsingSquareCarrierPrimalLabel n hn y) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_reachable_primalLabel_reachable n hn omega hxy

/--
[fkIsingSquareCompletedLoopGraph_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquareCompletedLoopGraph_reachable_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareCompletedLoopGraph n hn omega).Reachable x y ↔ (fkIsingSquareLoopGraph n hn omega).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareCompletedLoopGraph_reachable_iff n hn omega x y

/--
[fkIsingSquareCompletedLoopGraph_reachable_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquareCompletedLoopGraph_reachable_primalLabel_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareCompletedLoopGraph n hn omega).Reachable x y) :
-- imply
  (openSub (fkSquareBoxPlanar n).G omega ⊔ (fkIsingSquareDobrushinDomain n hn).wiring).Reachable (fkIsingSquareCarrierPrimalLabel n hn x) (fkIsingSquareCarrierPrimalLabel n hn y) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCompletedLoopGraph_reachable_primalLabel_reachable n hn omega hxy

/--
[fkIsingSquare_one_visit_completedLoop_componentCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_one_visit_completedLoop_componentCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hone : (fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) ∨ (¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east)) :
-- imply
  Nat.card (fkIsingSquareCompletedLoopGraph n hn (setOpen e.1 omega)).ConnectedComponent + 1 = Nat.card (fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)).ConnectedComponent := by
-- proof
  apply StatMech.Universality.fkIsingSquare_one_visit_completedLoop_componentCount n hn omega e hone

/--
[fkIsingSquare_double_visit_closed_endpoints_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_closed_endpoints_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_closed_endpoints_reachable n hn omega e hwest heast

/--
[fkIsingSquare_double_visit_clusterCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_clusterCount_eq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  numClustersBC (fkSquareBoxPlanar n).G (fkIsingSquareDobrushinDomain n hn).wiring (setOpen e.1 omega) = numClustersBC (fkSquareBoxPlanar n).G (fkIsingSquareDobrushinDomain n hn).wiring (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_clusterCount_eq n hn omega e hwest heast

/--
[fkIsingSquare_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareDobrushinDomain n hn).criticalMass (setOpen e.1 omega) = Real.sqrt 2 * (fkIsingSquareDobrushinDomain n hn).criticalMass (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed n hn omega e hwest heast

/--
[fkIsingSquare_double_visit_pointwise_contour_balance_of_discardedLoopTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_pointwise_contour_balance_of_discardedLoopTurn_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hloop : FKIsingSquareDiscardedLoopTurn n hn omega e) :
-- imply
  let D := fkIsingSquareDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareMedialCarrier n := .dart (e, .west) let E : FKIsingSquareMedialCarrier n := .dart (e, .east) let S : FKIsingSquareMedialCarrier n := .dart (e, .south) let N : FKIsingSquareMedialCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_pointwise_contour_balance_of_discardedLoopTurn n hn omega e hwest heast hloop


-- created on 2026-10-23
