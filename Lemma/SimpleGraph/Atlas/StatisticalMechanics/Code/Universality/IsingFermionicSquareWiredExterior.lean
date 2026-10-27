import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part5
open SimpleGraph StatMech StatMech.Universality


/--
[fkIsingSquareWireConfig_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWireConfig_wired_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : Sym2 (fkSquareBoxPlanar n).V}
-- given
  (he : fkIsingSquareIsWiredArcEdge n e) :
-- imply
  fkIsingSquareWireConfig n omega e = true := by
-- proof
  apply StatMech.Universality.fkIsingSquareWireConfig_wired n omega he

/--
[fkIsingSquareWireConfig_nonwired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWireConfig_nonwired_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : Sym2 (fkSquareBoxPlanar n).V}
-- given
  (he : ¬ fkIsingSquareIsWiredArcEdge n e) :
-- imply
  fkIsingSquareWireConfig n omega e = omega e := by
-- proof
  apply StatMech.Universality.fkIsingSquareWireConfig_nonwired n omega he

/--
[fkIsingSquareWireConfig_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWireConfig_setClosed_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : Sym2 (fkSquareBoxPlanar n).V}
-- given
  (he : FKIsingSquareSwitchableEdge n e) :
-- imply
  fkIsingSquareWireConfig n (setClosed e omega) = setClosed e (fkIsingSquareWireConfig n omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWireConfig_setClosed n omega e he

/--
[fkIsingSquareWireConfig_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWireConfig_setOpen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : Sym2 (fkSquareBoxPlanar n).V}
-- given
  (he : FKIsingSquareSwitchableEdge n e) :
-- imply
  fkIsingSquareWireConfig n (setOpen e omega) = setOpen e (fkIsingSquareWireConfig n omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWireConfig_setOpen n omega e he

/--
[fkIsingSquareWiredArcPathGraph_le_clique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWiredArcPathGraph_le_clique_eq
  {n : Nat} :
-- imply
  fkIsingSquareWiredArcPathGraph n ≤ boundaryCliqueGraph (fkIsingSquareWiredArc n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredArcPathGraph_le_clique n

/--
[fkIsingSquareWiredPred_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWiredPred_mem_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hx : fkIsingSquareWiredArc n x)
  (hgt : -(n : Int) < x.1 1) :
-- imply
  fkIsingSquareWiredArc n (fkIsingSquareWiredPred n x hx hgt) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPred_mem n x hx hgt

/--
[fkIsingSquareWiredPred_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWiredPred_adj_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hx : fkIsingSquareWiredArc n x)
  (hgt : -(n : Int) < x.1 1) :
-- imply
  (fkIsingSquareWiredArcPathGraph n).Adj (fkIsingSquareWiredPred n x hx hgt) x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPred_adj n x hx hgt

/--
[fkIsingSquareWiredArcPath_reachable_markedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWiredArcPath_reachable_markedA_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hx : fkIsingSquareWiredArc n x) :
-- imply
  (fkIsingSquareWiredArcPathGraph n).Reachable (fkIsingSquareMarkedA n) x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredArcPath_reachable_markedA n x hx

/--
[fkIsingSquareWiredArcPath_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareWiredArcPath_reachable_eq
  {n : Nat}
  {x y : (fkSquareBoxPlanar n).V}
-- given
  (hx : fkIsingSquareWiredArc n x)
  (hy : fkIsingSquareWiredArc n y) :
-- imply
  (fkIsingSquareWiredArcPathGraph n).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredArcPath_reachable n hx hy

/--
[fkIsingSquare_sup_wiredArcPath_reachable_iff_clique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquare_sup_wiredArcPath_reachable_iff_clique_eq
  {n : Nat}
  {H : SimpleGraph (fkSquareBoxPlanar n).V}
  {x y : (fkSquareBoxPlanar n).V} :
-- imply
  (H ⊔ fkIsingSquareWiredArcPathGraph n).Reachable x y ↔ (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquare_sup_wiredArcPath_reachable_iff_clique n H x y

/--
[fkIsingSquare_openSub_wireConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquare_openSub_wireConfig_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)} :
-- imply
  openSub (fkSquareBoxPlanar n).G (fkIsingSquareWireConfig n omega) = openSub (fkSquareBoxPlanar n).G omega ⊔ fkIsingSquareWiredArcPathGraph n := by
-- proof
  apply StatMech.Universality.fkIsingSquare_openSub_wireConfig n omega

/--
[fkIsingSquare_wireConfig_reachable_iff_gadget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquare_wireConfig_reachable_iff_gadget_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : (fkSquareBoxPlanar n).V} :
-- imply
  (openSub (fkSquareBoxPlanar n).G (fkIsingSquareWireConfig n omega)).Reachable x y ↔ (fkIsingSquareLiftPhysicalGraph n (openSub (fkSquareBoxPlanar n).G omega) ⊔ fkIsingSquareWiredExteriorGadget n).Reachable (.physical x) (.physical y) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_wireConfig_reachable_iff_gadget n omega x y

/--
[fkIsingSquareFaithfulPathUses_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareFaithfulPathUses_setClosed_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (he : FKIsingSquareSwitchableEdge n e.1) :
-- imply
  fkIsingSquareFaithfulPathUsesLocalSide n hn (setClosed e.1 omega) e side ↔ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 (fkIsingSquareWireConfig n omega)) e side := by
-- proof
  apply StatMech.Universality.fkIsingSquareFaithfulPathUses_setClosed n hn omega e he side

/--
[fkIsingSquareFaithfulPathUses_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean)
-/
@[path]
private lemma fkIsingSquareFaithfulPathUses_setOpen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (he : FKIsingSquareSwitchableEdge n e.1) :
-- imply
  fkIsingSquareFaithfulPathUsesLocalSide n hn (setOpen e.1 omega) e side ↔ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 (fkIsingSquareWireConfig n omega)) e side := by
-- proof
  apply StatMech.Universality.fkIsingSquareFaithfulPathUses_setOpen n hn omega e he side


-- created on 2026-10-23
