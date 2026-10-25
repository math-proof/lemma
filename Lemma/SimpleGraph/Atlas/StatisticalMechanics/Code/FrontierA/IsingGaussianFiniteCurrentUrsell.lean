import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFiniteCurrentUrsell.Part2
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[finiteIsingFourthUrsell_eq_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean)
-/
@[path]
private lemma finiteIsingFourthUrsell_eq_current_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  finiteIsingFourthUrsell G beta J i j k l = finiteCurrentFourthUrsell G beta J i j k l := by
-- proof
  apply StatMech.FrontierA.finiteIsingFourthUrsell_eq_current G beta J i j k l

/--
[finiteCurrentFourthUrsell_eq_allThree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean)
-/
@[path]
private lemma finiteCurrentFourthUrsell_eq_allThree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  finiteCurrentFourthUrsell G beta J i j k l = -2 * gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => grahamAllThreeConnected G m i j k l) / currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteCurrentFourthUrsell_eq_allThree G beta J hij hik hil hjk hjl hkl

/--
[finiteCurrentFourthUrsell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean)
-/
@[path]
private lemma finiteCurrentFourthUrsell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  finiteCurrentFourthUrsell G beta J i j k l <= 0 := by
-- proof
  apply StatMech.FrontierA.finiteCurrentFourthUrsell_nonpos G beta J hbeta hJ hij hik hil hjk hjl hkl

/--
[finiteCurrentTreeDiagram_eq_mass_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean)
-/
@[path]
private lemma finiteCurrentTreeDiagram_eq_mass_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  finiteCurrentTreeDiagram G beta J i j k l = finiteCurrentTreeDiagramMass G beta J i j k l / currentSum G beta J ∅ ^ 4 := by
-- proof
  apply StatMech.FrontierA.finiteCurrentTreeDiagram_eq_mass_div G beta J i j k l

/--
[finiteCurrent_treeDiagram_bound_iff_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean)
-/
@[path]
private lemma finiteCurrent_treeDiagram_bound_iff_mass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  -finiteCurrentFourthUrsell G beta J i j k l <= 2 * finiteCurrentTreeDiagram G beta J i j k l ↔ gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => grahamAllThreeConnected G m i j k l) * currentSum G beta J ∅ ^ 2 <= finiteCurrentTreeDiagramMass G beta J i j k l := by
-- proof
  apply StatMech.FrontierA.finiteCurrent_treeDiagram_bound_iff_mass G beta J hij hik hil hjk hjl hkl

/--
[finiteIsing_treeDiagram_bound_of_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean)
-/
@[path]
private lemma finiteIsing_treeDiagram_bound_of_mass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l)
  (hmass : gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => grahamAllThreeConnected G m i j k l) * currentSum G beta J ∅ ^ 2 <= finiteCurrentTreeDiagramMass G beta J i j k l) :
-- imply
  0 <= -finiteIsingFourthUrsell G beta J i j k l ∧ -finiteIsingFourthUrsell G beta J i j k l <= 2 * finiteCurrentTreeDiagram G beta J i j k l := by
-- proof
  apply StatMech.FrontierA.finiteIsing_treeDiagram_bound_of_mass G beta J hbeta hJ hij hik hil hjk hjl hkl hmass

/--
[gatedPairConnection_eq_twoPointMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean)
-/
@[path]
private lemma gatedPairConnection_eq_twoPointMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {x₁ x₂ y : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  gatedSourcePairSum G beta J (grahamPairSupport x₁ x₂) ∅ (fun m => CurrentConnected G m x₁ y) = currentSum G beta J (grahamPairSupport x₁ y) * currentSum G beta J (grahamPairSupport y x₂) := by
-- proof
  apply StatMech.FrontierA.gatedPairConnection_eq_twoPointMass G beta J x₁ x₂ y


-- created on 2026-10-23
