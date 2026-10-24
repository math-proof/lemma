import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite
open Finset Filter Set StatMech StatMech.Ising


/--
[grahamMarkedSite_strong_with_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterStrongMarkedSite.lean)
-/
@[path]
private lemma grahamMarkedSite_strong_with_parameter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
  {q : Real}
-- given
  (K : Sym2 V -> Real)
  (hK : forall e, 0 <= K e)
  (hq0 : 0 < q)
  (hq1 : q < 1) :
-- imply
  2 * grahamTwoPoint G.edgeFinset K k l * (grahamTwoPoint G.edgeFinset K i k - q ^ 2 * grahamTwoPoint G.edgeFinset K i l * grahamTwoPoint G.edgeFinset K k l) * (grahamTwoPoint G.edgeFinset K j k - q ^ 2 * grahamTwoPoint G.edgeFinset K j l * grahamTwoPoint G.edgeFinset K k l) <= (1 - q ^ 2 * grahamTwoPoint G.edgeFinset K k l ^ 2) * (-(grahamUrsell4 G.edgeFinset K i j k l + 2 * q ^ 2 * (grahamTwoPoint G.edgeFinset K i l * grahamTwoPoint G.edgeFinset K j l * grahamTwoPoint G.edgeFinset K k l))) := by
-- proof
  apply StatMech.Ising.grahamMarkedSite_strong_with_parameter G K hK i j k l q hq0 hq1

/--
[grahamMarkedSite_four_point_strong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterStrongMarkedSite.lean)
-/
@[path]
private lemma grahamMarkedSite_four_point_strong_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (K : Sym2 V -> Real)
  (hK : forall e, 0 <= K e) :
-- imply
  2 * grahamTwoPoint G.edgeFinset K k l * grahamBridgeGap G.edgeFinset K i k l * grahamBridgeGap G.edgeFinset K j k l <= (1 - grahamTwoPoint G.edgeFinset K k l ^ 2) * (-(grahamUrsell4 G.edgeFinset K i j k l + 2 * (grahamTwoPoint G.edgeFinset K i l * grahamTwoPoint G.edgeFinset K j l * grahamTwoPoint G.edgeFinset K k l))) := by
-- proof
  apply StatMech.Ising.grahamMarkedSite_four_point_strong G K hK i j k l

/--
[grahamMarkedSite_four_point_strong_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterStrongMarkedSite.lean)
-/
@[path]
private lemma grahamMarkedSite_four_point_strong_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : forall e, 0 <= J e) :
-- imply
  2 * grahamTwoPoint E J k l * grahamBridgeGap E J i k l * grahamBridgeGap E J j k l <= (1 - grahamTwoPoint E J k l ^ 2) * (-(grahamUrsell4 E J i j k l + 2 * (grahamTwoPoint E J i l * grahamTwoPoint E J j l * grahamTwoPoint E J k l))) := by
-- proof
  apply StatMech.Ising.grahamMarkedSite_four_point_strong_edgeFinset E J hdiag hJ i j k l


-- created on 2026-10-23
