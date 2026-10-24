import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicFiniteBoundaryCutoff
open StatMech StatMech.Universality


/--
[isingFiniteGraphBoundaryVertices_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphBoundaryVertices_nonempty_eq
  [Fintype V]
-- given
  (boundary : V → Prop)
  (hboundary : ∃ x, boundary x) :
-- imply
  (isingFiniteGraphBoundaryVertices boundary).Nonempty := by
-- proof
  apply StatMech.Universality.isingFiniteGraphBoundaryVertices_nonempty boundary hboundary

/--
[isingFiniteGraphDistanceToBoundary_le_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphDistanceToBoundary_le_dist_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x b : V}
-- given
  (boundary : V → Prop)
  (hboundary : ∃ x, boundary x)
  (hb : boundary b) :
-- imply
  isingFiniteGraphDistanceToBoundary G boundary hboundary x ≤ G.dist x b := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDistanceToBoundary_le_dist G boundary hboundary x b hb

/--
[isingFiniteGraphDistanceToBoundary_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphDistanceToBoundary_eq_zero_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (boundary : V → Prop)
  (hboundary : ∃ x, boundary x)
  (hx : boundary x) :
-- imply
  isingFiniteGraphDistanceToBoundary G boundary hboundary x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDistanceToBoundary_eq_zero G boundary hboundary x hx

/--
[isingFiniteGraphDistanceToBoundary_exists_eq_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphDistanceToBoundary_exists_eq_dist_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (boundary : V → Prop)
  (hboundary : ∃ x, boundary x) :
-- imply
  ∃ b, boundary b ∧ isingFiniteGraphDistanceToBoundary G boundary hboundary x = G.dist x b := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDistanceToBoundary_exists_eq_dist G boundary hboundary x

/--
[isingFiniteGraphDistanceToBoundary_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphDistanceToBoundary_adj_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x y : V}
-- given
  (boundary : V → Prop)
  (hboundary : ∃ x, boundary x)
  (hxy : G.Adj x y) :
-- imply
  isingFiniteGraphDistanceToBoundary G boundary hboundary y ≤ isingFiniteGraphDistanceToBoundary G boundary hboundary x + 1 ∧ isingFiniteGraphDistanceToBoundary G boundary hboundary x ≤ isingFiniteGraphDistanceToBoundary G boundary hboundary y + 1 := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDistanceToBoundary_adj G boundary hboundary hxy

/--
[isingFiniteGraphBoundaryTentCutoff_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphBoundaryTentCutoff_support_eq
  [Fintype V]
  {G : SimpleGraph V}
  {r : Nat}
-- given
  (boundary : V → Prop)
  (hboundary : ∃ x, boundary x) :
-- imply
  ∀ x, isingFiniteGraphBoundaryTentCutoff G boundary hboundary r x ≠ 0 → ¬ boundary x := by
-- proof
  apply StatMech.Universality.isingFiniteGraphBoundaryTentCutoff_support G boundary hboundary r

/--
[isingFiniteGraphBoundaryTentCutoff_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphBoundaryTentCutoff_lipschitz_eq
  [Fintype V]
  {G : SimpleGraph V}
  {r : Nat}
  {d : G.Dart}
-- given
  (boundary : V → Prop)
  (hboundary : ∃ x, boundary x)
  (hr : 0 < r) :
-- imply
  |isingFiniteGraphBoundaryTentCutoff G boundary hboundary r d.snd - isingFiniteGraphBoundaryTentCutoff G boundary hboundary r d.fst| ≤ 1 / (r : Real) := by
-- proof
  apply StatMech.Universality.isingFiniteGraphBoundaryTentCutoff_lipschitz G boundary hboundary r hr d

/--
[isingFiniteGraphBoundaryTentCutoff_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean)
-/
@[path]
private lemma isingFiniteGraphBoundaryTentCutoff_eq_one_eq
  [Fintype V]
  {G : SimpleGraph V}
  {r : Nat}
  {x : V}
-- given
  (boundary : V → Prop)
  (hboundary : ∃ x, boundary x)
  (hr : 0 < r)
  (hx : r ≤ isingFiniteGraphDistanceToBoundary G boundary hboundary x) :
-- imply
  isingFiniteGraphBoundaryTentCutoff G boundary hboundary r x = 1 := by
-- proof
  apply StatMech.Universality.isingFiniteGraphBoundaryTentCutoff_eq_one G boundary hboundary r hr x hx


-- created on 2026-10-23
