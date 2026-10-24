import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFullSources
open StatMech StatMech.Ising


/--
[lpReplicaOffdiagDecoratedSource_strictRoute_target_fullSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFullSources.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_strictRoute_target_fullSources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j k u v : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (hu : u = i ∨ u = j ∨ u = k)
  (hv : v = i ∨ v = j ∨ v = k)
  (huv : u ≠ v)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hfold : lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v))) :
-- imply
  let l := lpReplicaThirdOfThree i j k u v let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 (Finset.univ \ {d})) (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d}) RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) target) Finset.univ = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) l ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_strictRoute_target_fullSources G sites hsite hij hik hjk hu hv huv q z d hfold


-- created on 2026-10-23
