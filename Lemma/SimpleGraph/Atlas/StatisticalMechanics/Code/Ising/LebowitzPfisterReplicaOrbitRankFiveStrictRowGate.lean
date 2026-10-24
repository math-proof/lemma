import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRowGate
open StatMech StatMech.Ising


/--
[lpReplicaOffdiagDecoratedSource_strictRoute_target_rowGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRowGate.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_strictRoute_target_rowGate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j k u v : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
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
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites k)
  (hcd : c ≠ d)
  (hfold : lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v)))
  (hdisc : let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 (Finset.univ \ {d})) (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d}) let K' := lpReplicaPartialReflectCopiesRaw G sites z.1.1.1 {d} (Finset.univ \ {c}) ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K' lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let l := lpReplicaThirdOfThree i j k u v let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 (Finset.univ \ {d})) (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d}) let c' := lpReplicaPartialReflectCopyEquivRaw G sites z.1.1.1 {d} c LPReplicaRowGate G sites target (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) l ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) (lpReplicaSingletonFalseRowTag c') := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_strictRoute_target_rowGate G sites hsite hij hik hjk hu hv huv q z c d hc hcd hfold hdisc


-- created on 2026-10-23
