import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect_ghost1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSourceTrace.lean)
-/
@[path]
private lemma lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect_ghost1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) K lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let C := StatMech.Sharpness.RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m) K (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) let X := (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∩ C let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 ((Si ∆ Sj ∆ T) ∆ Si = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨ ((Si ∆ Sj ∆ T) ∆ Sj = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect_ghost1 G sites hsite hij m K hsrc hdisc

/--
[lpReplicaDecoratedSourceCanonicalHalf_missingSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSourceTrace.lean)
-/
@[path]
private lemma lpReplicaDecoratedSourceCanonicalHalf_missingSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 let X := lpReplicaDecoratedSourceCanonicalHalf G sites i j q z ((Si ∆ Sj ∆ T) ∆ Si = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨ ((Si ∆ Sj ∆ T) ∆ Sj = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedSourceCanonicalHalf_missingSource G sites hsite hij q z

/--
[lpReplicaDecoratedSourceCanonicalHalfTraceMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSourceTrace.lean)
-/
@[path]
private lemma lpReplicaDecoratedSourceCanonicalHalfTraceMap_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (lpReplicaDecoratedSourceCanonicalHalfTraceMap G sites hsite hij q) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedSourceCanonicalHalfTraceMap_injective G sites hsite hij q


-- created on 2026-10-23
