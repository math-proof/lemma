import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
open Finset StatMech StatMech.Ising


/--
[lpReplicaOrbitCollisionSplitTag_rowCopies_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorRecovery.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitTag_rowCopies_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a))}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  lpReplicaRowCopies G sites m (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) false = P := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitTag_rowCopies_false G sites m a P hP Sa Sb

/--
[lpReplicaOrbitCollisionSplitTag_originProfile_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorRecovery.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitTag_originProfile_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a))}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  lpReplicaTaggedOriginProfile G sites m (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) false = a := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitTag_originProfile_false G sites m a P hP Sa Sb

/--
[lpReplicaOrbitCollisionSplitTag_originProfile_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorRecovery.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitTag_originProfile_true_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a))}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  lpReplicaTaggedOriginProfile G sites m (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) true = lpReplicaReflectedResidual G sites m a := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitTag_originProfile_true G sites m a P hP Sa Sb

/--
[lpReplicaReflectCopyEquiv_cast_twice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorRecovery.lean)
-/
@[path]
private lemma lpReplicaReflectCopyEquiv_cast_twice_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {d : Copy (lpReplicaCurrentGraph G sites) p}
-- given
  (sites : I -> V)
  (p q r : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hpq : (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) = q)
  (hqr : (fun e => q (lpReplicaCurrentEdgeReflect G sites e)) = r)
  (hpr : p = r) :
-- imply
  cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hqr) (lpReplicaReflectCopyEquiv G sites q (cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hpq) (lpReplicaReflectCopyEquiv G sites p d))) = cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hpr) d := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopyEquiv_cast_twice G sites p q r hpq hqr hpr d

/--
[lpReplicaOrbitCollisionSplitEquiv_symm_taggedRowOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorRecovery.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitEquiv_symm_taggedRowOne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {d : Copy (lpReplicaCurrentGraph G sites) (lpReplicaTaggedRowProfile G sites m tag true)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  let a := lpReplicaTaggedOriginProfile G sites m tag false let P := lpReplicaRowCopies G sites m tag false let hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a := rfl let hb := lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag let dr0 := lpReplicaReflectCopyEquiv G sites (lpReplicaTaggedRowProfile G sites m tag true) d let dr : Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitEquiv_symm_taggedRowOne G sites m tag d

/--
[lpReplicaOrbitCollisionSplitTag_currentCopies_left_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorRecovery.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitTag_currentCopies_left_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a))}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  lpReplicaCurrentCopies G sites m (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) false false = (Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a (lpReplicaReflectedResidual G sites m a))).map (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitTag_currentCopies_left_false G sites m a P hP Sa Sb

/--
[lpReplicaOrbitCollisionSplitTag_currentCopies_right_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorRecovery.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitTag_currentCopies_right_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a))}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  lpReplicaCurrentCopies G sites m (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) true false = (Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a (lpReplicaReflectedResidual G sites m a))).map (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitTag_currentCopies_right_false G sites m a P hP Sa Sb

/--
[lpReplicaOrbitCollisionSplitTag_currentSubsets_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorRecovery.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitTag_currentSubsets_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  Function.Injective (fun x : Finset (Copy (lpReplicaCurrentGraph G sites) a) × Finset (Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a)) => lpReplicaOrbitCollisionSplitTag G sites m a P hP x.1 x.2) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitTag_currentSubsets_injective G sites m a P hP


-- created on 2026-10-23
