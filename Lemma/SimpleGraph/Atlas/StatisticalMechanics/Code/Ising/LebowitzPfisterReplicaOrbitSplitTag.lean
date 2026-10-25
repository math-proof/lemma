import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag.Part3
open Finset StatMech StatMech.Ising


/--
[lpReplicaCollisionSplit_complProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean)
-/
@[path]
private lemma lpReplicaCollisionSplit_complProfile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P) = fun e => lpReplicaReflectedResidual G sites m a (lpReplicaCurrentEdgeReflect G sites e) := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionSplit_complProfile G sites m a P hP

/--
[lpReplicaCopy_cast_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean)
-/
@[path]
private lemma lpReplicaCopy_cast_edge_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {c : Copy H p}
-- given
  (p q : H.edgeFinset -> Nat)
  (h : p = q) :
-- imply
  (cast (congrArg (Copy H) h) c).1 = c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCopy_cast_edge H p q h c

/--
[lpReplicaCopy_cast_index](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean)
-/
@[path]
private lemma lpReplicaCopy_cast_index_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {c : Copy H p}
-- given
  (p q : H.edgeFinset -> Nat)
  (h : p = q) :
-- imply
  (cast (congrArg (Copy H) h) c).2.val = c.2.val := by
-- proof
  apply StatMech.Ising.lpReplicaCopy_cast_index H p q h c

/--
[lpReplicaOrbitCollisionSplitEquiv_symm_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitEquiv_symm_left_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {d : Copy (lpReplicaCurrentGraph G sites) a}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm (lpReplicaCollisionLeftCopyEmbedding G sites a (lpReplicaReflectedResidual G sites m a) d) = ((lpReplicaCopySubsetEquivProfile G sites m P).symm (cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hP.symm) d)).1 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitEquiv_symm_left G sites m a P hP d

/--
[lpReplicaOrbitCollisionSplitEquiv_symm_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitEquiv_symm_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {d : Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a)}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm (lpReplicaCollisionRightCopyEmbedding G sites a (lpReplicaReflectedResidual G sites m a) d) = ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).symm (cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) (lpReplicaCollisionSplit_complProfile G sites m a P hP).symm) (lpReplicaReflectCopyEquiv G sites (lpReplicaReflectedResidual G sites m a) d))).1 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitEquiv_symm_right G sites m a P hP d

/--
[lpReplicaOrbitCollisionSplitEquiv_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitEquiv_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP c).1 = c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitEquiv_edge G sites m a P hP c

/--
[lpReplicaOrbitCollisionSplitEquiv_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitEquiv_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
-- imply
  endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites a (lpReplicaReflectedResidual G sites m a)) (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP c) = endsM (lpReplicaCurrentGraph G sites) m c := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitEquiv_ends G sites m a P hP c

/--
[lpReplicaRowGate_orbitCollisionSplitTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean)
-/
@[path]
private lemma lpReplicaRowGate_orbitCollisionSplitTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a))}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (ha : a <= m)
  (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
  (hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a)
  (hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites B (lpReplicaReflectedResidual G sites m a)) :
-- imply
  LPReplicaRowGate G sites m A (B.map lpReplicaCurrentReflect.toEmbedding) (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_orbitCollisionSplitTag G sites m a ha P hP Sa Sb A B hSa hSb


-- created on 2026-10-23
