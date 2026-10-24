import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent
open Finset StatMech StatMech.Ising


/--
[lpReplicaProfile_le_symmetrizedProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaProfile_le_symmetrizedProfile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  m <= lpReplicaSymmetrizedProfile G sites m := by
-- proof
  apply StatMech.Ising.lpReplicaProfile_le_symmetrizedProfile G sites m

/--
[lpReplicaProfile_le_of_symmetrizedProfile_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaProfile_le_of_symmetrizedProfile_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
-- given
  (sites : I -> V)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  m <= q := by
-- proof
  apply StatMech.Ising.lpReplicaProfile_le_of_symmetrizedProfile_eq G sites hm

/--
[lpReplicaSymmetrizedProfile_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaSymmetrizedProfile_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaSymmetrizedProfile G sites (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) = lpReplicaSymmetrizedProfile G sites m := by
-- proof
  apply StatMech.Ising.lpReplicaSymmetrizedProfile_reflect G sites m

/--
[lpReplicaProfileOrbitMass_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaProfileOrbitMass G sites beta J hf r A B q = ∑ m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // lpReplicaSymmetrizedProfile G sites p = q}, lpReplicaRowFiberMass G sites beta J hf r A B m.1 := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_eq_sum G sites beta J hf r A B q

/--
[lpReplicaReflectCopies_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaReflectCopies_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaReflectCopies G sites m (Finset.univ \ S) = Finset.univ \ lpReplicaReflectCopies G sites m S := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopies_compl G sites m S

/--
[lpReplicaReflectCopies_ghost_disconn_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaReflectCopies_ghost_disconn_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (Not (RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaReflectCopies G sites m S) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) <-> Not (RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) S lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopies_ghost_disconn_iff G sites m S

/--
[lpReplicaDisconnProfileTerm_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaDisconnProfileTerm_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaDisconnProfileTerm G sites beta J hf r (A.map lpReplicaCurrentReflect.toEmbedding) (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) = lpReplicaDisconnProfileTerm G sites beta J hf r A m := by
-- proof
  apply StatMech.Ising.lpReplicaDisconnProfileTerm_reflect G sites beta J hf r A m

/--
[lpReplicaReflectedResidual_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaReflectedResidual_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaReflectedResidual G sites (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (fun e => a (lpReplicaCurrentEdgeReflect G sites e)) = fun e => lpReplicaReflectedResidual G sites m a (lpReplicaCurrentEdgeReflect G sites e) := by
-- proof
  apply StatMech.Ising.lpReplicaReflectedResidual_reflect G sites m a

/--
[lpReplicaRowFiberMass_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaRowFiberMass_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaRowFiberMass G sites beta J hf r (A.map lpReplicaCurrentReflect.toEmbedding) (B.map lpReplicaCurrentReflect.toEmbedding) (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) = lpReplicaRowFiberMass G sites beta J hf r A B m := by
-- proof
  apply StatMech.Ising.lpReplicaRowFiberMass_reflect G sites beta J hf r A B m

/--
[lpReplicaProfileOrbitMass_reflectSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_reflectSources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaProfileOrbitMass G sites beta J hf r (A.map lpReplicaCurrentReflect.toEmbedding) (B.map lpReplicaCurrentReflect.toEmbedding) q = lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_reflectSources G sites beta J hf r A B q

/--
[lpReplicaCurrentReflect_seamSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_seamSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i : I}
-- given
  (sites : I -> V) :
-- imply
  (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i).map lpReplicaCurrentReflect.toEmbedding = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_seamSource G sites i

/--
[lpReplicaCurrentReflect_ghostSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_ghostSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  (lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1).map lpReplicaCurrentReflect.toEmbedding = lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_ghostSource G sites

/--
[lpReplicaCurrentReflect_offdiagSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_offdiagSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V) :
-- imply
  (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1).map lpReplicaCurrentReflect.toEmbedding = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_offdiagSource G sites i j

/--
[lpReplicaReflectSubprofile_le_partialReflectProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaReflectSubprofile_le_partialReflectProfile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) <= lpReplicaPartialReflectProfile G sites m p := by
-- proof
  apply StatMech.Ising.lpReplicaReflectSubprofile_le_partialReflectProfile G sites m p

/--
[lpReplicaSymmetrizedProfile_partialReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaSymmetrizedProfile_partialReflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hp : p <= m) :
-- imply
  lpReplicaSymmetrizedProfile G sites (lpReplicaPartialReflectProfile G sites m p) = lpReplicaSymmetrizedProfile G sites m := by
-- proof
  apply StatMech.Ising.lpReplicaSymmetrizedProfile_partialReflect G sites m p hp

/--
[lpReplicaPartialReflectProfile_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectProfile_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hp : p <= m) :
-- imply
  lpReplicaPartialReflectProfile G sites (lpReplicaPartialReflectProfile G sites m p) (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) = m := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectProfile_involutive G sites m p hp

/--
[lpReplicaSymmetrizedProfile_partialReflectCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaSymmetrizedProfile_partialReflectCopies_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaSymmetrizedProfile G sites (lpReplicaPartialReflectProfile G sites m (profileFlux (lpReplicaCurrentGraph G sites) m P)) = lpReplicaSymmetrizedProfile G sites m := by
-- proof
  apply StatMech.Ising.lpReplicaSymmetrizedProfile_partialReflectCopies G sites m P

/--
[card_lpReplicaCopyIndicesAtEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma card_lpReplicaCopyIndicesAtEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaCopyIndicesAtEdge G sites m P e).card = profileFlux (lpReplicaCurrentGraph G sites) m P e := by
-- proof
  apply StatMech.Ising.card_lpReplicaCopyIndicesAtEdge G sites m P e

/--
[lpReplicaCopySubsetEquivProfile_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaCopySubsetEquivProfile_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
-- imply
  (lpReplicaCopySubsetEquivProfile G sites m P c).1 = c.1.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCopySubsetEquivProfile_edge G sites m P c

/--
[lpReplicaCopySubsetEquivProfile_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaCopySubsetEquivProfile_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
-- imply
  lpReplicaCopySubsetEquivProfile G sites m P c = Sigma.mk c.1.1 (((lpReplicaCopyIndicesAtEdge G sites m P c.1.1).orderIsoOfFin (card_lpReplicaCopyIndicesAtEdge G sites m P c.1.1)).symm ⟨c.1.2, by simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter, Finset.mem_univ, true_and] using c.2⟩) := by
-- proof
  apply StatMech.Ising.lpReplicaCopySubsetEquivProfile_apply G sites m P c

/--
[lpReplicaCopySubsetEquivProfile_symm_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaCopySubsetEquivProfile_symm_cast_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P Q : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {d : Copy (lpReplicaCurrentGraph G sites) (profileFlux (lpReplicaCurrentGraph G sites) m P)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hPQ : P = Q) :
-- imply
  ((lpReplicaCopySubsetEquivProfile G sites m Q).symm (cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) (congrArg (profileFlux (lpReplicaCurrentGraph G sites) m) hPQ)) d)).1 = ((lpReplicaCopySubsetEquivProfile G sites m P).symm d).1 := by
-- proof
  apply StatMech.Ising.lpReplicaCopySubsetEquivProfile_symm_cast G sites m P Q hPQ d

/--
[lpReplicaCopySubsetEquivProfile_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaCopySubsetEquivProfile_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
-- imply
  endsM (lpReplicaCurrentGraph G sites) (profileFlux (lpReplicaCurrentGraph G sites) m P) (lpReplicaCopySubsetEquivProfile G sites m P c) = endsM (lpReplicaCurrentGraph G sites) m c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCopySubsetEquivProfile_ends G sites m P c

/--
[lpReplicaCollisionProfile_compl_eq_partialReflectProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaCollisionProfile_compl_eq_partialReflectProfile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) = lpReplicaPartialReflectProfile G sites m (profileFlux (lpReplicaCurrentGraph G sites) m P) := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionProfile_compl_eq_partialReflectProfile G sites m P

/--
[lpReplicaPartialReflectCopyEquivRaw_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopyEquivRaw_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1 = if c ∈ P then lpReplicaCurrentEdgeReflect G sites c.1 else c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopyEquivRaw_edge G sites m P c

/--
[lpReplicaPartialReflectCopyEquivRaw_index_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopyEquivRaw_index_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hc : c ∈ P) :
-- imply
  (lpReplicaPartialReflectCopyEquivRaw G sites m P c).2.val = profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P) (lpReplicaCurrentEdgeReflect G sites c.1) + (((lpReplicaCopyIndicesAtEdge G sites m P c.1).orderIsoOfFin (card_lpReplicaCopyIndicesAtEdge G sites m P c.1)).symm ⟨c.2, by simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter, Finset.mem_univ, true_and] using hc⟩).val := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopyEquivRaw_index_of_mem G sites m P c hc

/--
[lpReplicaPartialReflectCopyEquivRaw_index_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopyEquivRaw_index_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hc : c ∉ P) :
-- imply
  (lpReplicaPartialReflectCopyEquivRaw G sites m P c).2.val = (((lpReplicaCopyIndicesAtEdge G sites m (Finset.univ \ P) c.1).orderIsoOfFin (card_lpReplicaCopyIndicesAtEdge G sites m (Finset.univ \ P) c.1)).symm ⟨c.2, by simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and] using hc⟩).val := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopyEquivRaw_index_of_not_mem G sites m P c hc

/--
[lpReplicaPartialReflectCopiesRaw_selected_profileFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_selected_profileFlux_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  profileFlux (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaPartialReflectCopiesRaw G sites m P P) = fun e => profileFlux (lpReplicaCurrentGraph G sites) m P (lpReplicaCurrentEdgeReflect G sites e) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_selected_profileFlux G sites m P

/--
[lpReplicaPartialReflectCopiesRaw_selected_profile_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_selected_profile_inverse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) let P' := lpReplicaPartialReflectCopiesRaw G sites m P P lpReplicaPartialReflectProfile G sites target (profileFlux (lpReplicaCurrentGraph G sites) target P') = m := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_selected_profile_inverse G sites m P

/--
[lpReplicaPartialReflectCopyEquivRaw_ends_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopyEquivRaw_ends_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hc : c ∈ P) :
-- imply
  endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaPartialReflectCopyEquivRaw G sites m P c) = Sym2.map lpReplicaCurrentReflect (endsM (lpReplicaCurrentGraph G sites) m c) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopyEquivRaw_ends_of_mem G sites m P c hc

/--
[lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hc : c ∉ P) :
-- imply
  endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaPartialReflectCopyEquivRaw G sites m P c) = endsM (lpReplicaCurrentGraph G sites) m c := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem G sites m P c hc

/--
[lpReplicaPartialReflectCopiesRaw_selected_degK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_selected_degK_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {x : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.degK (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P P) (lpReplicaCurrentReflect x) = RandomCurrent.degK (endsM (lpReplicaCurrentGraph G sites) m) P x := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_selected_degK G sites m P x

/--
[lpReplicaPartialReflectCopiesRaw_selected_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_selected_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P P) = (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) P).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_selected_sources G sites m P

/--
[lpReplicaPartialReflectCopiesRaw_compl_degK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_compl_degK_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {x : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.degK (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P)) x = RandomCurrent.degK (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ \ P) x := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_compl_degK G sites m P x

/--
[lpReplicaPartialReflectCopiesRaw_compl_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_compl_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P)) = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ \ P) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_compl_sources G sites m P

/--
[lpReplicaPartialReflectCopiesRaw_compl_union_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_compl_union_selected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P) ∪ lpReplicaPartialReflectCopiesRaw G sites m P P = Finset.univ := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_compl_union_selected G sites m P

/--
[lpReplicaPartialReflectCopiesRaw_compl_disjoint_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_compl_disjoint_selected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Disjoint (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P)) (lpReplicaPartialReflectCopiesRaw G sites m P P) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_compl_disjoint_selected G sites m P

/--
[lpReplicaPartialReflectCopiesRaw_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_univ_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) Finset.univ = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ \ P) ∆ (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) P).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_univ_sources G sites m P

/--
[lpReplicaPartialReflect_rootComponent_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflect_rootComponent_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A : Finset (LPReplicaCurrentVertex V)}
  {root : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) = A) :
-- imply
  let P := edgeComponent (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ root let C := RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ root RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) Finset.univ = lpReplicaPartialReflectSource A C := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflect_rootComponent_sources G sites m A root hsrc

/--
[lpReplicaPartialReflectCopiesRaw_sdiff_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_sdiff_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P (K \ P)) = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (K \ P) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_sdiff_sources G sites m P K

/--
[lpReplicaPartialReflectCopiesRaw_sdiff_union_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_sdiff_union_selected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hPK : P ⊆ K) :
-- imply
  lpReplicaPartialReflectCopiesRaw G sites m P (K \ P) ∪ lpReplicaPartialReflectCopiesRaw G sites m P P = lpReplicaPartialReflectCopiesRaw G sites m P K := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_sdiff_union_selected G sites m P K hPK

/--
[lpReplicaPartialReflectCopiesRaw_sdiff_disjoint_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_sdiff_disjoint_selected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Disjoint (lpReplicaPartialReflectCopiesRaw G sites m P (K \ P)) (lpReplicaPartialReflectCopiesRaw G sites m P P) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_sdiff_disjoint_selected G sites m P K

/--
[lpReplicaPartialReflect_rowComponent_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflect_rowComponent_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {A : Finset (LPReplicaCurrentVertex V)}
  {root : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) K = A) :
-- imply
  let P := edgeComponent (endsM (lpReplicaCurrentGraph G sites) m) K root let C := RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m) K root RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P K) = lpReplicaPartialReflectSource A C := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflect_rowComponent_sources G sites m K A root hsrc

/--
[lpReplicaPartialReflect_rowComponent_ghost_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflect_rowComponent_ghost_disconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hdisc : Not (RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) K lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
-- imply
  let P := edgeComponent (endsM (lpReplicaCurrentGraph G sites) m) K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) Not (RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P K) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflect_rowComponent_ghost_disconn G sites m K hdisc

/--
[lpReplicaOffdiagRowComponent_partialReflectAllocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaOffdiagRowComponent_partialReflectAllocation_eq
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
  (hsrc : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hdisc : Not (RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) K lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
-- imply
  let C := RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m) K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 let P := lpReplicaPartialReflectSource (Si ∆ Sj ∆ T) C (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨ (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRowComponent_partialReflectAllocation G sites hsite hij m K hsrc hdisc

/--
[lpReplicaOffdiagRowComponent_partialReflectTargetAllocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaOffdiagRowComponent_partialReflectTargetAllocation_eq
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
  (hsrc : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hdisc : Not (RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) K lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
-- imply
  let P := edgeComponent (endsM (lpReplicaCurrentGraph G sites) m) K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let Q := RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P K) let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 (Q = Si ∧ (Si ∆ Sj ∆ T) ∆ Q = Sj ∆ T) ∨ (Q = Sj ∧ (Si ∆ Sj ∆ T) ∆ Q = Si ∆ T) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRowComponent_partialReflectTargetAllocation G sites hsite hij m K hsrc hdisc

/--
[lpReplicaPartialReflectCopiesRaw_inter_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_inter_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P T : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P)) = (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (T ∩ P)).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_inter_sources G sites m P T

/--
[lpReplicaPartialReflectCopiesRaw_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P T : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P T) = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (T \ P) ∆ (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (T ∩ P)).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_sources G sites m P T

/--
[lpReplicaPartialReflect_rowComponent_subconfig_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaPartialReflect_rowComponent_subconfig_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K T : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {root : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hTK : T ⊆ K) :
-- imply
  let P := edgeComponent (endsM (lpReplicaCurrentGraph G sites) m) K root let C := RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m) K root RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P T) = lpReplicaPartialReflectSource (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) T) C := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflect_rowComponent_subconfig_sources G sites m K T hTK root

/--
[lpReplicaReflectCopies_edgeComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaReflectCopies_edgeComponent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {root : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaReflectCopies G sites m (edgeComponent (endsM (lpReplicaCurrentGraph G sites) m) K root) = edgeComponent (endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaReflectCopies G sites m K) (lpReplicaCurrentReflect root) := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopies_edgeComponent G sites m K root

/--
[lpReplicaReflectCopies_edgeComponent_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean)
-/
@[path]
private lemma lpReplicaReflectCopies_edgeComponent_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {root : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (edgeComponent (endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaReflectCopies G sites m K) (lpReplicaCurrentReflect root)) = (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (edgeComponent (endsM (lpReplicaCurrentGraph G sites) m) K root)).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopies_edgeComponent_sources G sites m K root


-- created on 2026-10-23
