import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part10
open Finset StatMech StatMech.Ising


/--
[lpReplicaCurrentEdgeReflect_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCurrentEdgeReflect_val_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentEdgeReflect G sites e).1 = Sym2.map lpReplicaCurrentReflect e.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdgeReflect_val G sites e

/--
[lpReplicaCurrentEdgeReflect_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCurrentEdgeReflect_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  Function.Involutive (lpReplicaCurrentEdgeReflect G sites) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdgeReflect_involutive G sites

/--
[lpReplicaReflectCopyEquiv_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaReflectCopyEquiv_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (lpReplicaReflectCopyEquiv G sites m c) = Sym2.map lpReplicaCurrentReflect (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m c) := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopyEquiv_ends G sites m c

/--
[mem_lpReplicaReflectCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma mem_lpReplicaReflectCopies_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) :
-- imply
  c ∈ lpReplicaReflectCopies G sites m S ↔ (lpReplicaReflectCopyEquiv G sites m).symm c ∈ S := by
-- proof
  apply StatMech.Ising.mem_lpReplicaReflectCopies G sites m S c

/--
[lpReplicaReflectCopyEquiv_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaReflectCopyEquiv_incident_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
  {x : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentReflect x ∈ StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (lpReplicaReflectCopyEquiv G sites m c) ↔ x ∈ StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m c := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopyEquiv_incident G sites m c x

/--
[lpReplicaReflectCopies_degK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaReflectCopies_degK_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {x : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.RandomCurrent.degK (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaReflectCopies G sites m S) (lpReplicaCurrentReflect x) = StatMech.Sharpness.RandomCurrent.degK (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) S x := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopies_degK G sites m S x

/--
[lpReplicaReflectCopies_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaReflectCopies_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaReflectCopies G sites m S) = (StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) S).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopies_sources G sites m S

/--
[lpReplicaReflectCopies_adjStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaReflectCopies_adjStep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {a b : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.RandomCurrent.adjStep (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaReflectCopies G sites m S) (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔ StatMech.Sharpness.RandomCurrent.adjStep (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) S a b := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopies_adjStep G sites m S a b

/--
[lpReplicaReflectCopies_connK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaReflectCopies_connK_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {a b : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.RandomCurrent.connK (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaReflectCopies G sites m S) (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔ StatMech.Sharpness.RandomCurrent.connK (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) S a b := by
-- proof
  apply StatMech.Ising.lpReplicaReflectCopies_connK G sites m S a b

/--
[lpReplicaCollision_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollision_projection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (ha : a <= m) :
-- imply
  (fun e => a e + lpReplicaReflectedResidual G sites m a (lpReplicaCurrentEdgeReflect G sites e)) = m := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_projection G sites m a ha

/--
[lpReplicaCollisionCopyEquiv_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollisionCopyEquiv_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : LPReplicaCollisionCopy G sites a b}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaCollisionCopyEquiv G sites a b c).1 = c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionCopyEquiv_edge G sites a b c

/--
[lpReplicaCollisionCopyEquiv_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollisionCopyEquiv_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : LPReplicaCollisionCopy G sites a b}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionCopyEquiv G sites a b c) = c.1.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionCopyEquiv_ends G sites a b c

/--
[lpReplicaCollisionLeftCopyEmbedding_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollisionLeftCopyEmbedding_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) a}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionLeftCopyEmbedding G sites a b c) = StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) a c := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionLeftCopyEmbedding_ends G sites a b c

/--
[lpReplicaCollisionRightCopyEmbedding_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollisionRightCopyEmbedding_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) b}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRightCopyEmbedding G sites a b c) = Sym2.map lpReplicaCurrentReflect (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) b c) := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionRightCopyEmbedding_ends G sites a b c

/--
[randomCurrent_sources_map_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma randomCurrent_sources_map_embedding_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {f : K ↪ L}
  {S : Finset K}
-- given
  (endsK : K -> Sym2 W)
  (endsL : L -> Sym2 W)
  (hends : ∀ c, endsL (f c) = endsK c) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources endsL (S.map f) = StatMech.Sharpness.RandomCurrent.sources endsK S := by
-- proof
  apply StatMech.Ising.randomCurrent_sources_map_embedding endsK endsL f hends S

/--
[randomCurrent_connK_map_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma randomCurrent_connK_map_embedding_eq
  [Fintype V]
  [DecidableEq V]
  {f : K ↪ L}
  {S : Finset K}
  {u v : W}
-- given
  (endsK : K -> Sym2 W)
  (endsL : L -> Sym2 W)
  (hends : ∀ c, endsL (f c) = endsK c) :
-- imply
  StatMech.Sharpness.RandomCurrent.connK endsL (S.map f) u v ↔ StatMech.Sharpness.RandomCurrent.connK endsK S u v := by
-- proof
  apply StatMech.Ising.randomCurrent_connK_map_embedding endsK endsL f hends S u v

/--
[lpReplicaPairEquivCollisionSigma_apply_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaPairEquivCollisionSigma_apply_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaPairEquivCollisionSigma G sites (a, b)).1 = lpReplicaCollisionProfile G sites a b := by
-- proof
  apply StatMech.Ising.lpReplicaPairEquivCollisionSigma_apply_fst G sites a b

/--
[lpReplicaPairEquivCollisionSigma_apply_subprofile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaPairEquivCollisionSigma_apply_subprofile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaPairEquivCollisionSigma G sites (a, b)).2.1 = a := by
-- proof
  apply StatMech.Ising.lpReplicaPairEquivCollisionSigma_apply_subprofile G sites a b

/--
[lpReplicaWeight_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaWeight_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) = weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
-- proof
  apply StatMech.Ising.lpReplicaWeight_reflect G sites beta J hf r m

/--
[lpReplicaReflectedResidual_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaReflectedResidual_weight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a)) = weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) (fun e => m e - a e)) := by
-- proof
  apply StatMech.Ising.lpReplicaReflectedResidual_weight G sites beta J hf r m a

/--
[lpReplicaCollisionPredicateFiberMass_eq_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollisionPredicateFiberMass_eq_edgecopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  [DecidablePred (fun a => Q a (lpReplicaReflectedResidual G sites m a))]
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (Q : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Prop) :
-- imply
  lpReplicaCollisionPredicateFiberMass G sites beta J hf r m Q = ∑ S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m), if Q (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m S) (lpReplicaReflectedResidual G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m S)) then weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) else 0 := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionPredicateFiberMass_eq_edgecopy G sites beta J hf r m Q

/--
[lpReplicaCollision_tsum_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollision_tsum_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (f g : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real)
  (hf : Summable (fun a => ‖f a‖))
  (hg : Summable (fun b => ‖g b‖)) :
-- imply
  (∑' a, f a) * (∑' b, g b) = ∑' m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat, ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m}, f K.1 * g (lpReplicaReflectedResidual G sites m K.1) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_tsum_mul G sites f g hf hg

/--
[lpReplicaCollisionObservableFiberMass_eq_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollisionObservableFiberMass_eq_edgecopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (Theta : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real) :
-- imply
  lpReplicaCollisionObservableFiberMass G sites beta J hf r m Theta = ∑ S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m), Theta (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m S) (lpReplicaReflectedResidual G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m S)) * weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionObservableFiberMass_eq_edgecopy G sites beta J hf r m Theta

/--
[lpReplicaCollisionFiberMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean)
-/
@[path]
private lemma lpReplicaCollisionFiberMass_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCollisionFiberMass G sites beta J hf r m = (2 : Real) ^ (∑ e, m e) * weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionFiberMass_eq G sites beta J hf r m


-- created on 2026-10-23
