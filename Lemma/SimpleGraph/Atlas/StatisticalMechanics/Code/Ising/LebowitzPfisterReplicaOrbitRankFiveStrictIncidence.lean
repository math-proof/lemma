import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictIncidence
open StatMech StatMech.Ising


/--
[randomCurrent_sources_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma randomCurrent_sources_empty_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype E]
  [DecidableEq E]
-- given
  (ends : E -> Sym2 W) :
-- imply
  RandomCurrent.sources ends ∅ = ∅ := by
-- proof
  apply StatMech.Ising.randomCurrent_sources_empty ends

/--
[randomCurrent_connK_insert_edge_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma randomCurrent_connK_insert_edge_cases_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype E]
  [DecidableEq E]
  {K : Finset E}
  {d : E}
  {a b : W}
-- given
  (ends : E -> Sym2 W)
  (hconn : connK ends (insert d K) a b) :
-- imply
  connK ends K a b ∨ ∃ x ∈ ends d, ∃ y ∈ ends d, connK ends K a x ∧ connK ends K y b := by
-- proof
  apply StatMech.Ising.randomCurrent_connK_insert_edge_cases ends K d hconn

/--
[randomCurrent_connK_eq_or_common_edge_of_unique_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma randomCurrent_connK_eq_or_common_edge_of_unique_incidence_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype E]
  [DecidableEq E]
  {K : Finset E}
  {B : Finset W}
  {a b : W}
-- given
  (ends : E -> Sym2 W)
  (hsupport : K.biUnion (fun e => (ends e).toFinset) = B)
  (hunique : ∀ x ∈ B, ∃! e, e ∈ K ∧ x ∈ (ends e).toFinset)
  (ha : a ∈ B)
  (hconn : connK ends K a b) :
-- imply
  a = b ∨ ∃ e ∈ K, a ∈ ends e ∧ b ∈ ends e := by
-- proof
  apply StatMech.Ising.randomCurrent_connK_eq_or_common_edge_of_unique_incidence ends K B hsupport hunique ha hconn

/--
[lpReplica_threeSeam_toggle_two_eq_selected_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma lpReplica_threeSeam_toggle_two_eq_selected_third_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq W]
  {T : Finset W}
  {i j k u v : I}
-- given
  (S : I -> Finset W)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (hu : u = i ∨ u = j ∨ u = k)
  (hv : v = i ∨ v = j ∨ v = k)
  (huv : u ≠ v) :
-- imply
  let l := lpReplicaThirdOfThree i j k u v S i ∆ S j ∆ T ∆ (S u ∆ S v) = S k ∆ S l ∆ T := by
-- proof
  apply StatMech.Ising.lpReplica_threeSeam_toggle_two_eq_selected_third S T hij hik hjk hu hv huv

/--
[sym2_toFinset_map_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma sym2_toFinset_map_embedding_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq W]
  [DecidableEq X]
  {f : W → X}
  {e : Sym2 W}
-- given
  (hf : Function.Injective f) :
-- imply
  (Sym2.map f e).toFinset = e.toFinset.map ⟨f, hf⟩ := by
-- proof
  apply StatMech.Ising.sym2_toFinset_map_embedding f hf e

/--
[lpReplicaCurrentEdge_sameSide_of_fold_eq_distinct_sites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_sameSide_of_fold_eq_distinct_sites_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
  {u v : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (huv : u ≠ v)
  (hfold : lpReplicaCurrentFoldedEdge G sites e = s(Sum.inl (sites u), Sum.inl (sites v))) :
-- imply
  (∃ x y : V, e.1 = s((.inl (.inl x) : LPReplicaCurrentVertex V), .inl (.inl y))) ∨ (∃ x y : V, e.1 = s((.inl (.inr x) : LPReplicaCurrentVertex V), .inl (.inr y))) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_sameSide_of_fold_eq_distinct_sites G sites hsite e huv hfold

/--
[lpReplica_strictPhysicalRoute_reflected_endpoint_mem_tripleSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma lpReplica_strictPhysicalRoute_reflected_endpoint_mem_tripleSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j k u v : I}
  {d : Copy (lpReplicaCurrentGraph G sites) m}
  {x : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (hu : u = i ∨ u = j ∨ u = k)
  (hv : v = i ∨ v = j ∨ v = k)
  (huv : u ≠ v)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hfold : lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v)))
  (hx : x ∈ endsM (lpReplicaCurrentGraph G sites) m d) :
-- imply
  lpReplicaCurrentReflect x ∈ lpReplicaTripleSeamGhostSource sites i j k := by
-- proof
  apply StatMech.Ising.lpReplica_strictPhysicalRoute_reflected_endpoint_mem_tripleSource G sites hsite hij hik hjk hu hv huv m d hfold x hx

/--
[lpReplica_strictPhysicalRoute_disjoint_reflected_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma lpReplica_strictPhysicalRoute_disjoint_reflected_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : I}
  {d : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (huv : u ≠ v)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hfold : lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v))) :
-- imply
  Disjoint (endsM (lpReplicaCurrentGraph G sites) m d).toFinset (Sym2.map lpReplicaCurrentReflect (endsM (lpReplicaCurrentGraph G sites) m d)).toFinset := by
-- proof
  apply StatMech.Ising.lpReplica_strictPhysicalRoute_disjoint_reflected_ends G sites hsite huv m d hfold

/--
[lpReplica_partialReflect_strictMatchingRoute_doubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma lpReplica_partialReflect_strictMatchingRoute_doubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {B : Finset (LPReplicaCurrentVertex V)}
  {d : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hdK : d ∈ K)
  (hunique : ∀ x ∈ B, ∃! e, e ∈ K ∧ x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset)
  (hreflectedSupport : ∀ x ∈ endsM (lpReplicaCurrentGraph G sites) m d, lpReplicaCurrentReflect x ∈ B)
  (hdisjoint : Disjoint (endsM (lpReplicaCurrentGraph G sites) m d).toFinset (Sym2.map lpReplicaCurrentReflect (endsM (lpReplicaCurrentGraph G sites) m d)).toFinset) :
-- imply
  let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ {d})) (profileFlux (lpReplicaCurrentGraph G sites) m {d}) let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d} let d' := R d let K' := lpReplicaPartialReflectCopiesRaw G sites m {d} K d' ∈ K' ∧ (∀ x ∈ endsM (lpReplicaCurrentGraph G sites) target d', ∃ e' ∈ K', e' ≠ d' ∧ x ∈ endsM (lpReplicaCurrentGraph G sites) target e') := by
-- proof
  apply StatMech.Ising.lpReplica_partialReflect_strictMatchingRoute_doubleIncidence G sites m K B d hdK hunique hreflectedSupport hdisjoint

/--
[lpReplica_partialReflect_strictMatchingRoute_hasDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma lpReplica_partialReflect_strictMatchingRoute_hasDoubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : I}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {B : Finset (LPReplicaCurrentVertex V)}
  {d : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (huv : u ≠ v)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hdK : d ∈ K)
  (hunique : ∀ x ∈ B, ∃! e, e ∈ K ∧ x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset)
  (hreflectedSupport : ∀ x ∈ endsM (lpReplicaCurrentGraph G sites) m d, lpReplicaCurrentReflect x ∈ B)
  (hfold : lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v)))
  (hdisjoint : Disjoint (endsM (lpReplicaCurrentGraph G sites) m d).toFinset (Sym2.map lpReplicaCurrentReflect (endsM (lpReplicaCurrentGraph G sites) m d)).toFinset) :
-- imply
  let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ {d})) (profileFlux (lpReplicaCurrentGraph G sites) m {d}) LPReplicaStrictPhysicalDoubleIncidenceRaw G sites target (lpReplicaPartialReflectCopiesRaw G sites m {d} K) := by
-- proof
  apply StatMech.Ising.lpReplica_partialReflect_strictMatchingRoute_hasDoubleIncidence G sites hsite huv m K B d hdK hunique hreflectedSupport hfold hdisjoint

/--
[LPReplicaDecoratedOrbitAtom.hasStrictPhysicalDoubleIncidence_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean)
-/
@[path]
private lemma hasStrictPhysicalDoubleIncidence_cast_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A : Finset (LPReplicaCurrentVertex V)}
  {B C : Finset (LPReplicaCurrentVertex V)}
  {z : LPReplicaDecoratedOrbitAtom G sites A B q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : B = C) :
-- imply
  LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence G sites A C q (cast (congrArg (fun D => LPReplicaDecoratedOrbitAtom G sites A D q) h) z) ↔ LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence G sites A B q z := by
-- proof
  apply StatMech.Ising.LPReplicaDecoratedOrbitAtom.hasStrictPhysicalDoubleIncidence_cast G sites A q h z


-- created on 2026-10-23
