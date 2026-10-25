import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part13
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.Sharpness


/--
[inhom_real_eq_probV_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma inhom_real_eq_probV_of_mem_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
-- given
  (r : E -> Real)
  (hr0 : forall e, 0 <= r e)
  (hr1 : forall e, r e <= 1) :
-- imply
  (inhomBernoulliProductMeasure (fun e => (r e).toNNReal) (fun e => Real.toNNReal_le_one.mpr (hr1 e))).real A = probV r A := by
-- proof
  apply StatMech.Sharpness.inhom_real_eq_probV_of_mem r hr0 hr1 A

/--
[inhom_map_cfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma inhom_map_cfgEquiv_eq
  {sigma : E ≃ E}
-- given
  (p : E -> NNReal)
  (hp : forall e, p e <= 1)
  (hinv : forall e, p (sigma e) = p e) :
-- imply
  Measure.map (cfgEquiv sigma) (inhomBernoulliProductMeasure p hp) = inhomBernoulliProductMeasure p hp := by
-- proof
  apply StatMech.Sharpness.inhom_map_cfgEquiv p hp sigma hinv

/--
[measurable_cfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma measurable_cfgEquiv_eq
  {sigma : E ≃ F} :
-- imply
  Measurable (cfgEquiv sigma : ConfigSpace F -> ConfigSpace E) := by
-- proof
  apply StatMech.Sharpness.measurable_cfgEquiv sigma

/--
[abigRealParam_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigRealParam_some_some_eq
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  abigRealParam J beta h s(some x, some y) = pBeta (J s(x, y)) beta := by
-- proof
  apply StatMech.Sharpness.abigRealParam_some_some J beta h x y

/--
[abigRealParam_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigRealParam_some_none_eq
  {x : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  abigRealParam J beta h s(some x, none) = qField h := by
-- proof
  apply StatMech.Sharpness.abigRealParam_some_none J beta h x

/--
[abigRealParam_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigRealParam_mem_eq
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hJ : forall e, 0 <= J e) :
-- imply
  forall e, 0 <= abigRealParam J beta h e ∧ abigRealParam J beta h e <= 1 := by
-- proof
  apply StatMech.Sharpness.abigRealParam_mem J beta h hbeta hh hJ

/--
[qField_toNNReal_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma qField_toNNReal_le_one_eq
-- given
  (h : Real) :
-- imply
  (qField h).toNNReal <= 1 := by
-- proof
  apply StatMech.Sharpness.qField_toNNReal_le_one h

/--
[abigParam_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigParam_le_one_eq
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  forall e, abigParam J beta h e <= 1 := by
-- proof
  apply StatMech.Sharpness.abigParam_le_one J beta h

/--
[abigParam_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigParam_some_some_eq
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  abigParam J beta h s(some x, some y) = (pBeta (J s(x, y)) beta).toNNReal := by
-- proof
  apply StatMech.Sharpness.abigParam_some_some J beta h x y

/--
[abigParam_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigParam_some_none_eq
  {x : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  abigParam J beta h s(some x, none) = (qField h).toNNReal := by
-- proof
  apply StatMech.Sharpness.abigParam_some_none J beta h x

/--
[abigParam_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigParam_invariant_eq
  {sigma : V ≃ V}
  {e : Sym2 (Option V)}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y)) :
-- imply
  abigParam J beta h (abfsEdgeEquiv sigma e) = abigParam J beta h e := by
-- proof
  apply StatMech.Sharpness.abigParam_invariant J beta h sigma hJ e

/--
[abig_map_cfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_map_cfgEquiv_eq
  {sigma : V ≃ V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y)) :
-- imply
  Measure.map (cfgEquiv (abfsEdgeEquiv sigma)) (abigMeasure J beta h) = abigMeasure J beta h := by
-- proof
  apply StatMech.Sharpness.abig_map_cfgEquiv J beta h sigma hJ

/--
[abigMag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_nonneg_eq
  {G : SimpleGraph V}
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  0 <= abigMag G J o beta h := by
-- proof
  apply StatMech.Sharpness.abigMag_nonneg G J o beta h

/--
[abigParam_eq_zero_beta_of_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigParam_eq_zero_beta_of_nonpos_eq
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : beta <= 0)
  (hJ : forall e, 0 <= J e) :
-- imply
  abigParam J beta h = abigParam J 0 h := by
-- proof
  apply StatMech.Sharpness.abigParam_eq_zero_beta_of_nonpos J beta h hbeta hJ

/--
[abigMag_eq_zero_beta_of_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_eq_zero_beta_of_nonpos_eq
  {G : SimpleGraph V}
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : beta <= 0)
  (hJ : forall e, 0 <= J e) :
-- imply
  abigMag G J o beta h = abigMag G J o 0 h := by
-- proof
  apply StatMech.Sharpness.abigMag_eq_zero_beta_of_nonpos G J o beta h hbeta hJ

/--
[abigMag_eq_max_beta_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_eq_max_beta_zero_eq
  {G : SimpleGraph V}
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hJ : forall e, 0 <= J e) :
-- imply
  abigMag G J o beta h = abigMag G J o (max beta 0) h := by
-- proof
  apply StatMech.Sharpness.abigMag_eq_max_beta_zero G J o beta h hJ

/--
[mem_abigInternalEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma mem_abigInternalEdges_eq
  [DecidableEq W]
  {T : Finset W}
  {e : Sym2 W} :
-- imply
  e ∈ abigInternalEdges T ↔ ∃ x ∈ T, ∃ y ∈ T, e = s(x, y) := by
-- proof
  apply StatMech.Sharpness.mem_abigInternalEdges

/--
[abigInternalEdgeEquiv_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigInternalEdgeEquiv_mk_eq
  [DecidableEq W]
  {T : Finset W}
  {x y : T} :
-- imply
  (abigInternalEdgeEquiv T s(x, y) : Sym2 W) = s((x : W), (y : W)) := by
-- proof
  apply StatMech.Sharpness.abigInternalEdgeEquiv_mk T x y

/--
[abigGhostWindowEquiv_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigGhostWindowEquiv_none_eq
  [DecidableEq V]
  {S : Finset V} :
-- imply
  (abigGhostWindowEquiv S none : Option V) = none := by
-- proof
  apply StatMech.Sharpness.abigGhostWindowEquiv_none S

/--
[abigGhostWindowEquiv_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigGhostWindowEquiv_some_eq
  [DecidableEq V]
  {S : Finset V}
  {x : S} :
-- imply
  (abigGhostWindowEquiv S (some x) : Option V) = some (x : V) := by
-- proof
  apply StatMech.Sharpness.abigGhostWindowEquiv_some S x

/--
[abigWindowEdgeEquiv_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindowEdgeEquiv_mk_eq
  [DecidableEq V]
  {S : Finset V}
  {a b : Option S} :
-- imply
  (abigWindowEdgeEquiv S s(a, b) : Sym2 (Option V)) = s((abigGhostWindowEquiv S a : Option V), (abigGhostWindowEquiv S b : Option V)) := by
-- proof
  apply StatMech.Sharpness.abigWindowEdgeEquiv_mk S a b

/--
[abigWindowCoupling_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindowCoupling_mk_eq
  {S : Finset V}
  {x y : S}
-- given
  (J : Sym2 V -> Real) :
-- imply
  abigWindowCoupling J S s(x, y) = J s((x : V), (y : V)) := by
-- proof
  apply StatMech.Sharpness.abigWindowCoupling_mk J S x y

/--
[abigWindow_incidentCoupling_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindow_incidentCoupling_eq_sum_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {x : S}
-- given
  (J : Sym2 V -> Real) :
-- imply
  abcrIncidentCoupling (abigWindowGraph G S) (abigWindowCoupling J S) x = ∑ y : S, if G.Adj (x : V) (y : V) then J s((x : V), (y : V)) else 0 := by
-- proof
  apply StatMech.Sharpness.abigWindow_incidentCoupling_eq_sum G J S x

/--
[abigWindow_incidentCoupling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindow_incidentCoupling_le_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J0 : Real}
  {S : Finset V}
  {x : S}
-- given
  (J : Sym2 V -> Real)
  (hrow : abigUniformFiniteRowBound G J J0) :
-- imply
  abcrIncidentCoupling (abigWindowGraph G S) (abigWindowCoupling J S) x <= J0 := by
-- proof
  apply StatMech.Sharpness.abigWindow_incidentCoupling_le G J J0 hrow S x

/--
[abigUniformFiniteRowBound_of_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigUniformFiniteRowBound_of_tsum_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J0 : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ : forall e, 0 <= J e)
  (hsum : forall x, Summable (fun y => if G.Adj x y then J s(x, y) else 0))
  (hrow : forall x, (∑' y, if G.Adj x y then J s(x, y) else 0) <= J0) :
-- imply
  abigUniformFiniteRowBound G J J0 := by
-- proof
  apply StatMech.Sharpness.abigUniformFiniteRowBound_of_tsum G J J0 hJ hsum hrow

/--
[abigWindow_abfaParams_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindow_abfaParams_eq_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0) :
-- imply
  forall e : Sym2 (Option S), abfaParams (abigWindowGraph G S) (abigWindowCoupling J S) beta h e = abigRealParam J beta h (abigWindowEdgeEquiv S e) := by
-- proof
  apply StatMech.Sharpness.abigWindow_abfaParams_eq G J S beta h hJsupport

/--
[abigWindow_openSub_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindow_openSub_adj_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {eta : ConfigSpace (abigInternalEdges (abigGhostWindow S))}
  {a b : Option S} :
-- imply
  (openSub (withGhost (abigWindowGraph G S)) (cfgEquiv (abigWindowEdgeEquiv S) eta)).Adj a b ↔ (openSub (withGhost G) (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)).Adj (abigGhostWindowEquiv S a : Option V) (abigGhostWindowEquiv S b : Option V) := by
-- proof
  apply StatMech.Sharpness.abigWindow_openSub_adj G S eta a b

/--
[abigWindow_connWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindow_connWithin_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {eta : ConfigSpace (abigInternalEdges (abigGhostWindow S))}
  {a b : Option S} :
-- imply
  ConnWithin (withGhost (abigWindowGraph G S)) (cfgEquiv (abigWindowEdgeEquiv S) eta) Set.univ ⟨a, Set.mem_univ _⟩ ⟨b, Set.mem_univ _⟩ ↔ ConnWithin (withGhost G) (ih_fill (abigInternalEdges (abigGhostWindow S)) eta) (abigGhostWindow S : Set (Option V)) ⟨abigGhostWindowEquiv S a, (abigGhostWindowEquiv S a).property⟩ ⟨abigGhostWindowEquiv S b, (abigGhostWindowEquiv S b).property⟩ := by
-- proof
  apply StatMech.Sharpness.abigWindow_connWithin G S eta a b

/--
[abigWindow_preimage_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindow_preimage_connEvent_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o : S} :
-- imply
  (cfgEquiv (abigWindowEdgeEquiv S)) ⁻¹' connEvent (withGhost (abigWindowGraph G S)) Set.univ (some o) {none} = ih_section (connEvent (withGhost G) (abigGhostWindow S : Set (Option V)) (some (o : V)) {none}) (abigInternalEdges (abigGhostWindow S)) := by
-- proof
  apply StatMech.Sharpness.abigWindow_preimage_connEvent G S o

/--
[abig_connEvent_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_connEvent_congr_eq
  [DecidableEq W]
  {G : SimpleGraph W}
  {T : Finset W}
  {u v : W}
  {omega omega' : ConfigSpace (Sym2 W)}
-- given
  (hagree : ∀ e ∈ abigInternalEdges T, omega e = omega' e) :
-- imply
  omega ∈ connEvent G (T : Set W) u {v} ↔ omega' ∈ connEvent G (T : Set W) u {v} := by
-- proof
  apply StatMech.Sharpness.abig_connEvent_congr G T u v hagree

/--
[abig_connEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_connEvent_dependsOn_eq
  [DecidableEq W]
  {G : SimpleGraph W}
  {T : Finset W}
  {u v : W} :
-- imply
  StatMech.DependsOn (connEvent G (T : Set W) u {v}) (abigInternalEdges T : Set (Sym2 W)) := by
-- proof
  apply StatMech.Sharpness.abig_connEvent_dependsOn G T u v

/--
[abig_measurableSet_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_measurableSet_connEvent_eq
  [Countable W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {T : Finset W}
  {u v : W} :
-- imply
  MeasurableSet (connEvent G (T : Set W) u {v}) := by
-- proof
  apply StatMech.Sharpness.abig_measurableSet_connEvent G T u v

/--
[abig_connWithin_mono_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_connWithin_mono_set_eq
  {G : SimpleGraph W}
  {omega : ConfigSpace (Sym2 W)}
  {S T : Set W}
  {x y : S}
-- given
  (hST : S ⊆ T)
  (hconn : ConnWithin G omega S x y) :
-- imply
  ConnWithin G omega T ⟨x, hST x.property⟩ ⟨y, hST y.property⟩ := by
-- proof
  apply StatMech.Sharpness.abig_connWithin_mono_set G omega hST hconn

/--
[abig_connEvent_mono_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_connEvent_mono_set_eq
  {G : SimpleGraph W}
  {S T : Set W}
  {u v : W}
-- given
  (hST : S ⊆ T) :
-- imply
  connEvent G S u {v} ⊆ connEvent G T u {v} := by
-- proof
  apply StatMech.Sharpness.abig_connEvent_mono_set G hST u v

/--
[abig_iUnion_connEvent_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_iUnion_connEvent_exhaustion_eq
  [DecidableEq W]
  {G : SimpleGraph W}
  {u v : W}
-- given
  (T : Nat -> Finset W)
  (hcover : forall F : Finset W, exists n, F ⊆ T n) :
-- imply
  (⋃ n, connEvent G (T n : Set W) u {v}) = connEvent G Set.univ u {v} := by
-- proof
  apply StatMech.Sharpness.abig_iUnion_connEvent_exhaustion G T u v hcover

/--
[abig_measurableSet_connEvent_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_measurableSet_connEvent_univ_eq
  [Countable W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {u v : W}
-- given
  (T : Nat -> Finset W)
  (hcover : forall F : Finset W, exists n, F ⊆ T n) :
-- imply
  MeasurableSet (connEvent G Set.univ u {v}) := by
-- proof
  apply StatMech.Sharpness.abig_measurableSet_connEvent_univ G T u v hcover

/--
[abig_tendsto_real_connEvent_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_tendsto_real_connEvent_exhaustion_eq
  [Countable W]
  [DecidableEq W]
  {mu : Measure (ConfigSpace (Sym2 W))}
  [IsFiniteMeasure mu]
  {G : SimpleGraph W}
  {u v : W}
-- given
  (T : Nat -> Finset W)
  (hmono : Monotone T)
  (hcover : forall F : Finset W, exists n, F ⊆ T n) :
-- imply
  Tendsto (fun n => mu.real (connEvent G (T n : Set W) u {v})) atTop (nhds (mu.real (connEvent G Set.univ u {v}))) := by
-- proof
  apply StatMech.Sharpness.abig_tendsto_real_connEvent_exhaustion mu G T u v hmono hcover

/--
[abigMag_eq_of_automorphism](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_eq_of_automorphism_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {o : V}
  {sigma : V ≃ V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
  (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y))
  (T : Nat -> Finset (Option V))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
-- imply
  abigMag G J (sigma o) beta h = abigMag G J o beta h := by
-- proof
  apply StatMech.Sharpness.abigMag_eq_of_automorphism G J o beta h sigma hG hJ T hcover

/--
[abigMag_eq_of_transitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_eq_of_transitive_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (move : V -> (V ≃ V))
  (hmove : forall x, move x o = x)
  (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
  (hJ : forall x u v, J s(move x u, move x v) = J s(u, v))
  (T : Nat -> Finset (Option V))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
-- imply
  forall x, abigMag G J x beta h = abigMag G J o beta h := by
-- proof
  apply StatMech.Sharpness.abigMag_eq_of_transitive G J o beta h move hmove hG hJ T hcover

/--
[abig_coord_true_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_coord_true_prob_eq
  [Countable V]
  {e : Sym2 (Option V)}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  (abigMeasure J beta h).real {omega | omega e = true} = (abigParam J beta h e : Real) := by
-- proof
  apply StatMech.Sharpness.abig_coord_true_prob J beta h e

/--
[abig_realProb_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_realProb_cylinder_eq
  [Countable V]
  {F : Finset (Sym2 (Option V))}
  {A : Set (ConfigSpace F)}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  (abigMeasure J beta h).real (MeasureTheory.cylinder F A) = (inhomBernoulliProductMeasure (fun e : F => abigParam J beta h e) (fun e => abigParam_le_one J beta h e)).real A := by
-- proof
  apply StatMech.Sharpness.abig_realProb_cylinder J beta h F A

/--
[abig_finite_conn_prob_eq_marginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_finite_conn_prob_eq_marginal_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {o : V}
  {T : Finset (Option V)}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  (abigMeasure J beta h).real (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) = (inhomBernoulliProductMeasure (fun e : abigInternalEdges T => abigParam J beta h e) (fun e => abigParam_le_one J beta h e)).real (ih_section (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) (abigInternalEdges T)) := by
-- proof
  apply StatMech.Sharpness.abig_finite_conn_prob_eq_marginal G J o beta h T

/--
[abig_finite_conn_prob_eq_probV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_finite_conn_prob_eq_probV_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {o : V}
  {T : Finset (Option V)}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hJ : forall e, 0 <= J e) :
-- imply
  (abigMeasure J beta h).real (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) = probV (fun e : abigInternalEdges T => abigRealParam J beta h e) (ih_section (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) (abigInternalEdges T)) := by
-- proof
  apply StatMech.Sharpness.abig_finite_conn_prob_eq_probV G J o beta h hbeta hh hJ T

/--
[abig_abfaMag_eq_finiteConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_abfaMag_eq_finiteConn_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o : S}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0) :
-- imply
  abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta h = (abigMeasure J beta h).real (connEvent (withGhost G) (abigGhostWindow S : Set (Option V)) (some (o : V)) {none}) := by
-- proof
  apply StatMech.Sharpness.abig_abfaMag_eq_finiteConn G J S o beta h hbeta hh hJ hJsupport

/--
[abigWindowMag_le_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindowMag_le_envelope_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o x : S}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h <= abigWindowEnvelope G J S o beta h := by
-- proof
  apply StatMech.Sharpness.abigWindowMag_le_envelope G J S o x beta h

/--
[abigWindowEnvelope_monotoneOn_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindowEnvelope_monotoneOn_beta_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o : S}
-- given
  (J : Sym2 V -> Real)
  (h : Real)
  (hJ : forall e, 0 <= J e)
  (hh : 0 <= h) :
-- imply
  MonotoneOn (fun beta => abigWindowEnvelope G J S o beta h) (Ici 0) := by
-- proof
  apply StatMech.Sharpness.abigWindowEnvelope_monotoneOn_beta G J S o h hJ hh

/--
[abigWindowEnvelope_monotoneOn_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindowEnvelope_monotoneOn_field_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o : S}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ : forall e, 0 <= J e)
  (hbeta : 0 <= beta) :
-- imply
  MonotoneOn (fun h => abigWindowEnvelope G J S o beta h) (Ici 0) := by
-- proof
  apply StatMech.Sharpness.abigWindowEnvelope_monotoneOn_field G J S o beta hJ hbeta

/--
[abig_window_aizenmanBarsky_finiteEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_window_aizenmanBarsky_finiteEnvelope_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o : S}
-- given
  (J : Sym2 V -> Real)
  (beta h J0 : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hJ : forall e, 0 <= J e)
  (hrow : forall x : S, abcrIncidentCoupling (abigWindowGraph G S) (abigWindowCoupling J S) x <= J0) :
-- imply
  deriv (fun b => abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o b h) beta <= J0 * abigWindowEnvelope G J S o beta h * deriv (fun t => abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta t) h := by
-- proof
  apply StatMech.Sharpness.abig_window_aizenmanBarsky_finiteEnvelope G J S o beta h J0 hbeta hh hJ hrow

/--
[abigWindowEnvelope_le_mag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigWindowEnvelope_le_mag_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o : S}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (hInfiniteTarget : forall x : S, abigMag G J (x : V) beta h <= abigMag G J (o : V) beta h) :
-- imply
  abigWindowEnvelope G J S o beta h <= abigMag G J (o : V) beta h := by
-- proof
  apply StatMech.Sharpness.abigWindowEnvelope_le_mag G J S o beta h hbeta hh hJ hJsupport hInfiniteTarget

/--
[abig_window_aizenmanBarsky](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_window_aizenmanBarsky_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o : S}
-- given
  (J : Sym2 V -> Real)
  (beta h J0 : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (hrow : forall x : S, abcrIncidentCoupling (abigWindowGraph G S) (abigWindowCoupling J S) x <= J0)
  (hInfiniteTarget : forall x : S, abigMag G J (x : V) beta h <= abigMag G J (o : V) beta h) :
-- imply
  deriv (fun b => abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o b h) beta <= J0 * abigMag G J (o : V) beta h * deriv (fun t => abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta t) h := by
-- proof
  apply StatMech.Sharpness.abig_window_aizenmanBarsky G J S o beta h J0 hbeta hh hJ hJsupport hrow hInfiniteTarget

/--
[abig_tendsto_mag_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_tendsto_mag_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (T : Nat -> Finset (Option V))
  (hmono : Monotone T)
  (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
-- imply
  Tendsto (fun n => (abigMeasure J beta h).real (connEvent (withGhost G) (T n : Set (Option V)) (some o) {none})) atTop (nhds (abigMag G J o beta h)) := by
-- proof
  apply StatMech.Sharpness.abig_tendsto_mag_exhaustion G J o beta h T hmono hcover

/--
[abig_tendsto_abfaMag_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_tendsto_abfaMag_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hmono : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n)) :
-- imply
  Tendsto (fun n => abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n)) ⟨o, ho n⟩ beta h) atTop (nhds (abigMag G J o beta h)) := by
-- proof
  apply StatMech.Sharpness.abig_tendsto_abfaMag_exhaustion G J o beta h hbeta hh hJ hJsupport S ho hmono hcover

/--
[abigMag_monotoneOn_field_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_monotoneOn_field_of_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n)) :
-- imply
  MonotoneOn (fun h => abigMag G J o beta h) (Ici 0) := by
-- proof
  apply StatMech.Sharpness.abigMag_monotoneOn_field_of_exhaustion G J o beta hbeta hJ hJsupport S ho hmonoWindow hcover

/--
[abigMag_continuousAt_field_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_continuousAt_field_of_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 < h)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n)) :
-- imply
  ContinuousAt (fun t => abigMag G J o beta t) h := by
-- proof
  apply StatMech.Sharpness.abigMag_continuousAt_field_of_exhaustion G J o beta h hbeta hh hJ hJsupport S ho hmonoWindow hcover

/--
[abigMag_differentiableAt_field_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_differentiableAt_field_of_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 < h)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n)) :
-- imply
  DifferentiableAt Real (fun t => abigMag G J o beta t) h := by
-- proof
  apply StatMech.Sharpness.abigMag_differentiableAt_field_of_exhaustion G J o beta h hbeta hh hJ hJsupport S ho hmonoWindow hcover

/--
[abigMag_beta_lipschitz_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_beta_lipschitz_of_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (J0 beta gamma h : Real)
  (hJ0 : 0 <= J0)
  (hbeta : 0 <= beta)
  (hgamma : 0 <= gamma)
  (hh : 0 < h)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hrow : forall n (x : S n), abcrIncidentCoupling (abigWindowGraph G (S n)) (abigWindowCoupling J (S n)) x <= J0)
  (hInfiniteTarget : forall b t, 0 <= b -> 0 <= t -> forall n (x : S n), abigMag G J (x : V) b t <= abigMag G J o b t)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n)) :
-- imply
  |abigMag G J o gamma h - abigMag G J o beta h| <= (J0 / h) * |gamma - beta| := by
-- proof
  apply StatMech.Sharpness.abigMag_beta_lipschitz_of_exhaustion G J o J0 beta gamma h hJ0 hbeta hgamma hh hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover

/--
[abigMag_continuousAt_joint_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_continuousAt_joint_of_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (J0 beta h : Real)
  (hJ0 : 0 <= J0)
  (hbeta : 0 <= beta)
  (hh : 0 < h)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hrow : forall n (x : S n), abcrIncidentCoupling (abigWindowGraph G (S n)) (abigWindowCoupling J (S n)) x <= J0)
  (hInfiniteTarget : forall b t, 0 <= b -> 0 <= t -> forall n (x : S n), abigMag G J (x : V) b t <= abigMag G J o b t)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n)) :
-- imply
  ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h) := by
-- proof
  apply StatMech.Sharpness.abigMag_continuousAt_joint_of_exhaustion G J o J0 beta h hJ0 hbeta hh hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover

/--
[abigMag_deriv_field_nonneg_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abigMag_deriv_field_nonneg_of_monotone_eq
  [Countable V]
  {G : SimpleGraph V}
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hh : 0 < h)
  (hmono : MonotoneOn (fun t => abigMag G J o beta t) (Ici 0))
  (hdiff : DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
-- imply
  0 <= deriv (fun t => abigMag G J o beta t) h := by
-- proof
  apply StatMech.Sharpness.abigMag_deriv_field_nonneg_of_monotone G J o beta h hh hmono hdiff

/--
[abig_finiteMag_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_finiteMag_le_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {o : V}
  {T : Finset (Option V)}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  (abigMeasure J beta h).real (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) <= abigMag G J o beta h := by
-- proof
  apply StatMech.Sharpness.abig_finiteMag_le G J o beta h T

/--
[abig_finiteMag_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_finiteMag_mono_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {o : V}
  {S T : Finset (Option V)}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hST : S ⊆ T) :
-- imply
  (abigMeasure J beta h).real (connEvent (withGhost G) (S : Set (Option V)) (some o) {none}) <= (abigMeasure J beta h).real (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) := by
-- proof
  apply StatMech.Sharpness.abig_finiteMag_mono G J o beta h hST

/--
[abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J0 : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ0 : 0 <= J0)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hrow : forall n (x : S n), abcrIncidentCoupling (abigWindowGraph G (S n)) (abigWindowCoupling J (S n)) x <= J0)
  (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h -> forall n (x : S n), abigMag G J (x : V) beta h <= abigMag G J o beta h)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n))
  (hcontLimit : forall beta h, 0 <= beta -> 0 < h -> ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h))
  (hfieldDiffLimit : forall beta h, 0 <= beta -> 0 < h -> DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
-- proof
  apply StatMech.Sharpness.abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion G J o J0 hJ0 hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover hcontLimit hfieldDiffLimit

/--
[abig_aizenmanBarskyPhysical_unconditional_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_aizenmanBarskyPhysical_unconditional_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J0 : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ0 : 0 <= J0)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hrow : forall n (x : S n), abcrIncidentCoupling (abigWindowGraph G (S n)) (abigWindowCoupling J (S n)) x <= J0)
  (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h -> forall n (x : S n), abigMag G J (x : V) beta h <= abigMag G J o beta h)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n)) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
-- proof
  apply StatMech.Sharpness.abig_aizenmanBarskyPhysical_unconditional_exhaustion G J o J0 hJ0 hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover

/--
[abig_aizenmanBarskyPhysical_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_aizenmanBarskyPhysical_of_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J0 : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ0 : 0 <= J0)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hrow : forall n (x : S n), abcrIncidentCoupling (abigWindowGraph G (S n)) (abigWindowCoupling J (S n)) x <= J0)
  (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h -> forall n (x : S n), abigMag G J (x : V) beta h <= abigMag G J o beta h)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n))
  (hjointLimit : forall beta h, 0 <= beta -> 0 < h -> DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
-- proof
  apply StatMech.Sharpness.abig_aizenmanBarskyPhysical_of_exhaustion G J o J0 hJ0 hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover hjointLimit

/--
[abig_aizenmanBarskyPhysical_of_tsum_transitive_fieldRegular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_aizenmanBarskyPhysical_of_tsum_transitive_fieldRegular_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J0 : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ0 : 0 <= J0)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (hsum : forall x, Summable (fun y => if G.Adj x y then J s(x, y) else 0))
  (hrow : forall x, (∑' y, if G.Adj x y then J s(x, y) else 0) <= J0)
  (move : V -> (V ≃ V))
  (hmove : forall x, move x o = x)
  (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
  (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n))
  (hcontLimit : forall beta h, 0 <= beta -> 0 < h -> ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h))
  (hfieldDiffLimit : forall beta h, 0 <= beta -> 0 < h -> DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
-- proof
  apply StatMech.Sharpness.abig_aizenmanBarskyPhysical_of_tsum_transitive_fieldRegular G J o J0 hJ0 hJ hJsupport hsum hrow move hmove hG hJinv S ho hmonoWindow hcover hcontLimit hfieldDiffLimit

/--
[abig_aizenmanBarskyPhysical_of_tsum_transitive_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_aizenmanBarskyPhysical_of_tsum_transitive_unconditional_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J0 : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ0 : 0 <= J0)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (hsum : forall x, Summable (fun y => if G.Adj x y then J s(x, y) else 0))
  (hrow : forall x, (∑' y, if G.Adj x y then J s(x, y) else 0) <= J0)
  (move : V -> (V ≃ V))
  (hmove : forall x, move x o = x)
  (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
  (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n)) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
-- proof
  apply StatMech.Sharpness.abig_aizenmanBarskyPhysical_of_tsum_transitive_unconditional G J o J0 hJ0 hJ hJsupport hsum hrow move hmove hG hJinv S ho hmonoWindow hcover

/--
[abig_aizenmanBarskyPhysical_of_transitive_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_aizenmanBarskyPhysical_of_transitive_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J0 : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ0 : 0 <= J0)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (hrow : abigUniformFiniteRowBound G J J0)
  (move : V -> (V ≃ V))
  (hmove : forall x, move x o = x)
  (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
  (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n))
  (hjointLimit : forall beta h, 0 <= beta -> 0 < h -> DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
-- proof
  apply StatMech.Sharpness.abig_aizenmanBarskyPhysical_of_transitive_exhaustion G J o J0 hJ0 hJ hJsupport hrow move hmove hG hJinv S ho hmonoWindow hcover hjointLimit

/--
[abig_aizenmanBarskyPhysical_of_tsum_transitive_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_aizenmanBarskyPhysical_of_tsum_transitive_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J0 : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ0 : 0 <= J0)
  (hJ : forall e, 0 <= J e)
  (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
  (hsum : forall x, Summable (fun y => if G.Adj x y then J s(x, y) else 0))
  (hrow : forall x, (∑' y, if G.Adj x y then J s(x, y) else 0) <= J0)
  (move : V -> (V ≃ V))
  (hmove : forall x, move x o = x)
  (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
  (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
  (S : Nat -> Finset V)
  (ho : forall n, o ∈ S n)
  (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
  (hcover : forall F : Finset (Option V), exists n, F ⊆ abigGhostWindow (S n))
  (hjointLimit : forall beta h, 0 <= beta -> 0 < h -> DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
-- proof
  apply StatMech.Sharpness.abig_aizenmanBarskyPhysical_of_tsum_transitive_exhaustion G J o J0 hJ0 hJ hJsupport hsum hrow move hmove hG hJinv S ho hmonoWindow hcover hjointLimit

/--
[abig_ghost_edge_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_ghost_edge_prob_eq
  [Countable V]
  {x : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hh : 0 <= h) :
-- imply
  (abigMeasure J beta h).real {omega | omega s(some x, none) = true} = qField h := by
-- proof
  apply StatMech.Sharpness.abig_ghost_edge_prob J beta h hh x

/--
[abig_physical_edge_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean)
-/
@[path]
private lemma abig_physical_edge_prob_eq
  [Countable V]
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hJ : 0 <= J s(x, y)) :
-- imply
  (abigMeasure J beta h).real {omega | omega s(some x, some y) = true} = pBeta (J s(x, y)) beta := by
-- proof
  apply StatMech.Sharpness.abig_physical_edge_prob J beta h hbeta hJ


-- created on 2026-10-23
