/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Def.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part12
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


theorem abigWindow_incidentCoupling_le [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (J0 : Real)
    (hrow : abigUniformFiniteRowBound G J J0)
    (S : Finset V) (x : S) :
    abcrIncidentCoupling (abigWindowGraph G S)
      (abigWindowCoupling J S) x <= J0 := by
  rw [abigWindow_incidentCoupling_eq_sum G J S x]
  exact hrow S x


theorem abigUniformFiniteRowBound_of_tsum [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (J0 : Real)
    (hJ : forall e, 0 <= J e)
    (hsum : forall x, Summable (fun y =>
      if G.Adj x y then J s(x, y) else 0))
    (hrow : forall x, (∑' y,
      if G.Adj x y then J s(x, y) else 0) <= J0) :
    abigUniformFiniteRowBound G J J0 := by
  intro S x
  change (∑ y : S, (fun z : V =>
    if G.Adj (x : V) z then J s((x : V), z) else 0) y) <= J0
  calc
    _ = ∑ y ∈ S, if G.Adj (x : V) y
        then J s((x : V), y) else 0 := Finset.sum_coe_sort S _
    _ <= ∑' y, if G.Adj (x : V) y
        then J s((x : V), y) else 0 :=
      Summable.sum_le_tsum S (by
        intro y hy
        by_cases hxy : G.Adj (x : V) y
        · simp [hxy, hJ]
        · simp [hxy]) (hsum (x : V))
    _ <= J0 := hrow (x : V)


theorem abigWindow_abfaParams_eq [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (beta h : Real)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0) :
    forall e : Sym2 (Option S),
      abfaParams (abigWindowGraph G S) (abigWindowCoupling J S) beta h e =
        abigRealParam J beta h (abigWindowEdgeEquiv S e) := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abfaParams, abpdBetaFieldParams, paramOn, abfaLiftCoupling,
          abfaBaseCoupling, abigRealParam, FieldGhostDict.ghostCoupling,
          FieldGhostDict.ghostEdges, abigWindowEdgeEquiv, pBeta]
      · simp [abfaParams, abpdBetaFieldParams, paramOn, abigRealParam,
          FieldGhostDict.ghostCoupling, FieldGhostDict.ghostEdges,
          abigWindowEdgeEquiv]
      · simp [abfaParams, abpdBetaFieldParams, paramOn, abigRealParam,
          FieldGhostDict.ghostCoupling, FieldGhostDict.ghostEdges,
          abigWindowEdgeEquiv]
      · simp only [abfaParams, abpdBetaFieldParams, paramOn,
          abigWindowEdgeEquiv_mk, abigGhostWindowEquiv_some,
          abigRealParam_some_some]
        have hnotGhost : s(some x, some y) ∉
            FieldGhostDict.ghostEdges S := by
          simp [FieldGhostDict.ghostEdges]
        rw [if_neg hnotGhost, abfaLiftCoupling_some_some,
          abigWindowCoupling_mk]
        by_cases hxy : G.Adj x y
        · have hind : s(x, y) ∈ (abigWindowGraph G S).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset]
            exact hxy
          rw [if_pos hind]
        · have hind : s(x, y) ∉ (abigWindowGraph G S).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset]
            exact hxy
          rw [if_neg hind, hJsupport x y hxy]


theorem abigWindow_openSub_adj [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (eta : ConfigSpace (abigInternalEdges (abigGhostWindow S)))
    (a b : Option S) :
    (openSub (withGhost (abigWindowGraph G S))
        (cfgEquiv (abigWindowEdgeEquiv S) eta)).Adj a b ↔
      (openSub (withGhost G)
        (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)).Adj
        (abigGhostWindowEquiv S a : Option V)
        (abigGhostWindowEquiv S b : Option V) := by
  have hcoord : forall c d : Option S,
      cfgEquiv (abigWindowEdgeEquiv S) eta s(c, d) =
        ih_fill (abigInternalEdges (abigGhostWindow S)) eta
          s((abigGhostWindowEquiv S c : Option V),
            (abigGhostWindowEquiv S d : Option V)) := by
    intro c d
    have he : s((abigGhostWindowEquiv S c : Option V),
        (abigGhostWindowEquiv S d : Option V)) ∈
          abigInternalEdges (abigGhostWindow S) :=
      (mem_abigInternalEdges).2
        ⟨abigGhostWindowEquiv S c, (abigGhostWindowEquiv S c).property,
          abigGhostWindowEquiv S d, (abigGhostWindowEquiv S d).property, rfl⟩
    rw [cfgEquiv_apply, ih_fill, dif_pos he]
    congr 1
  rcases a with _ | x <;> rcases b with _ | y <;>
    simp [openSub, withGhost, abigWindowGraph, hcoord]


theorem abigWindow_connWithin [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (eta : ConfigSpace (abigInternalEdges (abigGhostWindow S)))
    (a b : Option S) :
    ConnWithin (withGhost (abigWindowGraph G S))
        (cfgEquiv (abigWindowEdgeEquiv S) eta) Set.univ
        ⟨a, Set.mem_univ _⟩ ⟨b, Set.mem_univ _⟩ ↔
      ConnWithin (withGhost G)
        (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)
        (abigGhostWindow S : Set (Option V))
        ⟨abigGhostWindowEquiv S a, (abigGhostWindowEquiv S a).property⟩
        ⟨abigGhostWindowEquiv S b, (abigGhostWindowEquiv S b).property⟩ := by
  constructor
  · intro hconn
    let f :
        ((openSub (withGhost (abigWindowGraph G S))
          (cfgEquiv (abigWindowEdgeEquiv S) eta)).induce Set.univ) →g
        ((openSub (withGhost G)
          (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)).induce
            (abigGhostWindow S : Set (Option V))) :=
      { toFun := fun z =>
          ⟨abigGhostWindowEquiv S z, (abigGhostWindowEquiv S z).property⟩
        map_rel' := fun {x y} hxy =>
          (abigWindow_openSub_adj G S eta x y).mp hxy }
    exact hconn.map f
  · intro hconn
    let f :
        ((openSub (withGhost G)
          (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)).induce
            (abigGhostWindow S : Set (Option V))) →g
        ((openSub (withGhost (abigWindowGraph G S))
          (cfgEquiv (abigWindowEdgeEquiv S) eta)).induce Set.univ) :=
      { toFun := fun z => ⟨(abigGhostWindowEquiv S).symm z, Set.mem_univ _⟩
        map_rel' := fun {x y} hxy => by
          apply (abigWindow_openSub_adj G S eta
            ((abigGhostWindowEquiv S).symm x)
            ((abigGhostWindowEquiv S).symm y)).mpr
          simpa using hxy }
    convert hconn.map f using 1 <;> simp [f]


theorem abigWindow_preimage_connEvent [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (o : S) :
    (cfgEquiv (abigWindowEdgeEquiv S)) ⁻¹'
        connEvent (withGhost (abigWindowGraph G S)) Set.univ
          (some o) {none} =
      ih_section
        (connEvent (withGhost G) (abigGhostWindow S : Set (Option V))
          (some (o : V)) {none})
        (abigInternalEdges (abigGhostWindow S)) := by
  ext eta
  change ConnToSet (withGhost (abigWindowGraph G S))
      (cfgEquiv (abigWindowEdgeEquiv S) eta) Set.univ (some o) {none} ↔
    ConnToSet (withGhost G)
      (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)
      (abigGhostWindow S : Set (Option V)) (some (o : V)) {none}
  constructor
  · rintro ⟨_, b, _, hb, hconn⟩
    have hbnone : b = none := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨(abigGhostWindowEquiv S (some o)).property, none,
      (abigGhostWindowEquiv S none).property, rfl,
      (abigWindow_connWithin G S eta (some o) none).mp hconn⟩
  · rintro ⟨_, b, _, hb, hconn⟩
    have hbnone : b = none := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨Set.mem_univ _, none, Set.mem_univ _, rfl,
      (abigWindow_connWithin G S eta (some o) none).mpr hconn⟩


theorem abig_connEvent_congr [DecidableEq W] (G : SimpleGraph W)
    (T : Finset W) (u v : W) {omega omega' : ConfigSpace (Sym2 W)}
    (hagree : ∀ e ∈ abigInternalEdges T, omega e = omega' e) :
    omega ∈ connEvent G (T : Set W) u {v} ↔
      omega' ∈ connEvent G (T : Set W) u {v} := by
  have hforward : ∀ {eta eta' : ConfigSpace (Sym2 W)},
      (∀ e ∈ abigInternalEdges T, eta e = eta' e) →
      eta ∈ connEvent G (T : Set W) u {v} →
      eta' ∈ connEvent G (T : Set W) u {v} := by
    intro eta eta' heq hconn
    rcases hconn with ⟨hu, b, hb, hbv, ⟨walk⟩⟩
    have hb_eq : b = v := Set.mem_singleton_iff.mp hbv
    subst b
    refine ⟨hu, v, hb, rfl, ⟨sab_inducedWalkTransfer G walk ?_⟩⟩
    intro e he
    apply heq e
    rcases he with ⟨z, hz, rfl⟩
    induction z using Sym2.inductionOn with
    | _ x y =>
        rw [Sym2.map_mk]
        exact (mem_abigInternalEdges).2
          ⟨x, x.property, y, y.property, rfl⟩
  constructor
  · exact hforward hagree
  · exact hforward (fun e he => (hagree e he).symm)


theorem abig_connEvent_dependsOn [DecidableEq W] (G : SimpleGraph W)
    (T : Finset W) (u v : W) :
    StatMech.DependsOn (connEvent G (T : Set W) u {v})
      (abigInternalEdges T : Set (Sym2 W)) := by
  intro omega omega' hagree
  exact abig_connEvent_congr G T u v
    (fun e he => (hagree e (by simpa using he)).symm)


theorem abig_measurableSet_connEvent [Countable W] [DecidableEq W]
    (G : SimpleGraph W) (T : Finset W) (u v : W) :
    MeasurableSet (connEvent G (T : Set W) u {v}) := by
  rw [ih_eq_cylinder_of_dependsOn (abigInternalEdges T)
    (abig_connEvent_dependsOn G T u v)]
  exact MeasurableSet.cylinder _ MeasurableSet.of_discrete


theorem abig_connWithin_mono_set (G : SimpleGraph W)
    (omega : ConfigSpace (Sym2 W)) {S T : Set W} (hST : S ⊆ T)
    {x y : S} (hconn : ConnWithin G omega S x y) :
    ConnWithin G omega T ⟨x, hST x.property⟩ ⟨y, hST y.property⟩ := by
  let f : ((openSub G omega).induce S) →g ((openSub G omega).induce T) :=
    { toFun := fun z => ⟨z, hST z.property⟩
      map_rel' := fun hab => hab }
  exact hconn.map f


theorem abig_connEvent_mono_set (G : SimpleGraph W) {S T : Set W}
    (hST : S ⊆ T) (u v : W) :
    connEvent G S u {v} ⊆ connEvent G T u {v} := by
  rintro omega ⟨hu, b, hb, hbv, hconn⟩
  refine ⟨hST hu, b, hST hb, hbv, ?_⟩
  exact abig_connWithin_mono_set G omega hST hconn


theorem abig_iUnion_connEvent_exhaustion [DecidableEq W]
    (G : SimpleGraph W) (T : Nat -> Finset W) (u v : W)
    (hcover : forall F : Finset W, exists n, F ⊆ T n) :
    (⋃ n, connEvent G (T n : Set W) u {v}) =
      connEvent G Set.univ u {v} := by
  ext omega
  constructor
  · rintro homega
    rw [Set.mem_iUnion] at homega
    obtain ⟨n, hn⟩ := homega
    exact abig_connEvent_mono_set G (Set.subset_univ _) u v hn
  · intro homega
    rcases homega with ⟨hu, b, hb, hbv, ⟨walk⟩⟩
    have hb_eq : b = v := Set.mem_singleton_iff.mp hbv
    subst b
    let ambient : (openSub G omega).Walk u v :=
      walk.map (SimpleGraph.Embedding.induce Set.univ).toHom
    obtain ⟨n, hn⟩ := hcover ambient.support.toFinset
    have hsupp : ∀ z, z ∈ ambient.support → z ∈ (T n : Set W) := by
      intro z hz
      exact hn (List.mem_toFinset.mpr hz)
    have huT : u ∈ (T n : Set W) := hsupp u ambient.start_mem_support
    have hvT : v ∈ (T n : Set W) := hsupp v ambient.end_mem_support
    rw [Set.mem_iUnion]
    refine ⟨n, huT, v, hvT, rfl, ?_⟩
    exact ⟨ambient.induce (T n : Set W) hsupp⟩


theorem abig_measurableSet_connEvent_univ [Countable W] [DecidableEq W]
    (G : SimpleGraph W) (T : Nat -> Finset W) (u v : W)
    (hcover : forall F : Finset W, exists n, F ⊆ T n) :
    MeasurableSet (connEvent G Set.univ u {v}) := by
  rw [← abig_iUnion_connEvent_exhaustion G T u v hcover]
  exact MeasurableSet.iUnion (fun n => abig_measurableSet_connEvent G (T n) u v)


theorem abig_tendsto_real_connEvent_exhaustion
    [Countable W] [DecidableEq W]
    (mu : Measure (ConfigSpace (Sym2 W))) [IsFiniteMeasure mu]
    (G : SimpleGraph W) (T : Nat -> Finset W) (u v : W)
    (hmono : Monotone T)
    (hcover : forall F : Finset W, exists n, F ⊆ T n) :
    Tendsto
      (fun n => mu.real (connEvent G (T n : Set W) u {v}))
      atTop (nhds (mu.real (connEvent G Set.univ u {v}))) := by
  let A : Nat -> Set (ConfigSpace (Sym2 W)) :=
    fun n => connEvent G (T n : Set W) u {v}
  have hAmono : Monotone A := by
    intro n m hnm
    exact abig_connEvent_mono_set G
      (fun x hx => hmono hnm hx) u v
  have hlim := tendsto_measure_iUnion_atTop (μ := mu) hAmono
  rw [abig_iUnion_connEvent_exhaustion G T u v hcover] at hlim
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hlim

section Marginals

variable [Countable V]


theorem abigMag_eq_of_automorphism [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (sigma : V ≃ V)
    (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
    (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y))
    (T : Nat -> Finset (Option V))
    (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
    abigMag G J (sigma o) beta h = abigMag G J o beta h := by
  let A := connEvent (withGhost G) Set.univ (some o) {none}
  have hA : MeasurableSet A := by
    exact abig_measurableSet_connEvent_univ
      (withGhost G) T (some o) none hcover
  have hpush := congrArg (fun mu :
      Measure (ConfigSpace (Sym2 (Option V))) => mu A)
    (abig_map_cfgEquiv J beta h sigma hJ)
  change (Measure.map (cfgEquiv (abfsEdgeEquiv sigma))
      (abigMeasure J beta h)) A = (abigMeasure J beta h) A at hpush
  rw [Measure.map_apply (measurable_cfgEquiv (abfsEdgeEquiv sigma)) hA,
    abfs_preimage_connEvent G sigma hG o] at hpush
  unfold abigMag Measure.real
  exact congrArg ENNReal.toReal hpush


theorem abigMag_eq_of_transitive [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJ : forall x u v, J s(move x u, move x v) = J s(u, v))
    (T : Nat -> Finset (Option V))
    (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
    forall x, abigMag G J x beta h = abigMag G J o beta h := by
  intro x
  rw [← hmove x]
  exact abigMag_eq_of_automorphism G J o beta h (move x)
    (hG x) (hJ x) T hcover


theorem abig_coord_true_prob (J : Sym2 V -> Real) (beta h : Real)
    (e : Sym2 (Option V)) :
    (abigMeasure J beta h).real {omega | omega e = true} =
      (abigParam J beta h e : Real) := by
  classical
  exact inhom_coord_true_prob (abigParam J beta h)
    (abigParam_le_one J beta h) e


theorem abig_realProb_cylinder (J : Sym2 V -> Real) (beta h : Real)
    (F : Finset (Sym2 (Option V)))
    (A : Set (ConfigSpace F)) :
    (abigMeasure J beta h).real (MeasureTheory.cylinder F A) =
      (inhomBernoulliProductMeasure
        (fun e : F => abigParam J beta h e)
        (fun e => abigParam_le_one J beta h e)).real A := by
  classical
  exact inhom_realProb_cylinder (abigParam J beta h)
    (abigParam_le_one J beta h) F A


theorem abig_finite_conn_prob_eq_marginal [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (T : Finset (Option V)) :
    (abigMeasure J beta h).real
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) =
      (inhomBernoulliProductMeasure
        (fun e : abigInternalEdges T => abigParam J beta h e)
        (fun e => abigParam_le_one J beta h e)).real
        (ih_section
          (connEvent (withGhost G) (T : Set (Option V)) (some o) {none})
          (abigInternalEdges T)) := by
  classical
  let A := connEvent (withGhost G) (T : Set (Option V)) (some o) {none}
  let F := abigInternalEdges T
  have hAcyl : A = MeasureTheory.cylinder F (ih_section A F) :=
    ih_eq_cylinder_of_dependsOn F
      (abig_connEvent_dependsOn (withGhost G) T (some o) none)
  calc
    (abigMeasure J beta h).real A =
        (abigMeasure J beta h).real
          (MeasureTheory.cylinder F (ih_section A F)) := congrArg _ hAcyl
    _ = (inhomBernoulliProductMeasure
          (fun e : F => abigParam J beta h e)
          (fun e => abigParam_le_one J beta h e)).real
          (ih_section A F) := abig_realProb_cylinder J beta h F _


theorem abig_finite_conn_prob_eq_probV [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (T : Finset (Option V)) :
    (abigMeasure J beta h).real
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) =
      probV (fun e : abigInternalEdges T => abigRealParam J beta h e)
        (ih_section
          (connEvent (withGhost G) (T : Set (Option V)) (some o) {none})
          (abigInternalEdges T)) := by
  rw [abig_finite_conn_prob_eq_marginal G J o beta h T]
  let r : abigInternalEdges T -> Real :=
    fun e => abigRealParam J beta h e
  have hr := fun e => abigRealParam_mem J beta h hbeta hh hJ e
  simpa [r, abigParam] using
    (inhom_real_eq_probV_of_mem r (fun e => (hr e).1)
      (fun e => (hr e).2)
      (ih_section
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none})
        (abigInternalEdges T)))


theorem abig_abfaMag_eq_finiteConn [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0) :
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta h =
      (abigMeasure J beta h).real
        (connEvent (withGhost G)
          (abigGhostWindow S : Set (Option V)) (some (o : V)) {none}) := by
  unfold abfaMag
  rw [abfs_probV_transfer (abigWindowEdgeEquiv S)]
  have hp : (fun y =>
      abfaParams (abigWindowGraph G S) (abigWindowCoupling J S) beta h
        ((abigWindowEdgeEquiv S).symm y)) =
      fun y : abigInternalEdges (abigGhostWindow S) =>
        abigRealParam J beta h y := by
    funext y
    simpa using abigWindow_abfaParams_eq G J S beta h hJsupport
      ((abigWindowEdgeEquiv S).symm y)
  rw [hp, abigWindow_preimage_connEvent G S o]
  exact (abig_finite_conn_prob_eq_probV G J (o : V) beta h
    hbeta hh hJ (abigGhostWindow S)).symm


end Marginals
end Sharpness
end StatMech
