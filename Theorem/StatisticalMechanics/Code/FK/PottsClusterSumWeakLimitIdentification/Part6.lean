/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem isClopen_pottsJointCylinder
    {d q : Nat} (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool)) :
    IsClopen (pottsJointCylinder spinSites spinSet edgeSites edgeSet) :=
  (isClopen_pottsSpinCylinder spinSites spinSet).prod
    (isClopen_cylinderEvent edgeSites edgeSet)

theorem pottsJointCylinder_eq_boxRestrict_preimage
    {d q n : Nat} (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool))
    (hspin : ∀ x ∈ spinSites, x ∈ box d n)
    (hedge : ∀ e ∈ edgeSites, e ∈ Set.range (edgeIncl d n)) :
    pottsJointCylinder spinSites spinSet edgeSites edgeSet =
      pottsBoxJointRestrict d n q ⁻¹'
        (pottsBoxJointRestrict d n q ''
          pottsJointCylinder spinSites spinSet edgeSites edgeSet) := by
  ext joint
  constructor
  · intro hjoint
    exact ⟨joint, hjoint, rfl⟩
  · rintro ⟨other, hother, heq⟩
    rcases hother with ⟨hotherSpin, hotherEdge⟩
    constructor
    · rw [mem_cylinder] at hotherSpin ⊢
      have hrestr := congrArg Prod.fst heq
      have heqSpin : spinSites.restrict joint.1 =
          spinSites.restrict other.1 := by
        funext x
        exact (congrFun hrestr ⟨x, hspin x x.2⟩).symm
      rw [heqSpin]
      exact hotherSpin
    · rw [mem_cylinder] at hotherEdge ⊢
      have hrestr := congrArg Prod.snd heq
      have heqEdge : edgeSites.restrict joint.2 =
          edgeSites.restrict other.2 := by
        funext e
        obtain ⟨eb, heb⟩ := hedge e e.2
        simpa only [pottsBoxJointRestrict, heb] using
          (congrFun hrestr eb).symm
      rw [heqEdge]
      exact hotherEdge

theorem exists_box_containing_jointCylinder
    {d q : Nat} (spinSites : Finset (Site d))
    (edgeSites : Finset (Sym2 (Site d))) :
    ∃ n : Nat,
      (∀ x ∈ spinSites, x ∈ box d n) ∧
      (∀ e ∈ edgeSites, e ∈ Set.range (edgeIncl d n)) := by
  classical
  let vertices : Finset (Site d) :=
    spinSites ∪ edgeSites.biUnion Sym2.toFinset
  obtain ⟨n, hn⟩ := Percolation.finite_subset_box
    (vertices : Set (Site d)) vertices.finite_toSet
  refine ⟨n, ?_, ?_⟩
  · intro x hx
    exact hn (by simp [vertices, hx])
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxv : x ∈ vertices := by
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨s(x, y), he, by simp⟩
        have hyv : y ∈ vertices := by
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨s(x, y), he, by simp⟩
        let xb : boxVerts d n := ⟨x, hn hxv⟩
        let yb : boxVerts d n := ⟨y, hn hyv⟩
        refine ⟨s(xb, yb), ?_⟩
        simp [edgeIncl, xb, yb]


theorem eventually_freeESJoint_eq_clusterSum_on_pottsJointCylinder
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool)) :
    Filter.EventuallyEq atTop
      (fun k => pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq)
          (pottsJointCylinder spinSites spinSet edgeSites edgeSet))
      (fun k => freeESJointFiniteMeasure d (phi k) q hp hp1 hq
        (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) := by
  obtain ⟨N, hspinN, hedgeN⟩ :=
    exists_box_containing_jointCylinder (q := q) spinSites edgeSites
  filter_upwards [eventually_ge_atTop N] with k hk
  have hNphi : N ≤ phi k := hk.trans (hphi.id_le k)
  let C := pottsJointCylinder spinSites spinSet edgeSites edgeSet
  let R := pottsBoxJointRestrict d (phi k) q
  let T := R '' C
  have hspin : ∀ x ∈ spinSites, x ∈ box d (phi k) := by
    intro x hx
    exact box_mono d hNphi (hspinN x hx)
  have hedge : ∀ e ∈ edgeSites,
      e ∈ Set.range (edgeIncl d (phi k)) := by
    intro e he
    obtain ⟨eb, heb⟩ := hedgeN e he
    refine ⟨innerEdgeLE d hNphi eb, ?_⟩
    rw [edgeIncl_innerEdgeLE, heb]
  have hC : C = R ⁻¹' T := by
    exact pottsJointCylinder_eq_boxRestrict_preimage
      spinSites spinSet edgeSites edgeSet hspin hedge
  have hrestricted :=
    (pottsClusterSumJointProbabilityMeasure_freeFinite_map_boxRestrict
      boundaryColor (phi k) hp hp1 hq).trans
      (freeESJointFiniteMeasure_map_boxRestrict
        d (phi k) q hp hp1 hq).symm
  calc
    pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq) C =
      ((pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq)).map
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable) T := by
        rw [ProbabilityMeasure.map_apply
          (pottsClusterSumJointProbabilityMeasure boundaryColor
            (freeFiniteMeasure d (phi k) hp hp1 hq))
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable
          MeasurableSet.of_discrete, ← hC]
    _ = ((freeESJointFiniteMeasure d (phi k) q hp hp1 hq).map
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable) T := by
        rw [hrestricted]
    _ = freeESJointFiniteMeasure d (phi k) q hp hp1 hq C := by
        rw [ProbabilityMeasure.map_apply
          (freeESJointFiniteMeasure d (phi k) q hp hp1 hq)
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable
          MeasurableSet.of_discrete, ← hC]

theorem map_snd_restrict_fst_preimage_apply
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (mu : Measure (alpha × beta)) {A : Set alpha} {B : Set beta}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.map Prod.snd (mu.restrict (Prod.fst ⁻¹' A)) B =
      mu (A ×ˢ B) := by
  rw [Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (hB.preimage measurable_snd)]
  simp only [Set.prod_eq]
  rw [inter_comm]

theorem map_fst_restrict_snd_preimage_apply
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (mu : Measure (alpha × beta)) {A : Set alpha} {B : Set beta}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.map Prod.fst (mu.restrict (Prod.snd ⁻¹' B)) A =
      mu (A ×ˢ B) := by
  rw [Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (hA.preimage measurable_fst)]
  rfl


theorem ProbabilityMeasure.ext_of_pottsJointCylinder
    {d q : Nat} (mu nu : ProbabilityMeasure (PottsJointConfig d q))
    (h : ∀ (spinSites : Finset (Site d))
      (spinSet : Set (∀ _x : spinSites, Fin q))
      (edgeSites : Finset (Sym2 (Site d)))
      (edgeSet : Set (∀ _e : edgeSites, Bool)),
      mu (pottsJointCylinder spinSites spinSet edgeSites edgeSet) =
        nu (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_prod
  intro A B hA hB
  have hedge (spinSites : Finset (Site d))
      (spinSet : Set (∀ _x : spinSites, Fin q)) :
      (mu : Measure _)
          (cylinder (α := fun _ : Site d => Fin q) spinSites spinSet ×ˢ B) =
        (nu : Measure _)
          (cylinder (α := fun _ : Site d => Fin q) spinSites spinSet ×ˢ B) := by
    let spinCylinder : Set (PottsConfig d q) :=
      cylinder (α := fun _ : Site d => Fin q) spinSites spinSet
    let muEdge : Measure (ConfigSpace (Sym2 (Site d))) :=
      Measure.map Prod.snd ((mu : Measure _).restrict (Prod.fst ⁻¹' spinCylinder))
    let nuEdge : Measure (ConfigSpace (Sym2 (Site d))) :=
      Measure.map Prod.snd ((nu : Measure _).restrict (Prod.fst ⁻¹' spinCylinder))
    have hspinCylinder : MeasurableSet spinCylinder := by
      exact MeasurableSet.cylinder spinSites MeasurableSet.of_discrete
    have hedgeMeasure : muEdge = nuEdge := by
      apply ext_of_generate_finite
        (measurableCylinders (fun _ : Sym2 (Site d) => Bool))
        generateFrom_measurableCylinders.symm
        isPiSystem_measurableCylinders
      · intro edgeCylinder hedgeCylinder
        rw [mem_measurableCylinders] at hedgeCylinder
        obtain ⟨edgeSites, edgeSet, hedgeSet, rfl⟩ := hedgeCylinder
        dsimp only [muEdge, nuEdge]
        rw [map_snd_restrict_fst_preimage_apply _
              hspinCylinder
              (MeasurableSet.cylinder edgeSites hedgeSet),
            map_snd_restrict_fst_preimage_apply _
              hspinCylinder
              (MeasurableSet.cylinder edgeSites hedgeSet)]
        have hh := congrArg (fun x : NNReal => (x : ENNReal))
          (h spinSites spinSet edgeSites edgeSet)
        simpa only [pottsJointCylinder,
          ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hh
      · change muEdge Set.univ = nuEdge Set.univ
        dsimp only [muEdge, nuEdge]
        rw [map_snd_restrict_fst_preimage_apply _
              hspinCylinder MeasurableSet.univ,
            map_snd_restrict_fst_preimage_apply _
              hspinCylinder MeasurableSet.univ]
        have huniv := congrArg (fun x : NNReal => (x : ENNReal))
          (h spinSites spinSet ∅ Set.univ)
        simpa [pottsJointCylinder,
          ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using huniv
    have hBmap := congrArg (fun rho : Measure (ConfigSpace (Sym2 (Site d))) => rho B)
      hedgeMeasure
    change (Measure.map Prod.snd
        ((mu : Measure _).restrict (Prod.fst ⁻¹' spinCylinder))) B =
      (Measure.map Prod.snd
        ((nu : Measure _).restrict (Prod.fst ⁻¹' spinCylinder))) B at hBmap
    rw [map_snd_restrict_fst_preimage_apply _ hspinCylinder hB,
      map_snd_restrict_fst_preimage_apply _ hspinCylinder hB] at hBmap
    exact hBmap
  let muSpin : Measure (PottsConfig d q) :=
    Measure.map Prod.fst ((mu : Measure _).restrict (Prod.snd ⁻¹' B))
  let nuSpin : Measure (PottsConfig d q) :=
    Measure.map Prod.fst ((nu : Measure _).restrict (Prod.snd ⁻¹' B))
  have hspinMeasure : muSpin = nuSpin := by
    apply ext_of_generate_finite
      (measurableCylinders (fun _ : Site d => Fin q))
      generateFrom_measurableCylinders.symm
      isPiSystem_measurableCylinders
    · intro spinCylinder hspinCylinder
      rw [mem_measurableCylinders] at hspinCylinder
      obtain ⟨spinSites, spinSet, hspinSet, rfl⟩ := hspinCylinder
      dsimp only [muSpin, nuSpin]
      rw [map_fst_restrict_snd_preimage_apply _
            (MeasurableSet.cylinder (α := fun _ : Site d => Fin q)
              spinSites hspinSet) hB,
          map_fst_restrict_snd_preimage_apply _
            (MeasurableSet.cylinder (α := fun _ : Site d => Fin q)
              spinSites hspinSet) hB]
      exact hedge spinSites spinSet
    · change muSpin Set.univ = nuSpin Set.univ
      dsimp only [muSpin, nuSpin]
      rw [map_fst_restrict_snd_preimage_apply _ MeasurableSet.univ hB,
        map_fst_restrict_snd_preimage_apply _ MeasurableSet.univ hB]
      have hfull := hedge ∅ Set.univ
      simpa using hfull
  have hAmap := congrArg (fun rho : Measure (PottsConfig d q) => rho A) hspinMeasure
  change (Measure.map Prod.fst
      ((mu : Measure _).restrict (Prod.snd ⁻¹' B))) A =
    (Measure.map Prod.fst
      ((nu : Measure _).restrict (Prod.snd ⁻¹' B))) A at hAmap
  rw [map_fst_restrict_snd_preimage_apply _ hA hB,
    map_fst_restrict_snd_preimage_apply _ hA hB] at hAmap
  exact hAmap

set_option maxHeartbeats 800000 in


theorem freeESJointWeakLimit_eq_clusterSum
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (Xi : ProbabilityMeasure (PottsJointConfig d q))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hjoint : Tendsto (fun k =>
        freeESJointFiniteMeasure d (phi k) q hp hp1 hq)
      atTop (nhds Xi))
    (hedge : Tendsto (fun k =>
        freeFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit))
    (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d) :
    Xi = pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
  let factorLimit :=
    pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit
  have hfactor : Tendsto (fun k =>
      pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq))
      atTop (nhds factorLimit) := by
    exact tendsto_pottsClusterSumJointProbabilityMeasure boundaryColor
      (fun k => freeFiniteMeasure d (phi k) hp hp1 hq)
      edgeLimit hedge hfinite
  apply ProbabilityMeasure.ext_of_pottsJointCylinder
  intro spinSites spinSet edgeSites edgeSet
  let C := pottsJointCylinder spinSites spinSet edgeSites edgeSet
  have hC : IsClopen C :=
    isClopen_pottsJointCylinder spinSites spinSet edgeSites edgeSet
  have hXi := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    hjoint hC
  have hfactorMass := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    hfactor hC
  have heq := eventually_freeESJoint_eq_clusterSum_on_pottsJointCylinder
    boundaryColor hp hp1 hq phi hphi spinSites spinSet edgeSites edgeSet
  have hfactorToXi : Tendsto (fun k =>
      pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq) C)
      atTop (nhds (Xi C)) :=
    hXi.congr' heq.symm
  simpa only [factorLimit, C] using
    tendsto_nhds_unique hfactorToXi hfactorMass


theorem freePottsJointWeakLimit_eq_clusterSum
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (hq : 0 < (q : Real))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (Xi : ProbabilityMeasure (PottsJointConfig d q))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hjoint : Tendsto (fun k =>
        freePottsJointFiniteMeasure d (phi k) q beta J hp hp1)
      atTop (nhds Xi))
    (hedge : Tendsto (fun k =>
        freeFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit))
    (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d) :
    Xi = pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
  apply freeESJointWeakLimit_eq_clusterSum boundaryColor hp hp1 hq
    phi hphi Xi edgeLimit
  · simpa [freeESJointFiniteMeasure, freePottsJointFiniteMeasure] using hjoint
  · exact hedge
  · exact hfinite

end StatMech.FK
