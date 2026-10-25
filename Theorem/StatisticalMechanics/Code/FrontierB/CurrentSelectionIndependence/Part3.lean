/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityLimits
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentPatternFactor.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
import Def.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

theorem latticeEdgePart_subset (d : ℕ)
    (S : Finset (Sym2 (Site d))) : latticeEdgePart d S ⊆ S :=
  Finset.filter_subset _ _

theorem latticeEdgePart_lattice (d : ℕ)
    (S : Finset (Sym2 (Site d))) :
    (↑(latticeEdgePart d S) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
  intro e he
  exact (Finset.mem_filter.mp he).2

theorem ae_eq_zero_of_measure_eq_one
    {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) (e : E)
    (hzero : (mu : Measure (InfiniteCurrentConfig E)) {m | m e = 0} = 1) :
    ∀ᵐ m ∂(mu : Measure (InfiniteCurrentConfig E)), m e = 0 := by
  rw [ae_iff]
  have hmeas : MeasurableSet
      {m : InfiniteCurrentConfig E | m e = 0} :=
    (measurable_pi_apply e) (MeasurableSet.singleton 0)
  have hset : {m : InfiniteCurrentConfig E | ¬m e = 0} =
      {m : InfiniteCurrentConfig E | m e = 0}ᶜ := by
    ext m
    simp
  rw [hset, measure_compl hmeas (measure_ne_top _ _), measure_univ, hzero]
  simp

theorem ae_nonlattice_zero_on_finset
    (d : ℕ) (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (S : Finset (Sym2 (Site d)))
    (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet →
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1) :
    ∀ᵐ m ∂(mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))),
      ∀ e ∈ S, e ∉ (hypercubicLattice d).edgeSet → m e = 0 := by
  rw [Finset.eventually_all]
  intro e heS
  by_cases he : e ∈ (hypercubicLattice d).edgeSet
  · filter_upwards with m hnot
    exact (hnot he).elim
  · filter_upwards [ae_eq_zero_of_measure_eq_one mu e (hzero e he)] with m hm
    exact fun _ => hm

theorem currentCylinder_singleton_reduce_lattice
    (d : ℕ) (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (S : Finset (Sym2 (Site d)))
    (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet →
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1)
    (a : ↑S → ℕ) :
    (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      if ∀ e : ↑S,
          e.1 ∉ (hypercubicLattice d).edgeSet → a e = 0 then
        (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder (latticeEdgePart d S)
            {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ)
              (latticeEdgePart_subset d S) a})
      else 0 := by
  let L := latticeEdgePart d S
  let aL := Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ)
    (latticeEdgePart_subset d S) a
  have hae := ae_nonlattice_zero_on_finset d mu S hzero
  split_ifs with ha
  · apply measure_congr
    filter_upwards [hae] with m hm
    apply propext
    change (restrictCurrent S m = a) ↔ restrictCurrent L m = aL
    constructor
    · intro h
      funext e
      exact congrFun h ⟨e.1, (latticeEdgePart_subset d S) e.2⟩
    · intro h
      funext e
      by_cases he : e.1 ∈ (hypercubicLattice d).edgeSet
      · let eL : ↑L := ⟨e.1, Finset.mem_filter.mpr ⟨e.2, he⟩⟩
        have hc := congrFun h eL
        exact hc
      · rw [show restrictCurrent S m e = 0 by
          exact hm e.1 e.2 he]
        exact (ha e he).symm
  · have hempty : (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (∅ : Set (InfiniteCurrentConfig (Sym2 (Site d)))) = 0 := measure_empty
    rw [← hempty]
    apply measure_congr
    filter_upwards [hae] with m hm
    apply propext
    change (restrictCurrent S m = a) ↔ False
    constructor
    · intro h
      apply ha
      intro e he
      rw [← congrFun h e]
      exact hm e.1 e.2 he
    · exact False.elim

theorem plusCurrentLimit_marginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply,
    currentCylinder_singleton_reduce_lattice d nu S
      (fun e he => plusCurrentLimit_nonlattice_zero
        d beta hbeta.le e he hnu) a,
    currentCylinder_singleton_reduce_lattice d rho S
      (fun e he => plusCurrentLimit_nonlattice_zero
        d beta hbeta.le e he hrho) a]
  split_ifs
  · have hL := plusCurrentLimit_latticeMarginal_eq d beta hbeta
      (latticeEdgePart d S) (latticeEdgePart_lattice d S)
      hphi hpsi hnu hrho
    have happ := congrArg (fun p : ProbabilityMeasure
      (↑(latticeEdgePart d S) → ℕ) =>
        (p : Measure (↑(latticeEdgePart d S) → ℕ))
          {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ)
            (latticeEdgePart_subset d S) a}) hL
    simpa only [currentMarginal_apply] using happ
  · rfl

theorem freeCurrentLimit_marginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply,
    currentCylinder_singleton_reduce_lattice d nu S
      (fun e he => freeCurrentLimit_nonlattice_zero
        d beta hbeta.le e he hnu) a,
    currentCylinder_singleton_reduce_lattice d rho S
      (fun e he => freeCurrentLimit_nonlattice_zero
        d beta hbeta.le e he hrho) a]
  split_ifs
  · have hL := freeCurrentLimit_latticeMarginal_eq d beta hbeta
      (latticeEdgePart d S) (latticeEdgePart_lattice d S)
      hphi hpsi hnu hrho
    have happ := congrArg (fun p : ProbabilityMeasure
      (↑(latticeEdgePart d S) → ℕ) =>
        (p : Measure (↑(latticeEdgePart d S) → ℕ))
          {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ)
            (latticeEdgePart_subset d S) a}) hL
    simpa only [currentMarginal_apply] using happ
  · rfl

theorem plusCurrentLimit_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    nu = rho := by
  apply ProbabilityMeasure.ext_of_currentMarginal_eq
  intro S
  exact plusCurrentLimit_marginal_eq d beta hbeta S hphi hpsi hnu hrho

theorem freeCurrentLimit_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    nu = rho := by
  apply ProbabilityMeasure.ext_of_currentMarginal_eq
  intro S
  exact freeCurrentLimit_marginal_eq d beta hbeta S hphi hpsi hnu hrho

theorem plusCurrentLimit_eq_infinitePlus
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu) :
    nu = infinitePlusCurrentMeasure d beta hbeta.le := by
  exact plusCurrentLimit_eq d beta hbeta hphi
    (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le) hnu
    (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)

theorem freeCurrentLimit_eq_infiniteFree
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu) :
    nu = infiniteFreeCurrentMeasure d beta hbeta.le := by
  exact freeCurrentLimit_eq d beta hbeta hphi
    (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le) hnu
    (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le)

theorem weakCurrent_tendsto_of_tight_of_subseq_unique
    {E : Type*} [Countable E]
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (nu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (htight : IsTightMeasureSet (Set.range fun n =>
      (mu n : Measure (InfiniteCurrentConfig E))))
    (hnuMem : nu ∈ closure (Set.range mu))
    (hunique : ∀ (rho : ProbabilityMeasure (InfiniteCurrentConfig E))
      (phi : ℕ → ℕ), StrictMono phi →
        WeakCurrentConverges (mu ∘ phi) rho → rho = nu) :
    WeakCurrentConverges mu nu := by
  let K : Set (ProbabilityMeasure (InfiniteCurrentConfig E)) :=
    closure (Set.range mu)
  have hK : IsCompact K := by
    apply isCompact_closure_of_isTightMeasureSet
    have heq : {m : Measure (InfiniteCurrentConfig E) |
        ∃ rho ∈ Set.range mu, (rho : Measure _) = m} =
        Set.range (fun n => (mu n : Measure (InfiniteCurrentConfig E))) := by
      ext m
      simp
    rw [heq]
    exact htight
  let muK : ℕ → K := fun n =>
    ⟨mu n, subset_closure (Set.mem_range_self n)⟩
  let nuK : K := ⟨nu, hnuMem⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hsub : Tendsto muK atTop (nhds nuK) := by
    apply tendsto_nhds_of_unique_mapClusterPt
    intro rho hrho
    obtain ⟨phi, hphi, hconv⟩ := hrho.tendsto_subseq
    apply Subtype.ext
    have hval : WeakCurrentConverges (mu ∘ phi) rho.1 := by
      have hc := (continuous_subtype_val.tendsto rho).comp hconv
      simpa [muK, Function.comp_def] using hc
    exact hunique rho.1 phi hphi hval
  have hval := (continuous_subtype_val.tendsto nuK).comp hsub
  simpa [muK, nuK] using hval

theorem plusBoxCurrentMeasure_tendsto_full
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    WeakCurrentConverges
      (fun n => plusBoxCurrentMeasure d n beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) := by
  let mu := fun n => plusBoxCurrentMeasure d n beta hbeta.le
  have hmem : infinitePlusCurrentMeasure d beta hbeta.le ∈
      closure (Set.range mu) := by
    apply isClosed_closure.mem_of_tendsto
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)
    filter_upwards with k
    exact subset_closure ⟨infiniteCurrentBoxSubsequence d beta hbeta.le k, rfl⟩
  exact weakCurrent_tendsto_of_tight_of_subseq_unique mu
    (infinitePlusCurrentMeasure d beta hbeta.le)
    (plusBoxCurrentMeasure_tight d beta hbeta.le) hmem
    (fun rho phi hphi hconv =>
      plusCurrentLimit_eq_infinitePlus d beta hbeta hphi hconv)

theorem freeBoxCurrentMeasure_tendsto_full
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    WeakCurrentConverges
      (fun n => freeBoxCurrentMeasure d n beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) := by
  let mu := fun n => freeBoxCurrentMeasure d n beta hbeta.le
  have hmem : infiniteFreeCurrentMeasure d beta hbeta.le ∈
      closure (Set.range mu) := by
    apply isClosed_closure.mem_of_tendsto
      (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le)
    filter_upwards with k
    exact subset_closure ⟨infiniteCurrentBoxSubsequence d beta hbeta.le k, rfl⟩
  exact weakCurrent_tendsto_of_tight_of_subseq_unique mu
    (infiniteFreeCurrentMeasure d beta hbeta.le)
    (freeBoxCurrentMeasure_tight d beta hbeta.le) hmem
    (fun rho phi hphi hconv =>
      freeCurrentLimit_eq_infiniteFree d beta hbeta hphi hconv)

theorem plusBoxCurrentMeasure_cylinder_tendsto_full
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun n => (plusBoxCurrentMeasure d n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A)) atTop
      (nhds ((infinitePlusCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A))) :=
  (plusBoxCurrentMeasure_tendsto_full d beta hbeta).cylinderENNReal S A

theorem freeBoxCurrentMeasure_cylinder_tendsto_full
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun n => (freeBoxCurrentMeasure d n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A)) atTop
      (nhds ((infiniteFreeCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A))) :=
  (freeBoxCurrentMeasure_tendsto_full d beta hbeta).cylinderENNReal S A

end StatMech.FrontierB
