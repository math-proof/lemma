/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredBoxLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Def.StatisticalMechanics.Code.FK.WiredDomChain
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem outProj_eq_false_of_range (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {e : Sym2 (boxVerts d (n+1))} (he : e ∈ Set.range (innerEdge d n)) :
    outProj d n ρ e = false := by
  obtain ⟨e', rfl⟩ := he
  unfold outProj
  rw [psiExt_innerEdge]

theorem outProj_eq_of_not_range (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {e : Sym2 (boxVerts d (n+1))} (he : e ∉ Set.range (innerEdge d n)) :
    outProj d n ρ e = ρ e := by
  unfold outProj
  rw [psiExt_eq_psi_of_not_range _ _ _ _ he]


theorem agreesOff_outProj (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    AgreesOff (innerEdgeFinset d n) (outProj d n ρ) ρ := by
  intro e he
  rw [mem_innerEdgeFinset] at he
  exact (outProj_eq_of_not_range n ρ he).symm


theorem outProj_idem (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    outProj d n (outProj d n ρ) = outProj d n ρ := by
  funext e
  by_cases hin : e ∈ Set.range (innerEdge d n)
  · rw [outProj_eq_false_of_range n _ hin, outProj_eq_false_of_range n ρ hin]
  · rw [outProj_eq_of_not_range n _ hin]


theorem filter_outProj_eq_condFibre (n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (hψ : outProj d n ψ = ψ) :
    Finset.univ.filter (fun ρ => outProj d n ρ = ψ)
      = condFibre (innerEdgeFinset d n) ψ := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_condFibre]
  refine ⟨fun h e he => by
    rw [mem_innerEdgeFinset] at he
    rw [← outProj_eq_of_not_range n ρ he, h], ?_⟩
  intro h
  have hpr : outProj d n ρ = outProj d n ψ := by
    funext e
    by_cases hin : e ∈ Set.range (innerEdge d n)
    · rw [outProj_eq_false_of_range n ρ hin, outProj_eq_false_of_range n ψ hin]
    · have he : e ∉ innerEdgeFinset d n := by rw [mem_innerEdgeFinset]; exact hin
      rw [outProj_eq_of_not_range n ρ hin, outProj_eq_of_not_range n ψ hin, h e he]
  rw [hpr, hψ]


theorem condFibre_congr_dom {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)} (h : AgreesOff F ψ ψ') :
    condFibre F ψ = condFibre F ψ' := by
  ext σ
  rw [mem_condFibre, mem_condFibre, agreesOff_congr h]


theorem condBcProb_congr_dom {V : Type*} [Fintype V] [DecidableEq V] (G C : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p q : ℝ) (F : Finset (Sym2 V)) (ψ ψ' ω : ConfigSpace (Sym2 V)) (h : AgreesOff F ψ ψ') :
    condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
  have hcond : AgreesOff F ψ ω ↔ AgreesOff F ψ' ω := by rw [agreesOff_congr h]
  have hfibre : condFibre F ψ = condFibre F ψ' := condFibre_congr_dom h
  unfold condBcProb inducedBcZ
  rw [hfibre]
  by_cases hω : AgreesOff F ψ ω
  · rw [if_pos hω, if_pos (hcond.mp hω)]
  · rw [if_neg hω, if_neg (fun h' => hω (hcond.mpr h'))]


theorem sum_fibreMass_eq_one (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
          bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ) = 1 := by
  classical
  set C := boundaryCliqueGraph (boxBoundary d (n+1))
  set F := innerEdgeFinset d n
  set G := boxGraph d (n+1)
  rw [show (∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre F ψ, bcProb G C p q σ))
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ Finset.univ.filter (fun ρ => outProj d n ρ = ψ), bcProb G C p q σ) from ?_]
  · rw [Finset.sum_fiberwise_of_maps_to
        (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
    exact bcProb_sum_eq_one G C hp hp1 hq
  · apply Finset.sum_congr rfl
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    rw [filter_outProj_eq_condFibre n ψ hψ.2]


theorem wiredSucc_bcProb_decompose (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ
        * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q ρ)
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
            bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ)
          * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ
              * condBcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q
                  (innerEdgeFinset d n) ψ ρ) := by
  classical
  set C := boundaryCliqueGraph (boxBoundary d (n+1))
  set F := innerEdgeFinset d n
  set G := boxGraph d (n+1)
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := outProj d n) (t := Finset.univ.filter (fun ψ => outProj d n ψ = ψ))
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.mem_filter] at hψ
  rw [filter_outProj_eq_condFibre n ψ hψ.2]
  
  have hRHS : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [hRHS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_condFibre] at hρ
  have hbc := bcProb_eq_fibreMass_mul_condBcProb G C hp hp1 hq F ρ
  have hfib : condFibre F ρ = condFibre F ψ := by
    ext σ
    rw [mem_condFibre, mem_condFibre, agreesOff_congr (agreesOff_symm hρ)]
  rw [hfib] at hbc
  have hcc : condBcProb G C p q F ρ ρ = condBcProb G C p q F ψ ρ :=
    condBcProb_congr_dom G C p q F ρ ψ ρ (agreesOff_symm hρ)
  rw [hcc] at hbc
  rw [hbc]
  ring


theorem condBcProb_innerRestrict_le (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
        * condBcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q
            (innerEdgeFinset d n) ψ ρ)
      ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [condBcProb_psiExt_sum_eq_inducedBox d n hp hp1 hq0 ψ (innerRestrict d n ⁻¹' A₀)]
  have hpre : psiExt d n ψ ⁻¹' (innerRestrict d n ⁻¹' A₀) = A₀ := by
    ext ω
    simp only [Set.mem_preimage, innerRestrict_psiExt]
  rw [hpre]
  exact condBcProb_psiExt_dominated_wired d n ψ hp hp1 hq hA₀


theorem wiredSucc_bcProb_innerEvent_le (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
        * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q ρ)
      ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set c := ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
      * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω with hc
  rw [wiredSucc_bcProb_decompose n hp hp1 hq0 (innerRestrict d n ⁻¹' A₀)]
  calc ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
            bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ)
          * (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
              * condBcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q
                  (innerEdgeFinset d n) ψ ρ)
        ≤ ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
            (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
              bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ) * c := by
            apply Finset.sum_le_sum
            intro ψ _
            apply mul_le_mul_of_nonneg_left (condBcProb_innerRestrict_le n hp hp1 hq ψ hA₀)
            exact Finset.sum_nonneg (fun σ _ =>
              bcProb_nonneg (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) hp hp1 hq0 σ)
    _ = (∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
            (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
              bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ)) * c := by
            rw [Finset.sum_mul]
    _ = c := by rw [sum_fibreMass_eq_one n hp hp1 hq0, one_mul]


theorem wiredFiniteMeasure_succ_real_innerRestrictEvent (n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n))))
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n+1))),
          (innerRestrict d n ⁻¹' S).indicator (fun _ => (1:ℝ)) ρ
            * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p 2 ρ := by
  have hw : (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
        (boxRestrict d n ⁻¹' S)
      = ((wiredFkPMF (boxGraph d (n+1)) (boxBoundary d (n+1)) hp hp1
            (by norm_num : (0:ℝ) < 2)).toMeasure
          (extendEdge d (n+1) ⁻¹' (boxRestrict d n ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d (n+1)) hmeas]
  have hpre : extendEdge d (n+1) ⁻¹' (boxRestrict d n ⁻¹' S) = innerRestrict d n ⁻¹' S := by
    ext ρ
    simp only [Set.mem_preimage, boxRestrict_extendEdge_succ]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)]
  exact Finset.sum_congr rfl (fun ρ _ => by rw [bcProb_clique_eq_wiredFkProb])


theorem wiredFiniteMeasure_succ_le_smallerBox (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      ≤ ∑ ω, S.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  rw [wiredFiniteMeasure_succ_real_innerRestrictEvent n hp hp1 S hmeas]
  exact wiredSucc_bcProb_innerEvent_le n hp hp1 (by norm_num) hS


theorem isIncreasing_connToBdryEvent (n : ℕ) :
    IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
  intro a b hab ha
  simp only [Set.mem_setOf_eq] at ha ⊢
  obtain ⟨y, hy, hconn⟩ := ha
  exact ⟨y, hy, hconn.mono (openSub_mono _ hab)⟩


theorem wiredFiniteMeasure_succ_le_boxBdryConnEvent (n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  have hS : IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} :=
    isIncreasing_connToBdryEvent n
  have hmeas : MeasurableSet (boxBdryConnEvent d n) := measurableSet_boxBdryConnEvent d n
  
  have hdom := wiredFiniteMeasure_succ_le_smallerBox n hp hp1 hS hmeas
  rw [wiredFiniteMeasure_real_boxBdryConnEvent_sum d n hp hp1]
  exact hdom


theorem openSub_succ_adj_inner (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x y : boxVerts d n) :
    (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Adj
        (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
  rw [openSub_adj, openSub_adj, boxGraph_adj_boxVertIncl]
  have he : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  rw [he,
    show boxRestrict d (n+1) ω (innerEdge d n s(x,y))
        = ω (edgeIncl d (n+1) (innerEdge d n s(x,y))) from rfl,
    edgeIncl_innerEdge]
  rfl


theorem boxBoundary_of_openSub_succ_adj_outer (n : ℕ) (hn : 1 ≤ n)
    (ω : ConfigSpace (Sym2 (Site d)))
    {x : boxVerts d n} {z : boxVerts d (n+1)} (hz : ¬ IsInnerVert d n z)
    (h : (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Adj (boxVertIncl d n x) z) :
    boxBoundary d n x := by
  rw [openSub_adj] at h
  obtain ⟨hadj, _⟩ := h
  have hnn : StatMech.Lattice.NearestNeighbour d (x : Site d) (z : Site d) := by
    have hcp := hadj; rw [boxGraph, SimpleGraph.comap_adj] at hcp; exact hcp
  exact ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn hz⟩


theorem boxVertIncl_boxOrigin (n : ℕ) :
    boxVertIncl d n (IsingFK.boxOrigin d n) = IsingFK.boxOrigin d (n+1) :=
  Subtype.ext rfl


theorem connToBdry_succ_of_connToBdry (n : ℕ) (hn : 1 ≤ n) (ω : ConfigSpace (Sym2 (Site d)))
    {v : boxVerts d (n+1)} (hv : boxBoundary d (n+1) v)
    (h : (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Reachable
        (IsingFK.boxOrigin d (n+1)) v) :
    ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  set OS := openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)
  set os := openSub (boxGraph d n) (boxRestrict d n ω)
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen OS.Adj (IsingFK.boxOrigin d (n+1)) w →
      (ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n)
        ∨ ∃ x : boxVerts d n, boxVertIncl d n x = w
            ∧ os.Reachable (IsingFK.boxOrigin d n) x) by
    rcases H v h with hdone | ⟨x, hx, hreach⟩
    · exact hdone
    · exfalso
      have hvinner : IsInnerVert d n v := by rw [← hx]; exact isInnerVert_boxVertIncl d n x
      rw [boxBoundary, mem_vertexBoundary] at hv
      exact hv.2 (by simpa using hvinner)
  intro w hw
  induction hw with
  | refl => exact Or.inr ⟨IsingFK.boxOrigin d n, boxVertIncl_boxOrigin n, SimpleGraph.Reachable.refl _⟩
  | @tail u w hru hadj ih =>
      rcases ih with hdone | ⟨x, hx, hreach⟩
      · exact Or.inl hdone
      · subst hx
        by_cases hw_inner : IsInnerVert d n w
        · obtain ⟨x', rfl⟩ := (isInnerVert_iff_range d n w).mp hw_inner
          exact Or.inr ⟨x', rfl,
            hreach.trans ((openSub_succ_adj_inner n ω x x').mp hadj).reachable⟩
        · exact Or.inl ⟨x, boxBoundary_of_openSub_succ_adj_outer n hn ω hw_inner hadj, hreach⟩


theorem boxBdryConnEvent_succ_subset (n : ℕ) (hn : 1 ≤ n) :
    boxBdryConnEvent d (n+1) ⊆ boxBdryConnEvent d n := by
  intro ω hω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq, ConnToBdry] at hω ⊢
  obtain ⟨v, hv, hconn⟩ := hω
  exact connToBdry_succ_of_connToBdry n hn ω hv hconn


theorem wiredFiniteMeasure_boxBdryConnEvent_antitone (n : ℕ) (hn : 1 ≤ n) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d (n+1))
      ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  refine le_trans ?_ (wiredFiniteMeasure_succ_le_boxBdryConnEvent n hp hp1)
  exact measureReal_mono (boxBdryConnEvent_succ_subset n hn)


end FK
end StatMech
