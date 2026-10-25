/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
import Instance.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


namespace OsfDoubleStar

theorem dsG_le_jdsG : dsG ≤ jdsG := by
  intro a b hab; revert hab; fin_cases a <;> fin_cases b <;> decide


theorem dsG_acyclic : dsG.IsAcyclic := IsAcyclic.anti dsG_le_jdsG jdsG_isTree.isAcyclic


theorem dsG_hub0_deg : dsG.degree 0 = 3 := by decide

theorem dsG_hub4_deg : dsG.degree 4 = 3 := by decide

theorem dsG_deg_pos (v : Fin 8) : 1 ≤ dsG.degree v := by fin_cases v <;> decide

end OsfDoubleStar

open Classical in


theorem osf_peeledBoxForest_twoStar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x x' : Site d} (a a' : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x ∨ y = x')
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (hadj' : ∀ i, (openSubgraph d ω).Adj x' (a' i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n) (habdry' : ∀ i, a' i ∈ vertexBoundary d n)
    (hxsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
             ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
             ¬ Connected d (removeSite x ω) (a 1) (a 2))
    (hx'sep : ¬ Connected d (removeSite x' ω) (a' 0) (a' 1) ∧
              ¬ Connected d (removeSite x' ω) (a' 0) (a' 2) ∧
              ¬ Connected d (removeSite x' ω) (a' 1) (a' 2))
    (lab : Fin 8 → Site d)
    (hlab : lab 0 = x ∧ lab 1 = a 0 ∧ lab 2 = a 1 ∧ lab 3 = a 2 ∧
            lab 4 = x' ∧ lab 5 = a' 0 ∧ lab 6 = a' 1 ∧ lab 7 = a' 2)
    (hlabinj : Function.Injective lab) :
    osf_PeeledBoxForest ω n := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hlab
  set Vset : Finset (Site d) := Finset.univ.image lab with hVset
  have hmem : ∀ i : Fin 8, lab i ∈ Vset := fun i => by
    rw [hVset, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, rfl⟩
  set e : Fin 8 ≃ (↑Vset : Type) :=
    Equiv.ofBijective (fun i => (⟨lab i, hmem i⟩ : (↑Vset : Type)))
      ⟨fun u v huv => hlabinj (Subtype.ext_iff.mp huv),
        fun ⟨y, hy⟩ => by
          rw [hVset, Finset.mem_image] at hy
          obtain ⟨i, _, rfl⟩ := hy
          exact ⟨i, rfl⟩⟩ with he
  have heval : ∀ i, (e i : Site d) = lab i := fun i => rfl
  
  let F₀ : SimpleGraph (↑Vset : Type) := OsfDoubleStar.dsG.map e.toEmbedding
  let hisoF : OsfDoubleStar.dsG ≃g F₀ := SimpleGraph.Iso.map e OsfDoubleStar.dsG
  have hisoApp : ∀ i : Fin 8, hisoF i = e i := fun i =>
    SimpleGraph.Iso.map_apply e OsfDoubleStar.dsG i
  have hF₀adj : ∀ u v : Fin 8, F₀.Adj (e u) (e v) ↔ OsfDoubleStar.dsG.Adj u v := by
    intro u v
    have := hisoF.map_adj_iff (v := u) (w := v)
    simpa [hisoApp] using this
  have hF₀ac : F₀.IsAcyclic := (hisoF.symm.isAcyclic_iff).mpr OsfDoubleStar.dsG_acyclic
  have hsurj : ∀ w : (↑Vset : Type), ∃ i : Fin 8, e i = w := fun w => e.surjective w
  
  have hdeg : ∀ i : Fin 8, F₀.degree (e i) = OsfDoubleStar.dsG.degree i := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hnbhd : F₀.neighborFinset (e i) = (OsfDoubleStar.dsG.neighborFinset i).image e := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨j, rfl⟩ := e.surjective w
        exact ⟨j, by rw [SimpleGraph.mem_neighborFinset]; exact (hF₀adj i j).mp hw, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rw [SimpleGraph.mem_neighborFinset] at hj
        exact (hF₀adj i j).mpr hj
    rw [hnbhd, Finset.card_image_of_injective _ e.injective]
  
  set lf0 : Fin 3 → Fin 8 := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 3 with hlf0
  set lf4 : Fin 3 → Fin 8 := fun i => match i with | 0 => 5 | 1 => 6 | 2 => 7 with hlf4
  
  set vx : Site d → (↑Vset : Type) := fun y => if y = x then e 0 else e 4 with hvxdef
  set b : Site d → Fin 3 → (↑Vset : Type) :=
    fun y i => if y = x then e (lf0 i) else e (lf4 i) with hbdef
  refine osf_peeledBoxForest_of_acyclic ω n Vset ⟨e 0⟩ F₀ hF₀ac vx b ?_ ?_ ?_ ?_
  · 
    intro u v huv
    obtain ⟨iu, rfl⟩ := hsurj u
    obtain ⟨iv, rfl⟩ := hsurj v
    rw [hF₀adj, OsfDoubleStar.dsG, fromRel_adj] at huv
    obtain ⟨hne, hor⟩ := huv
    rw [heval, heval]
    fin_cases iu <;> fin_cases iv <;>
      first
        | (simp only [Fin.isValue, Fin.reduceFinMk, h0, h1, h2, h3, h4, h5, h6, h7]
           first
            | exact hadj 0 | exact hadj 1 | exact hadj 2
            | exact (hadj 0).symm | exact (hadj 1).symm | exact (hadj 2).symm
            | exact hadj' 0 | exact hadj' 1 | exact hadj' 2
            | exact (hadj' 0).symm | exact (hadj' 1).symm | exact (hadj' 2).symm)
        | (simp only [OsfDoubleStar.dsAdj, reduceCtorEq, or_self] at hor)
  · 
    intro v
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg]; exact OsfDoubleStar.dsG_deg_pos i
  · 
    intro y hybox htri
    have hxe0 : (vx x : Site d) = x := by
      simp only [hvxdef, if_pos rfl]; rw [heval, h0]
    
    have hbvalx : ∀ i : Fin 3, (b x i : Site d) = a i := by
      intro i; simp only [hbdef, if_pos rfl]; rw [heval]
      fin_cases i <;> simp only [hlf0, Fin.isValue, Fin.reduceFinMk, h1, h2, h3]
    rcases hsingle y hybox htri with hyx | hyx
    · 
      subst hyx
      refine ⟨hxe0, ?_, ?_⟩
      · intro i
        refine ⟨?_, ?_⟩
        · 
          simp only [hvxdef, hbdef, if_pos rfl]
          refine Adj.reachable ?_
          rw [hF₀adj]
          fin_cases i <;> simp only [hlf0] <;> decide
        · simp only [hvxdef, hbdef, if_pos rfl]
          intro hh
          exact absurd (e.injective hh) (by fin_cases i <;> simp only [hlf0] <;> decide)
      · rw [hbvalx 0, hbvalx 1, hbvalx 2]; exact hxsep
    · 
      subst hyx
      by_cases hxx' : y = x
      · 
        subst hxx'
        refine ⟨hxe0, ?_, ?_⟩
        · intro i
          refine ⟨?_, ?_⟩
          · simp only [hvxdef, hbdef, if_pos rfl]
            refine Adj.reachable ?_
            rw [hF₀adj]; fin_cases i <;> simp only [hlf0] <;> decide
          · simp only [hvxdef, hbdef, if_pos rfl]
            intro hh
            exact absurd (e.injective hh) (by fin_cases i <;> simp only [hlf0] <;> decide)
        · rw [hbvalx 0, hbvalx 1, hbvalx 2]; exact hxsep
      · 
        have hbvalx' : ∀ i : Fin 3, (b y i : Site d) = a' i := by
          intro i; simp only [hbdef, if_neg hxx']; rw [heval]
          fin_cases i <;> simp only [hlf4, Fin.isValue, Fin.reduceFinMk, h5, h6, h7]
        refine ⟨?_, ?_, ?_⟩
        · simp only [hvxdef, if_neg hxx']; rw [heval, h4]
        · intro i
          refine ⟨?_, ?_⟩
          · simp only [hvxdef, hbdef, if_neg hxx']
            refine Adj.reachable ?_
            rw [hF₀adj]; fin_cases i <;> simp only [hlf4] <;> decide
          · simp only [hvxdef, hbdef, if_neg hxx']
            intro hh
            exact absurd (e.injective hh) (by fin_cases i <;> simp only [hlf4] <;> decide)
        · rw [hbvalx' 0, hbvalx' 1, hbvalx' 2]; exact hx'sep
  · 
    intro v hv
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg] at hv
    rw [heval]
    fin_cases i <;>
      simp only [Fin.isValue, Fin.reduceFinMk, h0, h1, h2, h3, h4, h5, h6, h7] <;>
      first
        | (exact absurd hv (by decide))
        | exact habdry 0 | exact habdry 1 | exact habdry 2
        | exact habdry' 0 | exact habdry' 1 | exact habdry' 2

end Percolation
end StatMech
