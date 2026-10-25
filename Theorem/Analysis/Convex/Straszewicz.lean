-- Author: @toskua, Avocado
-- Provenance: Adam Kiezun authored the original formalization
-- (commit 8a13ba393c1d23f85b900081c600941a4bdd56dc); @toskua, Avocado
-- authored only the Convexity.StdSimplex representation migration.

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.Module
import Mathlib.Topology.Bases
/-!
# Straszewicz's theorem on exposed points

Every extreme point of a compact convex set in a finite-dimensional real
normed space lies in the closure of its exposed points.

Primary source: S. Straszewicz, "Über exponierte Punkte abgeschlossener
Punktmengen", Fundamenta Mathematicae 24 (1935), 139–143,
DOI 10.4064/FM-24-1-139-143.
-/


namespace Convex.Straszewicz

open Set Metric Filter TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Convex hull of a compact set in a finite-dimensional space is compact. -/
theorem IsCompact.convexHull_of_compact {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · rw [convexHull_empty]
    exact isCompact_empty
  · set d := Module.finrank ℝ E with hd
    have himg : convexHull ℝ K =
        (fun p : Convexity.StdSimplex ℝ (Fin (d + 1)) × (Fin (d + 1) → E) =>
          ∑ i, p.1.weights i • p.2 i) ''
          (Set.univ ×ˢ {z : Fin (d + 1) → E | ∀ i, z i ∈ K}) := by
      apply Subset.antisymm
      · intro x hx
        rw [convexHull_eq_union] at hx
        simp only [Set.mem_iUnion, exists_prop] at hx
        obtain ⟨t, htK, htind, hxt⟩ := hx
        rw [Finset.convexHull_eq] at hxt
        obtain ⟨w, hw0, hw1, hcm⟩ := hxt
        have hxsum : x = ∑ y ∈ t, w y • y := by
          rw [← hcm, Finset.centerMass_eq_of_sum_1 t id hw1]
          simp only [id_eq]
        have hcard : t.card ≤ d + 1 := by
          have h1 := AffineIndependent.card_le_finrank_succ htind
          have hle := Submodule.finrank_le
            (vectorSpan ℝ (Set.range ((↑) : ↥t → E)))
          have hc : Fintype.card ↥t = t.card := Fintype.card_coe t
          omega
        classical
        have htne : t.Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          simp [h] at hw1
        have : Nonempty ↥t := (Finset.coe_nonempty.mpr htne).to_subtype
        let emb : ↥t ↪ Fin (d + 1) :=
          { toFun := fun i => Fin.castLE hcard (t.equivFin i)
            inj' := fun a b hab => t.equivFin.injective (Fin.ext (by
              have h2 := congrArg Fin.val hab
              simpa using h2)) }
        set r := Finset.univ.map emb with hr
        set w'' : Fin (d + 1) → ℝ := fun j =>
          if _ : j ∈ r then w ↑(Function.invFun (⇑emb) j) else 0 with hw''
        set z'' : Fin (d + 1) → E := fun j =>
          if h : j ∈ r then (↑(Function.invFun (⇑emb) j : ↥t) : E) else p₀ with hz''
        have hw''0 : ∀ j, 0 ≤ w'' j := by
          intro j
          by_cases hj : j ∈ r
          · simp only [hw'']
            rw [dite_eq_left hj]
            exact hw0 _ (Finset.mem_coe.mp (Function.invFun (⇑emb) j).2)
          · simp only [hw'']
            rw [dite_eq_right hj]
        have hw''1 : ∑ j, w'' j = 1 := by
          have hcongrw : ∀ i : ↥t,
              w ↑(Function.invFun (⇑emb) (emb i)) = w ↑i := fun i =>
            congrArg w
              (congrArg Subtype.val (Function.leftInverse_invFun emb.injective i))
          have e1 : ∑ j, w'' j = ∑ j ∈ r, w ↑(Function.invFun (⇑emb) j) := by
            rw [← Finset.sum_subset (Finset.subset_univ r) (fun j _ hjr => by
              simp only [hw'']
              rw [dite_eq_right hjr])]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            simp only [hw'']
            rw [dite_eq_left hj]
          have e2 : (∑ i ∈ (Finset.univ : Finset ↥t), w (i : E)) =
              ∑ y ∈ t, w y := by
            apply Finset.sum_bij (fun (i : ↥t) (_ : i ∈ (Finset.univ : Finset ↥t)) => (i : E))
            · intro i _
              exact Finset.mem_coe.mp i.2
            · intro i _ j _ h
              exact Subtype.ext h
            · intro y hy
              exact ⟨⟨y, Finset.mem_coe.mpr hy⟩, Finset.mem_univ _, rfl⟩
            · intro i _
              rfl
          rw [e1, hr, Finset.sum_map,
            Finset.sum_congr rfl (fun (x : ↥t) _ => hcongrw x), e2, hw1]
        let w' : Convexity.StdSimplex ℝ (Fin (d + 1)) :=
          { weights := Finsupp.equivFunOnFinite.symm w'',
            nonneg := by
              intro j
              simpa using hw''0 j
            total := by
              simpa [Finsupp.sum_fintype] using hw''1 }
        have hw'eq : ∀ j, w'.weights j = w'' j := fun j => rfl
        have hmem : (w', z'') ∈
            Set.univ ×ˢ {z : Fin (d + 1) → E | ∀ i, z i ∈ K} := by
          constructor
          · trivial
          · intro j
            by_cases hj : j ∈ r
            · simp only [hz'']
              rw [dite_eq_left hj]
              exact htK (Function.invFun (⇑emb) j).2
            · simp only [hz'']
              rw [dite_eq_right hj]
              exact hp₀
        refine ⟨(w', z''), hmem, ?_⟩
        change (∑ j, w'.weights j • z'' j) = x
        have e3 : (∑ j, w'.weights j • z'' j) = ∑ y ∈ t, w y • y := by
          have f1 : ∑ j, w'.weights j • z'' j
              = ∑ j ∈ r, w ↑(Function.invFun (⇑emb) j) •
                (↑(Function.invFun (⇑emb) j : ↥t) : E) := by
            rw [← Finset.sum_subset (Finset.subset_univ r) (fun j _ hjr => by
              rw [hw'eq j]
              simp only [hw'', hz'']
              rw [dite_eq_right hjr, dite_eq_right hjr, zero_smul])]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [hw'eq j]
            simp only [hw'', hz'']
            rw [dite_eq_left hj, dite_eq_left hj]
          have e4 : (∑ i ∈ (Finset.univ : Finset ↥t), w (i : E) • (i : E)) =
              ∑ y ∈ t, w y • y := by
            apply Finset.sum_bij (fun (i : ↥t) (_ : i ∈ (Finset.univ : Finset ↥t)) => (i : E))
            · intro i _
              exact Finset.mem_coe.mp i.2
            · intro i _ j _ h
              exact Subtype.ext h
            · intro y hy
              exact ⟨⟨y, Finset.mem_coe.mpr hy⟩, Finset.mem_univ _, rfl⟩
            · intro i _
              rfl
          have hcongrwz : ∀ i : ↥t, w ↑(Function.invFun (⇑emb) (emb i)) •
              (↑(Function.invFun (⇑emb) (emb i) : ↥t) : E) = w ↑i • ↑i := fun i => by
            rw [Function.leftInverse_invFun emb.injective i]
          rw [f1, hr, Finset.sum_map,
            Finset.sum_congr rfl (fun (x : ↥t) _ => hcongrwz x), e4]
        rw [e3, hxsum]
      · intro x hx
        obtain ⟨⟨w, z⟩, ⟨-, hzS⟩, rfl⟩ := hx
        exact Convex.sum_mem (convex_convexHull ℝ K) (t := Finset.univ)
          (fun i _ => w.nonneg i) (by simp)
          (fun i _ => subset_convexHull ℝ K (hzS i))
    have hdom : IsCompact
        ((Set.univ : Set (Convexity.StdSimplex ℝ (Fin (d + 1)))) ×ˢ
          {z : Fin (d + 1) → E | ∀ i, z i ∈ K}) :=
      isCompact_univ.prod (isCompact_pi_infinite (fun _ => hK))
    have hcont : Continuous
        (fun p : Convexity.StdSimplex ℝ (Fin (d + 1)) × (Fin (d + 1) → E) =>
          ∑ i, p.1.weights i • p.2 i) :=
      continuous_finsetSum _ fun i _ =>
        Continuous.smul
          ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_fst)
          ((continuous_apply i).comp continuous_snd)
    rw [himg]
    exact hdom.image hcont

end Convex.Straszewicz
