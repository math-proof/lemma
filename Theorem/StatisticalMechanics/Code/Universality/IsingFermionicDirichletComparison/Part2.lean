/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part2
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem IsingFiniteGraphHarmonicOn.add_const
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {boundary : V → Prop} {f : V → ℝ}
    (hf : IsingFiniteGraphHarmonicOn G boundary f) (c : ℝ) :
    IsingFiniteGraphHarmonicOn G boundary (fun x ↦ f x + c) := by
  intro x hx
  rw [isingFiniteGraphLaplacian_add_const]
  exact hf x hx


theorem isingFiniteGraph_laplacian_comparison
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (u h : V → ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hboundary : ∀ x, boundary x → u x ≤ h x)
    (hlap : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G h x ≤
        isingFiniteGraphLaplacian G u x) :
    ∀ x, u x ≤ h x := by
  classical
  let d : V → ℝ := fun x => u x - h x
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ d
    Finset.univ_nonempty
  have hmax (x : V) : d x ≤ d m := hm x (Finset.mem_univ x)
  by_contra hnot
  have hnot' : ∃ z, h z < u z := by
    simpa only [not_forall, not_le] using hnot
  obtain ⟨z, hz⟩ := hnot'
  have hmpos : 0 < d m := lt_of_lt_of_le (sub_pos.mpr hz) (hmax z)
  have hstep {x y : V} (hx : d x = d m) (hxy : G.Adj x y) : d y = d m := by
    have hxnot : ¬ boundary x := by
      intro hxb
      have hxbnd := hboundary x hxb
      have hdx : d x ≤ 0 := sub_nonpos.mpr hxbnd
      linarith
    have hterm : ∀ w ∈ G.neighborFinset x, d w - d x ≤ 0 := by
      intro w hw
      rw [hx]
      exact sub_nonpos.mpr (hmax w)
    have hsumle : (∑ w ∈ G.neighborFinset x, (d w - d x)) ≤ 0 :=
      Finset.sum_nonpos fun w hw => hterm w hw
    have hsumge : 0 ≤ ∑ w ∈ G.neighborFinset x, (d w - d x) := by
      have hxu := hlap x hxnot
      calc
        0 ≤ isingFiniteGraphLaplacian G u x -
            isingFiniteGraphLaplacian G h x := sub_nonneg.mpr hxu
        _ = ∑ w ∈ G.neighborFinset x, (d w - d x) := by
          unfold isingFiniteGraphLaplacian
          rw [← Finset.sum_sub_distrib]
          apply congrArg
            (fun f : V → ℝ => ∑ w ∈ G.neighborFinset x, f w)
          funext w
          dsimp only [d]
          ring
    have hsum : (∑ w ∈ G.neighborFinset x, (d w - d x)) = 0 :=
      le_antisymm hsumle hsumge
    have hyMem : y ∈ G.neighborFinset x := by simpa using hxy
    have hyzero :=
      (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hsum y hyMem
    linarith
  obtain ⟨b, hb, hmb⟩ := hhit m
  obtain ⟨p⟩ := hmb
  have hwalk : ∀ {x y : V}, G.Walk x y → d x = d m → d y = d m := by
    intro x y q
    induction q with
    | nil => exact fun hx => hx
    | @cons x y z hxy q ih =>
        intro hx
        exact ih (hstep hx hxy)
  have hpath : d b = d m := hwalk p rfl
  have hbnd := hboundary b hb
  have hdb : d b ≤ 0 := sub_nonpos.mpr hbnd
  linarith


theorem isingFiniteGraph_subharmonic_le_harmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (u h : V → ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteGraphSubharmonicOn G boundary u)
    (hh : IsingFiniteGraphHarmonicOn G boundary h)
    (hboundary : ∀ x, boundary x → u x ≤ h x) :
    ∀ x, u x ≤ h x := by
  apply isingFiniteGraph_laplacian_comparison G boundary u h hhit hboundary
  intro x hx
  rw [hh x hx]
  exact hu x hx


theorem isingFiniteGraph_harmonic_le_superharmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (h u : V → ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hh : IsingFiniteGraphHarmonicOn G boundary h)
    (hu : IsingFiniteGraphSuperharmonicOn G boundary u)
    (hboundary : ∀ x, boundary x → h x ≤ u x) :
    ∀ x, h x ≤ u x := by
  apply isingFiniteGraph_laplacian_comparison G boundary h u hhit hboundary
  intro x hx
  rw [hh x hx]
  exact hu x hx


theorem isingFiniteGraph_harmonic_boundary_stability
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (u v : V → ℝ) (eps : ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteGraphHarmonicOn G boundary u)
    (hv : IsingFiniteGraphHarmonicOn G boundary v)
    (hboundary : ∀ x, boundary x → |u x - v x| ≤ eps) :
    ∀ x, |u x - v x| ≤ eps := by
  have huv : ∀ x, u x ≤ v x + eps := by
    apply isingFiniteGraph_subharmonic_le_harmonic G boundary u
      (fun x ↦ v x + eps) hhit
    · intro x hx
      rw [hu x hx]
    · exact hv.add_const eps
    · intro x hx
      have hb := hboundary x hx
      rw [abs_le] at hb
      linarith
  have hvu : ∀ x, v x ≤ u x + eps := by
    apply isingFiniteGraph_subharmonic_le_harmonic G boundary v
      (fun x ↦ u x + eps) hhit
    · intro x hx
      rw [hv x hx]
    · exact hu.add_const eps
    · intro x hx
      have hb := hboundary x hx
      rw [abs_le] at hb
      linarith
  intro x
  rw [abs_le]
  constructor <;> linarith [huv x, hvu x]


theorem isingFiniteGraphDirichletOperator_injective
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    Function.Injective (isingFiniteGraphDirichletOperator G boundary) := by
  classical
  intro f g hfg
  have hopzero :
      isingFiniteGraphDirichletOperator G boundary (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hboundary : ∀ x, boundary x → (f - g) x = 0 := by
    intro x hx
    have h := congrFun hopzero x
    change (if boundary x then (f - g) x else
      isingFiniteGraphLaplacian G (f - g) x) = 0 at h
    simpa [hx] using h
  have hharmonic :
      IsingFiniteGraphHarmonicOn G boundary (f - g) := by
    intro x hx
    have h := congrFun hopzero x
    change (if boundary x then (f - g) x else
      isingFiniteGraphLaplacian G (f - g) x) = 0 at h
    simpa [hx] using h
  have hzero : IsingFiniteGraphHarmonicOn G boundary (fun _ ↦ 0) := by
    intro x hx
    unfold isingFiniteGraphLaplacian
    simp
  have hstable := isingFiniteGraph_harmonic_boundary_stability
    G boundary (f - g) (fun _ ↦ 0) 0 hhit hharmonic hzero
    (by
      intro x hx
      simp [hboundary x hx])
  apply sub_eq_zero.mp
  funext x
  have hx := hstable x
  simp only [Pi.sub_apply, sub_zero] at hx
  exact abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))


theorem isingFiniteGraph_exists_harmonic_extension
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (data : V → ℝ) :
    ∃ harmonic : V → ℝ,
      IsingFiniteGraphHarmonicOn G boundary harmonic ∧
        ∀ x, boundary x → harmonic x = data x := by
  classical
  let rhs : V → ℝ := fun x ↦ if boundary x then data x else 0
  have hsurj : Function.Surjective
      (isingFiniteGraphDirichletOperator G boundary) :=
    LinearMap.injective_iff_surjective.mp
      (isingFiniteGraphDirichletOperator_injective G boundary hhit)
  obtain ⟨harmonic, hharmonic⟩ := hsurj rhs
  refine ⟨harmonic, ?_, ?_⟩
  · intro x hx
    have h := congrFun hharmonic x
    change (if boundary x then harmonic x else
      isingFiniteGraphLaplacian G harmonic x) = rhs x at h
    simpa [rhs, hx] using h
  · intro x hx
    have h := congrFun hharmonic x
    change (if boundary x then harmonic x else
      isingFiniteGraphLaplacian G harmonic x) = rhs x at h
    simpa [rhs, hx] using h


end
end StatMech.Universality
