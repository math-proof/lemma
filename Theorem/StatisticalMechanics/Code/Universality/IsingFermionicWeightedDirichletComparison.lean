/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteWeightedLaplacian_const
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (c : Real) (x : V) :
    isingFiniteWeightedLaplacian conductance (fun _ ↦ c) x = 0 := by
  classical
  simp [isingFiniteWeightedLaplacian]


theorem isingFiniteWeighted_laplacian_comparison
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (u h : V → Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hboundary : ∀ x, boundary x → u x ≤ h x)
    (hlap : ∀ x, ¬ boundary x →
      isingFiniteWeightedLaplacian conductance h x ≤
        isingFiniteWeightedLaplacian conductance u x) :
    ∀ x, u x ≤ h x := by
  classical
  let d : V → Real := fun x ↦ u x - h x
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ d
    Finset.univ_nonempty
  have hmax (x : V) : d x ≤ d m := hm x (Finset.mem_univ x)
  by_contra hnot
  have hnot' : ∃ z, h z < u z := by
    simpa only [not_forall, not_le] using hnot
  obtain ⟨z, hz⟩ := hnot'
  have hmpos : 0 < d m := lt_of_lt_of_le (sub_pos.mpr hz) (hmax z)
  have hstep {x y : V} (hx : d x = d m) (hxy : G.Adj x y) :
      d y = d m := by
    have hxnot : ¬ boundary x := by
      intro hxb
      have hxbnd := hboundary x hxb
      have hdx : d x ≤ 0 := sub_nonpos.mpr hxbnd
      linarith
    have hterm : ∀ w ∈ (Finset.univ : Finset V),
        conductance x w * (d w - d x) ≤ 0 := by
      intro w _
      exact mul_nonpos_of_nonneg_of_nonpos (hconductance x w)
        (sub_nonpos.mpr (by rw [hx]; exact hmax w))
    have hsumle :
        (∑ w, conductance x w * (d w - d x)) ≤ 0 :=
      Finset.sum_nonpos hterm
    have hsumge :
        0 ≤ ∑ w, conductance x w * (d w - d x) := by
      have hxu := hlap x hxnot
      calc
        0 ≤ isingFiniteWeightedLaplacian conductance u x -
            isingFiniteWeightedLaplacian conductance h x := sub_nonneg.mpr hxu
        _ = ∑ w, conductance x w * (d w - d x) := by
          unfold isingFiniteWeightedLaplacian
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro w _
          dsimp only [d]
          ring
    have hsum : (∑ w, conductance x w * (d w - d x)) = 0 :=
      le_antisymm hsumle hsumge
    have hyzero : conductance x y * (d y - d x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hsum y (Finset.mem_univ y)
    have hdiff : d y - d x = 0 := by
      rcases mul_eq_zero.mp hyzero with hc | hd
      · exact False.elim ((ne_of_gt (hpositive hxy)) hc)
      · exact hd
    linarith
  obtain ⟨b, hb, hmb⟩ := hhit m
  obtain ⟨p⟩ := hmb
  have hwalk : ∀ {x y : V}, G.Walk x y → d x = d m → d y = d m := by
    intro x y q
    induction q with
    | nil => exact fun hx ↦ hx
    | @cons x y z hxy q ih =>
        intro hx
        exact ih (hstep hx hxy)
  have hpath : d b = d m := hwalk p rfl
  have hbnd := hboundary b hb
  have hdb : d b ≤ 0 := sub_nonpos.mpr hbnd
  linarith

theorem isingFiniteWeighted_subharmonic_le_harmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (u h : V → Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteWeightedSubharmonicOn conductance boundary u)
    (hh : IsingFiniteWeightedHarmonicOn conductance boundary h)
    (hboundary : ∀ x, boundary x → u x ≤ h x) :
    ∀ x, u x ≤ h x := by
  apply isingFiniteWeighted_laplacian_comparison G conductance boundary
    u h hconductance hpositive hhit hboundary
  intro x hx
  rw [hh x hx]
  exact hu x hx

theorem isingFiniteWeighted_harmonic_le_superharmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (h u : V → Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hh : IsingFiniteWeightedHarmonicOn conductance boundary h)
    (hu : IsingFiniteWeightedSuperharmonicOn conductance boundary u)
    (hboundary : ∀ x, boundary x → h x ≤ u x) :
    ∀ x, h x ≤ u x := by
  apply isingFiniteWeighted_laplacian_comparison G conductance boundary
    h u hconductance hpositive hhit hboundary
  intro x hx
  rw [hh x hx]
  exact hu x hx


theorem isingFiniteWeighted_subharmonic_le_const
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (u : V → Real) (c : Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteWeightedSubharmonicOn conductance boundary u)
    (hboundary : ∀ x, boundary x → u x ≤ c) :
    ∀ x, u x ≤ c := by
  apply isingFiniteWeighted_subharmonic_le_harmonic G conductance boundary
    u (fun _ ↦ c) hconductance hpositive hhit hu
  · intro x hx
    exact isingFiniteWeightedLaplacian_const conductance c x
  · exact hboundary


theorem isingFiniteWeighted_const_le_superharmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (u : V → Real) (c : Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteWeightedSuperharmonicOn conductance boundary u)
    (hboundary : ∀ x, boundary x → c ≤ u x) :
    ∀ x, c ≤ u x := by
  apply isingFiniteWeighted_harmonic_le_superharmonic G conductance boundary
    (fun _ ↦ c) u hconductance hpositive hhit
  · intro x hx
    exact isingFiniteWeightedLaplacian_const conductance c x
  · exact hu
  · exact hboundary


theorem isingFiniteWeightedLaplacian_add
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (f g : V → Real) (x : V) :
    isingFiniteWeightedLaplacian conductance (fun y ↦ f y + g y) x =
      isingFiniteWeightedLaplacian conductance f x +
        isingFiniteWeightedLaplacian conductance g x := by
  classical
  unfold isingFiniteWeightedLaplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring


theorem isingFiniteWeightedLaplacian_const_mul
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (c : Real) (f : V → Real) (x : V) :
    isingFiniteWeightedLaplacian conductance (fun y ↦ c * f y) x =
      c * isingFiniteWeightedLaplacian conductance f x := by
  classical
  unfold isingFiniteWeightedLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring


theorem isingFiniteWeightedLaplacian_add_const
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (f : V → Real) (c : Real) (x : V) :
    isingFiniteWeightedLaplacian conductance (fun y ↦ f y + c) x =
      isingFiniteWeightedLaplacian conductance f x := by
  rw [isingFiniteWeightedLaplacian_add,
    isingFiniteWeightedLaplacian_const]
  ring


end
end StatMech.Universality
