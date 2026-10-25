/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity.Part2


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem isingFiniteWeightedPointPoissonBarrier_eq_localized
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) :
    isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit source =
      isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        (fun x => x = source) hconductance hpositive hhit := by
  rfl

theorem isingFiniteWeightedPointPoissonBarrier_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source x : V) (hx : boundary x) :
    isingFiniteWeightedPointPoissonBarrier G conductance boundary
      hconductance hpositive hhit source x = 0 := by
  rw [isingFiniteWeightedPointPoissonBarrier_eq_localized]
  exact isingFiniteWeightedLocalizedPoissonBarrier_boundary
    G conductance boundary (fun y => y = source)
    hconductance hpositive hhit x hx

theorem isingFiniteWeightedPointPoissonBarrier_laplacian_source
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) (hsource : Not (boundary source)) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit source) source = -1 := by
  rw [isingFiniteWeightedPointPoissonBarrier_eq_localized]
  exact isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
    G conductance boundary (fun y => y = source)
    hconductance hpositive hhit source hsource rfl

theorem isingFiniteWeightedPointPoissonBarrier_laplacian_off_source
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source x : V) (hx : Not (boundary x)) (hxs : x ≠ source) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit source) x = 0 := by
  rw [isingFiniteWeightedPointPoissonBarrier_eq_localized]
  exact isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
    G conductance boundary (fun y => y = source)
    hconductance hpositive hhit x hx hxs

theorem isingFiniteWeightedPointPoissonBarrier_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) :
    forall x, 0 <= isingFiniteWeightedPointPoissonBarrier
      G conductance boundary hconductance hpositive hhit source x := by
  rw [isingFiniteWeightedPointPoissonBarrier_eq_localized]
  exact isingFiniteWeightedLocalizedPoissonBarrier_nonneg
    G conductance boundary (fun y => y = source)
    hconductance hpositive hhit


theorem isingFiniteWeightedPointPoissonBarrier_comm
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (hsymm : forall x y, conductance x y = conductance y x)
    (a b : V) (ha : Not (boundary a)) (hb : Not (boundary b)) :
    isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit a b =
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit b a := by
  classical
  let Pa := isingFiniteWeightedPointPoissonBarrier G conductance boundary
    hconductance hpositive hhit a
  let Pb := isingFiniteWeightedPointPoissonBarrier G conductance boundary
    hconductance hpositive hhit b
  have hpair := isingFiniteWeightedLaplacian_pair_comm
    conductance hsymm Pa Pb
  have hleft :
      (∑ x, Pa x * isingFiniteWeightedLaplacian conductance Pb x) =
        -Pa b := by
    calc
      _ = ∑ x, if x = b then -Pa x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hxb : boundary x
        · have hPa : Pa x = 0 := by
            exact isingFiniteWeightedPointPoissonBarrier_boundary
              G conductance boundary hconductance hpositive hhit a x hxb
          by_cases hEq : x = b
          · subst x
            exact False.elim (hb hxb)
          · simp [hPa, hEq]
        · by_cases hEq : x = b
          · subst x
            rw [isingFiniteWeightedPointPoissonBarrier_laplacian_source
              G conductance boundary hconductance hpositive hhit b hb]
            simp
          · rw [isingFiniteWeightedPointPoissonBarrier_laplacian_off_source
              G conductance boundary hconductance hpositive hhit b x hxb hEq]
            simp [hEq]
      _ = -Pa b := by simp
  have hright :
      (∑ x, Pb x * isingFiniteWeightedLaplacian conductance Pa x) =
        -Pb a := by
    calc
      _ = ∑ x, if x = a then -Pb x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hxa : boundary x
        · have hPb : Pb x = 0 := by
            exact isingFiniteWeightedPointPoissonBarrier_boundary
              G conductance boundary hconductance hpositive hhit b x hxa
          by_cases hEq : x = a
          · subst x
            exact False.elim (ha hxa)
          · simp [hPb, hEq]
        · by_cases hEq : x = a
          · subst x
            rw [isingFiniteWeightedPointPoissonBarrier_laplacian_source
              G conductance boundary hconductance hpositive hhit a ha]
            simp
          · rw [isingFiniteWeightedPointPoissonBarrier_laplacian_off_source
              G conductance boundary hconductance hpositive hhit a x hxa hEq]
            simp [hEq]
      _ = -Pb a := by simp
  rw [hleft, hright] at hpair
  dsimp only [Pa, Pb] at hpair ⊢
  linarith


theorem isingFiniteWeightedPointPoissonBarrier_le_of_superharmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) (hsource : Not (boundary source)) (barrier : V -> Real)
    (hboundary : forall x, boundary x -> 0 <= barrier x)
    (hsourceLap : isingFiniteWeightedLaplacian conductance barrier source <= -1)
    (hoffLap : forall x, Not (boundary x) -> x ≠ source ->
      isingFiniteWeightedLaplacian conductance barrier x <= 0) :
    forall x, isingFiniteWeightedPointPoissonBarrier
      G conductance boundary hconductance hpositive hhit source x <=
        barrier x := by
  apply isingFiniteWeighted_laplacian_comparison
    G conductance boundary
    (isingFiniteWeightedPointPoissonBarrier G conductance boundary
      hconductance hpositive hhit source)
    barrier hconductance hpositive hhit
  · intro x hx
    rw [isingFiniteWeightedPointPoissonBarrier_boundary
      G conductance boundary hconductance hpositive hhit source x hx]
    exact hboundary x hx
  · intro x hx
    by_cases hxs : x = source
    · subst x
      rw [isingFiniteWeightedPointPoissonBarrier_laplacian_source
        G conductance boundary hconductance hpositive hhit source hsource]
      exact hsourceLap
    · rw [isingFiniteWeightedPointPoissonBarrier_laplacian_off_source
        G conductance boundary hconductance hpositive hhit source x hx hxs]
      exact hoffLap x hx hxs


theorem isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b) :
    isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit =
      ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional,
        isingFiniteWeightedPointPoissonBarrier G conductance boundary
          hconductance hpositive hhit z := by
  classical
  have hrhs :
      (fun x => if boundary x then (0 : Real) else
        if exceptional x then -1 else 0) =
        ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional,
          (fun x => if boundary x then (0 : Real) else
            if x = z then -1 else 0) := by
    funext x
    by_cases hxb : boundary x
    · simp [hxb]
    · by_cases hxe : exceptional x
      · simp [isingFiniteWeightedInteriorExceptionalSources, hxb, hxe]
      · simp [isingFiniteWeightedInteriorExceptionalSources, hxb, hxe]
  unfold isingFiniteWeightedLocalizedPoissonBarrier
    isingFiniteWeightedPointPoissonBarrier
  calc
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit
        (fun x => if boundary x then 0 else if exceptional x then -1 else 0) =
      isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit
        (∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
          boundary exceptional,
          (fun x => if boundary x then 0 else if x = z then -1 else 0)) :=
      congrArg (isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit) hrhs
    _ = ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
          boundary exceptional,
        isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit
          (fun x => if boundary x then 0 else if x = z then -1 else 0) :=
      isingFiniteWeightedDirichletSolve_sum G conductance boundary
        hconductance hpositive hhit _ _


theorem isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (x : V) (B : Real)
    (hpoint : forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional ->
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit z x <= B) :
    isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x <=
      (isingFiniteWeightedInteriorExceptionalSources
        boundary exceptional).card * B := by
  rw [isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point]
  simp only [Finset.sum_apply]
  calc
    (∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
        boundary exceptional,
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit z x) <=
      ∑ _z ∈ isingFiniteWeightedInteriorExceptionalSources
        boundary exceptional, B := by
          apply Finset.sum_le_sum
          intro z hz
          exact hpoint z hz
    _ = (isingFiniteWeightedInteriorExceptionalSources
          boundary exceptional).card * B := by
      simp


theorem isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (hsymm : forall x y, conductance x y = conductance y x)
    (x : V) (hx : Not (boundary x)) (B : Real)
    (hpoint : forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional ->
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit x z <= B) :
    isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x <=
      (isingFiniteWeightedInteriorExceptionalSources
        boundary exceptional).card * B := by
  apply isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul
    G conductance boundary exceptional hconductance hpositive hhit x B
  intro z hz
  have hz' : Not (boundary z) := by
    have hzpair : Not (boundary z) ∧ exceptional z := by
      simpa [isingFiniteWeightedInteriorExceptionalSources] using hz
    exact hzpair.1
  rw [isingFiniteWeightedPointPoissonBarrier_comm
    G conductance boundary hconductance hpositive hhit hsymm z x hz' hx]
  exact hpoint z hz

end
end StatMech.Universality
