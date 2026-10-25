/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Def.StatisticalMechanics.Code.Universality.HexStandardCount


namespace StatMech.Universality

open Filter HexWalk Topology

open scoped Real Topology

noncomputable section

@[simp] theorem hexRootedVertices_head (h : ℤ) (ts : List ℤ) :
    (hexRootedVertices h ts).headI = 0 := by
  cases ts <;> simp [hexRootedVertices, verticesAux]

@[simp] theorem verticesAux_headI (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (verticesAux m h ts).headI = m + halfStep h := by
  cases ts <;> rfl


theorem verticesAux_injective_of_legal :
    ∀ (s : List ℤ) (m : ℂ) (h : ℤ),
      (∀ u ∈ s, u = 1 ∨ u = -1) →
      ∀ t : List ℤ, (∀ u ∈ t, u = 1 ∨ u = -1) →
        verticesAux m h s = verticesAux m h t → s = t := by
  intro s
  induction s with
  | nil =>
      intro m h hs t ht heq
      have hlen := congrArg List.length heq
      have htlen := length_verticesAux m h t
      simp only [verticesAux_nil, List.length_singleton] at hlen
      rw [htlen] at hlen
      have : t.length = 0 := by omega
      exact (List.length_eq_zero_iff.mp this).symm
  | cons u us ih =>
      intro m h hs t ht heq
      cases t with
      | nil =>
          have hlen := congrArg List.length heq
          simp [length_verticesAux] at hlen
      | cons v vs =>
          have hu : u = 1 ∨ u = -1 := hs u (by simp)
          have hv : v = 1 ∨ v = -1 := ht v (by simp)
          have htails :
              verticesAux (m + halfStep h + halfStep (h + u)) (h + u) us =
                verticesAux (m + halfStep h + halfStep (h + v)) (h + v) vs := by
            change
              (m + halfStep h) ::
                  verticesAux (m + halfStep h + halfStep (h + u)) (h + u) us =
                (m + halfStep h) ::
                  verticesAux (m + halfStep h + halfStep (h + v)) (h + v) vs at heq
            exact (List.cons.inj heq).2
          have hheads := congrArg List.headI htails
          simp only [verticesAux_headI] at hheads
          have hstep : halfStep (h + u) = halfStep (h + v) := by
            linear_combination (1 / 2 : ℂ) * hheads
          have hmod : (6 : ℤ) ∣ (h + u - (h + v)) :=
            (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj hstep)
          have huv : u = v := by
            rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
            · rfl
            · rcases hmod with ⟨k, hk⟩
              omega
            · rcases hmod with ⟨k, hk⟩
              omega
            · rfl
          subst v
          have hus : ∀ z ∈ us, z = 1 ∨ z = -1 :=
            fun z hz => hs z (by simp [hz])
          have hvs : ∀ z ∈ vs, z = 1 ∨ z = -1 :=
            fun z hz => ht z (by simp [hz])
          exact congrArg (List.cons u)
            (ih (m + halfStep h + halfStep (h + u)) (h + u)
              hus vs hvs htails)


end
end StatMech.Universality
