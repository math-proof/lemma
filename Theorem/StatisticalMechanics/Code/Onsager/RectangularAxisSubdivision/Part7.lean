/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part6


namespace StatMech.Onsager

open BaseCase

@[simp] theorem onsDirectionWordTorusDart_direction
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length]
    (k : Fin word.length) :
    (onsDirectionWordTorusDart L word k).2 = word.get (-k) := by
  simp [onsDirectionWordTorusDart]


theorem onsDirectionWordTorusDart_valid
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length]
    (mx my : ℤ)
    (hdisp : (word.map stepOf).sum = ((L : ℤ) * mx, (L : ℤ) * my)) :
    ∀ k : Fin word.length,
      (onsDirectionWordTorusDart L word k).1 =
        ons_dirStep L
          (onsDirectionWordTorusDart L word (k + 1)).2
          (onsDirectionWordTorusDart L word (k + 1)).1 := by
  let dir : Fin word.length → Fin 4 := word.get
  have htotal : ∑ i, stepOf (dir i) = ((L : ℤ) * mx, (L : ℤ) * my) := by
    rw [← List.sum_ofFn]
    change (List.ofFn fun i => stepOf (word.get i)).sum = _
    rw [show (List.ofFn fun i => stepOf (word.get i)) =
      word.map stepOf by
        simpa [List.get_eq_getElem] using
          (List.ofFn_getElem_eq_map word stepOf)]
    exact hdisp
  intro k
  change ons_reduceSite L (BaseCase.pos dir (-k)) =
    ons_dirStep L (dir (-(k + 1)))
      (ons_reduceSite L (BaseCase.pos dir (-(k + 1))))
  have hj : -(k + 1) + 1 = -k := by abel
  rw [← hj]
  cases word with
  | nil => exact False.elim ((NeZero.ne 0) rfl)
  | cons a tail =>
      by_cases hjlast : -(k + 1) = Fin.last tail.length
      · rw [hjlast]
        rw [Fin.last_add_one, NoDoubleWind.pos_zero]
        rw [← ons_reduceSite_add_step]
        rw [ons_pos_last_add_step]
        calc
          ons_reduceSite L 0 =
              ons_reduceSite L ((L : ℤ) * mx, (L : ℤ) * my) := by
                simp [ons_reduceSite]
          _ = ons_reduceSite L (∑ i, stepOf (dir i)) :=
            (congrArg (ons_reduceSite L) htotal).symm
      · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjlast
        rw [← hi]
        have hisucc : i.castSucc + 1 = i.succ := by
          apply Fin.ext
          simp
        rw [hisucc, ons_pos_succ_cast, ons_reduceSite_add_step]

theorem onsDirectionWordTorusDart_nonUturn
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length]
    (hcyclic : onsCyclicDirectionNonUturn word) :
    ∀ k : Fin word.length,
      (onsDirectionWordTorusDart L word k).2 ≠
        (onsDirectionWordTorusDart L word (k + 1)).2 + 2 := by
  have hword : List.ofFn word.get = word := List.ofFn_get word
  have hcyclic' : onsCyclicDirectionNonUturn (List.ofFn word.get) := by
    rwa [hword]
  intro k
  simp only [onsDirectionWordTorusDart_direction]
  change onsDirectionNonUturn (word.get (-(k + 1)))
    (word.get (-k))
  have h := onsCyclicDirectionNonUturn_ofFn_apply word.get hcyclic' (-(k + 1))
  have hidx : -(k + 1) + 1 = -k := by abel
  rw [hidx] at h
  exact h

theorem onsDirectionWordTorusDart_exponentX_sum
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length] :
    (∑ k, ons_dirExponentX
      (onsDirectionWordTorusDart L word k).2) =
      (word.map ons_dirExponentX).sum := by
  calc
    _ = ∑ k, ons_dirExponentX (word.get (-k)) := by simp
    _ = ∑ k, ons_dirExponentX (word.get k) :=
      Equiv.sum_comp (Equiv.neg (Fin word.length))
        (fun k ↦ ons_dirExponentX (word.get k))
    _ = _ := by
      rw [← List.sum_ofFn]
      congr 1
      simpa [List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map word ons_dirExponentX)

theorem onsDirectionWordTorusDart_exponentY_sum
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length] :
    (∑ k, ons_dirExponentY
      (onsDirectionWordTorusDart L word k).2) =
      (word.map ons_dirExponentY).sum := by
  calc
    _ = ∑ k, ons_dirExponentY (word.get (-k)) := by simp
    _ = ∑ k, ons_dirExponentY (word.get k) :=
      Equiv.sum_comp (Equiv.neg (Fin word.length))
        (fun k ↦ ons_dirExponentY (word.get k))
    _ = _ := by
      rw [← List.sum_ofFn]
      congr 1
      simpa [List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map word ons_dirExponentY)


theorem onsDiagonalShearDirectionWord_cyclicNonUturn
    (word : List (Fin 4))
    (hcyclic : onsCyclicDirectionNonUturn word) :
    onsCyclicDirectionNonUturn (onsDiagonalShearDirectionWord word) := by
  refine ⟨onsDiagonalShearDirectionWord_isChain word hcyclic.1, ?_⟩
  intro a ha b hb
  obtain ⟨d, hdlast, had⟩ :=
    onsDiagonalShearDirectionWord_getLast?_mem word ha
  obtain ⟨e, hehead, hbe⟩ :=
    onsDiagonalShearDirectionWord_head?_mem word hb
  exact onsDiagonalShearDirectionBlock_bridge d e
    (hcyclic.2 d hdlast e hehead) a had b hbe


theorem onsAnisotropicDirectionWord_cyclicNonUturn
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4))
    (hcyclic : onsCyclicDirectionNonUturn word) :
    onsCyclicDirectionNonUturn
      (onsAnisotropicDirectionWord width height word) := by
  refine ⟨onsAnisotropicDirectionWord_isChain width height hwidth hheight
    word hcyclic.1, ?_⟩
  intro a ha b hb
  obtain ⟨d, hdlast, had⟩ := onsAnisotropicDirectionWord_getLast?_mem
    width height hwidth hheight word ha
  obtain ⟨e, hehead, hbe⟩ := onsAnisotropicDirectionWord_head?_mem
    width height hwidth hheight word hb
  have hscale (x : Fin 4) : 0 < onsAnisotropicStepScale width height x := by
    fin_cases x <;> simp [onsAnisotropicStepScale, hwidth, hheight]
  exact onsReplicateDirection_bridge d e _ _ (hscale d) (hscale e)
    (hcyclic.2 d hdlast e hehead) a had b hbe

theorem onsDiagonalShearDirectionBlock_step_sum (d : Fin 4) :
    ((onsDiagonalShearDirectionBlock d).map stepOf).sum =
      ((stepOf d).1 + (stepOf d).2, (stepOf d).1 - (stepOf d).2) := by
  fin_cases d <;> rfl

theorem onsDiagonalShearDirectionWord_step_sum (word : List (Fin 4)) :
    ((onsDiagonalShearDirectionWord word).map stepOf).sum =
      (((word.map stepOf).sum).1 + ((word.map stepOf).sum).2,
        ((word.map stepOf).sum).1 - ((word.map stepOf).sum).2) := by
  induction word with
  | nil => simp [onsDiagonalShearDirectionWord, Prod.ext_iff]
  | cons d tail ih =>
      rw [onsDiagonalShearDirectionWord, List.flatMap_cons,
        List.map_append, List.sum_append,
        onsDiagonalShearDirectionBlock_step_sum]
      change _ +
        ((onsDiagonalShearDirectionWord tail).map stepOf).sum = _
      rw [ih]
      apply Prod.ext <;> simp <;> ring


end StatMech.Onsager
