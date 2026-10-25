/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part4


namespace StatMech.Onsager

open BaseCase

theorem onsDirectionNonUturn_self (d : Fin 4) :
    onsDirectionNonUturn d d := by
  fin_cases d <;> simp [onsDirectionNonUturn]

theorem onsDiagonalShearDirectionBlock_isChain (d : Fin 4) :
    List.IsChain onsDirectionNonUturn
      (onsDiagonalShearDirectionBlock d) := by
  fin_cases d <;> simp [onsDiagonalShearDirectionBlock,
    onsDirectionNonUturn]

theorem onsDiagonalShearDirectionBlock_bridge
    (d e : Fin 4) (hde : onsDirectionNonUturn d e) :
    ∀ a ∈ (onsDiagonalShearDirectionBlock d).getLast?,
      ∀ b ∈ (onsDiagonalShearDirectionBlock e).head?,
        onsDirectionNonUturn a b := by
  fin_cases d <;> fin_cases e <;>
    simp [onsDiagonalShearDirectionBlock, onsDirectionNonUturn] at hde ⊢


theorem onsDiagonalShearDirectionWord_isChain
    (word : List (Fin 4))
    (hchain : List.IsChain onsDirectionNonUturn word) :
    List.IsChain onsDirectionNonUturn
      (onsDiagonalShearDirectionWord word) := by
  induction word with
  | nil => exact List.IsChain.nil
  | cons d tail ih =>
      rw [onsDiagonalShearDirectionWord_cons]
      apply (onsDiagonalShearDirectionBlock_isChain d).append
        (ih (List.isChain_cons.mp hchain).2)
      cases tail with
      | nil => simp
      | cons e rest =>
          have hhead : (onsDiagonalShearDirectionWord (e :: rest)).head? =
              (onsDiagonalShearDirectionBlock e).head? := by
            rw [onsDiagonalShearDirectionWord_cons]
            fin_cases e <;> rfl
          rw [hhead]
          exact onsDiagonalShearDirectionBlock_bridge d e
            (List.isChain_cons_cons.mp hchain).1

theorem onsReplicateDirection_isChain (d : Fin 4) (n : ℕ) :
    List.IsChain onsDirectionNonUturn (List.replicate n d) := by
  induction n with
  | zero => exact List.IsChain.nil
  | succ n ih =>
      rw [List.replicate_succ]
      apply List.IsChain.cons ih
      simp only [List.head?_replicate]
      split_ifs
      · simp
      · simpa using onsDirectionNonUturn_self d

theorem onsReplicateDirection_bridge
    (d e : Fin 4) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hde : onsDirectionNonUturn d e) :
    ∀ a ∈ (List.replicate m d).getLast?,
      ∀ b ∈ (List.replicate n e).head?,
        onsDirectionNonUturn a b := by
  simp [List.getLast?_replicate, List.head?_replicate, hm.ne', hn.ne', hde]


theorem onsAnisotropicDirectionWord_isChain
    (width height : ℕ)
    (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4))
    (hchain : List.IsChain onsDirectionNonUturn word) :
    List.IsChain onsDirectionNonUturn
      (onsAnisotropicDirectionWord width height word) := by
  have hscale (d : Fin 4) : 0 < onsAnisotropicStepScale width height d := by
    fin_cases d <;> simp [onsAnisotropicStepScale, hwidth, hheight]
  induction word with
  | nil => exact List.IsChain.nil
  | cons d tail ih =>
      rw [onsAnisotropicDirectionWord_cons]
      apply (onsReplicateDirection_isChain d _).append
        (ih (List.isChain_cons.mp hchain).2)
      cases tail with
      | nil => simp
      | cons e rest =>
          simpa [onsAnisotropicDirectionWord_cons,
            List.head?_replicate, (hscale e).ne'] using
            (onsReplicateDirection_bridge d e _ _ (hscale d) (hscale e)
              (List.isChain_cons_cons.mp hchain).1)

theorem onsDiagonalShearDirectionWord_head?_mem
    (word : List (Fin 4)) {a : Fin 4}
    (ha : a ∈ (onsDiagonalShearDirectionWord word).head?) :
    ∃ d ∈ word.head?,
      a ∈ (onsDiagonalShearDirectionBlock d).head? := by
  cases word with
  | nil => simp at ha
  | cons d tail =>
      refine ⟨d, by simp, ?_⟩
      fin_cases d <;>
        simpa [onsDiagonalShearDirectionWord_cons,
          onsDiagonalShearDirectionBlock] using ha

theorem onsDiagonalShearDirectionWord_getLast?_mem
    (word : List (Fin 4)) {a : Fin 4}
    (ha : a ∈ (onsDiagonalShearDirectionWord word).getLast?) :
    ∃ d ∈ word.getLast?,
      a ∈ (onsDiagonalShearDirectionBlock d).getLast? := by
  induction word with
  | nil => simp at ha
  | cons d tail ih =>
      cases tail with
      | nil =>
          refine ⟨d, by simp, ?_⟩
          simpa [onsDiagonalShearDirectionWord_cons] using ha
      | cons e rest =>
          have hne : onsDiagonalShearDirectionWord (e :: rest) ≠ [] := by
            fin_cases e <;>
              simp [onsDiagonalShearDirectionWord_cons,
                onsDiagonalShearDirectionBlock]
          have ha' : a ∈
              (onsDiagonalShearDirectionWord (e :: rest)).getLast? := by
            rw [onsDiagonalShearDirectionWord_cons,
              List.getLast?_append_of_ne_nil _ hne] at ha
            exact ha
          obtain ⟨x, hxlast, hax⟩ := ih ha'
          exact ⟨x, by simpa using hxlast, hax⟩

theorem onsAnisotropicDirectionWord_head?_mem
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4)) {a : Fin 4}
    (ha : a ∈ (onsAnisotropicDirectionWord width height word).head?) :
    ∃ d ∈ word.head?,
      a ∈ (List.replicate
        (onsAnisotropicStepScale width height d) d).head? := by
  have hscale (d : Fin 4) : 0 < onsAnisotropicStepScale width height d := by
    fin_cases d <;> simp [onsAnisotropicStepScale, hwidth, hheight]
  cases word with
  | nil => simp at ha
  | cons d tail =>
      refine ⟨d, by simp, ?_⟩
      simpa [onsAnisotropicDirectionWord_cons, List.head?_replicate,
        (hscale d).ne'] using ha

theorem onsAnisotropicDirectionWord_getLast?_mem
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4)) {a : Fin 4}
    (ha : a ∈ (onsAnisotropicDirectionWord width height word).getLast?) :
    ∃ d ∈ word.getLast?,
      a ∈ (List.replicate
        (onsAnisotropicStepScale width height d) d).getLast? := by
  have hscale (d : Fin 4) : 0 < onsAnisotropicStepScale width height d := by
    fin_cases d <;> simp [onsAnisotropicStepScale, hwidth, hheight]
  induction word with
  | nil => simp at ha
  | cons d tail ih =>
      cases tail with
      | nil =>
          refine ⟨d, by simp, ?_⟩
          simpa [onsAnisotropicDirectionWord_cons] using ha
      | cons e rest =>
          have hne :
              onsAnisotropicDirectionWord width height (e :: rest) ≠ [] := by
            intro hnil
            have hlen := congrArg List.length hnil
            simp [onsAnisotropicDirectionWord_cons,
              (hscale e).ne'] at hlen
          have ha' : a ∈
              (onsAnisotropicDirectionWord width height
                (e :: rest)).getLast? := by
            rw [onsAnisotropicDirectionWord_cons,
              List.getLast?_append_of_ne_nil _ hne] at ha
            exact ha
          obtain ⟨x, hxlast, hax⟩ := ih ha'
          exact ⟨x, by simpa using hxlast, hax⟩


end StatMech.Onsager
