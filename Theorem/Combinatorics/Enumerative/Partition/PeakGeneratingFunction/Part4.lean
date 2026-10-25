/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part7


namespace MetaMathlibExt

lemma pgf_rg_join_iff {n k : ℕ} (i : Fin n) (u : Fin i.val → Fin k)
    (v : Fin (n - 1 - i.val) → Fin (k + 1)) :
    IsSurjectiveRestrictedGrowthString (pgf_joinFirst ⟨i, u, v⟩) ↔
      IsSurjectiveRestrictedGrowthString u := by
  constructor
  · rintro ⟨_, hgrowth⟩
    constructor
    · intro a
      have halt : a.castSucc < Fin.last k := Fin.castSucc_lt_last a
      obtain ⟨j, hji, hj⟩ := hgrowth i a.castSucc (by
        rw [pgf_joinFirst_top]
        exact halt)
      let j' : Fin i.val := ⟨j.val, hji⟩
      refine ⟨j', ?_⟩
      apply Fin.castSucc_injective
      calc
        (u j').castSucc = pgf_joinFirst ⟨i, u, v⟩
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := (pgf_joinFirst_before i u v j').symm
        _ = pgf_joinFirst ⟨i, u, v⟩ j := by
          congr 1
        _ = a.castSucc := hj
    · intro j a ha
      let jg : Fin n := ⟨j.val, lt_trans j.isLt i.isLt⟩
      have hjg : pgf_joinFirst ⟨i, u, v⟩ jg = (u j).castSucc := by
        exact pgf_joinFirst_before i u v j
      obtain ⟨l, hlj, hl⟩ := hgrowth jg a.castSucc (by
        rw [hjg]
        exact Fin.castSucc_lt_castSucc_iff.mpr ha)
      let l' : Fin i.val := ⟨l.val, lt_trans hlj j.isLt⟩
      refine ⟨l', hlj, ?_⟩
      apply Fin.castSucc_injective
      calc
        (u l').castSucc = pgf_joinFirst ⟨i, u, v⟩
            ⟨l'.val, lt_trans l'.isLt i.isLt⟩ := (pgf_joinFirst_before i u v l').symm
        _ = pgf_joinFirst ⟨i, u, v⟩ l := by
          congr 1
        _ = a.castSucc := hl
  · rintro ⟨hsurj, hgrowth⟩
    constructor
    · intro a
      by_cases ha : a = Fin.last k
      · exact ⟨i, by simpa [ha] using pgf_joinFirst_top ⟨i, u, v⟩⟩
      · obtain ⟨j, hj⟩ := hsurj (a.castPred ha)
        refine ⟨⟨j.val, lt_trans j.isLt i.isLt⟩, ?_⟩
        rw [show (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin n) =
            ⟨j.val, lt_trans j.isLt i.isLt⟩ by rfl,
          pgf_joinFirst_before]
        rw [hj, Fin.castSucc_castPred]
    · intro j a ha
      by_cases hji : j.val < i.val
      · let j' : Fin i.val := ⟨j.val, hji⟩
        have hj : pgf_joinFirst ⟨i, u, v⟩ j = (u j').castSucc := by
          calc
            pgf_joinFirst ⟨i, u, v⟩ j = pgf_joinFirst ⟨i, u, v⟩
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
              congr 1
            _ = (u j').castSucc := pgf_joinFirst_before i u v j'
        have hane : a ≠ Fin.last k := by
          intro hatop
          rw [hatop, hj] at ha
          exact (Fin.castSucc_lt_last (u j')).asymm ha
        let a' : Fin k := a.castPred hane
        have haj : a' < u j' := by
          apply Fin.castSucc_lt_castSucc_iff.mp
          simpa only [a', Fin.castSucc_castPred] using (hj ▸ ha)
        obtain ⟨l, hlj, hl⟩ := hgrowth j' a' haj
        refine ⟨⟨l.val, lt_trans (lt_trans hlj j'.isLt) i.isLt⟩, ?_, ?_⟩
        · exact hlj
        · rw [pgf_joinFirst_before]
          simp only [hl, a', Fin.castSucc_castPred]
      · by_cases haTop : a = Fin.last k
        · rw [haTop] at ha
          exact False.elim ((not_lt_of_ge (Fin.le_last _)) ha)
        · obtain ⟨l, hl⟩ := hsurj (a.castPred haTop)
          refine ⟨⟨l.val, lt_trans l.isLt i.isLt⟩, ?_, ?_⟩
          · exact lt_of_lt_of_le l.isLt (Nat.le_of_not_gt hji)
          · rw [pgf_joinFirst_before, hl, Fin.castSucc_castPred]

end MetaMathlibExt
