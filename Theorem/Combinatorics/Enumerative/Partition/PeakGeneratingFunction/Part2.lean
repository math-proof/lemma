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
import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part5


namespace MetaMathlibExt

lemma pgf_decodeFirst_injective (n m : ℕ) :
    Function.Injective (pgf_decodeFirst n m) := by
  rintro (u | d) (u' | d') h
  · congr 1
    funext j
    apply Fin.castSucc_injective
    exact congrFun h j
  · have hi := congrFun h d'.1
    simp only [pgf_decodeFirst, Function.comp_apply, pgf_joinFirst_top] at hi
    exact False.elim (Fin.castSucc_ne_last _ hi)
  · have hi := congrFun h d.1
    simp only [pgf_decodeFirst, Function.comp_apply, pgf_joinFirst_top] at hi
    exact False.elim (Fin.castSucc_ne_last _ hi.symm)
  · congr 1
    exact pgf_joinFirst_injective n m h

lemma pgf_decodeFirst_surjective (n m : ℕ) :
    Function.Surjective (pgf_decodeFirst n m) := by
  intro w
  by_cases htop : ∃ i, w i = Fin.last m
  · have hex : ∃ r : ℕ, ∃ hr : r < n, w ⟨r, hr⟩ = Fin.last m := by
      obtain ⟨i, hi⟩ := htop
      exact ⟨i.val, i.isLt, hi⟩
    let p := Nat.find hex
    have hpspec : ∃ hp : p < n, w ⟨p, hp⟩ = Fin.last m := by
      simpa [p] using Nat.find_spec hex
    obtain ⟨hp, hptop⟩ := hpspec
    have hbefore : ∀ r < p, ∀ hr : r < n, w ⟨r, hr⟩ ≠ Fin.last m := by
      intro r hr hrn heq
      exact (Nat.find_min hex (by simpa [p] using hr)) ⟨hrn, heq⟩
    let i : Fin n := ⟨p, hp⟩
    let u : Fin p → Fin m := fun j =>
      (w ⟨j.val, lt_trans j.isLt hp⟩).castPred (hbefore j.val j.isLt _)
    let v : Fin (n - 1 - p) → Fin (m + 1) := fun j =>
      w ⟨p + 1 + j.val, by omega⟩
    refine ⟨Sum.inr ⟨i, u, v⟩, ?_⟩
    funext j
    change pgf_joinFirst ⟨i, u, v⟩ j = w j
    unfold pgf_joinFirst
    dsimp only [i]
    by_cases hjp : j.val < p
    · rw [dite_eq_left hjp]
      dsimp only [u]
      rw [Fin.castSucc_castPred]
    · rw [dite_eq_right hjp]
      by_cases hjpeq : j.val = p
      · rw [dite_eq_left hjpeq]
        have hji : j = ⟨p, hp⟩ := Fin.ext hjpeq
        rw [hji, hptop]
      · rw [dite_eq_right hjpeq]
        dsimp only [v]
        congr 1
        apply Fin.ext
        dsimp
        omega
  · let u : Fin n → Fin m := fun i => (w i).castPred (fun hi => htop ⟨i, hi⟩)
    refine ⟨Sum.inl u, ?_⟩
    funext i
    change (u i).castSucc = w i
    exact Fin.castSucc_castPred _ _

end MetaMathlibExt
