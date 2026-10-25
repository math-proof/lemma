/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part2
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCard_original_add_reflected {n k : ℕ} (hn : 0 < n)
    (q : ZagPlaneConfig n hn k) :
    Nat.card (ZagOriginalPoints q) + Nat.card (ZagReflectedPoints q) = n - k := by
  classical
  let e := q.1.1.1
  let π := q.1.2
  let D := zagDiagonal e π
  let exc := Nat.card {x : Fin n // zagExceedance e π x}
  have hπ : cycleQuotientCount π = k := q.2.1
  have hD : cycleQuotientCount D = 1 := q.2.2
  have hDinv : cycleQuotientCount D⁻¹ = 1 := by
    rw [zagCycleQuotientCount_inv, hD]
  have horig : Nat.card (ZagOriginalPoints q) = n - exc - k := by
    simpa only [e, π, exc, hπ] using zagCard_nontrivialAntiExceedances e π
  have hrefExc : Nat.card {x : Fin n //
      zagExceedance (zagReverseOrder hn e) D⁻¹ x} = n - exc - 1 := by
    simpa only [e, π, D, exc] using zagCard_reflected_exceedances hn e π
  have href : Nat.card (ZagReflectedPoints q) = n - (n - exc - 1) - 1 := by
    simpa only [e, π, D, hDinv, hrefExc] using
      zagCard_nontrivialAntiExceedances (zagReverseOrder hn e) D⁻¹
  let base := e (zagBasePoint ⟨0, hn⟩)
  let x₀ := π.symm base
  have hx₀ : ¬zagExceedance e π x₀ := by
    intro hx
    have hright : e.symm (π x₀) = zagBasePoint ⟨0, hn⟩ := by
      change e.symm (π (π.symm base)) = zagBasePoint ⟨0, hn⟩
      rw [π.apply_symm_apply]
      change e.symm (e (zagBasePoint ⟨0, hn⟩)) = zagBasePoint ⟨0, hn⟩
      rw [e.symm_apply_apply]
    rw [zagExceedance, hright, Fin.lt_def] at hx
    exact Nat.not_lt_zero _ hx
  have hexc_lt_raw : Nat.card {x : Fin n // zagExceedance e π x} < n := by
    rw [Nat.card_eq_fintype_card]
    simpa only [Fintype.card_fin] using
      (Fintype.card_subtype_lt (p := zagExceedance e π) hx₀)
  have hexc_lt : exc < n := by
    simpa only [exc] using hexc_lt_raw
  have hanti_card :
      Nat.card {x : Fin n // ¬zagExceedance e π x} = n - exc := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_fin, exc]
  have hcycle_le_anti :
      cycleQuotientCount π ≤
        Nat.card {x : Fin n // ¬zagExceedance e π x} := by
    calc
      cycleQuotientCount π =
          Nat.card {x : Fin n // zagTrivialAntiExceedance e π x} :=
        (zagCard_trivialAntiExceedances e π).symm
      _ = Nat.card {x : {x : Fin n // ¬zagExceedance e π x} //
          zagTrivialAntiExceedance e π x.1} :=
        Nat.card_congr (zagTrivialAntiExceedanceEquiv e π)
      _ ≤ Nat.card {x : Fin n // ¬zagExceedance e π x} := by
        simp only [Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_le _
  have hsum : exc + k ≤ n := by
    rw [hanti_card, hπ] at hcycle_le_anti
    omega
  rw [horig, href]
  omega

end MetaMathlibExt
