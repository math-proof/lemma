import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Eq.of.In.In.Lt.Lt.EqBiUnion.EqSum_Card
open Finset Stirling.conditionset


@[main]
private lemma main
  {n k : ℕ}
  {x : Fin k → Finset ℕ}
  {a : ℕ}
  {i1 i2 : Fin k}
-- given
  (hx : x ∈ Stirling.conditionset n k)
  (h1 : a ∈ x i1)
  (h2 : a ∈ x i2) :
-- imply
  i1 = i2 := by
-- proof
  set w : ℕ → Finset ℕ := fun i => if h : i < k then x ⟨i, h⟩ else ∅ with hw
  have h₀ : ∑ i ∈ Finset.range k, (w i).card = n := by
    rw [← hx.2.1, ← Fin.sum_univ_eq_sum_range (fun i => (w i).card)]
    simp [hw]
  have h₁ : (Finset.range k).biUnion w = Finset.range n := by
    rw [← hx.1]
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    ·
      rintro ⟨i, hi, ha⟩
      exact ⟨⟨i, hi⟩, by simpa [hw, hi] using ha⟩
    ·
      rintro ⟨i, ha⟩
      exact ⟨i, i.isLt, by simpa [hw, i.isLt] using ha⟩
  exact Fin.ext (Eq.of.In.In.Lt.Lt.EqBiUnion.EqSum_Card h₀ h₁ i1.isLt i2.isLt (by simpa [hw] using h1) (by simpa [hw] using h2))


-- created on 2026-10-07
