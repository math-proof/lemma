import Mathlib
import sympy.Basic
import Lemma.ModularCurve.LaurentCoeff
open scoped BigOperators


/--
[ModularCurve_exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange.lean)
-/
@[path]
private lemma main
  [Field L] [Algebra ℚ L]
  {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
  {x : LaurentSeries L}
-- given
  (hx : x ∈ ModularCurve.laurentBaseChange L F₀) :
-- imply
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → L) (g : ι → ↥F₀) (κ : Type) (_ : Fintype κ) (d : κ → L) (h : κ → ↥F₀),
      (∑ j, algebraMap L (LaurentSeries L) (d j) * ModularCurve.coeffEmb L ((h j : ↥F₀) : LaurentSeries ℚ)) ≠ 0 ∧
      x * (∑ j, algebraMap L (LaurentSeries L) (d j) * ModularCurve.coeffEmb L ((h j : ↥F₀) : LaurentSeries ℚ)) =
        ∑ i, algebraMap L (LaurentSeries L) (c i) * ModularCurve.coeffEmb L ((g i : ↥F₀) : LaurentSeries ℚ) := by
-- proof
  classical
    set S : Set (LaurentSeries L) := ⇑(ModularCurve.coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)) with hS
    have hspan : ∀ r : LaurentSeries L, r ∈ Algebra.adjoin L S →
        ∃ (ι : Type) (_ : Fintype ι) (c : ι → L) (g : ι → ↥F₀),
          ∑ i, algebraMap L (LaurentSeries L) (c i) * ModularCurve.coeffEmb L ((g i : ↥F₀) : LaurentSeries ℚ) = r := by
      intro r hr
      induction hr using Algebra.adjoin_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        exact ⟨PUnit, inferInstance, fun _ => 1, fun _ => ⟨a, ha⟩, by simp⟩
      | algebraMap l =>
        exact ⟨PUnit, inferInstance, fun _ => l, fun _ => ⟨1, F₀.one_mem⟩, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨ι, _, c, g, rfl⟩ := hy
        obtain ⟨κ, _, d, h, rfl⟩ := hz
        refine ⟨ι ⊕ κ, inferInstance, Sum.elim c d, Sum.elim g h, ?_⟩
        simp [Fintype.sum_sum_type]
      | mul y z _ _ hy hz =>
        obtain ⟨ι, _, c, g, rfl⟩ := hy
        obtain ⟨κ, _, d, h, rfl⟩ := hz
        refine ⟨ι × κ, inferInstance, fun p => c p.1 * d p.2, fun p => ⟨(g p.1 : LaurentSeries ℚ) * (h p.2 : LaurentSeries ℚ), F₀.mul_mem (g p.1).2 (h p.2).2⟩, ?_⟩
        rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [map_mul]
        ring
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
    obtain ⟨ι, _, c, g, hcg⟩ := hspan r hr
    if hs0 : s = 0 then
      refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PUnit, inferInstance, fun _ => 1, fun _ => ⟨1, F₀.one_mem⟩, ?_, ?_⟩
      · simp
      · simp [hs0]
    else
      obtain ⟨κ, _, d, h, hdh⟩ := hspan s hs
      refine ⟨ι, inferInstance, c, g, κ, inferInstance, d, h, ?_, ?_⟩
      ·
        rwa [hdh]
      · rw [hdh, hcg, div_mul_cancel₀ r hs0]


-- created on 2026-10-23
