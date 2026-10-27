import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory


private lemma map_mul_right_absolutelyContinuous
  {G : Type*}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [MeasurableSpace G]
  [BorelSpace G]
  [LocallyCompactSpace G]
  [T2Space G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (h : G) :
  (μ.map (· * h)) ≪ μ := by
  have : (μ.map (· * h)).Regular := Measure.Regular.map (Homeomorph.mulRight h)
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular (μ.map (· * h)) μ]
  apply Measure.smul_absolutelyContinuous

private lemma aesm_comp_mul_right
  {G : Type*}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [MeasurableSpace G]
  [BorelSpace G]
  [LocallyCompactSpace G]
  [T2Space G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] {f : G → ℂ}
  (hf : AEStronglyMeasurable f μ) (h : G) : AEStronglyMeasurable (fun g => f (g * h)) μ :=
  (hf.mono_ac (map_mul_right_absolutelyContinuous μ h)).comp_measurable (measurable_mul_const h)

private lemma helper_main
  {G : Type*}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [MeasurableSpace G]
  [BorelSpace G]
  [LocallyCompactSpace G]
  [T2Space G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  {n : ℕ} (ψ : Fin n → (G →* ℂ)) (hψ : Function.Injective ψ) (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
  (h : AEStronglyMeasurable (fun g => ∑ i, c i * ψ i g) μ) (i : Fin n) :
  AEStronglyMeasurable (⇑(ψ i)) μ := by
  classical
  have hsep : ∀ k : Fin n, k ≠ i → ∃ h : G, ψ i h ≠ ψ k h := by
    intro k hk
    by_contra hcon
    push Not at hcon
    exact hk (hψ (MonoidHom.ext fun g => (hcon g).symm))
  choose! hsel hselne using hsep
  let F : Finset (Fin n) → G → ℂ := fun S g =>
    ∑ k, c k * (∏ m ∈ S, (ψ k (hsel m) - ψ m (hsel m))) * ψ k g
  have hF : ∀ S : Finset (Fin n), AEStronglyMeasurable (F S) μ := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa [F] using h
    | insert m S hm ih =>
      have htr := aesm_comp_mul_right μ ih (hsel m)
      have hcomb : F (insert m S) = fun g => F S (g * hsel m) - ψ m (hsel m) * F S g := by
        funext g
        simp only [F, Finset.prod_insert hm, map_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
      rw [hcomb]
      exact htr.sub (ih.const_mul _)
  set S : Finset (Fin n) := Finset.univ.erase i with hS
  set d : ℂ := c i * ∏ m ∈ S, (ψ i (hsel m) - ψ m (hsel m)) with hd
  have hdne : d ≠ 0 := by
    refine mul_ne_zero (hc i) (Finset.prod_ne_zero_iff.mpr fun m hm => ?_)
    exact sub_ne_zero.mpr (hselne m (Finset.ne_of_mem_erase hm))
  have hFS : F S = fun g => d * ψ i g := by
    funext g
    simp only [F]
    rw [Finset.sum_eq_single i]
    ·
      intro k _ hk
      have h0 : (∏ m ∈ S, (ψ k (hsel m) - ψ m (hsel m))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)
      rw [h0, mul_zero, zero_mul]
    · exact fun hi => absurd (Finset.mem_univ i) hi
  have hmain : AEStronglyMeasurable (fun g => d * ψ i g) μ := by rw [← hFS]; exact hF S
  have := hmain.const_mul d⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hdne, one_mul] at this
  exact this

open MeasureTheory _root_.Measure _root_.MeasureTheory.Measure in
/--
[MeasureTheory_aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom.lean)
-/
@[path]
private lemma main
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  {n : ℕ}
  {ψ : Fin n → (G →* ℂ)}
  {c : Fin n → ℂ}
  {i : Fin n}
-- given
  (hψ : Function.Injective ψ)
  (hc : ∀ i, c i ≠ 0)
  (h : AEStronglyMeasurable (fun g => ∑ i, c i * ψ i g) μ) :
-- imply
  AEStronglyMeasurable (⇑(ψ i)) μ :=
-- proof
  helper_main μ ψ hψ c hc h i


-- created on 2026-10-23
