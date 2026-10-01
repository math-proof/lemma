import Mathlib.MeasureTheory.Integral.Prod
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {m : ℕ}
  {f : (Fin (m + 1) → ℝ) → E}
-- given
  (hf : Integrable f volume) :
-- imply
  ∫ v : Fin (m + 1) → ℝ, f v = ∫ v : Fin m → ℝ, ∫ b : ℝ, f (Fin.snoc v b) := by
-- proof
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have hmp : MeasurePreserving e volume ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last m)
  have hi : Integrable (fun z => f (e.symm z)) ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
    (hmp.symm.integrable_comp hf.aestronglyMeasurable).mpr hf
  have heq : ∀ (b : ℝ) (v : Fin m → ℝ), e.symm (b, v) = Fin.snoc v b := by
    intro b v
    show Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ) (Fin.last m) (b, v) = Fin.snoc v b
    rw [Fin.insertNthEquiv_last]
    rfl
  calc
    _ = ∫ z, f (e.symm z) ∂(volume.prod volume) := ((hmp.symm.integral_comp e.symm.measurableEmbedding) f).symm
    _ = ∫ b : ℝ, ∫ v : Fin m → ℝ, f (e.symm (b, v)) := integral_prod _ hi
    _ = ∫ v : Fin m → ℝ, ∫ b : ℝ, f (e.symm (b, v)) := integral_integral_swap hi
    _ = _ := by simp only [heq]


-- created on 2026-10-01
