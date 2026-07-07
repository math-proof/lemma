import sympy.series.limits
import sympy.core.singleton
import Lemma.Int.GeAbs
import Lemma.Int.GeAbs_0
import Lemma.Int.GtNeg.is.Lt_Neg
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Nat.Lt.of.Lt.Le
open Nat Int


@[main, comm, mp and, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → -∞ ↔ ∀ δ : ℝ, x < δ := by
-- proof
  refine ⟨fun ⟨hx, hx'⟩ r ↦ ?_, fun h ↦ ?_⟩
  ·
    apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonpos _ hx.le
    apply Lt.of.Lt.Le hx'
    apply ArchimedeanClass.mk_map_nonneg_of_archimedean Hyperreal.coeRingHom
  ·
    have hx : x < 0 := h 0
    refine ⟨h 0, fun n ↦ ?_⟩
    simpa [Abs.eq.Neg.of.Lt_0 hx, GtNeg.is.Lt_Neg] using h (-n)


@[main, comm, mp and, mpr]
private lemma neg
-- given
  (x : ℝ*) :
-- imply
  x → -∞ ↔ ∀ δ : ℝ⁻, x < δ := by
-- proof
  rw [main]
  constructor
  <;> intro h
  ·
    intro ⟨δ, hδ⟩
    have h := h δ
    convert h
  ·
    if h_x : x < 0 then
      intro δ
      have h_δ := GeAbs_0 δ
      have h := h ⟨-|δ| - 1, by linarith⟩
      simp at h
      have h_δ := GeAbs (-δ : ℝ*)
      simp at h_δ
      linarith
    else
      have h := h ⟨-1, by simp⟩
      simp_all
      linarith


-- created on 2025-12-25
