import sympy.series.limits
import sympy.core.singleton
import Lemma.Int.GeAbs
import Lemma.Int.GeAbs_0
import Lemma.Nat.Lt.of.Lt.Le
import Lemma.Int.EqAbs.of.Gt_0
open Nat Int


@[main, comm, mp and, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → +∞ ↔ ∀ δ : ℝ, x > δ := by
-- proof
  refine ⟨fun ⟨hx, hx'⟩ r ↦ ?_, fun h ↦ ?_, ⟩
  ·
    apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg _ hx.le
    apply Lt.of.Lt.Le hx'
    apply ArchimedeanClass.mk_map_nonneg_of_archimedean Hyperreal.coeRingHom
  ·
    have hx : 0 < x := h 0
    refine ⟨h 0, fun n ↦ ?_⟩
    simpa [EqAbs.of.Gt_0 hx] using! h n


@[main, comm, mp and, mpr]
private lemma pos
-- given
  (x : ℝ*) :
-- imply
  x → +∞ ↔ ∀ δ : ℝ⁺, x > δ := by
-- proof
  rw [main]
  constructor <;>
    intro h
  ·
    intro ⟨δ, hδ⟩
    have h := h δ
    convert h
  ·
    if h_x : x > 0 then
      intro δ
      have h_δ := GeAbs_0 δ
      have h := h ⟨|δ| + 1, by linarith⟩
      simp at h
      have h_δ := GeAbs (δ : ℝ*)
      linarith
    else
      have h := h 1
      simp_all
      linarith


-- created on 2025-12-25
