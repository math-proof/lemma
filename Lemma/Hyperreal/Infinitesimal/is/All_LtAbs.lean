import sympy.series.limits
import sympy.core.singleton
import Lemma.Int.LtAbs.is.LtNeg.Lt
open Int


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → 0 ↔ ∀ δ : ℝ⁺, |x| < δ := by
-- proof
  simp [LtAbs.is.LtNeg.Lt]
  constructor
  ·
    intro h a ha
    have hx := h.le
    have hst := ArchimedeanClass.stdPart_eq_zero.mpr (ne_of_gt h)
    constructor
    ·
      apply ArchimedeanClass.lt_of_lt_stdPart Hyperreal.coeRingHom hx
      rw [hst]
      exact neg_lt_zero.mpr ha
    ·
      apply ArchimedeanClass.lt_of_stdPart_lt Hyperreal.coeRingHom hx
      rwa [hst]
  ·
    intro h
    have h1 := h 1 zero_lt_one
    have hx := ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean Hyperreal.coeRingHom h1.1.le h1.2.le
    have hst := ArchimedeanClass.stdPart_eq Hyperreal.coeRingHom
      (fun s hs => by simpa using (h (-s) (neg_pos.mpr hs)).1.le)
      (fun s hs => by simpa using (h s hs).2.le)
    rw [lt_iff_le_and_ne]
    constructor
    ·
      exact hx
    ·
      exact Ne.symm (ArchimedeanClass.stdPart_eq_zero.mp hst)


-- created on 2025-12-08
