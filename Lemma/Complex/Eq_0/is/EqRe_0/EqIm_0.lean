import Lemma.Complex.Eq.of.Re.Im
open Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq_0.is.EqRe_0.EqIm_0 |
| comm | Complex.EqRe_0.EqIm_0.is.Eq_0 |
| mp | Complex.EqRe_0.EqIm_0.of.Eq_0 |
| mpr | Complex.Eq_0.of.EqRe_0.EqIm_0 |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (z : ℂ) :
-- imply
  z = 0 ↔ re z = 0 ∧ im z = 0 := by
-- proof
  constructor
  ·
    intro h
    simp [h]
  ·
    intro ⟨h_Re, h_Im⟩
    apply Eq.of.Re.Im <;>
    ·
      simp
      assumption


-- created on 2025-01-17
-- updated on 2026-08-18
