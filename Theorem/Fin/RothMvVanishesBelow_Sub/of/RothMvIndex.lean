module

public import Mathlib
public import Theorem.Fin.CoeffRothTranslateM.eq.EvalRothMvHasse
public import Theorem.Fin.RothMvHasse_RothMvHasse.eq.SMul_RothMvHasse.of.RothMvIndex
public import Theorem.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvVanishesBelow_hasse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvVanishesBelow_Sub.of.RothMvIndex
  {m : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
-- given
  (hP : rothMvVanishesBelow P x r t)
  (i : RothMvIndex m) :
-- imply
  rothMvVanishesBelow (rothMvHasse i P) x r (t - rothMvWeight r i) := by
-- proof
  intro j hj
  rw [CoeffRothTranslateM.eq.EvalRothMvHasse,
    RothMvHasse_RothMvHasse.eq.SMul_RothMvHasse.of.RothMvIndex]
  have hw : rothMvWeight r (i + j) < t := by
    rw [RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex]
    linarith
  have hz := hP (i + j) hw
  rw [CoeffRothTranslateM.eq.EvalRothMvHasse] at hz
  simp [hz]


-- created on 2026-10-21
