import Mathlib
import Lemma.Fin.RothMvVanishesBelowNeg
import Lemma.Fin.RothMvVanishesBelow.of.Le
import Lemma.Fin.RothMvVanishesBelow_Max
import Lemma.Fin.RothMvVanishesBelow_Sum.of.All_RothMvVanishesBelow
import Lemma.Fin.RothMvVanishesBelow.of.All_RothMvVanishesBelow
import Lemma.Fin.RothMvVanishesBelow_Sub.of.RothMvIndex
import Lemma.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
import Lemma.Fin.RothMvVanishesBelow.of.Le_0
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothHasseDet_vanishesBelow_of_rowWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {T ρ : ℝ}
-- given
  (u v : Fin k → RothMvIndex m)
  (hP : rothMvVanishesBelow P x r T)
  (hu : ∀ s, rothMvWeight r (u s) ≤ ρ) :
-- imply
  rothMvVanishesBelow (rothHasseDet P u v) x r
    (∑ t, max 0 (T - ρ - rothMvWeight r (v t))) := by
-- proof
  classical
  unfold rothHasseDet
  let M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) R) :=
    fun s t ↦ rothMvHasse (u s + v t) P
  change rothMvVanishesBelow M.det x r _
  rw [Matrix.det_apply M]
  apply RothMvVanishesBelow_Sum.of.All_RothMvVanishesBelow
  intro σ _
  have hentry : ∀ s : Fin k,
      rothMvVanishesBelow (rothMvHasse (u (σ s) + v s) P) x r
        (max 0 (T - ρ - rothMvWeight r (v s))) := by
    intro s
    apply RothMvVanishesBelow.of.Le (RothMvVanishesBelow_Max
      (RothMvVanishesBelow.of.Le_0 (rothMvHasse (u (σ s) + v s) P) x r (le_refl 0))
      (RothMvVanishesBelow_Sub.of.RothMvIndex hP (u (σ s) + v s)))
    rw [RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex]
    exact max_le_max le_rfl (by linarith [hu (σ s)])
  have hprod := RothMvVanishesBelow.of.All_RothMvVanishesBelow Finset.univ
    (fun s : Fin k ↦ rothMvHasse (u (σ s) + v s) P)
    (fun s ↦ max 0 (T - ρ - rothMvWeight r (v s)))
    (fun s _ ↦ hentry s)
  obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
  · simpa [M, hsign] using hprod
  · simpa [M, hsign] using RothMvVanishesBelowNeg hprod


-- created on 2026-10-21
