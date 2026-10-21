import Mathlib
import Lemma.Fin.RothMvVanishesBelowNeg
import Lemma.Fin.RothMvVanishesBelow.of.Le
import Lemma.Fin.RothMvVanishesBelow_Sum.of.All_RothMvVanishesBelow
import Lemma.Fin.RothMvVanishesBelow.of.All_RothMvVanishesBelow
import Lemma.Fin.RothMvVanishesBelow_Sub.of.RothMvIndex
import Lemma.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothHasseDet_vanishesBelow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {T : ℝ}
-- given
  (hP : rothMvVanishesBelow P x r T)
  (u v : Fin k → RothMvIndex m) :
-- imply
  rothMvVanishesBelow (rothHasseDet P u v) x r
    ((k : ℝ) * T - ∑ s, rothMvWeight r (u s) - ∑ t, rothMvWeight r (v t)) := by
-- proof
  classical
  unfold rothHasseDet
  let M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) R) :=
    fun s t ↦ rothMvHasse (u s + v t) P
  change rothMvVanishesBelow M.det x r _
  rw [Matrix.det_apply M]
  apply RothMvVanishesBelow_Sum.of.All_RothMvVanishesBelow
  intro σ _
  have hprod := RothMvVanishesBelow.of.All_RothMvVanishesBelow Finset.univ
    (fun s : Fin k ↦ rothMvHasse (u (σ s) + v s) P)
    (fun s : Fin k ↦ T - rothMvWeight r (u (σ s) + v s))
    (fun s _ ↦ RothMvVanishesBelow_Sub.of.RothMvIndex hP (u (σ s) + v s))
  have hprod' : rothMvVanishesBelow (∏ s, M (σ s) s) x r
    ((k : ℝ) * T - ∑ s, rothMvWeight r (u s) - ∑ t, rothMvWeight r (v t)) := by
    apply RothMvVanishesBelow.of.Le hprod
    simp only [RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex,
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsum : (∑ s, rothMvWeight r (u (σ s))) = ∑ s, rothMvWeight r (u s) :=
      Equiv.sum_comp σ (fun s ↦ rothMvWeight r (u s))
    rw [hsum]
    linarith
  obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
  · simpa [hsign] using hprod'
  · simpa [hsign] using RothMvVanishesBelowNeg hprod'


-- created on 2026-10-21
