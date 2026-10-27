import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.KatzLevelP
import Lemma.Int.P2MUtil
open Int


/--
[ModularCurve_IsLevelPStructure_isUnit_xP_sub_xQ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_IsLevelPStructure_isUnit_xP_sub_xQ.lean)
-/
@[path]
private lemma main
  [CommRing T]
  {ℓ : ℕ} [Fact ℓ.Prime]
  {W : WeierstrassCurve T}
  {D : ModularCurve.LevelPData T}
-- given
  (hℓ3 : 3 ≤ ℓ)
  (hD : ModularCurve.IsLevelPStructure W ℓ D) :
-- imply
  IsUnit (D.xP - D.xQ) := by
-- proof
  have h1 : 1 ∈ Finset.Icc 1 ((ℓ - 1) / 2) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hdvd : (D.xQ * (W.ΨSq ((1 : ℕ) : ℤ)).eval D.xP - (W.Φ ((1 : ℕ) : ℤ)).eval D.xP) ∣
    ModularCurve.indepElt W ℓ D.xP D.xQ :=
    Finset.dvd_prod_of_mem (fun a : ℕ => D.xQ * (W.ΨSq a).eval D.xP - (W.Φ a).eval D.xP) h1
  have hu := isUnit_of_dvd_unit hdvd hD.isUnit_indepElt_PQ
  simp only [Nat.cast_one, WeierstrassCurve.ΨSq_one, WeierstrassCurve.Φ_one, Polynomial.eval_one,
    Polynomial.eval_X, mul_one] at hu
  rw [← neg_sub]
  apply hu.neg


-- created on 2026-10-24
