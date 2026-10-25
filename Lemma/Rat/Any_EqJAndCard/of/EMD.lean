import Mathlib
import sympy.Basic
import Def.ModularCurve_EMD
import Lemma.ModularCurve.GenusNumerics
import Lemma.Int.P2MUtil


/--
[ModularCurve_exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD.lean)
-/
@[path]
private lemma main
  {N : ℕ} [NeZero N]
  {j₀ : AlgebraicClosure ℚ}
-- given
  (hEMD : ModularCurve.EMD N j₀) :
-- imply
  ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      Nat.card (Quot (fun ψ ψ' : ModularCurve.Emb N j₀ => ModularCurve.SamePlace ψ.1 ψ'.1)) = Nat.card (Quot (fun H H' : ModularCurve.CycSub E₀ N => ModularCurve.SameOrbit E₀ H.1 H'.1)) := by
-- proof
  obtain ⟨E₀, hE₀, hj, Φ, hΦ⟩ := hEMD
  exact ⟨E₀, hE₀, hj, Nat.card_congr (Quot.congr Φ (fun ψ ψ' => hΦ ψ ψ'))⟩


-- created on 2026-10-23
