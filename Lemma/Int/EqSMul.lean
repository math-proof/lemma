import Mathlib
import sympy.Basic

open WeierstrassCurve

/--
[WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {W : WeierstrassCurve R} :
-- imply
  (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange R) • W = W := by
-- proof
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_neg_one, Units.val_neg, Units.val_one] <;> ring


-- created on 2026-10-03
