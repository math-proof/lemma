module
public import Mathlib
public import Theorem.Fin.RothPolyL1_RothAuxTerm.le.PowMul2RothCoordinateBaseSum.of.RothBox
public import Theorem.Polynomial.NatAbsCoeff.le.RothPolyL1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin Polynomial


public section

/--
[rothAuxMatrix_entry_natAbs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
-- given
  (u : RothLowIndex r γ × Fin (rothIntegralPolynomial α).natDegree)
  (j : RothBox r) :
-- imply
  ((rothAuxMatrix α r γ u j).natAbs : ℝ) ≤
    ((2 * rothCoordinateBase α) ^ (∑ h, r h) : ℕ) := by
-- proof
  exact_mod_cast
    (NatAbsCoeff.le.RothPolyL1 (rothAuxTerm α u.1.1 j) u.2).trans
      (RothPolyL1_RothAuxTerm.le.PowMul2RothCoordinateBaseSum.of.RothBox α u.1.1 j)


-- created on 2026-10-21
