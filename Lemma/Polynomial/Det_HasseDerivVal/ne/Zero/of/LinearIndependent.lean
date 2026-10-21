import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.Det_PowDerivativeGetVal.ne.Zero.of.LinearIndependent
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_poly_hasse_wronskian_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ}
  (f : Fin k → ℚ[X])
-- given
  (hf : LinearIndependent ℚ f) :
-- imply
  (Matrix.det fun s j ↦ hasseDeriv s.val (f j)) ≠ 0 := by
-- proof
  let A : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ (derivative^[s.val]) (f j)
  let H : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ hasseDeriv s.val (f j)
  have hder : A.det ≠ 0 := Det_PowDerivativeGetVal.ne.Zero.of.LinearIndependent f hf
  intro hhasse
  apply hder
  have heq : A.det =
      C (∏ s : Fin k, (s.val.factorial : ℚ)) * H.det := by
    classical
    rw [Matrix.det_apply A, Matrix.det_apply H, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    have hprod : ∏ s, A (σ s) s =
        C (∏ s : Fin k, (s.val.factorial : ℚ)) * ∏ s, H (σ s) s := by
      have hfactor : (∏ s : Fin k, ((σ s).val.factorial : ℚ)) =
          ∏ s : Fin k, (s.val.factorial : ℚ) :=
        Equiv.prod_comp σ (fun s : Fin k ↦ (s.val.factorial : ℚ))
      dsimp [A, H]
      rw [← hfactor, map_prod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro s _
      have hfac :=
        congrFun (factorial_smul_hasseDeriv (R := ℚ) (σ s).val) (f s)
      simpa [smul_eq_mul] using hfac.symm
    rw [hprod]
    obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
    · simp [hsign]
    · simp [hsign]
  rw [heq, hhasse, mul_zero]


-- created on 2026-10-21
