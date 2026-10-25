import Mathlib
import sympy.Basic
import Lemma.WeierstrassCurve.ReduceHom
import Lemma.Int.P2MUtil

open WeierstrassCurve IsLocalRing

/--
[WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero.lean)
-/
@[path]
private lemma main
  [Field L] [DecidableEq L]
  {A : ValuationSubring L} [DecidableEq (ResidueField A)]
  {W : WeierstrassCurve A}
  {N : ℕ}
  {P Q : (W.map A.subtype).toAffine.Point}
-- given
  (hΔ : (W.map (residue A)).Δ ≠ 0)
  (hN : (N : ResidueField A) ≠ 0)
  (hP : N • P = 0)
  (hQ : N • Q = 0)
  (h : reduceHom hΔ P = reduceHom hΔ Q) :
-- imply
  P = Q := by
-- proof
  have h1 : N • (P - Q) = 0 := by rw [nsmul_sub, hP, hQ, sub_zero]
  have h2 : reducePoint hΔ (P - Q) = 0 := by
    show reduceHom hΔ (P - Q) = 0
    rw [map_sub, h, sub_self]
  have key : P - Q = 0 := by
    generalize hR : P - Q = R at h1 h2
    cases R with
    | zero => rfl
    | some x y hxy =>
      exfalso
      have hx : x ∈ A := X_mem_of_nsmul_eq_zero' W hN hxy h1
      rw [reducePoint_some_of_mem hΔ hxy hx] at h2
      exact Affine.Point.some_ne_zero _ h2
  exact sub_eq_zero.mp key


-- created on 2026-10-23
