import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.TateModuleTrace
open WeierstrassCurve.Affine


/--
[Isogeny.restrictTorsion_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TateModuleTrace.lean)
-/
@[path]
lemma Isogeny.restrictTorsion_coe
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : Isogeny E E}
  {n : ℤ}
  {P : torsionSubgroup E n} :
-- imply
  (α.restrictTorsion n P).val = α.toAddMonoidHom P.val :=
-- proof
  rfl

/--
[Matrix.cayleyHamilton_fin_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TateModuleTrace.lean)
-/
@[path]
lemma Matrix.cayleyHamilton_fin_two
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {n : ℕ}
  {M : Matrix (Fin 2) (Fin 2) (ZMod n)} :
-- imply
  M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0 := by
-- proof
  have htr : M.trace = M 0 0 + M 1 1 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    simp [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, htr, hdet] <;>
    ring

/--
[Matrix.constraint_from_two_char_polys](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TateModuleTrace.lean)
-/
@[path]
lemma Matrix.constraint_from_two_char_polys
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {n : ℕ}
  {M : Matrix (Fin 2) (Fin 2) (ZMod n)}
  {t d : ZMod n}
-- given
  (hrestr : M * M - t • M + d • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0)
  (hCH : M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0) :
-- imply
  (M.trace - t) • M + (d - M.det) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0 := by
-- proof
  have key : M * M - M.trace • M + M.det • 1 - (M * M - t • M + d • 1) =
    (t - M.trace) • M + (M.det - d) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.mul_apply, Matrix.one_apply, smul_eq_mul, Fin.sum_univ_two]
    ring
  have h_eq : (t - M.trace) • M + (M.det - d) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0 := by
    rw [← key, hCH, hrestr, sub_zero]
  have : (M.trace - t) • M + (d - M.det) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) =
    -((t - M.trace) • M + (M.det - d) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n))) := by
    ext i j
    simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, smul_eq_mul]
    ring
  rw [this, h_eq, neg_zero]
/-- From the relation `(tr M - t)•M + (d - det M)•I = 0` on the torsion matrix,
deduce that the algebraic trace equals `tr M` and the degree equals `det M`
modulo `n` (requires `n` coprime to the characteristic). -/


-- created on 2026-10-23
