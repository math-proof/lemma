import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothTranslate_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {m : ℕ}
  (x y : Fin m → R) (P : MvPolynomial (Fin m) R) :
-- imply
  MvPolynomial.eval y (rothTranslate m x P) =
    MvPolynomial.eval (fun h ↦ y h + x h) P := by
-- proof
  have rothTranslate_finSuccEquiv {n : ℕ}
    (x : Fin (n + 1) → R) (P : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.finSuccEquiv R n (rothTranslate (n + 1) x P) =
      Polynomial.map (rothTranslate n (fun h ↦ x h.succ))
        (Polynomial.taylor (MvPolynomial.C (x 0))
          (MvPolynomial.finSuccEquiv R n P)) := by
    simp only [rothTranslate, AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk,
      AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.toRingHom_eq_coe,
      AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, RingEquiv.coe_mk, EquivLike.coe_coe, Function.comp_apply,
      Polynomial.taylorAlgHom_apply, AlgEquiv.apply_symm_apply]
    change Polynomial.map (rothTranslate n (fun h ↦ x h.succ))
      (Polynomial.taylor (MvPolynomial.C (x 0)) (MvPolynomial.finSuccEquiv R n P)) = _
    rfl
  revert x y P
  induction m with
  | zero =>
    intro x y P
    change MvPolynomial.eval y P = MvPolynomial.eval (fun h ↦ y h + x h) P
    apply congrArg (fun z : Fin 0 → R ↦ MvPolynomial.eval z P)
      (Subsingleton.elim _ _)
  | succ n ih =>
    intro x y P
    let xt : Fin n → R := fun h ↦ x h.succ
    let yt : Fin n → R := fun h ↦ y h.succ
    let p : Polynomial (MvPolynomial (Fin n) R) := MvPolynomial.finSuccEquiv R n P
    have hy : y = Fin.cons (y 0) yt := by
      ext h
      refine Fin.cases ?_ (fun h ↦ ?_) h <;> simp [yt]
    have hxy : (fun h ↦ y h + x h) =
        Fin.cons (y 0 + x 0) (fun h ↦ yt h + xt h) := by
      ext h
      refine Fin.cases ?_ (fun h ↦ ?_) h <;> simp [xt, yt]
    rw [hxy, hy]
    rw [MvPolynomial.eval_eq_eval_mv_eval']
    rw [rothTranslate_finSuccEquiv]
    change Polynomial.eval (y 0)
      (Polynomial.map (MvPolynomial.eval yt)
        (Polynomial.map (rothTranslate n xt)
          (Polynomial.taylor (MvPolynomial.C (x 0)) p))) = _
    rw [Polynomial.map_map]
    have hhom :
      (MvPolynomial.eval yt).comp (rothTranslate n xt) =
        MvPolynomial.eval (fun h ↦ yt h + xt h) := by
      apply DFunLike.ext _ _
      intro Q
      apply ih xt yt Q
    rw [hhom, Polynomial.map_taylor]
    rw [Polynomial.taylor_eval]
    rw [MvPolynomial.eval_eq_eval_mv_eval']
    simp only [MvPolynomial.eval_C, Fin.cons_zero]
    rfl


-- created on 2026-10-21
