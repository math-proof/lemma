import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothTranslate_finSuccEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ} [CommRing S]
  (x : Fin (n + 1) → S) (P : MvPolynomial (Fin (n + 1)) S) :
-- imply
  MvPolynomial.finSuccEquiv S n (rothTranslate (n + 1) x P) =
    Polynomial.map (rothTranslate n (fun h ↦ x h.succ))
      (Polynomial.taylor (MvPolynomial.C (x 0))
        (MvPolynomial.finSuccEquiv S n P)) := by
-- proof
  simp only [rothTranslate, AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk,
    AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.toRingHom_eq_coe,
    AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
    RingHom.coe_coe, RingEquiv.coe_mk, EquivLike.coe_coe, Function.comp_apply,
    Polynomial.taylorAlgHom_apply, AlgEquiv.apply_symm_apply]
  change Polynomial.map (rothTranslate n (fun h ↦ x h.succ))
      (Polynomial.taylor (MvPolynomial.C (x 0)) (MvPolynomial.finSuccEquiv S n P)) = _
  rfl


-- created on 2026-10-21
