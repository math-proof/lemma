import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothTranslate_coeff_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ} [CommRing S]
  (x : Fin (n + 1) → S) (P : MvPolynomial (Fin (n + 1)) S)
  (a : ℕ) (i : RothMvIndex n) :
-- imply
  (rothTranslate (n + 1) x P).coeff (i.cons a) =
    (rothTranslate n (fun h ↦ x h.succ)
      ((Polynomial.taylor (MvPolynomial.C (x 0))
        (MvPolynomial.finSuccEquiv S n P)).coeff a)).coeff i := by
-- proof
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff i (rothTranslate (n + 1) x P) a]
  simp only [rothTranslate, AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk,
    AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.toRingHom_eq_coe,
    AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
    RingHom.coe_coe, RingEquiv.coe_mk, EquivLike.coe_coe, Polynomial.coe_mapRingHom,
    Function.comp_apply, Polynomial.taylorAlgHom_apply, Polynomial.map_taylor,
    AlgEquiv.apply_symm_apply]
  rw [← Polynomial.map_taylor, Polynomial.coeff_map]


-- created on 2026-10-21
