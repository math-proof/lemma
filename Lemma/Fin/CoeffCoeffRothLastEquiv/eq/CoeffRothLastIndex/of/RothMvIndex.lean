import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothLastEquiv_coeff_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ} [CommSemiring R]
-- given
  (P : MvPolynomial (Fin (n + 1)) R)
  (a : ℕ)
  (i : RothMvIndex n) :
-- imply
  ((rothLastEquiv R n P).coeff a).coeff i = P.coeff (rothLastIndex i a) := by
-- proof
  let d := rothLastIndex i a
  have hmap : Finsupp.mapDomain finSuccEquivLast d = Finsupp.optionElim a i := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain]
    change (Finsupp.equivCongrLeft finSuccEquivLast) d = _
    simp [d, rothLastIndex]
    ext b
    simp [Finsupp.equivMapDomain_apply]
  unfold rothLastEquiv
  rw [AlgEquiv.trans_apply, MvPolynomial.optionEquivLeft_coeff_coeff]
  rw [← hmap, MvPolynomial.renameEquiv_apply,
    MvPolynomial.coeff_rename_mapDomain finSuccEquivLast finSuccEquivLast.injective]


-- created on 2026-10-21
