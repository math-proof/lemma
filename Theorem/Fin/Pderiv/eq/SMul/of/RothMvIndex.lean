module

public import Mathlib
public import Theorem.Fin.RothMvHasse_Single1.eq.Pderiv
public import Theorem.Fin.RothMvHasse_RothMvHasse.eq.SMul_RothMvHasse.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_pderiv_hasse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.Pderiv.eq.SMul.of.RothMvIndex
  {m : ℕ}
  (h : Fin m) (i : RothMvIndex m) (P : MvPolynomial (Fin m) ℚ) :
-- imply
  MvPolynomial.pderiv h (rothMvHasse i P) =
    (i h + 1 : ℚ) • rothMvHasse (i + Finsupp.single h 1) P := by
-- proof
  rw [← RothMvHasse_Single1.eq.Pderiv,
    RothMvHasse_RothMvHasse.eq.SMul_RothMvHasse.of.RothMvIndex]
  have hprod :
    (∏ b : Fin m,
        (Nat.choose ((i + (Finsupp.single h 1 : RothMvIndex m)) b) (i b) : ℚ)) =
      (i h + 1 : ℚ) := by
    rw [Finset.prod_eq_single h]
    ·
      simp
    ·
      intro b _ hbh
      simp [hbh]
    ·
      simp
  rw [hprod]


-- created on 2026-10-21
