import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_NodeLocalized
import Lemma.Int.P2MUtil

open ModularCurve ModularCurve.NodeLocalized

/--
[ModularCurve_modularRing_eq_range_modularEval](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_modularRing_eq_range_modularEval.lean)
-/
@[path]
private lemma main
  [CommRing L]
  {N : ℕ} [NeZero N]
  {A : Subring L} :
-- imply
  CharPReduction.modularRing N A = (NodeLocalized.modularEval N A).range := by
-- proof
  apply le_antisymm
  ·
    rw [CharPReduction.modularRing, Subring.closure_le]
    rintro x (⟨c, rfl⟩ | rfl | rfl)
    · exact ⟨MvPolynomial.C c, by simp [NodeLocalized.modularEval]⟩
    · exact ⟨MvPolynomial.X 0, by simp [NodeLocalized.modularEval]⟩
    · exact ⟨MvPolynomial.X 1, by simp [NodeLocalized.modularEval]⟩
  ·
    rintro x ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      exact CharPReduction.constSeries_mem_modularRing N A c
    | add p r hp hr => rw [map_add]; exact add_mem hp hr
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [NodeLocalized.modularEval, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact CharPReduction.jqModC_mem_modularRing N A
      · exact CharPReduction.jqNModC_mem_modularRing N A


-- created on 2026-10-23
