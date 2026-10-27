import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Polynomial.Wronskian.ne.Zero.of.NeNatDegree_NatDegree.Ne_0.Ne_0
open Polynomial


/--
[roth_wronskian_eq_zero_imp_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  [Field K] [CharZero K]
  {f g : K[X]}
-- given
  (hw : wronskian f g = 0)
  (hf : f ≠ 0) :
-- imply
  ∃ c : K, g = c • f := by
-- proof
  if hg : g = 0 then
    refine ⟨0, ?_⟩
    simp [hg]
  else
    have hdeg : f.natDegree = g.natDegree := by
      by_contra hne
      apply Wronskian.ne.Zero.of.NeNatDegree_NatDegree.Ne_0.Ne_0 hne hf hg hw
    let c := g.leadingCoeff / f.leadingCoeff
    let h := g - c • f
    have hdegree : h.degree < f.degree := by
      have hc : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hg)
        (leadingCoeff_ne_zero.mpr hf)
      have hcf : c • f ≠ 0 := smul_ne_zero hc hf
      have hlt : h.degree < g.degree := by
        apply degree_sub_lt_left
        ·
          rw [degree_eq_natDegree hg, degree_eq_natDegree hcf]
          rw [natDegree_smul f hc]
          exact_mod_cast hdeg.symm
        ·
          apply hg
        ·
          dsimp [c]
          rw [leadingCoeff_smul_of_smul_regular f
            (IsSMulRegular.of_ne_zero hc : IsSMulRegular K c)]
          simp only [smul_eq_mul]
          apply Eq.symm
          apply div_mul_cancel₀ g.leadingCoeff (leadingCoeff_ne_zero.mpr hf)
      simpa [degree_eq_natDegree hf, degree_eq_natDegree hg, hdeg] using hlt
    have hwr : wronskian f h = 0 := by
      dsimp [h]
      unfold wronskian
      simp only [derivative_sub, derivative_smul]
      unfold wronskian at hw
      simp only [smul_eq_C_mul]
      calc
        _ = f * g.derivative - f.derivative * g := by ring
        _ = 0 := hw
    have hh : h = 0 := by
      by_contra hh
      apply Wronskian.ne.Zero.of.NeNatDegree_NatDegree.Ne_0.Ne_0 _ hf hh hwr
      ·
        intro heq
        have := hdegree
        rw [degree_eq_natDegree hf, degree_eq_natDegree hh, heq] at this
        apply lt_irrefl _ this
    refine ⟨c, ?_⟩
    apply sub_eq_zero.mp hh


-- created on 2026-10-21
