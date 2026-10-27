import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Algebra.Polynomial.L1Norm
import Lemma.Polynomial.L1Norm


namespace Polynomial

/--
[natDegree_eq_of_monic_of_l1Norm_sub_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/DegreeStability.lean)
-/
@[path]
lemma natDegree_eq_of_monic_of_l1Norm_sub_lt_one
  [Ring K] [Nontrivial K]
  {v : AbsoluteValue K ℝ}
  {f g : Polynomial K}
-- given
  (hf : f.Monic)
  (hg : g.Monic)
  (h : l1Norm v (f - g) < 1) :
-- imply
  f.natDegree = g.natDegree := by
-- proof
  apply le_antisymm
  · by_contra hle
    push Not at hle
    have hg0 : g.coeff f.natDegree = 0 := coeff_eq_zero_of_natDegree_lt hle
    have hcoeff : (f - g).coeff f.natDegree = 1 := by
      rw [coeff_sub, hf.coeff_natDegree, hg0, sub_zero]
    have hmem : f.natDegree ∈ (f - g).support :=
      mem_support_iff.mpr (by rw [hcoeff]; exact one_ne_zero)
    have hbound := Finset.single_le_sum (s := (f - g).support)
      (f := fun i => v ((f - g).coeff i)) (fun i _ => v.nonneg _) hmem
    rw [l1Norm_def] at h
    simpa [hcoeff] using hbound.trans_lt h
  · by_contra hle
    push Not at hle
    have hf0 : f.coeff g.natDegree = 0 := coeff_eq_zero_of_natDegree_lt hle
    have hcoeff : (f - g).coeff g.natDegree = -1 := by
      rw [coeff_sub, hf0, hg.coeff_natDegree, zero_sub]
    have hmem : g.natDegree ∈ (f - g).support :=
      mem_support_iff.mpr (by rw [hcoeff]; exact neg_ne_zero.mpr one_ne_zero)
    have hbound := Finset.single_le_sum (s := (f - g).support)
      (f := fun i => v ((f - g).coeff i)) (fun i _ => v.nonneg _) hmem
    rw [l1Norm_def] at h
    simpa [hcoeff] using hbound.trans_lt h

end Polynomial


-- created on 2026-10-20
-- updated on 2026-10-26
