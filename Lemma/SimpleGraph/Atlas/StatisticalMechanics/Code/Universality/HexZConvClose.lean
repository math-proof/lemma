import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexZConvClose
open StatMech StatMech.Universality


/--
[hzc_truncSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_truncSet_finite_eq
  {a : ℂ}
  {N : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  (hzc_truncSet a h0 N).Finite := by
-- proof
  apply StatMech.Universality.hzc_truncSet_finite a h0 N

/--
[hzc_mem_truncFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_mem_truncFinset_eq
  {a : ℂ}
  {N : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  ts ∈ hzc_truncFinset a h0 N ↔ (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).numVertices < N := by
-- proof
  apply StatMech.Universality.hzc_mem_truncFinset a h0 N ts

/--
[hzc_filterCard_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_filterCard_eq_eq
  {a : ℂ}
  {N n : ℕ}
-- given
  (h0 : ℤ)
  (hn : n < N) :
-- imply
  ((hzc_truncFinset a h0 N).filter (fun ts => (ofTurns a h0 ts).numVertices = n)).card = hzc_sawCount a h0 n := by
-- proof
  apply StatMech.Universality.hzc_filterCard_eq a h0 N n hn

/--
[hzc_sawCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_sawCount_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hzc_sawCount a h0 0 = 0 := by
-- proof
  apply StatMech.Universality.hzc_sawCount_zero a h0

/--
[hzc_trunc_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_trunc_wt_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (h : ts ∈ hzc_truncFinset a h0 N) :
-- imply
  hexSAWwt a h0 x ts = x ^ (ofTurns a h0 ts).numVertices := by
-- proof
  apply StatMech.Universality.hzc_trunc_wt a h0 x N h

/--
[hzc_partial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_partial_eq_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts = ∑ n ∈ Finset.range N, (hzc_sawCount a h0 n : ℝ) * x ^ n := by
-- proof
  apply StatMech.Universality.hzc_partial_eq a h0 x N

/--
[hzc_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_wt_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
  {d : hzc_Dn a h0 N}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hzc_wtγ a h0 x N d := by
-- proof
  apply StatMech.Universality.hzc_wt a h0 hx N d

/--
[hzc_partial_eq_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_partial_eq_attach_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  ∑ d : hzc_Dn a h0 N, hzc_wtγ a h0 x N d = ∑ n ∈ Finset.range N, (hzc_sawCount a h0 n : ℝ) * x ^ n := by
-- proof
  apply StatMech.Universality.hzc_partial_eq_attach a h0 x N

/--
[hzc_nil_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_nil_isLegalSAW_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 []).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hzc_nil_isLegalSAW a h0

/--
[hzc_nil_mem_truncFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_nil_mem_truncFinset_eq
  {a : ℂ}
  {N : ℕ}
-- given
  (h0 : ℤ)
  (hN : 2 ≤ N) :
-- imply
  [] ∈ hzc_truncFinset a h0 N := by
-- proof
  apply StatMech.Universality.hzc_nil_mem_truncFinset a h0 hN

/--
[hzc_sawCount_one_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean)
-/
@[path]
private lemma hzc_sawCount_one_pos_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  1 ≤ hzc_sawCount a h0 1 := by
-- proof
  apply StatMech.Universality.hzc_sawCount_one_pos a h0


-- created on 2026-10-23
