import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Polynomial.Interlacing
open scoped ComplexOrder NNReal
open Polynomial


/--
[eval_re_nonpos_of_upperInterlacing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma eval_re_nonpos_of_upperInterlacing_eq
  {p : Polynomial ℂ}
  {a x : ℝ}
-- given
  (hmonic : p.Monic)
  (hrooted : p.IsRealRooted)
  (ha : p.HasUpperInterlacingPoint a)
  (hax : a ≤ x)
  (hx : x ≤ p.maxRealRoot)
  (hdegree : 0 < p.natDegree) :
-- imply
  (p.eval (x : ℂ)).re ≤ 0 := by
-- proof
  apply Polynomial.eval_re_nonpos_of_upperInterlacing hmonic hrooted ha hax hx hdegree

/--
[exists_maxRealRoot_le_weightedSum_of_commonUpperInterlacing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma exists_maxRealRoot_le_weightedSum_of_commonUpperInterlacing_eq
  [Fintype ι] [Nonempty ι]
  {w : ι → ℝ}
  {P : ι → Polynomial ℂ}
-- given
  (hw : ∀ i, 0 ≤ w i)
  (hmonic : ∀ i, (P i).Monic)
  (hrooted : ∀ i, (P i).IsRealRooted)
  (hdegree : ∀ i, 0 < (P i).natDegree)
  (hcommon : HasCommonUpperInterlacing P)
  (hsumMonic : (∑ i, (w i : ℂ) • P i).Monic)
  (hsumRooted : (∑ i, (w i : ℂ) • P i).IsRealRooted) :
-- imply
  ∃ i, (P i).maxRealRoot ≤ (∑ j, (w j : ℂ) • P j).maxRealRoot := by
-- proof
  apply Polynomial.exists_maxRealRoot_le_weightedSum_of_commonUpperInterlacing w P hw hmonic hrooted hdegree hcommon hsumMonic hsumRooted

/--
[exists_maxRealRoot_le_weightedSum_of_segment_realRooted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma exists_maxRealRoot_le_weightedSum_of_segment_realRooted_eq
  [Fintype ι]
  {w : ι → ℝ}
  {P : ι → Polynomial ℂ}
  {n : ℕ}
-- given
  (hne : Nonempty ι)
  (hn : 0 < n)
  (hw : ∀ i, 0 ≤ w i)
  (hfamily : ∀ i, (P i).IsMonicOfDegree n)
  (hsum : (∑ i, (w i : ℂ) • P i).IsMonicOfDegree n)
  (hsegments : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 → ((1 - (t : ℂ)) • (∑ j, (w j : ℂ) • P j) + (t : ℂ) • P i).IsRealRooted) :
-- imply
  ∃ i, (P i).maxRealRoot ≤ (∑ j, (w j : ℂ) • P j).maxRealRoot := by
-- proof
  apply Polynomial.exists_maxRealRoot_le_weightedSum_of_segment_realRooted hne w P hn hw hfamily hsum hsegments


-- created on 2026-10-20
