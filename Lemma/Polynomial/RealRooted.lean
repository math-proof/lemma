import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.RealRooted

open Polynomial

/--
[isRealRooted_of_map_star_eq_self_of_roots_im_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma isRealRooted_of_map_star_eq_self_of_roots_im_nonpos_eq
-- given
  (p : Polynomial ℂ) (hp0 : p ≠ 0)
  (hreal : Polynomial.map (starRingEnd ℂ) p = p)
  (hupper : ∀ z ∈ p.roots, z.im ≤ 0) :
-- imply
  p.IsRealRooted := by
-- proof
  apply isRealRooted_of_map_star_eq_self_of_roots_im_nonpos
  · exact hp0
  · exact hreal
  · exact hupper


/--
[root_re_le_maxRealRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma root_re_le_maxRealRoot_eq
-- given
  {p : Polynomial ℂ} {z : ℂ} (hz : z ∈ p.roots) :
-- imply
  z.re ≤ p.maxRealRoot := by
-- proof
  apply root_re_le_maxRealRoot
  exact hz


/--
[exists_root_re_eq_maxRealRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma exists_root_re_eq_maxRealRoot_eq
-- given
  {p : Polynomial ℂ} (hp : p.roots ≠ 0) :
-- imply
  ∃ z ∈ p.roots, z.re = p.maxRealRoot := by
-- proof
  apply exists_root_re_eq_maxRealRoot
  exact hp


/--
[roots_ne_zero_of_natDegree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma roots_ne_zero_of_natDegree_pos_eq
-- given
  {p : Polynomial ℂ} (hp : 0 < p.natDegree) :
-- imply
  p.roots ≠ 0 := by
-- proof
  apply roots_ne_zero_of_natDegree_pos
  exact hp


/--
[coe_maxRealRoot_mem_roots](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma coe_maxRealRoot_mem_roots_eq
-- given
  {p : Polynomial ℂ} (hp : p.IsRealRooted) (hdegree : 0 < p.natDegree) :
-- imply
  (p.maxRealRoot : ℂ) ∈ p.roots := by
-- proof
  apply coe_maxRealRoot_mem_roots
  · exact hp
  · exact hdegree


/--
[eval_re_pos_of_maxRealRoot_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma eval_re_pos_of_maxRealRoot_lt_eq
-- given
  {p : Polynomial ℂ} (hmonic : p.Monic) (hrooted : p.IsRealRooted)
  {x : ℝ} (hx : p.maxRealRoot < x) :
-- imply
  0 < (p.eval (x : ℂ)).re := by
-- proof
  apply eval_re_pos_of_maxRealRoot_lt
  · exact hmonic
  · exact hrooted
  · exact hx


/--
[eval_re_nonneg_of_maxRealRoot_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma eval_re_nonneg_of_maxRealRoot_le_eq
-- given
  {p : Polynomial ℂ} (hmonic : p.Monic) (hrooted : p.IsRealRooted)
  {x : ℝ} (hx : p.maxRealRoot ≤ x) :
-- imply
  0 ≤ (p.eval (x : ℂ)).re := by
-- proof
  apply eval_re_nonneg_of_maxRealRoot_le
  · exact hmonic
  · exact hrooted
  · exact hx


-- created on 2026-10-09
