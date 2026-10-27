import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.Polynomial.RealRooted.Part2
open Polynomial
open scoped ComplexOrder

namespace Polynomial

/--
[isRealRooted_of_map_star_eq_self_of_roots_im_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
lemma isRealRooted_of_map_star_eq_self_of_roots_im_nonpos
-- given
  (p : Polynomial ℂ) (hp0 : p ≠ 0)
  (hreal : Polynomial.map (starRingEnd ℂ) p = p)
  (hupper : ∀ z ∈ p.roots, z.im ≤ 0) :
-- imply
  p.IsRealRooted := by
-- proof
  intro z hz
  have hzroot : p.eval z = 0 := (Polynomial.mem_roots hp0).mp hz
  have hconj_eval : p.eval (star z) = 0 := by
    have hmap := Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) z
    rw [hreal, hzroot] at hmap
    simpa using hmap
  have hconj : star z ∈ p.roots := (Polynomial.mem_roots hp0).mpr hconj_eval
  have hzle := hupper z hz
  have hconjle := hupper (star z) hconj
  have hstarim : (star z).im = -z.im := by rfl
  rw [hstarim] at hconjle
  linarith
  · exact hp0
  · exact hreal
  · exact hupper

end Polynomial

namespace Polynomial

/--
[root_re_le_maxRealRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
lemma root_re_le_maxRealRoot
-- given
  {p : Polynomial ℂ} {z : ℂ} (hz : z ∈ p.roots) :
-- imply
  z.re ≤ p.maxRealRoot := by
-- proof
  classical
  rw [maxRealRoot]
  split_ifs with h
  · apply Finset.le_max'
    simpa using Multiset.mem_map.mpr ⟨z, hz, rfl⟩
  · exfalso
    apply h
    exact ⟨z.re, by simpa using Multiset.mem_map.mpr ⟨z, hz, rfl⟩⟩
  exact hz

end Polynomial

namespace Polynomial

/--
[exists_root_re_eq_maxRealRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
lemma exists_root_re_eq_maxRealRoot
-- given
  {p : Polynomial ℂ} (hp : p.roots ≠ 0) :
-- imply
  ∃ z ∈ p.roots, z.re = p.maxRealRoot := by
-- proof
  classical
  have hnonempty : (p.roots.map Complex.re).toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    simpa only [ne_eq, Multiset.map_eq_zero] using hp
  rw [maxRealRoot]
  split_ifs with h
  · have hmem := Finset.max'_mem (p.roots.map Complex.re).toFinset h
    rw [Multiset.mem_toFinset] at hmem
    obtain ⟨z, hz, hzeq⟩ := Multiset.mem_map.mp hmem
    exact ⟨z, hz, hzeq⟩
  · exact (h hnonempty).elim
  exact hp

end Polynomial

namespace Polynomial

/--
[roots_ne_zero_of_natDegree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
lemma roots_ne_zero_of_natDegree_pos
-- given
  {p : Polynomial ℂ} (hp : 0 < p.natDegree) :
-- imply
  p.roots ≠ 0 := by
-- proof
  intro hzero
  have hdegree : p.natDegree = 0 :=
    (IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero (k := ℂ) (p := p)).mp hzero
  omega
  exact hp

end Polynomial

namespace Polynomial

/--
[coe_maxRealRoot_mem_roots](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
lemma coe_maxRealRoot_mem_roots
-- given
  {p : Polynomial ℂ} (hp : p.IsRealRooted) (hdegree : 0 < p.natDegree) :
-- imply
  (p.maxRealRoot : ℂ) ∈ p.roots := by
-- proof
  obtain ⟨z, hz, hreal⟩ :=
    exists_root_re_eq_maxRealRoot (roots_ne_zero_of_natDegree_pos hdegree)
  have him : z.im = 0 := hp z hz
  have hzeq : z = (p.maxRealRoot : ℂ) := by
    apply Complex.ext
    · simpa using hreal
    · simpa using him
  rwa [← hzeq]
  · exact hp
  · exact hdegree

end Polynomial

namespace Polynomial

/--
[eval_re_pos_of_maxRealRoot_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
lemma eval_re_pos_of_maxRealRoot_lt
-- given
  {p : Polynomial ℂ} (hmonic : p.Monic) (hrooted : p.IsRealRooted)
  {x : ℝ} (hx : p.maxRealRoot < x) :
-- imply
  0 < (p.eval (x : ℂ)).re := by
-- proof
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmonic]
  have hprod : 0 < (p.roots.map (fun z ↦ (x : ℂ) - z)).prod := by
    apply Multiset.prod_pos
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [RCLike.pos_iff]
    constructor
    · exact sub_pos.mpr (lt_of_le_of_lt (root_re_le_maxRealRoot hz) hx)
    · simpa using hrooted z hz
  exact (RCLike.pos_iff.mp hprod).1
  · exact hmonic
  · exact hrooted
  · exact hx

end Polynomial

namespace Polynomial

/--
[eval_re_nonneg_of_maxRealRoot_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
lemma eval_re_nonneg_of_maxRealRoot_le
-- given
  {p : Polynomial ℂ} (hmonic : p.Monic) (hrooted : p.IsRealRooted)
  {x : ℝ} (hx : p.maxRealRoot ≤ x) :
-- imply
  0 ≤ (p.eval (x : ℂ)).re := by
-- proof
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmonic]
  have hprod : 0 ≤ (p.roots.map (fun z ↦ (x : ℂ) - z)).prod := by
    apply Multiset.prod_nonneg
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [RCLike.nonneg_iff]
    constructor
    · exact sub_nonneg.mpr (root_re_le_maxRealRoot hz |>.trans hx)
    · simpa using hrooted z hz
  exact (RCLike.nonneg_iff.mp hprod).1
end Polynomial
  · exact hmonic
  · exact hrooted
  · exact hx

-- created on 2026-10-09
-- updated on 2026-10-26
