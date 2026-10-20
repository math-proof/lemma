/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10ZetaSide.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import sympy.atlas.NumberTheory.LSeries.RiemannZeta
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10: the zeta side

The right side `(1 - n^(r+1)) ζ(-r)` shared by the Entry 10 identities of B. C. Berndt,
*Ramanujan's Notebooks, Part I* (Springer, 1985), Chapter 7, and its meromorphicity. It lives in
the `Entry10Zeta4` namespace because that entry's frozen statement pins this name.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zeta4

noncomputable section

def chapter7Entry10ZetaSide (n : ℕ) (r : ℂ) : ℂ :=
  (1 - Complex.cpow (n : ℂ) (r + 1)) * riemannZeta (-r)

theorem meromorphicOn_chapter7Entry10ZetaSide (n : ℕ) (hn : 0 < n) :
    MeromorphicOn (chapter7Entry10ZetaSide n) Set.univ := by
  have hpow : AnalyticOnNhd ℂ (fun r : ℂ => Complex.cpow (n : ℂ) (r + 1)) Set.univ :=
    fun r _ => ((differentiable_id.add_const 1).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))).analyticAt r
  exact (analyticOnNhd_const.sub hpow).meromorphicOn.mul
    (meromorphicOn_riemannZeta.comp_analyticOnNhd analyticOnNhd_id.neg (Set.mapsTo_univ _ _))

end

end Entry10Zeta4
