import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry10ZetaSide
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry10Zeta4


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zeta4

/--
[meromorphicOn_chapter7Entry10ZetaSide](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10ZetaSide.lean)
-/
@[path]
lemma meromorphicOn_chapter7Entry10ZetaSide
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  MeromorphicOn (chapter7Entry10ZetaSide n) Set.univ := by
-- proof
  have hpow : AnalyticOnNhd ℂ (fun r : ℂ => Complex.cpow (n : ℂ) (r + 1)) Set.univ :=
    fun r _ => ((differentiable_id.add_const 1).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))).analyticAt r
  exact (analyticOnNhd_const.sub hpow).meromorphicOn.mul
    (meromorphicOn_riemannZeta.comp_analyticOnNhd analyticOnNhd_id.neg (Set.mapsTo_univ _ _))
end



-- created on 2026-10-20
-- updated on 2026-10-23
