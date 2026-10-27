import Mathlib
import Initialize.Tactic.Attr.Basic
open MvPolynomial


/--
[mvpoly_connected_grading](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)

Unfolded form of `IsConnectedGrading k (MvPolynomial (Fin n) k) (homogeneousSubmodule (Fin n) k)`
(`𝒮 0 = (Algebra.linearMap k S).range`); sympy atlas import is currently unbuildable.
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ} :
-- imply
  homogeneousSubmodule (Fin n) k 0 = (Algebra.linearMap k (MvPolynomial (Fin n) k)).range := by
-- proof
  ext p
  simp only [mem_homogeneousSubmodule, LinearMap.mem_range]
  constructor
  ·
    intro hp
    refine ⟨p.coeff 0, ?_⟩
    simp only [Algebra.linearMap_apply, algebraMap_eq]
    ext d
    simp only [coeff_C]
    split_ifs with hd
    ·
      exact hd ▸ rfl
    ·
      symm
      exact hp.coeff_eq_zero ((Finsupp.degree_eq_zero_iff d).not.mpr (Ne.symm hd))
  ·
    rintro ⟨c, rfl⟩
    simp only [Algebra.linearMap_apply, algebraMap_eq]
    exact isHomogeneous_C (Fin n) c


-- created on 2026-10-24
