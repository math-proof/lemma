import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal
open MvPolynomial Classical Lec5BezoutPascal


namespace Lec5BezoutPascal

/--
[hypersurfaceMultiplicity_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean)
-/
@[path]
lemma hypersurfaceMultiplicity_spec
  {k : Type*}
  [Field k]
  {n : ℕ}
  {g : MvPolynomial (Fin n) k}
  {p : Fin n → k}
-- given
  (hg : g ≠ 0) :
-- imply
  MvPolynomial.homogeneousComponent (hypersurfaceMultiplicity k g p hg) (translatePoly k g p) ≠ 0 :=
-- proof
  Nat.find_spec (exists_homogeneousComponent_ne_zero k (translatePoly k g p)
    (translatePoly_ne_zero k g p hg))

end Lec5BezoutPascal

namespace Lec5BezoutPascal

/--
[hypersurfaceMultiplicity_min](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean)
-/
@[path]
lemma hypersurfaceMultiplicity_min
  {k : Type*}
  [Field k]
  {n : ℕ}
  {g : MvPolynomial (Fin n) k}
  {p : Fin n → k}
  {m : ℕ}
-- given
  (hg : g ≠ 0)
  (hm : m < hypersurfaceMultiplicity k g p hg) :
-- imply
  MvPolynomial.homogeneousComponent m (translatePoly k g p) = 0 := by
-- proof
  by_contra h
  exact Nat.lt_irrefl _ (lt_of_lt_of_le hm (Nat.find_min' _ h))

end Lec5BezoutPascal

namespace Lec5BezoutPascal

/--
[bezout_projective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean)
-/
@[path]
lemma bezout_projective
  {k : Type*}
  [Field k]
  {k : Type*}
  [Field k]
  {d e : ℕ}
  {f g : MvPolynomial (Fin 3) k}
  {S : Finset (ProjectivePoint k f g)}
-- given
  (hd : 0 < d)
  (he : 0 < e)
  (hf_homog : f.IsHomogeneous d)
  (hg_homog : g.IsHomogeneous e)
  (hf_ne : f ≠ 0)
  (hg_ne : g ≠ 0)
  (hcoprime : IsCoprime f g)
  (hS : ∀ p, projLocalIntersectionMultiplicity k f g p ≠ 0 → p ∈ S)
  (hS' : ∀ p ∈ S, projLocalIntersectionMultiplicity k f g p ≠ 0) :
-- imply
  S.sum (fun p => projLocalIntersectionMultiplicity k f g p) = d * e :=
-- proof
  projective_bezout_multiplicity_sum k d e hd he f g hf_homog hg_homog hf_ne hg_ne hcoprime S hS hS'

end Lec5BezoutPascal

/--
[translatePoly_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean)
-/
@[path]
private lemma translatePoly_injective_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {p : Fin n → k} :
-- imply
  Function.Injective (fun g => translatePoly k g p) := by
-- proof
  apply Lec5BezoutPascal.translatePoly_injective k p

/--
[translatePoly_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean)
-/
@[path]
private lemma translatePoly_ne_zero_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {g : MvPolynomial (Fin n) k}
  {p : Fin n → k}
-- given
  (hg : g ≠ 0) :
-- imply
  translatePoly k g p ≠ 0 := by
-- proof
  apply Lec5BezoutPascal.translatePoly_ne_zero k g p hg

/--
[exists_homogeneousComponent_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean)
-/
@[path]
private lemma exists_homogeneousComponent_ne_zero_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {φ : MvPolynomial (Fin n) k}
-- given
  (h : φ ≠ 0) :
-- imply
  ∃ m : ℕ, MvPolynomial.homogeneousComponent m φ ≠ 0 := by
-- proof
  apply Lec5BezoutPascal.exists_homogeneousComponent_ne_zero k φ h


-- created on 2026-10-23
