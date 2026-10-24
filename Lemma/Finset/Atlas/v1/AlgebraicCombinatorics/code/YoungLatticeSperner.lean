import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner
open SpernerProperty YoungLattice YoungLattice.Lmn QuotientIsoLmn GroupActions WreathOrbits Finset MulAction
open scoped Classical Pointwise
open QuotientIsoLmn GroupActions WreathOrbits Finset MulAction


namespace YoungLattice.Lmn

/--
[hasSpernerProperty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
lemma hasSpernerProperty
  {m n : ℕ}
  {m n : ℕ} :
-- imply
  HasSpernerProperty (α := Lmn m n) := by
-- proof
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
  letI := quotientPoset_gradedPoset (m * n) (wreathSubgroup m n)
  obtain ⟨e, hgrade⟩ := quotientPosetIsoLmn m n
  exact hasSpernerProperty_of_orderIso e hgrade boolean_quotient_sperner

end YoungLattice.Lmn

namespace YoungLattice.Lmn

/--
[Lmn_isRankUnimodal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
lemma Lmn_isRankUnimodal
  {m n : ℕ}
  {m n : ℕ} :
-- imply
  IsRankUnimodal (α := Lmn m n) := by
-- proof
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
  letI := quotientPoset_gradedPoset (m * n) (wreathSubgroup m n)
  obtain ⟨e, hgrade⟩ := quotientPosetIsoLmn m n
  exact isRankUnimodal_of_orderIso e hgrade boolean_quotient_unimodal

end YoungLattice.Lmn

namespace YoungLattice.Lmn

/--
[isRankSymmetric_and_isRankUnimodal_and_hasSpernerProperty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
lemma isRankSymmetric_and_isRankUnimodal_and_hasSpernerProperty
  {m n : ℕ}
  {m n : ℕ} :
-- imply
  IsRankSymmetric (α := Lmn m n) ∧ IsRankUnimodal (α := Lmn m n) ∧ HasSpernerProperty (α := Lmn m n) :=
-- proof
  ⟨Lmn_isRankSymmetric m n, Lmn_isRankUnimodal m n, hasSpernerProperty m n⟩

end YoungLattice.Lmn

/--
[wreathElemToPerm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
private lemma wreathElemToPerm_apply_eq
  {m n : ℕ}
  {g : WreathElem m n}
  {p : Fin m × Fin n} :
-- imply
  wreathElemToPerm g p = g.actOn p := by
-- proof
  apply YoungLattice.Lmn.wreathElemToPerm_apply g p

/--
[sum_rowSize_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
private lemma sum_rowSize_eq_card_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  ∑ i : Fin m, rowSize S i = S.card := by
-- proof
  apply YoungLattice.Lmn.sum_rowSize_eq_card S

/--
[image_finProdFinEquiv_actOnSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
private lemma image_finProdFinEquiv_actOnSet_eq
  {m n : ℕ}
  {g : WreathElem m n}
  {S : Finset (Fin m × Fin n)} :
-- imply
  (g.actOnSet S).image finProdFinEquiv = (finProdFinEquiv.permCongr (wreathElemToPerm g)) • (S.image finProdFinEquiv) := by
-- proof
  apply YoungLattice.Lmn.image_finProdFinEquiv_actOnSet g S

/--
[smul_image_symm_eq_actOnSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
private lemma smul_image_symm_eq_actOnSet_eq
  {m n : ℕ}
  {g : WreathElem m n}
  {A : Finset (Fin (m * n))} :
-- imply
  ((finProdFinEquiv.permCongr (wreathElemToPerm g)) • A).image finProdFinEquiv.symm = g.actOnSet (A.image finProdFinEquiv.symm) := by
-- proof
  apply YoungLattice.Lmn.smul_image_symm_eq_actOnSet g A

/--
[wreathSubgroup_orbit_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
private lemma wreathSubgroup_orbit_of_sameOrbit_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
-- given
  (h : WreathOrbits.SameOrbit S T) :
-- imply
  ∃ (g : ↥(wreathSubgroup m n)), g • (S.image finProdFinEquiv) = T.image finProdFinEquiv := by
-- proof
  apply YoungLattice.Lmn.wreathSubgroup_orbit_of_sameOrbit S T h

/--
[sameOrbit_of_wreathSubgroup_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
private lemma sameOrbit_of_wreathSubgroup_orbit_eq
  {m n : ℕ}
  {A : Finset (Fin (m * n))}
  {g : ↥(wreathSubgroup m n)} :
-- imply
  WreathOrbits.SameOrbit (A.image finProdFinEquiv.symm) ((g • A).image finProdFinEquiv.symm) := by
-- proof
  apply YoungLattice.Lmn.sameOrbit_of_wreathSubgroup_orbit A g

/--
[sumParts_gridYoungToLmn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
private lemma sumParts_gridYoungToLmn_eq
  {m n : ℕ}
  {S : GridYoungDiagram m n} :
-- imply
  sumParts (gridYoungToLmn S) = S.val.card := by
-- proof
  apply YoungLattice.Lmn.sumParts_gridYoungToLmn S

/--
[grade_composed_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean)
-/
@[path]
private lemma grade_composed_iso_eq
  {m n : ℕ}
  {A : Finset (Fin (m * n))} :
-- imply
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n) grade ℕ ((wreathQuotientIsoLmn m n) (wreathQuotientMk (A.image finProdFinEquiv.symm))) = A.card := by
-- proof
  apply YoungLattice.Lmn.grade_composed_iso A


-- created on 2026-10-23
