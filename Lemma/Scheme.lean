import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.Variety

open AlgebraicGeometry

/--
[isVariety_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Variety.lean)
-/
@[path]
private lemma isVariety_iff_eq
-- given
  (k : Type*) [Field k]
  (X : Scheme) [X.Over (Spec (CommRingCat.of k))] :
-- imply
  (IsVariety k X ↔
    IsSeparated (X ↘ Spec (CommRingCat.of k)) ∧
      LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) ∧
        QuasiCompact (X ↘ Spec (CommRingCat.of k)) ∧
          GeometricallyReduced (X ↘ Spec (CommRingCat.of k))) :=
-- proof
  @AlgebraicGeometry.IsVariety.isVariety_iff k _ X _

/--
[quasiSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Variety.lean)
-/
@[path]
private lemma quasiSeparated_eq
-- given
  (k : Type*) [Field k]
  (X : Scheme) [X.Over (Spec (CommRingCat.of k))]
  [IsVariety k X] :
-- imply
  (QuasiSeparated (X ↘ Spec (CommRingCat.of k))) :=
-- proof
  @AlgebraicGeometry.IsVariety.quasiSeparated k _ X _ _


-- created on 2026-10-09
