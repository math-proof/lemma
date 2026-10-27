import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueMap
open LaurentSeries
open HahnSeries


namespace LaurentSeries

/--
[residue_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean)
-/
@[path]
lemma residue_apply
  {k : Type*}
  [Field k]
  {k}
  {f : LaurentSeries k} :
-- imply
  residue k f = f.coeff (-1) :=
-- proof
  rfl

end LaurentSeries

namespace LaurentSeries

/--
[residue_single_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean)
-/
@[path]
lemma residue_single_neg_one
  {k : Type*}
  [Field k]
  {k}
  {a : k} :
-- imply
  residue k (HahnSeries.single (-1 : ℤ) a) = a :=
-- proof
  HahnSeries.coeff_single_same (-1 : ℤ) a

end LaurentSeries

namespace LaurentSeries

/--
[residue_single_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean)
-/
@[path]
lemma residue_single_of_ne
  {k : Type*}
  [Field k]
  {k}
  {n : ℤ}
  {a : k}
-- given
  (h : n ≠ -1) :
-- imply
  residue k (HahnSeries.single n a) = 0 :=
-- proof
  HahnSeries.coeff_single_of_ne (Ne.symm h)

end LaurentSeries

namespace LaurentSeries

/--
[residue_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean)
-/
@[path]
lemma residue_zero
  {k : Type*}
  [Field k]
  {k} :
-- imply
  residue k (0 : LaurentSeries k) = 0 :=
-- proof
  map_zero _

end LaurentSeries

namespace LaurentSeries

/--
[residue_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean)
-/
@[path]
lemma residue_add
  {k : Type*}
  [Field k]
  {k}
  {f g : LaurentSeries k} :
-- imply
  residue k (f + g) = residue k f + residue k g :=
-- proof
  map_add _ f g

end LaurentSeries

namespace LaurentSeries

/--
[residue_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean)
-/
@[path]
lemma residue_smul
  {k : Type*}
  [Field k]
  {k}
  {c : k}
  {f : LaurentSeries k} :
-- imply
  residue k (c • f) = c • residue k f :=
-- proof
  map_smul _ c f

end LaurentSeries

namespace LaurentSeries

/--
[residue_ofPowerSeries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean)
-/
@[path]
lemma residue_ofPowerSeries
  {k : Type*}
  [Field k]
  {k}
  {f : PowerSeries k} :
-- imply
  residue k (HahnSeries.ofPowerSeries ℤ k f) = 0 := by
-- proof
  simp only [residue_apply, ofPowerSeries_apply]
  apply embDomain_notin_range
  simp only [Set.mem_range, not_exists]
  intro n
  show ¬ (↑n : ℤ) = (-1 : ℤ)
  omega

end LaurentSeries

namespace LaurentSeries

/--
[residue_uniformizer_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean)
-/
@[path]
lemma residue_uniformizer_inv
  {k : Type*}
  [Field k]
  {k} :
-- imply
  residue k (HahnSeries.single (-1 : ℤ) (1 : k)) = 1 := by
-- proof
  simp

end LaurentSeries


-- created on 2026-10-23
