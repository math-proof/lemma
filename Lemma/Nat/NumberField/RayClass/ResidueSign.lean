import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.ResidueSign
open scoped nonZeroDivisors
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[residueSignMap_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ResidueSign.lean)
-/
@[path]
lemma residueSignMap_eq_one_iff
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  residueSignMap m x = 1 ↔ IsRayElementOne m (x : Kˣ) := by
-- proof
  rw [← MonoidHom.mem_ker, residueSignMap_ker]
  constructor
  · intro h
    obtain ⟨hfin, hpos⟩ := (mem_rayOneElements_iff m x).mp h
    exact ⟨x.property, hfin, hpos⟩
  · intro h
    exact (mem_rayOneElements_iff m x).mpr ⟨h.congruent, h.positive⟩

end NumberField.Modulus

/--
[residueSignMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ResidueSign.lean)
-/
@[path]
private lemma residueSignMap_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  residueSignMap m x = (infiniteSignMap m x, finiteResidueMap m x) := by
-- proof
  apply NumberField.Modulus.residueSignMap_apply m x

/--
[mem_rayOneElements_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ResidueSign.lean)
-/
@[path]
private lemma mem_rayOneElements_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  x ∈ rayOneElements m ↔
    CongruentOneAtFinitePart m (x : Kˣ) ∧
    PositiveAtInfinitePart m (x : Kˣ) := by
-- proof
  apply NumberField.Modulus.mem_rayOneElements_iff m x

/--
[residueSignMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ResidueSign.lean)
-/
@[path]
private lemma residueSignMap_surjective_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Surjective (residueSignMap m) := by
-- proof
  apply NumberField.Modulus.residueSignMap_surjective m

/--
[residueSignMap_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ResidueSign.lean)
-/
@[path]
private lemma residueSignMap_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (residueSignMap m).ker = rayOneElements m := by
-- proof
  apply NumberField.Modulus.residueSignMap_ker m

/--
[rayElementsQuotientEquivResidueSign_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ResidueSign.lean)
-/
@[path]
private lemma rayElementsQuotientEquivResidueSign_mk_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayElementsQuotientEquivResidueSign m (QuotientGroup.mk x) =
    residueSignMap m x := by
-- proof
  apply NumberField.Modulus.rayElementsQuotientEquivResidueSign_mk m x


-- created on 2026-10-20
-- updated on 2026-10-23
