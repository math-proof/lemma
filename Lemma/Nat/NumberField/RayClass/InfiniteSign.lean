import Mathlib
import sympy.Basic
import Theorem.NumberTheory.NumberField.RayClass.InfiniteSign.Part4
open NumberField
open Modulus


/--
[signAtRealPlace_apply_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InfiniteSign.lean)
-/
@[path]
private lemma signAtRealPlace_apply_eq_one_iff_eq
  [Field K] [NumberField K]
  {w : RealPlace K}
  {x : Kˣ} :
-- imply
  signAtRealPlace w x = 1 ↔
    0 < InfinitePlace.embedding_of_isReal w.property (x : K) := by
-- proof
  apply NumberField.Modulus.signAtRealPlace_apply_eq_one_iff w x

/--
[infiniteSignMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InfiniteSign.lean)
-/
@[path]
private lemma infiniteSignMap_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m}
  {w : m.infinitePart} :
-- imply
  infiniteSignMap m x w = signAtRealPlace (w : RealPlace K) (x : Kˣ) := by
-- proof
  apply NumberField.Modulus.infiniteSignMap_apply m x w

/--
[infiniteSignMap_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InfiniteSign.lean)
-/
@[path]
private lemma infiniteSignMap_eq_one_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  infiniteSignMap m x = 1 ↔ PositiveAtInfinitePart m (x : Kˣ) := by
-- proof
  apply NumberField.Modulus.infiniteSignMap_eq_one_iff m x

/--
[mem_positiveRayElements_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InfiniteSign.lean)
-/
@[path]
private lemma mem_positiveRayElements_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  x ∈ positiveRayElements m ↔ PositiveAtInfinitePart m (x : Kˣ) := by
-- proof
  apply NumberField.Modulus.mem_positiveRayElements_iff m x


-- created on 2026-10-20
