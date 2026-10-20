import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.ChromaticSymmetric
open SimpleGraph


/--
[SameChromaticSymmetricFunction.refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean)
-/
@[path]
private lemma SameChromaticSymmetricFunction_refl_eq
  [Finite V]
  {H : SimpleGraph W}
  {G : SimpleGraph V} :
-- imply
  SameChromaticSymmetricFunction G G := by
-- proof
  apply SimpleGraph.SameChromaticSymmetricFunction.refl G

/--
[SameChromaticSymmetricFunction.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean)
-/
@[path]
private lemma SameChromaticSymmetricFunction_symm_eq
  [Finite V] [Finite W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
-- given
  (h : SameChromaticSymmetricFunction G H) :
-- imply
  SameChromaticSymmetricFunction H G := by
-- proof
  apply SimpleGraph.SameChromaticSymmetricFunction.symm h

/--
[SameChromaticSymmetricFunction.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean)
-/
@[path]
private lemma SameChromaticSymmetricFunction_trans_eq
  [Finite V] [Finite W] [Finite U]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {K : SimpleGraph U}
-- given
  (hGH : SameChromaticSymmetricFunction G H)
  (hHK : SameChromaticSymmetricFunction H K) :
-- imply
  SameChromaticSymmetricFunction G K := by
-- proof
  apply SimpleGraph.SameChromaticSymmetricFunction.trans hGH hHK

/--
[SameChromaticSymmetricFunction.of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean)
-/
@[path]
private lemma SameChromaticSymmetricFunction_of_iso_eq
  [Finite V] [Finite W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
-- given
  (e : G ≃g H) :
-- imply
  SameChromaticSymmetricFunction G H := by
-- proof
  apply SimpleGraph.SameChromaticSymmetricFunction.of_iso e


-- created on 2026-10-20
