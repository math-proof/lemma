import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Fourier.PrincipalMinor
open Fourier


/--
[principalMinorMatrix_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean)
-/
@[path]
private lemma principalMinorMatrix_apply_eq
  [CommRing R]
  {M : ℕ}
  {root : RootData M R}
  {S : Finset (ZMod M)}
  {i j : S} :
-- imply
  principalMinorMatrix M root S i j = root.zeta ^ (i.val * j.val).val := by
-- proof
  apply Fourier.principalMinorMatrix_apply M root S i j

/--
[principalMinorDet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean)
-/
@[path]
private lemma principalMinorDet_empty_eq
  [CommRing R]
  {M : ℕ}
  {root : RootData M R} :
-- imply
  principalMinorDet M root ∅ = 1 := by
-- proof
  apply Fourier.principalMinorDet_empty M root

/--
[principalMinorDet_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean)
-/
@[path]
private lemma principalMinorDet_singleton_eq
  [CommRing R]
  {M : ℕ}
  {root : RootData M R}
  {a : ZMod M} :
-- imply
  principalMinorDet M root {a} = root.zeta ^ (a * a).val := by
-- proof
  apply Fourier.principalMinorDet_singleton M root a


-- created on 2026-10-20
