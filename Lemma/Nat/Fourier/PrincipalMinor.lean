import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Fourier.PrincipalMinor
open Fourier


namespace Fourier

/--
[principalMinorMatrix_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean)
-/
@[path]
lemma principalMinorMatrix_apply
  [CommRing R]
  (M : ℕ)
  (root : RootData M R)
  (S : Finset (ZMod M))
  (i j : S) :
-- imply
  principalMinorMatrix M root S i j = root.zeta ^ (i.val * j.val).val := by
-- proof
  simp [principalMinorMatrix]

/--
[principalMinorDet_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean)
-/
@[path]
lemma principalMinorDet_singleton
  [CommRing R]
  (M : ℕ)
  (root : RootData M R)
  (a : ZMod M) :
-- imply
  principalMinorDet M root {a} = root.zeta ^ (a * a).val := by
-- proof
  simp [principalMinorDet, principalMinorMatrix_apply]

end Fourier

namespace Fourier

/--
[principalMinorDet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean)
-/
@[path]
lemma principalMinorDet_empty
  [CommRing R]
  {M : ℕ}
  {root : RootData M R} :
-- imply
  principalMinorDet M root ∅ = 1 := by
-- proof
  simp [principalMinorDet]

end Fourier


-- created on 2026-10-20
-- updated on 2026-10-28
