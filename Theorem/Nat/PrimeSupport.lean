module

public import Mathlib
public import Def.NumberTheory.PrimeSupport

public section

open Nat


namespace Nat

/--
[samePrimeSupport_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeSupport.lean)
-/
public theorem samePrimeSupport_refl
  {a : ℕ} :
-- imply
  SamePrimeSupport a a :=
-- proof
  fun _ _ => Iff.rfl

end Nat

namespace Nat

/--
[SamePrimeSupport.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeSupport.lean)
-/
public theorem SamePrimeSupport.symm
  {a b : ℕ}
-- given
  (h : SamePrimeSupport a b) :
-- imply
  SamePrimeSupport b a :=
-- proof
  fun p hp => Iff.symm (h p hp)

end Nat

namespace Nat

/--
[SamePrimeSupport.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeSupport.lean)
-/
public theorem SamePrimeSupport.trans
  {a b c : ℕ}
-- given
  (h0 : SamePrimeSupport a b)
  (h1 : SamePrimeSupport b c) :
-- imply
  SamePrimeSupport a c :=
-- proof
  fun p hp => (h0 p hp).trans (h1 p hp)

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
