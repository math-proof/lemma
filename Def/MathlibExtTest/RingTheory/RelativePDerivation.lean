/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/RelativePDerivation.lean -/


import Instance.RingTheory.RelativePDerivation
import Lemma.Int.RelativePDerivation
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Theorem.MathlibExtTest.RingTheory.RelativePDerivation
open MetaMathlibExt


-- Zero ring is terminal: the unique ring hom to ZMod 1.
def uZero (A : Type*) [CommRing A] : A →+* ZMod 1 where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

-- Real RelativePDerivation into the zero ring ZMod 1.
-- All laws hold because ZMod 1 is subsingleton (0 = 1).
def zeroDerivation (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] :
    RelativePDerivation p (uZero A) where
  toFun _ := 0
  map_one := rfl
  map_add _ _ := Subsingleton.elim _ _
  map_mul _ _ := Subsingleton.elim _ _

