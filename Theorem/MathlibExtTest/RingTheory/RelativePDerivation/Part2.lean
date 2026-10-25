/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/RelativePDerivation.lean -/


import Instance.RingTheory.RelativePDerivation
import Lemma.Int.RelativePDerivation
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Def.MathlibExtTest.RingTheory.RelativePDerivation
open MetaMathlibExt


-- Exercise the bundled structure end-to-end.
example (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] :
    let d := zeroDerivation A p
    (d : A → ZMod 1) 1 = 0 ∧
    (∀ x y : A, (d : A → ZMod 1) (x + y) =
      (d : A → ZMod 1) x + (d : A → ZMod 1) y + pDerivationCorrection p (uZero A x) (uZero A y)) ∧
    (∀ x y : A, (d : A → ZMod 1) (x * y) =
      (uZero A x) ^ p * (d : A → ZMod 1) y +
      (uZero A y) ^ p * (d : A → ZMod 1) x +
      (p : ZMod 1) * (d : A → ZMod 1) x * (d : A → ZMod 1) y) := by
  refine ⟨rfl, fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

-- CoeFun works.
example (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] (x : A) :
    (zeroDerivation A p : A → ZMod 1) x = 0 := rfl

