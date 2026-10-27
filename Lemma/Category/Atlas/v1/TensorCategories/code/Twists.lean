import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TensorCategories.code.Twists.Part2
open CategoryTheory TensorCategories
open scoped TensorProduct
open TensorCategories CategoryTheory


/--
[GaugeEquiv.equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean)
-/
@[path]
lemma GaugeEquiv.equivalence
  {R : Type u}
  [CommSemiring R]
  {H : Type u}
  [Semiring H]
  [Bialgebra R H] :
-- imply
  Equivalence (GaugeEquiv (R := R) (H := H)) where refl :=
-- proof
  GaugeEquiv.refl
    symm := GaugeEquiv.symm
    trans := GaugeEquiv.trans
namespace BialgebraTwist
variable (R : Type u) [CommSemiring R]
variable (H : Type u) [Semiring H] [HopfAlgebra R H]

/--
[GaugeEquiv.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean)
-/
@[path]
private lemma refl_eq
  {R : Type u}
  [CommSemiring R]
  {H : Type u}
  [Semiring H]
  [Bialgebra R H]
  {J : (H ⊗[R] H)ˣ} :
-- imply
  GaugeEquiv J J := by
-- proof
  apply GaugeEquiv.refl J

/--
[GaugeEquiv.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean)
-/
@[path]
private lemma symm_eq
  {R : Type u}
  [CommSemiring R]
  {H : Type u}
  [Semiring H]
  [Bialgebra R H]
  {J₁ J₂ : (H ⊗[R] H)ˣ}
-- given
  (h : GaugeEquiv J₁ J₂) :
-- imply
  GaugeEquiv J₂ J₁ := by
-- proof
  apply GaugeEquiv.symm h

/--
[GaugeEquiv.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean)
-/
@[path]
private lemma trans_eq
  {R : Type u}
  [CommSemiring R]
  {H : Type u}
  [Semiring H]
  [Bialgebra R H]
  {J₁ J₂ J₃ : (H ⊗[R] H)ˣ}
-- given
  (h₁₂ : GaugeEquiv J₁ J₂)
  (h₂₃ : GaugeEquiv J₂ J₃) :
-- imply
  GaugeEquiv J₁ J₃ := by
-- proof
  apply GaugeEquiv.trans h₁₂ h₂₃


-- created on 2026-10-23
