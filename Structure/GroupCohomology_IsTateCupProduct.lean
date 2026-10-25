import Mathlib
import Abbrev.GroupCohomology_TateCohomology
import Lemma.GroupCohomology.TateSeam
import Def.GroupCohomology_TateShiftMaps
import Abbrev.GroupCohomology_CochainCup
import Structure.GroupCohomology_IsGradedCupProduct
import Abbrev.GroupCohomology_TateCupFamily

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace Rep

section family

variable (k G : Type u) [CommRing k] [Group G] [Fintype G]


structure IsTateCupProduct (cup : TateCupFamily k G) : Prop where
  cup_ofNat_succ : ∀ (A B : Rep.{u} k G) (cup' : groupCohomology.GradedCupFamily A B)
      (_hcup' : groupCohomology.IsGradedCupProduct A B cup') (p q : ℕ)
      (x : groupCohomology A (p + 1)) (y : groupCohomology B (q + 1)),
    cup A B (p + 1 : ℕ) (q + 1 : ℕ) (p + 1 + (q + 1) : ℕ) (Nat.cast_add (p + 1) (q + 1)).symm x y
      = cup' (p + 1) (q + 1) x y
  map_cup : ∀ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') (p q r : ℤ) (h : p + q = r)
      (x : A.tateCohomology p) (y : B.tateCohomology q),
    (tateMap (φ ⊗ₘ ψ) r).hom (cup A B p q r h x y) = cup A' B' p q r h ((tateMap φ p).hom x) ((tateMap ψ q).hom y)
  delta_cup : ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (B : Rep.{u} k G)
      (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) (p q r : ℤ) (h : p + q = r)
      (x : X.X₃.tateCohomology p) (y : B.tateCohomology q),
    (tateδ hXB r).hom (cup X.X₃ B p q r h x y) = cup X.X₁ B (p + 1) q (r + 1) (by omega) ((tateδ hX p).hom x) y
  cup_delta : ∀ (A : Rep.{u} k G) {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
      (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
      (x : A.tateCohomology p) (y : X.X₃.tateCohomology q),
    (tateδ hAX r).hom (cup A X.X₃ p q r h x y)
      = ((p.negOnePow : ℤ) : k) • cup A X.X₁ p (q + 1) (r + 1) (by omega) x ((tateδ hX q).hom y)

end family
end Rep
