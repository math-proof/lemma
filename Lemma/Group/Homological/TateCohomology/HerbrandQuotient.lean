import Mathlib
import sympy.Basic
import sympy.atlas.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
open CategoryTheory
open TateCohomology


/--
[tateHomologyCard_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma tateHomologyCard_zero_eq
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G} :
-- imply
  tateHomologyCard M 0 = tateCohomologyCard M (-1) := by
-- proof
  apply TateCohomology.tateHomologyCard_zero M

/--
[tateCohomologyCard_eq_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma tateCohomologyCard_eq_natCast_eq
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
  {n : ℤ} [Finite ↥(tateCohomology M n)] :
-- imply
  tateCohomologyCard M n = Nat.card ↥(tateCohomology M n) := by
-- proof
  apply TateCohomology.tateCohomologyCard_eq_natCast M n

/--
[herbrandQuotient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_eq_eq
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
-- given
  (h : HerbrandFinite M) :
-- imply
  herbrandQuotient M h = (Nat.card ↥(tateCohomology M 0) : ℚ) /
      Nat.card ↥(tateCohomology M (-1)) := by
-- proof
  apply TateCohomology.herbrandQuotient_eq M h

/--
[herbrandQuotient_den_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_den_pos_eq
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
-- given
  (h : HerbrandFinite M) :
-- imply
  0 < Nat.card ↥(tateCohomology M (-1)) := by
-- proof
  apply TateCohomology.herbrandQuotient_den_pos M h

/--
[herbrandQuotient_den_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_den_ne_zero_eq
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
-- given
  (h : HerbrandFinite M) :
-- imply
  Nat.card ↥(tateCohomology M (-1)) ≠ 0 := by
-- proof
  apply TateCohomology.herbrandQuotient_den_ne_zero M h

/--
[herbrandQuotient_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_pos_eq
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
-- given
  (h : HerbrandFinite M) :
-- imply
  0 < herbrandQuotient M h := by
-- proof
  apply TateCohomology.herbrandQuotient_pos M h

/--
[herbrandQuotient_congr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_congr_eq
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M N : Rep R G}
  {hM : HerbrandFinite M}
  {hN : HerbrandFinite N}
-- given
  (e₀ : ↥(tateCohomology M 0) ≃ ↥(tateCohomology N 0))
  (e₁ : ↥(tateCohomology M (-1)) ≃ ↥(tateCohomology N (-1))) :
-- imply
  herbrandQuotient M hM = herbrandQuotient N hN := by
-- proof
  apply TateCohomology.herbrandQuotient_congr e₀ e₁


-- created on 2026-10-20
