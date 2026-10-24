import Mathlib
import sympy.Basic
import sympy.atlas.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
open CategoryTheory
open TateCohomology


namespace TateCohomology

/--
[tateCohomologyCard_eq_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma tateCohomologyCard_eq_natCast
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
  {n : ℤ} [Finite ↥(tateCohomology M n)] :
-- imply
  tateCohomologyCard M n = Nat.card ↥(tateCohomology M n) :=
-- proof
  Nat.cast_card.symm

end TateCohomology

namespace TateCohomology

/--
[herbrandQuotient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_eq
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
-- given
  (h : HerbrandFinite M) :
-- imply
  herbrandQuotient M h = (Nat.card ↥(tateCohomology M 0) : ℚ) /
      Nat.card ↥(tateCohomology M (-1)) :=
-- proof
  rfl

end TateCohomology

namespace TateCohomology

/--
[herbrandQuotient_den_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_den_pos
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
-- given
  (h : HerbrandFinite M) :
-- imply
  0 < Nat.card ↥(tateCohomology M (-1)) := by
-- proof
  have := h.2
  exact Nat.card_pos

end TateCohomology

namespace TateCohomology

/--
[herbrandQuotient_den_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_den_ne_zero
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
-- given
  (h : HerbrandFinite M) :
-- imply
  Nat.card ↥(tateCohomology M (-1)) ≠ 0 :=
-- proof
  ne_of_gt (herbrandQuotient_den_pos M h)

end TateCohomology

namespace TateCohomology

/--
[herbrandQuotient_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_pos
  {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {M : Rep R G}
-- given
  (h : HerbrandFinite M) :
-- imply
  0 < herbrandQuotient M h := by
-- proof
  have := h.1
  have := h.2
  rw [herbrandQuotient_eq]
  exact div_pos (Nat.cast_pos.mpr Nat.card_pos) (Nat.cast_pos.mpr Nat.card_pos)

end TateCohomology

namespace TateCohomology

/--
[herbrandQuotient_congr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean)
-/
@[path]
private lemma herbrandQuotient_congr
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
  rw [herbrandQuotient_eq, herbrandQuotient_eq, Nat.card_congr e₀,
    Nat.card_congr e₁]

end TateCohomology

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


-- created on 2026-10-20
-- updated on 2026-10-24
