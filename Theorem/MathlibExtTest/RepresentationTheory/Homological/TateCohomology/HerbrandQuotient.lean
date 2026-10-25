/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean -/


import Def.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient.Part2
import Lemma.Int.TateCohomologyCard.eq.CardTateCohomology
open CategoryTheory TateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

#check @TateCohomology.tateCohomologyCard
#check @TateCohomology.tateHomologyCard
#check @TateCohomology.HerbrandFinite
#check @TateCohomology.herbrandQuotient

-- Every definition elaborates on Tate cohomology carriers.


-- Degree-zero homology conversion, by the conversion theorem and by `simp`.
noncomputable example (M : Rep R G) :
    tateHomologyCard M 0 = tateCohomologyCard M (-1) :=
  tateHomologyCard_zero M

noncomputable example (M : Rep R G) :
    tateHomologyCard M 0 = tateCohomologyCard M (-1) := by simp

-- Generic integer-index homology conversion.
noncomputable example (M : Rep R G) (n : ℤ) :
    tateHomologyCard M n = tateCohomologyCard M (-n - 1) := rfl

-- Cardinal-valued API agrees with `Nat.card` under finiteness.
noncomputable example (M : Rep R G) [Finite ↥(tateCohomology M 0)] :
    tateCohomologyCard M 0 = Nat.card ↥(tateCohomology M 0) :=
  tateCohomologyCard_eq_natCast M 0

-- Quotient unfolding as a ratio of `Nat.card`s.
noncomputable example (M : Rep R G) (h : HerbrandFinite M) :
    herbrandQuotient M h = (Nat.card ↥(tateCohomology M 0) : ℚ) /
      Nat.card ↥(tateCohomology M (-1)) :=
  herbrandQuotient_eq M h

-- Denominator positivity, nonzeroness, and quotient positivity.
noncomputable example (M : Rep R G) (h : HerbrandFinite M) :
    0 < Nat.card ↥(tateCohomology M (-1)) :=
  herbrandQuotient_den_pos M h

noncomputable example (M : Rep R G) (h : HerbrandFinite M) :
    Nat.card ↥(tateCohomology M (-1)) ≠ 0 :=
  herbrandQuotient_den_ne_zero M h

noncomputable example (M : Rep R G) (h : HerbrandFinite M) :
    0 < herbrandQuotient M h :=
  herbrandQuotient_pos M h

-- Invariance under carrier equivalences, including the reflexive case.
noncomputable example (M N : Rep R G) (hM : HerbrandFinite M)
    (hN : HerbrandFinite N)
    (e₀ : ↥(tateCohomology M 0) ≃ ↥(tateCohomology N 0))
    (e₁ : ↥(tateCohomology M (-1)) ≃ ↥(tateCohomology N (-1))) :
    herbrandQuotient M hM = herbrandQuotient N hN :=
  herbrandQuotient_congr e₀ e₁

noncomputable example (M : Rep R G) (h : HerbrandFinite M) :
    herbrandQuotient M h = herbrandQuotient M h :=
  herbrandQuotient_congr (Equiv.refl _) (Equiv.refl _)

