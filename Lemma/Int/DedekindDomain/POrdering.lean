import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.POrdering
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

/--
[isPOrdering_unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma isPOrdering_unfold
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R} :
-- imply
  IsPOrdering p S a ↔
    S.Infinite ∧ (∀ n, a n ∈ S) ∧
    ∀ n, ∀ x ∈ S,
    pOrderingValuation p a n (a n) ≤
    pOrderingValuation p a n x :=
-- proof
  Iff.rfl

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[IsPOrdering.infinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma IsPOrdering.infinite
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (h : IsPOrdering p S a) :
-- imply
  S.Infinite :=
-- proof
  h.1

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[IsPOrdering.mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma IsPOrdering.mem
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
  {n : ℕ}
-- given
  (h : IsPOrdering p S a) :
-- imply
  a n ∈ S :=
-- proof
  h.2.1 n

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[IsPOrdering.min_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma IsPOrdering.min_le
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
  {n : ℕ}
  {x : R}
-- given
  (h : IsPOrdering p S a)
  (hx : x ∈ S) :
-- imply
  pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x :=
-- proof
  h.2.2 n x hx

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[IsPOrdering.isLeast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma IsPOrdering.isLeast
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
  {n : ℕ}
-- given
  (h : IsPOrdering p S a) :
-- imply
  IsLeast (pOrderingValuation p a n '' S)
    (pOrderingValuation p a n (a n)) := by
-- proof
  constructor
  · exact ⟨a n, h.mem n, rfl⟩
  · intro y hy
    obtain ⟨x, hxS, rfl⟩ := hy
    exact h.min_le n x hxS

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[IsPOrdering.intro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma IsPOrdering.intro
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (hinf : S.Infinite)
  (hmem : ∀ n, a n ∈ S)
  (hmin : ∀ n, ∀ x ∈ S, pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x) :
-- imply
  IsPOrdering p S a :=
-- proof
  ⟨hinf, hmem, hmin⟩

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[pOrderingValuation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma pOrderingValuation_zero
  [CommRing R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {a : ℕ → R}
  {x : R} :
-- imply
  pOrderingValuation p a 0 x = 0 := by
-- proof
  unfold pOrderingValuation
  rw [Finset.range_zero, Finset.prod_empty,
    Ideal.span_singleton_one]
  have hunit : ¬ IsUnit p.asIdeal := by
    rwa [Ideal.isUnit_iff]
  have htop : (⊤ : Ideal R) = 1 := Ideal.one_eq_top.symm
  rw [htop]
  exact emultiplicity_of_one_right hunit

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[isPOrdering_iff_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma isPOrdering_iff_pos
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R} :
-- imply
  IsPOrdering p S a ↔
    S.Infinite ∧ (∀ n, a n ∈ S) ∧
    ∀ n, 1 ≤ n → ∀ x ∈ S,
    pOrderingValuation p a n (a n) ≤
    pOrderingValuation p a n x := by
-- proof
  constructor
  · intro h
    exact ⟨h.infinite, h.mem, fun n _ x hx => h.min_le n x hx⟩
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro n x hx
    by_cases hn : 1 ≤ n
    · exact h.2.2 n hn x hx
    · have hn0 : n = 0 := by omega
      subst hn0
      rw [pOrderingValuation_zero, pOrderingValuation_zero]

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
