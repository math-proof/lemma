import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.POrdering
open IsDedekindDomain.HeightOneSpectrum


/--
[isPOrdering_unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
private lemma isPOrdering_unfold_eq
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R} :
-- imply
  IsPOrdering p S a ↔
    S.Infinite ∧ (∀ n, a n ∈ S) ∧
    ∀ n, ∀ x ∈ S,
    pOrderingValuation p a n (a n) ≤
    pOrderingValuation p a n x := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.isPOrdering_unfold

/--
[IsPOrdering.infinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
private lemma IsPOrdering_infinite_eq
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (h : IsPOrdering p S a) :
-- imply
  S.Infinite := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.IsPOrdering.infinite h

/--
[IsPOrdering.mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
private lemma IsPOrdering_mem_eq
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
  {n : ℕ}
-- given
  (h : IsPOrdering p S a) :
-- imply
  a n ∈ S := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.IsPOrdering.mem h n

/--
[IsPOrdering.min_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
private lemma IsPOrdering_min_le_eq
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
  pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.IsPOrdering.min_le h n x hx

/--
[IsPOrdering.isLeast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
private lemma IsPOrdering_isLeast_eq
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
  apply IsDedekindDomain.HeightOneSpectrum.IsPOrdering.isLeast h

/--
[IsPOrdering.intro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
private lemma IsPOrdering_intro_eq
  [CommRing R] [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (hinf : S.Infinite)
  (hmem : ∀ n, a n ∈ S)
  (hmin : ∀ n, ∀ x ∈ S, pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x) :
-- imply
  IsPOrdering p S a := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.IsPOrdering.intro hinf hmem hmin

/--
[pOrderingValuation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
private lemma pOrderingValuation_zero_eq
  [CommRing R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {a : ℕ → R}
  {x : R} :
-- imply
  pOrderingValuation p a 0 x = 0 := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.pOrderingValuation_zero p a x

/--
[isPOrdering_iff_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
private lemma isPOrdering_iff_pos_eq
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
  apply IsDedekindDomain.HeightOneSpectrum.isPOrdering_iff_pos


-- created on 2026-10-20
