import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.POrdering
import Lemma.Int.DedekindDomain.POrdering
open IsDedekindDomain.HeightOneSpectrum


/--
[test_val_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_val_zero
  [CommRing R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {a : ℕ → R}
  {x : R} :
-- imply
  pOrderingValuation p a 0 x = 0 :=
-- proof
  pOrderingValuation_zero p a x

/--
[test_val_zero_tie](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_val_zero_tie
  [CommRing R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {a : ℕ → R}
  {x : R} :
-- imply
  pOrderingValuation p a 0 (a 0) ≤ pOrderingValuation p a 0 x := by
-- proof
  rw [pOrderingValuation_zero, pOrderingValuation_zero]

/--
[test_val_unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_val_unfold
  [CommRing R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {a : ℕ → R}
  {n : ℕ}
  {x : R} :
-- imply
  pOrderingValuation p a n x = emultiplicity p.asIdeal (Ideal.span {(Finset.range n).prod fun k => x - a k}) :=
-- proof
  rfl

/--
[test_prefix_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_prefix_succ
  [CommRing R]
  {a : ℕ → R}
  {n : ℕ}
  {x : R} :
-- imply
  (Finset.range (n + 1)).prod (fun k => x - a k) = ((Finset.range n).prod (fun k => x - a k)) * (x - a n) :=
-- proof
  Finset.prod_range_succ _ _

/--
[test_proj_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_proj_infinite
  [CommRing R]
  [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (h : IsPOrdering p S a) :
-- imply
  S.Infinite :=
-- proof
  h.infinite

/--
[test_proj_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_proj_mem
  [CommRing R]
  [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
  {n : ℕ}
-- given
  (h : IsPOrdering p S a) :
-- imply
  a n ∈ S :=
-- proof
  h.mem n

/--
[test_proj_min](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_proj_min
  [CommRing R]
  [IsDedekindDomain R]
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
  h.min_le n x hx

/--
[test_proj_isLeast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_proj_isLeast
  [CommRing R]
  [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
  {n : ℕ}
-- given
  (h : IsPOrdering p S a) :
-- imply
  IsLeast (pOrderingValuation p a n '' S) (pOrderingValuation p a n (a n)) :=
-- proof
  h.isLeast

/--
[test_constructor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_constructor
  [CommRing R]
  [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (h : IsPOrdering p S a) :
-- imply
  IsPOrdering p S a :=
-- proof
  IsPOrdering.intro h.infinite h.mem (fun n x hx => h.min_le n x hx)

/--
[test_unfold_roundtrip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_unfold_roundtrip
  [CommRing R]
  [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (h : IsPOrdering p S a) :
-- imply
  S.Infinite ∧ (∀ n, a n ∈ S) ∧ ∀ n, ∀ x ∈ S, pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x :=
-- proof
  isPOrdering_unfold.mp h

/--
[test_pos_forward](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_pos_forward
  [CommRing R]
  [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (h : IsPOrdering p S a) :
-- imply
  S.Infinite ∧ (∀ n, a n ∈ S) ∧ ∀ n, 1 ≤ n → ∀ x ∈ S, pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x :=
-- proof
  isPOrdering_iff_pos.mp h

/--
[test_pos_backward](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/POrdering.lean)
-/
@[path]
lemma test_pos_backward
  [CommRing R]
  [IsDedekindDomain R]
  {p : IsDedekindDomain.HeightOneSpectrum R}
  {S : Set R}
  {a : ℕ → R}
-- given
  (h : S.Infinite ∧ (∀ n, a n ∈ S) ∧ ∀ n, 1 ≤ n → ∀ x ∈ S, pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x) :
-- imply
  IsPOrdering p S a :=
-- proof
  isPOrdering_iff_pos.mpr h


-- created on 2026-10-23
