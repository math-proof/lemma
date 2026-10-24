import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.AlgebraicGeometry
open MvPolynomial Set Cardinal
open Cardinal


/--
[isGalois_iff_normal_and_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma isGalois_iff_normal_and_separable
  [Field k]
  [Field K]
  [Algebra k K]
  [Field k]
  [Field L]
  [Algebra k L] :
-- imply
  IsGalois k L ↔ Normal k L ∧ Algebra.IsSeparable k L :=
-- proof
  isGalois_iff.trans And.comm

/--
[affineSpace_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma affineSpace_eq_univ
  [Field k]
  [Field K]
  [Algebra k K] :
-- imply
  affineSpace σ K = Set.univ :=
-- proof
  rfl

/--
[mem_affineRationalPoints_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma mem_affineRationalPoints_iff
  [Field k]
  [Field K]
  [Algebra k K]
  {L : IntermediateField k K}
  {x : σ → K} :
-- imply
  x ∈ affineRationalPoints σ L ↔ ∀ i : σ, x i ∈ L :=
-- proof
  Iff.rfl

/--
[mem_affineGaloisFixedPoints_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma mem_affineGaloisFixedPoints_iff
  [Field k]
  [Field K]
  [Algebra k K]
  {L : IntermediateField k K}
  {x : σ → K} :
-- imply
  x ∈ affineGaloisFixedPoints σ L ↔ ∀ φ : K ≃ₐ[k] K, φ ∈ L.fixingSubgroup → φ • x = x := by
-- proof
  unfold affineGaloisFixedPoints
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h φ hφ; simpa using h ⟨φ, hφ⟩
  · intro h ⟨φ, hφ⟩; simpa using h φ hφ

/--
[affineRationalPoints_subset_galoisFixedPoints](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma affineRationalPoints_subset_galoisFixedPoints
  [Field k]
  [Field K]
  [Algebra k K]
  {L : IntermediateField k K} :
-- imply
  affineRationalPoints σ L ⊆ affineGaloisFixedPoints σ L := by
-- proof
  intro x hx
  rw [mem_affineGaloisFixedPoints_iff]
  intro φ hφ
  ext i
  simp only [Pi.smul_apply, AlgEquiv.smul_def]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hφ
  exact hφ (x i) (hx i)

/--
[galoisFixedPoints_subset_affineRationalPoints](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma galoisFixedPoints_subset_affineRationalPoints
  [Field k]
  [Field K]
  [Algebra k K]
  [IsGalois k K]
  {L : IntermediateField k K} :
-- imply
  affineGaloisFixedPoints σ L ⊆ affineRationalPoints σ L := by
-- proof
  intro x hx
  rw [mem_affineGaloisFixedPoints_iff] at hx
  intro i
  rw [← InfiniteGalois.fixedField_fixingSubgroup L]
  rw [IntermediateField.mem_fixedField_iff]
  intro φ hφ
  have hi := congr_fun (hx φ hφ) i
  simp only [Pi.smul_apply] at hi
  exact hi

/--
[mem_zeroLocusOfSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma mem_zeroLocusOfSet_iff
  [Field k]
  [Field K]
  [Algebra k K]
  {S : Set (MvPolynomial σ K)}
  {x : σ → K} :
-- imply
  x ∈ zeroLocusOfSet K S ↔ ∀ p ∈ S, aeval x p = 0 := by
-- proof
  unfold zeroLocusOfSet
  rw [MvPolynomial.zeroLocus_span]
  rfl

/--
[zeroLocusOfSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma zeroLocusOfSet_eq
  [Field k]
  [Field K]
  [Algebra k K]
  {S : Set (MvPolynomial σ K)} :
-- imply
  zeroLocusOfSet K S = {x : σ → K | ∀ p ∈ S, aeval x p = 0} := by
-- proof
  ext x; simp

/--
[mem_lRationalPoints_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma mem_lRationalPoints_iff
  [Field k]
  [Field K]
  [Algebra k K]
  {S : Set (MvPolynomial σ K)}
  {L : IntermediateField k K}
  {x : σ → K} :
-- imply
  x ∈ lRationalPoints K S L ↔ (∀ f ∈ S, aeval x f = 0) ∧ (∀ i : σ, x i ∈ L) := by
-- proof
  simp [lRationalPoints]

/--
[isAffineAlgebraicSet_zeroLocus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma isAffineAlgebraicSet_zeroLocus
  [Field k]
  [Field K]
  [Algebra k K]
  {I : Ideal (MvPolynomial σ K)} :
-- imply
  IsAffineAlgebraicSet K (MvPolynomial.zeroLocus K I) :=
-- proof
  ⟨I, rfl⟩

/--
[mem_vanishingIdealOfSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma mem_vanishingIdealOfSet_iff
  [Field k]
  [Field K]
  [Algebra k K]
  {V : Set (σ → K)}
  {f : MvPolynomial σ K} :
-- imply
  f ∈ vanishingIdealOfSet K V ↔ ∀ x ∈ V, aeval x f = 0 :=
-- proof
  MvPolynomial.mem_vanishingIdeal_iff

/--
[vanishingIdealOfSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma vanishingIdealOfSet_eq
  [Field k]
  [Field K]
  [Algebra k K]
  {V : Set (σ → K)} :
-- imply
  (vanishingIdealOfSet K V : Set (MvPolynomial σ K)) = {f | ∀ x ∈ V, aeval x f = 0} := by
-- proof
  ext f; simp

/--
[coordinateRing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma coordinateRing_eq
  [Field k]
  [Field K]
  [Algebra k K]
  {V : Set (σ → K)} :
-- imply
  coordinateRing K σ V = (MvPolynomial σ K ⧸ MvPolynomial.vanishingIdeal K V) :=
-- proof
  rfl

/--
[isNoetherianRing_iff_every_ideal_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma isNoetherianRing_iff_every_ideal_fg
  [Field k]
  [Field K]
  [Algebra k K]
  {R : Type*}
  [CommRing R] :
-- imply
  IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
-- proof
  isNoetherianRing_iff_ideal_fg R

/--
[hilbert_basis_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma hilbert_basis_theorem
  [Field k]
  [Field K]
  [Algebra k K]
  {R : Type*}
  [CommRing R]
  [IsNoetherianRing R] :
-- imply
  IsNoetherianRing (Polynomial R) :=
-- proof
  Polynomial.isNoetherianRing

/--
[radical_eq_setOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma radical_eq_setOf
  [Field k]
  [Field K]
  [Algebra k K]
  [CommSemiring R]
  {I : Ideal R} :
-- imply
  (I.radical : Set R) = {f | ∃ n : ℕ, 0 < n ∧ f ^ n ∈ I} := by
-- proof
  ext f
  simp only [SetLike.mem_coe, Ideal.mem_radical_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.succ_pos n, by rw [pow_succ]; exact I.mul_mem_right f hn⟩
  · rintro ⟨n, -, hn⟩
    exact ⟨n, hn⟩

/--
[radical_is_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma radical_is_ideal
  [Field k]
  [Field K]
  [Algebra k K]
  [CommSemiring R]
  {I : Ideal R} :
-- imply
  ∃ J : Ideal R, (J : Set R) = {f | ∃ n : ℕ, f ^ n ∈ I} :=
-- proof
  ⟨I.radical, by ext; simp [Ideal.mem_radical_iff]⟩

/--
[vanishingIdealOfSet_isRadical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma vanishingIdealOfSet_isRadical
  [Field k]
  [Field K]
  [Algebra k K]
  {V : Set (σ → K)} :
-- imply
  (vanishingIdealOfSet K V).IsRadical := by
-- proof
  rw [← Ideal.radical_eq_iff]
  ext f
  simp only [Ideal.mem_radical_iff]
  constructor
  · rintro ⟨n, hn⟩
    intro x hx
    have : aeval x (f ^ n) = 0 := hn x hx
    rw [map_pow] at this
    exact (pow_eq_zero_iff'.mp this).1
  · intro h
    exact ⟨1, by simpa using h⟩

/--
[vanishingIdealOfSet_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma vanishingIdealOfSet_union
  [Field k]
  [Field K]
  [Algebra k K]
  {V₁ V₂ : Set (σ → K)} :
-- imply
  vanishingIdealOfSet K (V₁ ∪ V₂) = vanishingIdealOfSet K V₁ ⊓ vanishingIdealOfSet K V₂ := by
-- proof
  ext f
  simp only [mem_vanishingIdealOfSet_iff, Ideal.mem_inf, Set.mem_union]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun ⟨h1, h2⟩ x hx => hx.elim (h1 x) (h2 x)⟩

/--
[isAffineAlgebraicSet_inter_zeroLocus_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma isAffineAlgebraicSet_inter_zeroLocus_singleton
  [Field k]
  [Field K]
  [Algebra k K]
  {V : Set (σ → K)}
  {f : MvPolynomial σ K}
-- given
  (hV : IsAffineAlgebraicSet K V) :
-- imply
  IsAffineAlgebraicSet K (V ∩ {x | aeval x f = 0}) := by
-- proof
  obtain ⟨I, rfl⟩ := hV
  exact ⟨I ⊔ Ideal.span {f}, by
    ext x
    simp only [Set.mem_inter_iff, MvPolynomial.mem_zeroLocus_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxI, hxf⟩ p hp
      have : I ⊔ Ideal.span {f} ≤ RingHom.ker (aeval x) :=
        sup_le (fun q hq => RingHom.mem_ker.mpr (hxI q hq))
          (fun q hq => RingHom.mem_ker.mpr (by
            obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hq
            rw [map_mul, hxf, zero_mul]))
      exact RingHom.mem_ker.mp (this hp)
    · intro hx
      exact ⟨fun p hp => hx p (Ideal.mem_sup_left hp),
        hx f (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))⟩⟩

/--
[zeroLocus_vanishingIdealOfSet_zeroLocus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma zeroLocus_vanishingIdealOfSet_zeroLocus
  [Field k]
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  [Empty.Finite σ]
  {J : Ideal (MvPolynomial σ K)} :
-- imply
  MvPolynomial.zeroLocus K (vanishingIdealOfSet K (MvPolynomial.zeroLocus K J)) = MvPolynomial.zeroLocus K J := by
-- proof
  unfold vanishingIdealOfSet
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
  apply le_antisymm (MvPolynomial.zeroLocus_anti_mono Ideal.le_radical)
  intro x hx p hp
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hp
  have := hx (p ^ n) hn
  rw [map_pow] at this
  exact (pow_eq_zero_iff'.mp this).1

/--
[IsIrreducibleAffineAlgebraicSet.vanishingIdeal_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma IsIrreducibleAffineAlgebraicSet.vanishingIdeal_isPrime
  [Field k]
  [Field K]
  [Algebra k K]
  {V : Set (σ → K)}
-- given
  (hIrr : IsIrreducibleAffineAlgebraicSet K V) :
-- imply
  (vanishingIdealOfSet K V).IsPrime := by
-- proof
  obtain ⟨hAlg, hNe, hIrr⟩ := hIrr
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hNe
    have := (mem_vanishingIdealOfSet_iff V 1).mp (h ▸ Submodule.mem_top) x hx
    simp at this
  · intro f g hfg
    let V₁ := V ∩ {x | aeval x f = 0}
    let V₂ := V ∩ {x | aeval x g = 0}
    have hVunion : V = V₁ ∪ V₂ := by
      ext x
      simp only [V₁, V₂, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hx
        have := (mem_vanishingIdealOfSet_iff V (f * g)).mp hfg x hx
        rw [map_mul] at this
        obtain h | h := mul_eq_zero.mp this
        · exact .inl ⟨hx, h⟩
        · exact .inr ⟨hx, h⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    rcases hIrr V₁ V₂
      (isAffineAlgebraicSet_inter_zeroLocus_singleton V f hAlg)
      (isAffineAlgebraicSet_inter_zeroLocus_singleton V g hAlg)
      hVunion with h | h
    · left
      rw [mem_vanishingIdealOfSet_iff]
      intro x hx
      exact (h ▸ hx : x ∈ V₁).2
    · right
      rw [mem_vanishingIdealOfSet_iff]
      intro x hx
      exact (h ▸ hx : x ∈ V₂).2

/--
[prime_vanishingIdeal_implies_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma prime_vanishingIdeal_implies_irreducible
  [Field k]
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  [Empty.Finite σ]
  {V : Set (σ → K)}
-- given
  (hAlg : IsAffineAlgebraicSet K V)
  (hPrime : (vanishingIdealOfSet K V).IsPrime) :
-- imply
  IsIrreducibleAffineAlgebraicSet K V := by
-- proof
  obtain ⟨I, rfl⟩ := hAlg
  refine ⟨⟨I, rfl⟩, ?_, ?_⟩
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp only [h, vanishingIdealOfSet, MvPolynomial.vanishingIdeal_empty] at hPrime
    exact hPrime.ne_top rfl
  · intro V₁ V₂ ⟨J₁, hV₁⟩ ⟨J₂, hV₂⟩ hunion
    have hIV := hunion ▸ vanishingIdealOfSet_union V₁ V₂
    have hprod : vanishingIdealOfSet K V₁ * vanishingIdealOfSet K V₂ ≤
      vanishingIdealOfSet K (MvPolynomial.zeroLocus K I) := hIV ▸ Ideal.mul_le_inf
    obtain h₁ | h₂ := hPrime.mul_le.mp hprod
    · left
      rw [hV₁]
      have heq := le_antisymm h₁
        (MvPolynomial.vanishingIdeal_anti_mono (hunion ▸ Set.subset_union_left))
      have : MvPolynomial.zeroLocus K (vanishingIdealOfSet K V₁) =
        MvPolynomial.zeroLocus K (vanishingIdealOfSet K (MvPolynomial.zeroLocus K I)) := by
        rw [heq]
      rw [hV₁, zeroLocus_vanishingIdealOfSet_zeroLocus,
        zeroLocus_vanishingIdealOfSet_zeroLocus] at this
      exact this.symm
    · right
      rw [hV₂]
      have heq := le_antisymm h₂
        (MvPolynomial.vanishingIdeal_anti_mono (hunion ▸ Set.subset_union_right))
      have : MvPolynomial.zeroLocus K (vanishingIdealOfSet K V₂) =
        MvPolynomial.zeroLocus K (vanishingIdealOfSet K (MvPolynomial.zeroLocus K I)) := by
        rw [heq]
      rw [hV₂, zeroLocus_vanishingIdealOfSet_zeroLocus,
        zeroLocus_vanishingIdealOfSet_zeroLocus] at this
      exact this.symm

/--
[algebraicSet_irreducible_iff_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma algebraicSet_irreducible_iff_prime
  [Field k]
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  [Empty.Finite σ]
  {V : Set (σ → K)}
-- given
  (hAlg : IsAffineAlgebraicSet K V) :
-- imply
  IsIrreducibleAffineAlgebraicSet K V ↔ (vanishingIdealOfSet K V).IsPrime :=
-- proof
  ⟨IsIrreducibleAffineAlgebraicSet.vanishingIdeal_isPrime,
    prime_vanishingIdeal_implies_irreducible hAlg⟩

/--
[isAffineAlgebraicSet_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma isAffineAlgebraicSet_singleton
  [Field k]
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  [Empty.Finite σ]
  {P : σ → K} :
-- imply
  IsAffineAlgebraicSet K ({P} : Set (σ → K)) :=
-- proof
  ⟨vanishingIdealOfSet K {P}, by
    show {P} = zeroLocus K (vanishingIdeal K {P})
    apply le_antisymm
    · exact zeroLocus_vanishingIdeal_le ({P} : Set (σ → K))
    · intro x hx
      rw [mem_zeroLocus_iff] at hx
      rw [mem_singleton_iff]
      funext i
      have hmem : (X i - C (P i) : MvPolynomial σ K) ∈
        vanishingIdeal K ({P} : Set (σ → K)) := by
        rw [mem_vanishingIdeal_iff]
        intro y hy; rw [mem_singleton_iff] at hy; subst hy; simp
      have heval := hx _ hmem
      simp at heval
      exact sub_eq_zero.mp heval⟩

/--
[vanishingIdealOfSet_singleton_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma vanishingIdealOfSet_singleton_isMaximal
  [Field k]
  [Field K]
  [Algebra k K]
  {P : σ → K} :
-- imply
  (vanishingIdealOfSet K ({P} : Set (σ → K))).IsMaximal :=
-- proof
  MvPolynomial.instIsMaximalVanishingIdealSingletonForallSet

/--
[maximal_iff_vanishingIdealOfSet_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma maximal_iff_vanishingIdealOfSet_singleton
  [Field k]
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  [Empty.Finite σ]
  {I : Ideal (MvPolynomial σ K)} :
-- imply
  I.IsMaximal ↔ ∃ P : σ → K, I = vanishingIdealOfSet K ({P} : Set (σ → K)) :=
-- proof
  MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton
open Cardinal
universe u v w w'

/--
[transcendence_bases_same_cardinality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma transcendence_bases_same_cardinality
  [Field k]
  [Field K]
  [Algebra k K]
  {k : Type u}
  {L : Type v}
  [Field k]
  [Field L]
  [Algebra k L]
  {ι : Type w}
  {ι' : Type w}
  {x : ι → L}
  {y : ι' → L}
-- given
  (hx : IsTranscendenceBasis k x)
  (hy : IsTranscendenceBasis k y) :
-- imply
  #ι = #ι' :=
-- proof
  hx.cardinalMk_eq hy

/--
[perfectField_iff_perfectRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
lemma perfectField_iff_perfectRing
  [Field k]
  [Field K]
  [Algebra k K]
  {k : Type*}
  [Field k]
  {p : ℕ}
  [ExpChar k p] :
-- imply
  PerfectField k ↔ PerfectRing k p := by
-- proof
  constructor
  · intro; exact PerfectField.toPerfectRing p
  · intro; exact PerfectRing.toPerfectField k p

/--
[isAffineAlgebraicSet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
private lemma isAffineAlgebraicSet_empty_eq
  [Field k]
  [Field K]
  [Algebra k K] :
-- imply
  IsAffineAlgebraicSet K (∅ : Set (σ → K)) := by
-- proof
  apply isAffineAlgebraicSet_empty

/--
[isAffineAlgebraicSet_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
private lemma isAffineAlgebraicSet_union_eq
  [Field k]
  [Field K]
  [Algebra k K]
  {V₁ V₂ : Set (σ → K)}
-- given
  (h₁ : IsAffineAlgebraicSet K V₁)
  (h₂ : IsAffineAlgebraicSet K V₂) :
-- imply
  IsAffineAlgebraicSet K (V₁ ∪ V₂) := by
-- proof
  apply isAffineAlgebraicSet_union h₁ h₂

/--
[isAffineAlgebraicSet_sInter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean)
-/
@[path]
private lemma isAffineAlgebraicSet_sInter_eq
  [Field k]
  [Field K]
  [Algebra k K]
  {A : Set (Set (σ → K))}
-- given
  (hA : ∀ V ∈ A, IsAffineAlgebraicSet K V) :
-- imply
  IsAffineAlgebraicSet K (⋂₀ A) := by
-- proof
  apply isAffineAlgebraicSet_sInter A hA


-- created on 2026-10-23
