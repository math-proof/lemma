import Mathlib
import sympy.Basic


attribute [local instance] Ideal.Quotient.field

@[local instance]
instance {R : Type*} [CommRing R] (I : MaximalSpectrum R) : I.asIdeal.IsMaximal :=
  I.isMaximal


private lemma nondeg_iff
  [CommRing R] [CommRing S] [Algebra R S] :
-- imply
  (Algebra.traceForm R S).Nondegenerate ↔
    ∀ x : S, (∀ y, Algebra.trace R S (x * y) = 0) → x = 0 := by
-- proof
  constructor
  ·
    intro h x hx
    apply h.1 x
    intro y
    rw [Algebra.traceForm_apply]
    apply hx y
  ·
    intro h
    refine ⟨fun x hx => h x fun y => ?_, fun y hy => h y fun x => ?_⟩
    ·
      have := hx y
      rwa [Algebra.traceForm_apply] at this
    ·
      have := hy x
      rwa [Algebra.traceForm_apply, mul_comm] at this

private lemma nondeg_of_algEquiv
  [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (e : B ≃ₐ[R] C)
-- given
  (h : (Algebra.traceForm R C).Nondegenerate) :
-- imply
  (Algebra.traceForm R B).Nondegenerate := by
-- proof
  rw [nondeg_iff] at h ⊢
  intro x hx
  apply (map_eq_zero_iff e e.injective).mp (h (e x) fun z => by
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [← map_mul, Algebra.trace_eq_of_algEquiv]
    apply hx y)

private lemma nondeg_iff_of_algEquiv
  [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (e : B ≃ₐ[R] C) :
-- imply
  (Algebra.traceForm R B).Nondegenerate ↔ (Algebra.traceForm R C).Nondegenerate :=
  ⟨fun h => nondeg_of_algEquiv e.symm h, fun h => nondeg_of_algEquiv e h⟩

private lemma trace_pi_apply
  [CommRing R]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
  (x : ∀ i, A i) :
-- imply
  Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) := by
-- proof
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b) x, Matrix.trace]
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply,
    Pi.mul_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i) (x i), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [Pi.single_eq_same]

private lemma nondeg_pi_iff
  [Field K]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Module.Finite K (A i)] :
-- imply
  (Algebra.traceForm K (∀ i, A i)).Nondegenerate ↔
    ∀ i, (Algebra.traceForm K (A i)).Nondegenerate := by
-- proof
  simp only [nondeg_iff]
  constructor
  ·
    intro h i x hx
    have key := h (Pi.single i x) fun y => by
      rw [trace_pi_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      if hj : j = i then
        subst hj
        rw [Pi.mul_apply, Pi.single_eq_same]
        apply hx (y j)
      else
        rw [Pi.mul_apply, Pi.single_eq_of_ne hj, zero_mul, map_zero]
    have := congrFun key i
    rwa [Pi.single_eq_same] at this
  ·
    intro h x hx
    funext i
    refine h i (x i) fun y => ?_
    have key := hx (Pi.single i y)
    rw [trace_pi_apply, Finset.sum_eq_single i] at key
    · rwa [Pi.mul_apply, Pi.single_eq_same] at key
    ·
      intro j _ hj
      rw [Pi.mul_apply, Pi.single_eq_of_ne hj, mul_zero, map_zero]
    ·
      intro hi
      apply absurd (Finset.mem_univ i) hi

private lemma nondeg_iff_isSeparable
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
-- imply
  (Algebra.traceForm K L).Nondegenerate ↔ Algebra.IsSeparable K L := by
-- proof
  constructor
  ·
    intro h
    by_contra hs
    have h0 := Algebra.trace_eq_zero_of_not_isSeparable hs
    rw [nondeg_iff] at h
    exact one_ne_zero (h 1 fun y => by rw [h0, LinearMap.zero_apply])
  ·
    intro _
    apply traceForm_nondegenerate K L

private lemma main_of_isReduced
  {K : Type u} [Field K]
  {B : Type u} [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] :
-- imply
  Algebra.FormallyUnramified K B ↔ (Algebra.traceForm K B).Nondegenerate := by
-- proof
  classical
  let _ : IsArtinianRing B := IsArtinianRing.of_finite K B
  let _ : ∀ I : MaximalSpectrum B, Module.Finite K (B ⧸ I.asIdeal) := fun I =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let e : B ≃ₐ[K] ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal :=
    (IsArtinianRing.equivPi B).restrictScalars K
  have h1 : Algebra.FormallyUnramified K B ↔
      Algebra.FormallyUnramified K (∀ I : MaximalSpectrum B, B ⧸ I.asIdeal) :=
    ⟨fun _ => Algebra.FormallyUnramified.of_equiv e,
     fun _ => Algebra.FormallyUnramified.of_equiv e.symm⟩
  rw [h1, Algebra.FormallyUnramified.pi_iff, nondeg_iff_of_algEquiv e, nondeg_pi_iff]
  refine forall_congr' fun I => ?_
  rw [Algebra.FormallyUnramified.iff_isSeparable K (B ⧸ I.asIdeal), nondeg_iff_isSeparable]

private lemma isReduced_of_nondeg
  [Field K] [CommRing B] [Algebra K B]
-- given
  (h : (Algebra.traceForm K B).Nondegenerate) :
-- imply
  IsReduced B := by
-- proof
  refine ⟨fun x hx => (nondeg_iff.mp h) x fun y => ?_⟩
  apply (Algebra.isNilpotent_trace_of_isNilpotent
    (Commute.isNilpotent_mul_right (Commute.all x y) hx)).eq_zero


/--
[Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {B : Type u} [CommRing B] [Algebra K B] [Module.Finite K B] :
-- imply
  Algebra.FormallyUnramified K B ↔ (Algebra.traceForm K B).Nondegenerate := by
-- proof
  constructor
  ·
    intro h
    let _ : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field K B
    apply (main_of_isReduced (K := K) (B := B)).mp h
  ·
    intro h
    let _ : IsReduced B := isReduced_of_nondeg h
    apply (main_of_isReduced (K := K) (B := B)).mpr h


-- created on 2026-10-13
