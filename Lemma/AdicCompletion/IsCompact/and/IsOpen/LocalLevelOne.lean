import sympy.Basic
import Mathlib
import Lemma.AdicCompletion.Support.AdelicDock

open IsDedekindDomain NumberField AdicCompletion

/--
[AdelicDock_isCompact_and_isOpen_localLevelOne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_isCompact_and_isOpen_localLevelOne.lean)
-/
private lemma setOf_isLocalLevelOne_eq
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) (N : Ideal R) :
-- imply
  {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m}
    = ((⋂ i, ⋂ j, (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m i j) ⁻¹'
          (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
        ∩ (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m 1 0) ⁻¹'
          {y | Valued.v y ≤ AdelicLevel.idealBound R N v})
      ∩ (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m 1 1 - 1) ⁻¹'
          {y | Valued.v y ≤ AdelicLevel.idealBound R N v} := by
-- proof
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  exact ⟨fun h => ⟨⟨h.integral, h.lowerLeft⟩, h.lowerRight⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

private lemma isOpen_adicCompletionIntegers
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) :
-- imply
  IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
-- proof
  Valued.isOpen_valuationSubring (v.adicCompletion K)

private lemma isOpen_setOf_isLocalLevelOne
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) (N : Ideal R) (hN : N ≠ ⊥) :
-- imply
  IsOpen {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m} := by
-- proof
  rw [setOf_isLocalLevelOne_eq]
  refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
  ·
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_adicCompletionIntegers R K v).preimage (continuous_id.matrix_elem i j)
  ·
    exact (AdelicLevel.isOpen_setOf_valued_le_idealBound R K v hN).preimage (continuous_id.matrix_elem 1 0)
  ·
    exact (AdelicLevel.isOpen_setOf_valued_le_idealBound R K v hN).preimage
      ((continuous_id.matrix_elem 1 1).sub continuous_const)

private lemma isClosed_setOf_isLocalLevelOne
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) (N : Ideal R) :
-- imply
  IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m} := by
-- proof
  rw [setOf_isLocalLevelOne_eq]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  ·
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (Valued.isClosed_valuationSubring (v.adicCompletion K)).preimage (continuous_id.matrix_elem i j)
  ·
    exact (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := K) v N).preimage (continuous_id.matrix_elem 1 0)
  ·
    exact (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := K) v N).preimage
      ((continuous_id.matrix_elem 1 1).sub continuous_const)

private lemma coe_localLevelOne_eq
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) (N : Ideal R) :
-- imply
  (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K)))
    = (Units.val ⁻¹'
        {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m})
      ∩ ((fun g : GL (Fin 2) (v.adicCompletion K) =>
            ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
        {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m}) := by
-- proof
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff]
  rfl

private lemma isOpen_localLevelOne
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) (N : Ideal R) (hN : N ≠ ⊥) :
-- imply
  IsOpen (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
-- proof
  rw [coe_localLevelOne_eq]
  exact ((isOpen_setOf_isLocalLevelOne R K v N hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLocalLevelOne R K v N hN).preimage Units.continuous_coe_inv)

private lemma isClosed_localLevelOne
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) (N : Ideal R) :
-- imply
  IsClosed (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
-- proof
  rw [coe_localLevelOne_eq]
  exact ((isClosed_setOf_isLocalLevelOne R K v N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLocalLevelOne R K v N).preimage Units.continuous_coe_inv)

private lemma isCompact_adicCompletionIntegers
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) [Module.Free ℤ R] [Module.Finite ℤ R] :
-- imply
  IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
-- proof
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers K)))

private lemma isCompact_setOf_integral
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) [Module.Free ℤ R] [Module.Finite ℤ R] :
-- imply
  IsCompact {g : GL (Fin 2) (v.adicCompletion K) |
    (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
    ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      ∈ v.adicCompletionIntegers K} := by
-- proof
  set C : Set (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    {m | ∀ i j, m i j ∈ v.adicCompletionIntegers K} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 =>
        Set.pi Set.univ fun _ : Fin 2 => (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers R K v
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : {g : GL (Fin 2) (v.adicCompletion K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K} =
      (Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
        (C ×ˢ (MulOpposite.op '' C)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      Set.mem_image, hC_def]
    constructor
    ·
      rintro ⟨h1, h2⟩
      exact ⟨h1, _, h2, rfl⟩
    ·
      rintro ⟨h1, m, hm, hm'⟩
      refine ⟨h1, ?_⟩
      have : m = ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
        MulOpposite.op_injective hm'
      rwa [← this]
  rwa [heq]

private lemma isCompact_localLevelOne
-- given
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) (N : Ideal R) [Module.Free ℤ R] [Module.Finite ℤ R] :
-- imply
  IsCompact (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) :=
-- proof
  (isCompact_setOf_integral R K v).of_isClosed_subset (isClosed_localLevelOne R K v N) fun k hk => by
    rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff] at hk
    exact ⟨hk.1.integral, hk.2.integral⟩

@[path]
private lemma main
-- given
  [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) :
-- imply
  IsCompact (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      IsOpen (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) :=
-- proof
  ⟨isCompact_localLevelOne (𝓞 K) K v N, isOpen_localLevelOne (𝓞 K) K v N hN⟩


-- created on 2026-10-09
