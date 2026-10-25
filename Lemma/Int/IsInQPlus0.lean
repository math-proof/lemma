import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.CategoryO.Part3


/--
[PositiveRootData.IsInQPlus_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma PositiveRootData.IsInQPlus_zero
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ} :
-- imply
  rd.IsInQPlus 0 :=
-- proof
  ⟨fun _ => 0, by simp⟩

/--
[PositiveRootData.IsInQPlus_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma PositiveRootData.IsInQPlus_trans
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wt0 μ ν : Δ.𝔥 →ₗ[R] R}
-- given
  (h0 : rd.IsInQPlus (wt0 - μ))
  (h1 : rd.IsInQPlus (μ - ν)) :
-- imply
  rd.IsInQPlus (wt0 - ν) := by
-- proof
  have heq : wt0 - ν = (wt0 - μ) + (μ - ν) := by abel
  rw [heq]
  obtain ⟨c₁, hc₁⟩ := h1
  obtain ⟨c₂, hc₂⟩ := h2
  refine ⟨fun α => c₁ α + c₂ α, ?_⟩
  simp only [hc₁, hc₂, ← Finset.sum_add_distrib, add_nsmul]

/--
[PBW.weightSpace_spanFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma PBW.weightSpace_spanFinite
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {S : Finset M}
  {μ : Δ.𝔥 →ₗ[R] R}
-- given
  (hS : LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤)
  (hS_wt : ∀ v ∈ S, ∃ wt : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt)
  (hbnd : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)), ∀ ν ∈ weights Δ M, ∃ w ∈ bds, rd.IsInQPlus (w - ν)) :
-- imply
  ∃ (T : Finset (WeightSpace Δ M μ)), Submodule.span R (T : Set (WeightSpace Δ M μ)) = ⊤ :=
-- proof
  pbw_weightSpace_spanFinite S hS hS_wt hbnd μ

/--
[CategoryO.weightSpace_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.weightSpace_finiteDimensional
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  {μ : Δ.𝔥 →ₗ[R] R}
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  Module.Finite R (WeightSpace Δ M μ) := by
-- proof
  classical
  obtain ⟨S, hS_gen⟩ := hM.finitely_generated
  have hwd := hM.weight_decomp
  choose Ss vs hvs using (fun s => hwd s)
  let S' : Finset M := S.biUnion (fun s => (Ss s).image (fun ν => (vs s ν : M)))
  have hS'_wt : ∀ v ∈ S', ∃ wt : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt := by
    intro v hv
    simp only [S', Finset.mem_biUnion, Finset.mem_image] at hv
    obtain ⟨s, _, ν, _, rfl⟩ := hv
    exact ⟨ν, (vs s ν).property⟩
  have hS'_gen : LieSubmodule.lieSpan R 𝔤 (S' : Set M) = ⊤ := by
    rw [eq_top_iff, ← hS_gen]
    apply LieSubmodule.lieSpan_le.mpr
    intro s hs
    have hsum : s = ∑ ν ∈ Ss s, (vs s ν : M) := hvs s
    rw [hsum]
    apply sum_mem
    intro ν hν
    apply LieSubmodule.subset_lieSpan
    show (vs s ν : M) ∈ (S' : Set M)
    simp only [S', Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨s, hs, ν, hν, rfl⟩
  obtain ⟨T, hT⟩ := PBW.weightSpace_spanFinite S' hS'_gen hS'_wt hM.weight_bound μ
  exact Module.Finite.of_fg_top ⟨T, hT⟩

/--
[hilbert_noether_commRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma hilbert_noether_commRing
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [IsNoetherianRing R]
  [CommRing A]
  [Algebra R A]
  [Group G]
  [Fintype G]
  {algAct : G →* (A ≃ₐ[R] A)}
-- given
  (hA_fg : Subalgebra.FG (⊤ : Subalgebra R A)) :
-- imply
  (Subalgebra.invariants G algAct).FG := by
-- proof
  letI : MulSemiringAction G A := MulSemiringAction.compHom A algAct
  letI : SMulCommClass G R A := ⟨fun g r a => by
    show (algAct g) (r • a) = r • (algAct g) a
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, Algebra.smul_def]⟩
  haveI : Algebra.FiniteType R A := ⟨hA_fg⟩
  have hfg := hilbert_noether_fg (R := R) (A := A) (G := G)
  have hfg_sub : (FixedPoints.subalgebra R A G).FG :=
    (Subalgebra.fg_iff_finiteType _).mpr hfg
  have heq : FixedPoints.subalgebra R A G = Subalgebra.invariants G algAct := by
    ext a
    simp only [FixedPoints.subalgebra, Subalgebra.invariants, Subalgebra.mem_mk,
      Subsemiring.mem_mk, Submonoid.mem_mk]
    constructor
    · intro ha g; exact ha g
    · intro ha g; exact ha g
  rwa [← heq]

/--
[symmetric_algebra_fg_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma symmetric_algebra_fg_top
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  {R : Type*}
  [CommRing R]
  {L : Type*}
  [LieRing L]
  [LieAlgebra R L]
  [IsLieAbelian L]
  [Module.Free R L]
  [Module.Finite R L] :
-- imply
  Subalgebra.FG (⊤ : Subalgebra R (SymmetricAlgebra R L)) := by
-- proof
  by_cases hR : Nontrivial R
  · have hb := Module.Free.chooseBasis R L
    haveI : Finite (Module.Free.ChooseBasisIndex R L) := Module.Finite.finite_basis hb
    haveI : Algebra.FiniteType R (MvPolynomial (Module.Free.ChooseBasisIndex R L) R) :=
      Algebra.FiniteType.instMvPolynomialOfFinite
    haveI : Algebra.FiniteType R (SymmetricAlgebra R L) :=
      Algebra.FiniteType.equiv ‹Algebra.FiniteType R (MvPolynomial _ R)›
        (SymmetricAlgebra.equivMvPolynomial hb).symm
    exact Algebra.FiniteType.out
  · rw [not_nontrivial_iff_subsingleton] at hR
    haveI := hR
    refine ⟨∅, ?_⟩
    have : Subsingleton (SymmetricAlgebra R L) := by
      have h01 : (0 : R) = 1 := Subsingleton.elim _ _
      constructor; intro a b
      have : ∀ (x : SymmetricAlgebra R L), x = 0 := by
        intro x
        calc x = (1 : R) • x := by simp
          _ = (0 : R) • x := by rw [h01]
          _ = 0 := by simp
      rw [this a, this b]
    ext x
    simp [Subsingleton.elim x (algebraMap R _ 0)]

/--
[center_element_integral_on_catO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma center_element_integral_on_catO
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M}
  {z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)}
-- given
  (hM : IsCategoryO Δ rd M)
  (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
-- imply
  ∃ (p : Polynomial R), p.Monic ∧ Polynomial.aeval (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤)) p = 0 := by
-- proof
  classical
  obtain ⟨S, hS_gen⟩ := hM.finitely_generated
  have hwd := hM.weight_decomp
  choose Ss vs hvs using (fun s => hwd s)
  let S' : Finset M := S.biUnion (fun s => (Ss s).image (fun ν => (vs s ν : M)))
  let Λ : Finset (Δ.𝔥 →ₗ[R] R) := S.biUnion (fun s => Ss s)
  have hS'_wt : ∀ v ∈ S', ∃ wt : Δ.𝔥 →ₗ[R] R, wt ∈ Λ ∧ v ∈ WeightSpace Δ M wt := by
    intro v hv
    simp only [S', Finset.mem_biUnion, Finset.mem_image] at hv
    obtain ⟨s, hs, ν, hν, rfl⟩ := hv
    exact ⟨ν, Finset.mem_biUnion.mpr ⟨s, hs, hν⟩, (vs s ν).property⟩
  have hS'_gen : LieSubmodule.lieSpan R 𝔤 (S' : Set M) = ⊤ := by
    rw [eq_top_iff, ← hS_gen]
    apply LieSubmodule.lieSpan_le.mpr
    intro s hs
    have hsum : s = ∑ ν ∈ Ss s, (vs s ν : M) := hvs s
    rw [hsum]
    apply sum_mem
    intro ν hν
    apply LieSubmodule.subset_lieSpan
    show (vs s ν : M) ∈ (S' : Set M)
    simp only [S', Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨s, hs, ν, hν, rfl⟩
  let E : Submodule R M := ⨆ μ ∈ Λ, WeightSpace Δ M μ
  have hμ_fin : ∀ μ ∈ Λ, Module.Finite R (WeightSpace Δ M μ) :=
    fun μ _ => CategoryO.weightSpace_finiteDimensional hM μ
  have hE_fin : E.FG := by
    apply Submodule.fg_biSup Λ
    intro μ hμ
    have : (⊤ : Submodule R ↥(WeightSpace Δ M μ)).FG := Module.finite_def.mp (hμ_fin μ hμ)
    rwa [Submodule.fg_top] at this
  have hS'_in_E : ∀ v ∈ S', v ∈ E := by
    intro v hv
    obtain ⟨wt, hwt_mem, hv_wt⟩ := hS'_wt v hv
    exact Submodule.mem_iSup_of_mem wt (Submodule.mem_iSup_of_mem hwt_mem hv_wt)
  have hz_preserves_wt : ∀ μ (m : M), m ∈ WeightSpace Δ M μ →
    ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m ∈ WeightSpace Δ M μ := by
    intro μ m hm h
    have hcomm : (z : UniversalEnvelopingAlgebra R 𝔤) *
      UniversalEnvelopingAlgebra.ι R (h : 𝔤) =
      UniversalEnvelopingAlgebra.ι R (h : 𝔤) * (z : UniversalEnvelopingAlgebra R 𝔤) := by
      have hz := z.property
      rw [Subalgebra.mem_center_iff] at hz
      exact (hz _).symm
    rw [← hcompat (h : 𝔤)]
    change (ueaAct (UniversalEnvelopingAlgebra.ι R ↑h) *
      ueaAct (↑z)) m = μ h • (ueaAct (↑z)) m
    rw [← map_mul, hcomm.symm, map_mul]
    change (ueaAct (↑z)) ((ueaAct (UniversalEnvelopingAlgebra.ι R ↑h)) m) = _
    rw [hcompat (h : 𝔤), hm h]
    exact (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤)).map_smul (μ h) m
  have hz_preserves_E : ∀ m ∈ E, ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m ∈ E := by
    intro m hm
    rw [show E = ⨆ μ ∈ Λ, WeightSpace Δ M μ from rfl] at hm ⊢
    rw [Submodule.mem_iSup_finset_iff_exists_sum] at hm ⊢
    obtain ⟨f, hf⟩ := hm
    refine ⟨fun μ => ⟨ueaAct (↑z) (f μ), hz_preserves_wt μ _ (f μ).property⟩, ?_⟩
    rw [← hf]
    simp only [map_sum]
  haveI hE_mod_fin : Module.Finite R E := Module.Finite.of_fg hE_fin
  let zE : Module.End R E :=
    (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤)).restrict hz_preserves_E
  obtain ⟨p, hp_monic, hp_aeval⟩ := LinearMap.exists_monic_and_aeval_eq_zero R zE
  have aeval_restrict_val : ∀ (q : Polynomial R) (e : M) (he : e ∈ E),
    (((Polynomial.aeval zE) q) ⟨e, he⟩ : M) =
    (Polynomial.aeval (ueaAct (↑z))) q e := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ hq₁ hq₂ =>
      intro e he
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hq₁ e he, hq₂ e he]
    | monomial n r =>
      intro e he
      simp only [Polynomial.aeval_monomial]
      change ↑((r • (ueaAct (↑z)).restrict hz_preserves_E ^ n) ⟨e, he⟩) =
        (r • ueaAct (↑z) ^ n) e
      simp only [LinearMap.smul_apply, Submodule.coe_smul]
      congr 1
      rw [Module.End.pow_restrict]; rfl
  have aeval_commutes : ∀ (q : Polynomial R) (x : 𝔤),
    Commute ((Polynomial.aeval (ueaAct (↑z))) q)
      (ueaAct (UniversalEnvelopingAlgebra.ι R x)) := by
    intro q x
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ hq₁ hq₂ => rw [map_add]; exact hq₁.add_left hq₂
    | monomial n r =>
      simp only [Polynomial.aeval_monomial]
      have hcomm_end : Commute (ueaAct (↑z)) (ueaAct (UniversalEnvelopingAlgebra.ι R x)) := by
        show ueaAct (↑z) * ueaAct (UniversalEnvelopingAlgebra.ι R x) =
          ueaAct (UniversalEnvelopingAlgebra.ι R x) * ueaAct (↑z)
        rw [← map_mul, ← map_mul]
        congr 1
        have hz := z.property
        rw [Subalgebra.mem_center_iff] at hz
        exact (hz _).symm
      exact (Algebra.commute_algebraMap_left r _).mul_left (hcomm_end.pow_left n)
  refine ⟨p, hp_monic, ?_⟩
  have hp_on_E : ∀ e ∈ E, (Polynomial.aeval (ueaAct (↑z))) p e = 0 := by
    intro e he
    have hzero : ((Polynomial.aeval zE) p) ⟨e, he⟩ = 0 := by
      rw [hp_aeval]; rfl
    rw [← aeval_restrict_val p e he]; exact congrArg Subtype.val hzero
  have hp_lie : ∀ (x : 𝔤) (m : M),
    (Polynomial.aeval (ueaAct (↑z))) p (⁅x, m⁆) =
    ⁅x, (Polynomial.aeval (ueaAct (↑z))) p m⁆ := by
    intro x m'
    rw [← hcompat x, ← hcompat x]
    have hcomm := aeval_commutes p x
    change ((Polynomial.aeval (ueaAct (↑z))) p)
      ((ueaAct (UniversalEnvelopingAlgebra.ι R x)) m') =
      (ueaAct (UniversalEnvelopingAlgebra.ι R x))
        (((Polynomial.aeval (ueaAct (↑z))) p) m')
    exact DFunLike.congr_fun hcomm.eq m'
  ext m
  simp only [LinearMap.zero_apply]
  let pz := (Polynomial.aeval (ueaAct (↑z))) p
  let kerPz : LieSubmodule R 𝔤 M :=
    { toSubmodule := LinearMap.ker pz
      lie_mem := by
        intro x m' hm'
        change m' ∈ LinearMap.ker pz at hm'
        change ⁅x, m'⁆ ∈ LinearMap.ker pz
        rw [LinearMap.mem_ker] at hm' ⊢
        rw [hp_lie x m', hm']
        exact lie_zero x }
  have hS'_in_ker : (S' : Set M) ⊆ (kerPz : Set M) := by
    intro v hv
    show v ∈ LinearMap.ker pz
    rw [LinearMap.mem_ker]
    exact hp_on_E v (hS'_in_E v hv)
  have hspan_le : LieSubmodule.lieSpan R 𝔤 (S' : Set M) ≤ kerPz :=
    LieSubmodule.lieSpan_le.mpr hS'_in_ker
  have hm_in_span : m ∈ LieSubmodule.lieSpan R 𝔤 (S' : Set M) := by
    rw [hS'_gen]; trivial
  have hm_in_ker := hspan_le hm_in_span
  show pz m = 0
  exact (LinearMap.mem_ker.mp hm_in_ker)

/--
[GeneralizedEigenspaceCenter.toLieSubmodule_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma GeneralizedEigenspaceCenter.toLieSubmodule_coe
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M}
  {chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R}
-- given
  (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
-- imply
  (GeneralizedEigenspaceCenter.toLieSubmodule M ueaAct hcompat chi : Submodule R M) = GeneralizedEigenspaceCenter M ueaAct chi :=
-- proof
  rfl

/--
[commute_pow_sub_smul_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma commute_pow_sub_smul_id
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {f g : Module.End R M}
  {c : R}
  {k : ℕ}
  {x : M}
-- given
  (hcomm : g * f = f * g) :
-- imply
  ((f - c • (LinearMap.id : Module.End R M)) ^ k) (g x) = g (((f - c • (LinearMap.id : Module.End R M)) ^ k) x) := by
-- proof
  have h1 : Commute g (f - c • (LinearMap.id : Module.End R M)) := by
    rw [Commute, SemiconjBy, mul_sub, sub_mul, hcomm]
    congr 1; ext y; simp
  exact congr_fun (congr_arg DFunLike.coe (h1.pow_right k).symm) x

/--
[idealChainFilt_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma idealChainFilt_antitone
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {T : ι → Module.End R M} :
-- imply
  ∀ n : ℕ, idealChainFilt T (n + 1) ≤ idealChainFilt T n := by
-- proof
  intro n; induction n with
  | zero => exact le_top
  | succ n ih => exact iSup_mono (fun z => Submodule.map_mono ih)

/--
[mem_idealChainFilt_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma mem_idealChainFilt_succ
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {T : ι → Module.End R M}
  {n : ℕ}
  {z : ι}
  {m : M}
-- given
  (hm : m ∈ idealChainFilt T n) :
-- imply
  T z m ∈ idealChainFilt T (n + 1) :=
-- proof
  Submodule.mem_iSup_of_mem z (Submodule.mem_map.mpr ⟨m, hm, rfl⟩)

/--
[idealChainFilt_lie_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma idealChainFilt_lie_stable
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {T : ι → Module.End R M}
  {n : ℕ}
-- given
  (hcomm : ∀ (x : 𝔤) (z : ι) (m : M), ⁅x, T z m⁆ = T z ⁅x, m⁆) :
-- imply
  ∀ (x : 𝔤) (m : M), m ∈ idealChainFilt T n → ⁅x, m⁆ ∈ idealChainFilt T n := by
-- proof
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro xl m hm
    change m ∈ idealStepFilt T (idealChainFilt T k) at hm
    change ⁅xl, m⁆ ∈ idealStepFilt T (idealChainFilt T k)
    simp only [idealStepFilt] at hm ⊢
    apply Submodule.iSup_induction
      (motive := fun y => ⁅xl, y⁆ ∈ ⨆ z, Submodule.map (T z) (idealChainFilt T k))
      (fun z => Submodule.map (T z) (idealChainFilt T k)) hm
    · intro z y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨m₀, hm₀, rfl⟩ := hy
      rw [hcomm]
      apply Submodule.mem_iSup_of_mem z
      exact Submodule.mem_map.mpr ⟨⁅xl, m₀⁆, ih xl m₀ hm₀, rfl⟩
    · simp [lie_zero]
    · intro y₁ y₂ hy₁ hy₂
      rw [lie_add]
      exact Submodule.add_mem _ hy₁ hy₂

/--
[CategoryO.detecting_submodule_gives_chain_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.detecting_submodule_gives_chain_bound
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {E : Submodule R M}
  {n : ℕ}
-- given
  (hdetect : ∀ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ → ∃ x, x ∈ (N₂ : Submodule R M) ⊓ E ∧ x ∉ (N₁ : Submodule R M))
  (hE_bound : ∀ (chain : Fin (n + 2) → Submodule R M), (∀ i, chain i ≤ E) → StrictMono chain → False) :
-- imply
  ∀ (chain : Fin (n + 2) → LieSubmodule R 𝔤 M), StrictMono chain → False := by
-- proof
  intro chain hchain
  let chain' : Fin (n + 2) → Submodule R M := fun i => (chain i : Submodule R M) ⊓ E
  have hchain' : StrictMono chain' := by
    intro i j hij
    have hlt := hchain hij
    obtain ⟨x, hx_mem, hx_not⟩ := hdetect (chain i) (chain j) hlt
    apply lt_of_le_of_ne
    · intro y hy
      exact ⟨(hchain.monotone hij.le) hy.1, hy.2⟩
    · intro heq
      have hxi : x ∈ chain' i := by rw [heq]; exact hx_mem
      exact hx_not (Submodule.mem_inf.mp hxi).1
  have hle : ∀ i, chain' i ≤ E := fun i => inf_le_right
  exact hE_bound chain' hle hchain'

/--
[section4_weightSpace_iSupIndep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma section4_weightSpace_iSupIndep
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M] :
-- imply
  iSupIndep fun μ : Δ.𝔥 →ₗ[R] R => (WeightSpace Δ M μ : Submodule R M) := by
-- proof
  haveI : IsLieAbelian Δ.𝔥 := Δ.h_abelian
  simp_rw [fun μ => weightSpace_eq_mathlib_weightSpace (Δ := Δ) (M := M) μ]
  exact ((LieSubmodule.iSupIndep_toSubmodule.mpr
    (LieModule.iSupIndep_genWeightSpace R Δ.𝔥 M)).comp
    DFunLike.coe_injective).mono
    fun χ => LieModule.weightSpace_le_genWeightSpace M (χ ·)

/--
[weightSpace_iSupIndep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma weightSpace_iSupIndep
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M] :
-- imply
  iSupIndep fun μ : Δ.𝔥 →ₗ[R] R => (WeightSpace Δ M μ : Submodule R M) :=
-- proof
  section4_weightSpace_iSupIndep

/--
[weightSpace_sum_eq_zero_components](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma weightSpace_sum_eq_zero_components
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {S : Finset (Δ.𝔥 →ₗ[R] R)}
  {v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ}
  {μ : Δ.𝔥 →ₗ[R] R}
-- given
  (hsum : ∑ μ ∈ S, (v μ : M) = 0)
  (hμ : μ ∈ S) :
-- imply
  (v μ : M) = 0 := by
-- proof
  have hindep := @weightSpace_iSupIndep R _ 𝔤 _ _ Δ M _ _ _ _
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero] at hindep
  exact hindep S (fun σ => (v σ : M)) (fun σ _ => (v σ).property) hsum μ hμ

/--
[lieSubmodule_weight_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma lieSubmodule_weight_decomp
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {N : LieSubmodule R 𝔤 M}
  {m : M}
-- given
  (hwd : HasWeightDecomposition Δ M)
  (hm : m ∈ N) :
-- imply
  ∃ (T : Finset (Δ.𝔥 →ₗ[R] R)) (w : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ), m = ∑ μ ∈ T, (w μ : M) ∧ ∀ μ ∈ T, (w μ : M) ∈ N := by
-- proof
  obtain ⟨S, v, hdecomp⟩ := hwd m
  refine ⟨S, v, hdecomp, fun ν hν => ?_⟩
  have mk_weight : ∀ σ : Δ.𝔥 →ₗ[R] R,
    (LieSubmodule.Quotient.mk' N (v σ : M)) ∈ WeightSpace Δ (M ⧸ N) σ := by
    intro σ h
    rw [show ⁅(h : 𝔤), LieSubmodule.Quotient.mk' N (v σ : M)⁆ =
      LieSubmodule.Quotient.mk' N ⁅(h : 𝔤), (v σ : M)⁆ from rfl]
    rw [(v σ).property h]
    exact map_smul (LieSubmodule.Quotient.mk' N).toLinearMap (σ h) (v σ : M)
  let qv : (σ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ (M ⧸ N) σ :=
    fun σ => ⟨LieSubmodule.Quotient.mk' N (v σ : M), mk_weight σ⟩
  have hsum : ∑ σ ∈ S, (qv σ : M ⧸ N) = 0 := by
    simp only [qv]
    rw [show ∑ σ ∈ S, (LieSubmodule.Quotient.mk' N (v σ : M) : M ⧸ N) =
      LieSubmodule.Quotient.mk' N (∑ σ ∈ S, (v σ : M)) from
      (map_sum (LieSubmodule.Quotient.mk' N).toLinearMap (fun σ => (v σ : M)) S).symm]
    rw [← hdecomp]
    exact (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr hm
  have hν_zero := weightSpace_sum_eq_zero_components S qv hsum ν hν
  simp only [qv] at hν_zero
  rwa [LieSubmodule.Quotient.mk_eq_zero (N := N)] at hν_zero

/--
[weightDecomp_component_mem_lieSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma weightDecomp_component_mem_lieSubmodule
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {N : LieSubmodule R 𝔤 M}
  {m : M}
  {S : Finset (Δ.𝔥 →ₗ[R] R)}
  {v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ}
  {μ : Δ.𝔥 →ₗ[R] R}
-- given
  (hwd : HasWeightDecomposition Δ M)
  (hm : m ∈ N)
  (hdecomp : m = ∑ μ ∈ S, (v μ : M))
  (hμ : μ ∈ S) :
-- imply
  (v μ : M) ∈ N := by
-- proof
  classical
  obtain ⟨T, w, hdecomp_w, hw_mem⟩ := lieSubmodule_weight_decomp hwd N m hm
  let d : (ν : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M ν := fun ν =>
    ⟨(if ν ∈ S then (v ν : M) else 0) - (if ν ∈ T then (w ν : M) else 0),
      (WeightSpace Δ M ν).sub_mem
        (by split_ifs with h; exact (v ν).property; exact (WeightSpace Δ M ν).zero_mem)
        (by split_ifs with h; exact (w ν).property; exact (WeightSpace Δ M ν).zero_mem)⟩
  have hdsum : ∑ ν ∈ S ∪ T, (d ν : M) = 0 := by
    simp only [d, sub_eq_add_neg]
    rw [Finset.sum_add_distrib]
    have hv_sum : ∑ ν ∈ S ∪ T, (if ν ∈ S then (v ν : M) else 0) = ∑ ν ∈ S, (v ν : M) := by
      rw [← Finset.sum_filter]
      congr 1; ext ν; simp [Finset.mem_filter, Finset.mem_union]; tauto
    have hw_sum : ∑ ν ∈ S ∪ T, (-(if ν ∈ T then (w ν : M) else 0)) = -(∑ ν ∈ T, (w ν : M)) := by
      conv_lhs => arg 2; ext ν; rw [apply_ite Neg.neg, neg_zero]
      rw [← Finset.sum_filter]
      have hfilt : Finset.filter (fun a => a ∈ T) (S ∪ T) = T := by
        ext ν; simp [Finset.mem_filter, Finset.mem_union]; tauto
      rw [hfilt, Finset.sum_neg_distrib]
    rw [hv_sum, hw_sum, ← hdecomp, ← hdecomp_w, add_neg_cancel]
  have hd_zero := weightSpace_sum_eq_zero_components (S ∪ T) d hdsum μ
    (Finset.mem_union_left T hμ)
  simp only [d] at hd_zero
  rw [if_pos hμ] at hd_zero
  rw [sub_eq_zero] at hd_zero
  rw [hd_zero]
  split_ifs with h
  · exact hw_mem μ h
  · exact N.zero_mem

/--
[IsCategoryO_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma IsCategoryO_quotient
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
  {Z : LieSubmodule R 𝔤 X}
-- given
  (hXO : IsCategoryO Δ rd X) :
-- imply
  IsCategoryO Δ rd (X ⧸ Z) where finitely_generated := by
-- proof
  classical
  obtain ⟨S, hS⟩ := hXO.finitely_generated
  refine ⟨S.image (LieSubmodule.Quotient.mk' Z), ?_⟩
  rw [eq_top_iff]
  intro q _
  obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z q
  have hx : x ∈ (LieSubmodule.lieSpan R 𝔤 (S : Set X) : LieSubmodule R 𝔤 X) := by
    rw [hS]; trivial
  suffices LieSubmodule.map (LieSubmodule.Quotient.mk' Z)
    (LieSubmodule.lieSpan R 𝔤 (S : Set X)) ≤
    LieSubmodule.lieSpan R 𝔤
      (↑(S.image (LieSubmodule.Quotient.mk' Z)) : Set (X ⧸ Z)) by
    exact this ⟨x, hx, rfl⟩
  rw [LieSubmodule.map_le_iff_le_comap, LieSubmodule.lieSpan_le]
  intro s hs
  apply LieSubmodule.mem_comap.mpr
  apply LieSubmodule.subset_lieSpan
  simp only [Finset.coe_image]
  exact Set.mem_image_of_mem _ hs
  weight_decomp := by
    intro m_bar
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z m_bar
    obtain ⟨S, v, hm⟩ := hXO.weight_decomp m
    refine ⟨S, fun μ => ⟨(LieSubmodule.Quotient.mk' Z) (v μ : X), fun h => ?_⟩, ?_⟩
    · rw [← LieModuleHom.map_lie]
      rw [(v μ).prop h]
      exact map_smul (LieSubmodule.Quotient.mk' Z).toLinearMap (μ h) (v μ : X)
    · conv_lhs => rw [hm]
      rw [map_sum]
  weight_bound := by
    obtain ⟨bds, hbds⟩ := hXO.weight_bound
    refine ⟨bds, fun μ hμ => hbds μ ?_⟩
    rw [weights, Set.mem_setOf_eq] at hμ ⊢
    intro hbot
    apply hμ; clear hμ
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z q
    obtain ⟨S, v, hm⟩ := hXO.weight_decomp m
    have mk_wt : ∀ ν, (LieSubmodule.Quotient.mk' Z (v ν : X)) ∈
      WeightSpace Δ (X ⧸ Z) ν := by
      intro ν h
      rw [← LieModuleHom.map_lie, (v ν).prop h]
      exact map_smul (LieSubmodule.Quotient.mk' Z).toLinearMap (ν h) (v ν : X)
    classical
    let S' := {μ} ∪ S
    let w : (ν : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ (X ⧸ Z) ν := fun ν =>
      ⟨(if ν ∈ S then (LieSubmodule.Quotient.mk' Z (v ν : X)) else 0) -
        (if ν = μ then LieSubmodule.Quotient.mk' Z m else 0),
        (WeightSpace Δ (X ⧸ Z) ν).sub_mem
          (by split_ifs with h
            · exact mk_wt ν
            · exact (WeightSpace Δ (X ⧸ Z) ν).zero_mem)
          (by split_ifs with h
            · exact h ▸ hq
            · exact (WeightSpace Δ (X ⧸ Z) ν).zero_mem)⟩
    have hsum : ∑ ν ∈ S', (w ν : X ⧸ Z) = 0 := by
      simp only [w, S']
      rw [Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have hlhs : (∑ x ∈ {μ} ∪ S, (if x ∈ S then
        (LieSubmodule.Quotient.mk' Z) ↑(v x) else 0)) =
        ∑ x ∈ S, (LieSubmodule.Quotient.mk' Z) ↑(v x) := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp [Finset.mem_filter]
        tauto
      have hrhs : (∑ x ∈ {μ} ∪ S, (if x = μ then
        (LieSubmodule.Quotient.mk' Z) m else 0)) =
        (LieSubmodule.Quotient.mk' Z) m := by
        rw [Finset.sum_ite_eq']
        simp
      rw [hlhs, hrhs]
      conv_rhs => rw [hm]
      rw [map_sum]
    have hwμ := weightSpace_sum_eq_zero_components S' w hsum μ
      (Finset.mem_union_left S (Finset.mem_singleton_self μ))
    simp only [w] at hwμ
    simp only [if_true] at hwμ
    rw [sub_eq_zero] at hwμ
    split_ifs at hwμ with h
    ·
      have hv_zero : (v μ : X) = 0 := by
        rw [eq_bot_iff] at hbot
        exact hbot (v μ).property
      rwa [hv_zero, map_zero] at hwμ
    ·
      exact hwμ.symm

/--
[CategoryO.subquotient_has_weight_vector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.subquotient_has_weight_vector
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {N₁ N₂ : LieSubmodule R 𝔤 M}
-- given
  (hM : IsCategoryO Δ rd M)
  (hlt : N₁ < N₂) :
-- imply
  ∃ γ, ∃ x, x ∈ (N₂ : Submodule R M) ⊓ WeightSpace Δ M γ ∧ x ∉ (N₁ : Submodule R M) := by
-- proof
  obtain ⟨x, hx_N2, hx_N1⟩ := SetLike.exists_of_lt hlt
  obtain ⟨S, v, hdecomp⟩ := hM.weight_decomp x
  by_contra h_all
  push Not at h_all
  apply hx_N1
  rw [hdecomp]
  apply (N₁ : Submodule R M).sum_mem
  intro μ hμS
  have hv_N2 : (v μ : M) ∈ N₂ :=
    weightDecomp_component_mem_lieSubmodule hM.weight_decomp N₂ x hx_N2 S v hdecomp μ hμS
  have hv_wt : (v μ : M) ∈ WeightSpace Δ M μ := (v μ).property
  exact h_all μ (v μ : M) ⟨hv_N2, hv_wt⟩

/--
[PositiveRootData.qPlus_cone_inter_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma PositiveRootData.qPlus_cone_inter_finite
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {a b : Δ.𝔥 →ₗ[R] R} :
-- imply
  ∃ (T : Finset (Δ.𝔥 →ₗ[R] R)), ∀ γ, rd.IsInQPlus (a - γ) → rd.IsInQPlus (b - γ) → γ ∈ T :=
-- proof
  rd.cone_inter_finite a b

/--
[casimir_coset_weight_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma casimir_coset_weight_finite
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  ∃ (T : Finset (Δ.𝔥 →ₗ[R] R)), ∀ γ, γ ∈ weights Δ M → rd.IsInQPlus (wt - γ) → γ ∈ T := by
-- proof
  classical
  obtain ⟨bds, hbds⟩ := hM.weight_bound
  let Tw : (Δ.𝔥 →ₗ[R] R) → Finset (Δ.𝔥 →ₗ[R] R) :=
    fun w => (rd.qPlus_cone_inter_finite w wt).choose
  have hTw : ∀ w γ, rd.IsInQPlus (w - γ) → rd.IsInQPlus (wt - γ) → γ ∈ Tw w :=
    fun w => (rd.qPlus_cone_inter_finite w wt).choose_spec
  refine ⟨bds.biUnion Tw, fun γ hγ_wt hγ_qplus => ?_⟩
  obtain ⟨w, hw_mem, hw_qplus⟩ := hbds γ hγ_wt
  exact Finset.mem_biUnion.mpr ⟨w, hw_mem, hTw w γ hw_qplus hγ_qplus⟩

/--
[CategoryO.casimir_weight_finiteness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.casimir_weight_finiteness
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)), ∀ γ, (∃ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ ∧ ∃ x, x ∈ (N₂ : Submodule R M) ⊓ WeightSpace Δ M γ ∧ x ∉ (N₁ : Submodule R M)) → γ ∈ S := by
-- proof
  classical
  obtain ⟨bds, hbds⟩ := hM.weight_bound
  choose Twt hTwt using fun wt => casimir_coset_weight_finite Δ rd M hM wt
  refine ⟨bds.biUnion Twt, fun γ hγ => ?_⟩
  obtain ⟨N₁, N₂, hlt, x, hx_mem, hx_not⟩ := hγ
  have hx_wt : x ∈ (WeightSpace Δ M γ : Submodule R M) :=
    (Submodule.mem_inf.mp hx_mem).2
  have hx_ne : x ≠ 0 := by
    intro h; apply hx_not; rw [h]; exact (N₁ : Submodule R M).zero_mem
  have hγ_wt : γ ∈ weights Δ M := by
    show WeightSpace Δ M γ ≠ ⊥
    intro h
    have : x ∈ (⊥ : Submodule R M) := h ▸ hx_wt
    simp at this
    exact hx_ne this
  obtain ⟨wt, hwt_mem, hwt_qplus⟩ := hbds γ hγ_wt
  have hγ_in_Twt : γ ∈ Twt wt := (hTwt wt) γ hγ_wt hwt_qplus
  exact Finset.mem_biUnion.mpr ⟨wt, hwt_mem, hγ_in_Twt⟩

/--
[CategoryO.casimir_singular_weight_detection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.casimir_singular_weight_detection
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)), ∀ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ → ∃ γ ∈ S, ∃ x, x ∈ (N₂ : Submodule R M) ⊓ WeightSpace Δ M γ ∧ x ∉ (N₁ : Submodule R M) := by
-- proof
  obtain ⟨S, hS_finite⟩ := CategoryO.casimir_weight_finiteness hM
  exact ⟨S, fun N₁ N₂ hlt => by
    obtain ⟨γ, x, hx_mem, hx_not⟩ := CategoryO.subquotient_has_weight_vector hM N₁ N₂ hlt
    exact ⟨γ, hS_finite γ ⟨N₁, N₂, hlt, x, hx_mem, hx_not⟩, x, hx_mem, hx_not⟩⟩

/--
[strictMono_fin_le_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma strictMono_fin_le_val
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  {n : ℕ}
  {f : Fin n → ℕ}
-- given
  (hf : StrictMono f) :
-- imply
  ∀ i : Fin n, i.val ≤ f i := by
-- proof
  intro ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hj : j < n := by omega
    have h1 : f ⟨j, hj⟩ < f ⟨j + 1, hi⟩ := hf (Fin.mk_lt_mk.mpr (by omega))
    have h2 : j ≤ f ⟨j, hj⟩ := ih hj
    show j + 1 ≤ f ⟨j + 1, hi⟩; omega

/--
[findim_submodule_chain_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma findim_submodule_chain_bound
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [DivisionRing K]
  [AddCommGroup V]
  [Module K V]
  {E : Submodule K V}
  [FiniteDimensional K E] :
-- imply
  ∀ (chain : Fin (Module.finrank K E + 2) → Submodule K V), (∀ i, chain i ≤ E) → StrictMono chain → False := by
-- proof
  intro chain hle hmon
  have hfd : ∀ i, FiniteDimensional K ↥(chain i) :=
    fun i => Submodule.finiteDimensional_of_le (hle i)
  have hbound : ∀ i, Module.finrank K ↥(chain i) ≤ Module.finrank K E :=
    fun i => Submodule.finrank_mono (hle i)
  have hfm : StrictMono (fun i => Module.finrank K ↥(chain i)) := by
    intro a b hab; exact Submodule.finrank_lt_finrank_of_lt (hmon hab)
  have hge := strictMono_fin_le_val hfm ⟨Module.finrank K E + 1, by omega⟩
  have hle' := hbound ⟨Module.finrank K E + 1, by omega⟩
  simp at hge; omega

/--
[CategoryO.weightSpaceSum_chain_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.weightSpaceSum_chain_bound
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {S : Finset (Δ.𝔥 →ₗ[R] R)}
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  ∃ (n : ℕ), ∀ (chain : Fin (n + 2) → Submodule R M), (∀ i, chain i ≤ ⨆ μ ∈ S, WeightSpace Δ M μ) → StrictMono chain → False := by
-- proof
  have hE_fd : FiniteDimensional R ↥(⨆ μ ∈ S, WeightSpace Δ M μ) := by
    have hfg : (⨆ μ ∈ S, WeightSpace Δ M μ).FG := by
      apply Submodule.fg_biSup S
      intro μ _
      have hfin := CategoryO.weightSpace_finiteDimensional hM μ
      have htop : (⊤ : Submodule R (WeightSpace Δ M μ)).FG := Module.finite_def.mp hfin
      rwa [Submodule.fg_top] at htop
    change Module.Finite R ↥(⨆ μ ∈ S, WeightSpace Δ M μ)
    rw [Module.finite_def, Submodule.fg_top]; exact hfg
  exact ⟨Module.finrank R ↥(⨆ μ ∈ S, WeightSpace Δ M μ),
    findim_submodule_chain_bound _⟩

/--
[CategoryO.casimir_detecting_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.casimir_detecting_submodule
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  ∃ (E : Submodule R M) (n : ℕ), (∀ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ → ∃ x, x ∈ (N₂ : Submodule R M) ⊓ E ∧ x ∉ (N₁ : Submodule R M)) ∧ (∀ (chain : Fin (n + 2) → Submodule R M), (∀ i, chain i ≤ E) → StrictMono chain → False) := by
-- proof
  obtain ⟨S, hS_detect⟩ := CategoryO.casimir_singular_weight_detection hM
  obtain ⟨n, hE_bound⟩ := CategoryO.weightSpaceSum_chain_bound hM S
  refine ⟨⨆ μ ∈ S, WeightSpace Δ M μ, n, ?_, ?_⟩
  · intro N₁ N₂ hlt
    obtain ⟨γ, hγS, x, hx_mem, hx_not⟩ := hS_detect N₁ N₂ hlt
    exact ⟨x, Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx_mem).1,
      Submodule.mem_iSup_of_mem γ (Submodule.mem_iSup_of_mem hγS
        (Submodule.mem_inf.mp hx_mem).2)⟩, hx_not⟩
  · exact hE_bound

/--
[CategoryO.finite_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.finite_length
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  ∃ (n : ℕ), ∀ (chain : Fin (n + 2) → LieSubmodule R 𝔤 M), StrictMono chain → False := by
-- proof
  obtain ⟨E, n, hdetect, hE_bound⟩ := CategoryO.casimir_detecting_submodule hM
  exact ⟨n, CategoryO.detecting_submodule_gives_chain_bound E hdetect n hE_bound⟩

/--
[CategoryO.wellFoundedGT](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.wellFoundedGT
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  WellFoundedGT (LieSubmodule R 𝔤 M) := by
-- proof
  obtain ⟨n, hn⟩ := CategoryO.finite_length hM
  rw [WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => ?_⟩
  apply hn (fun (i : Fin (n + 2)) => f i)
  intro i j hij
  exact f.map_rel_iff.2 hij

/--
[lie_hom_commutes_uea_act](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma lie_hom_commutes_uea_act
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule L N]
  [LieModule R L N]
  {f : M →ₗ⁅R, L⁆ N}
  {u : UniversalEnvelopingAlgebra R L}
  {m : M} :
-- imply
  f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)) u) m) = ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N)) u) (f m) := by
-- proof
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u
  suffices h : ∀ m' : M,
    f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
      ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)) m') =
    ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
      ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)) (f m') from h m
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro m'
    simp only [Algebra.algebraMap_eq_smul_one]
    simp
  | ι x =>
    intro m'
    rw [show (UniversalEnvelopingAlgebra.mkAlgHom R L) ((TensorAlgebra.ι R) x) =
      (UniversalEnvelopingAlgebra.ι R) x from rfl]
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, UniversalEnvelopingAlgebra.lift_ι_apply]
    simp only [LieModule.toEnd_apply_apply]
    exact f.map_lie x m'
  | mul a b ha hb =>
    intro m'
    rw [map_mul, map_mul, map_mul]
    show f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
      ((UniversalEnvelopingAlgebra.mkAlgHom R L) a))
      (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
        ((UniversalEnvelopingAlgebra.mkAlgHom R L) b)) m')) =
      ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
        ((UniversalEnvelopingAlgebra.mkAlgHom R L) a))
        (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
          ((UniversalEnvelopingAlgebra.mkAlgHom R L) b)) (f m'))
    rw [ha]
    congr 1
    exact hb m'
  | add a b ha hb =>
    intro m'
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add]
    congr 1
    · exact ha m'
    · exact hb m'

/--
[verma_singular_one_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma verma_singular_one_dim
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {μ : Δ.𝔥 →ₗ[R] R}
  {v₁ v₂ : M}
-- given
  (hM : IsVermaModule Δ M wt)
  (hv₁_ne : v₁ ≠ 0)
  (hv₁_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v₁⁆ = μ h • v₁)
  (hv₁_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v₁⁆ = 0)
  (hv₂_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v₂⁆ = μ h • v₂)
  (hv₂_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v₂⁆ = 0) :
-- imply
  ∃ (c : R), v₂ = c • v₁ := by
-- proof
  letI : Module (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M := instModuleUEASubalg Δ.𝔫_neg M
  obtain ⟨φ, hφ⟩ := hM.free_over_nminus
  set u₁ := φ.symm v₁
  set u₂ := φ.symm v₂
  have hv₁_eq : φ u₁ = v₁ := LinearEquiv.apply_symm_apply φ v₁
  have hv₂_eq : φ u₂ = v₂ := LinearEquiv.apply_symm_apply φ v₂
  have hφu₁ : φ u₁ = (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec := by
    have key : φ u₁ = u₁ • φ (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := by
      have : u₁ = u₁ * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one u₁).symm
      conv_lhs => rw [this]; exact φ.map_smul u₁ 1
    rw [key, hφ]; rfl
  have hφu₂ : φ u₂ = (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec := by
    have key : φ u₂ = u₂ • φ (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := by
      have : u₂ = u₂ * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one u₂).symm
      conv_lhs => rw [this]; exact φ.map_smul u₂ 1
    rw [key, hφ]; rfl
  have hu₁_ne : (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec ≠ 0 := by
    rw [← hφu₁, hv₁_eq]; exact hv₁_ne
  have hu₁_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
    (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec⁆ =
    μ h • (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec := by
    intro h; rw [← hφu₁, hv₁_eq]; exact hv₁_wt h
  have hu₂_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
    (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec⁆ =
    μ h • (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec := by
    intro h; rw [← hφu₂, hv₂_eq]; exact hv₂_wt h
  have hu₁_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤),
    (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec⁆ = 0 := by
    intro e; rw [← hφu₁, hv₁_eq]; exact hv₁_npos e
  have hu₂_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤),
    (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec⁆ = 0 := by
    intro e; rw [← hφu₂, hv₂_eq]; exact hv₂_npos e
  obtain ⟨c, hc⟩ := pbw_nminus_singular_proportional hM μ u₁ u₂
    hu₁_ne hu₁_wt hu₁_npos hu₂_wt hu₂_npos
  refine ⟨c, ?_⟩
  rw [← hv₂_eq, ← hv₁_eq, hφu₂, hφu₁, hc]

/--
[verma_hom_unique_up_to_scalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma verma_hom_unique_up_to_scalar
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup Mmu]
  [Module R Mmu]
  [LieRingModule 𝔤 Mmu]
  [LieModule R 𝔤 Mmu]
  [AddCommGroup Mlam]
  [Module R Mlam]
  [LieRingModule 𝔤 Mlam]
  [LieModule R 𝔤 Mlam]
  {wt_mu wt_lam : Δ.𝔥 →ₗ[R] R}
  {eta eta' : Mmu →ₗ⁅R, 𝔤⁆ Mlam}
-- given
  (hMmu : IsVermaModule Δ Mmu wt_mu)
  (hMlam : IsVermaModule Δ Mlam wt_lam)
  (heta_ne : eta ≠ 0) :
-- imply
  ∃ (c : R), ∀ m, eta' m = c • eta m := by
-- proof
  have heta_vmu_ne : eta hMmu.highestWeightVec ≠ 0 := by
    intro h
    apply heta_ne
    have hker : hMmu.highestWeightVec ∈ LieModuleHom.ker eta :=
      LieModuleHom.mem_ker.mpr h
    have hspan_le : LieSubmodule.lieSpan R 𝔤 {hMmu.highestWeightVec} ≤
      LieModuleHom.ker eta :=
      LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hker)
    have hker_top : LieModuleHom.ker eta = ⊤ :=
      eq_top_iff.mpr (hMmu.generates ▸ hspan_le)
    ext m
    have hm : m ∈ LieModuleHom.ker eta := hker_top ▸ LieSubmodule.mem_top m
    simp [LieModuleHom.mem_ker.mp hm]
  obtain ⟨c, hc⟩ := verma_singular_one_dim wt_lam hMlam wt_mu
    (eta hMmu.highestWeightVec) (eta' hMmu.highestWeightVec)
    heta_vmu_ne
    (fun h => by rw [← LieModuleHom.map_lie]; rw [hMmu.cartan_action]; simp [map_smul])
    (fun e => by rw [← LieModuleHom.map_lie]; rw [hMmu.npos_action]; simp)
    (fun h => by rw [← LieModuleHom.map_lie]; rw [hMmu.cartan_action]; simp [map_smul])
    (fun e => by rw [← LieModuleHom.map_lie]; rw [hMmu.npos_action]; simp)
  have hval : (eta' - c • eta) hMmu.highestWeightVec = 0 := by
    simp [LieModuleHom.sub_apply, LieModuleHom.smul_apply, hc, sub_self]
  have hker_top : LieModuleHom.ker (eta' - c • eta) = ⊤ := by
    have hker : hMmu.highestWeightVec ∈ LieModuleHom.ker (eta' - c • eta) :=
      LieModuleHom.mem_ker.mpr hval
    have hspan_le : LieSubmodule.lieSpan R 𝔤 {hMmu.highestWeightVec} ≤
      LieModuleHom.ker (eta' - c • eta) := by
      apply LieSubmodule.lieSpan_le.mpr
      intro x hx
      rwa [Set.mem_singleton_iff.mp hx]
    exact eq_top_iff.mpr (hMmu.generates ▸ hspan_le)
  exact ⟨c, fun m => by
    have hm : m ∈ LieModuleHom.ker (eta' - c • eta) := hker_top ▸ LieSubmodule.mem_top m
    rw [LieModuleHom.mem_ker] at hm
    have : (eta' - c • eta) m = 0 := hm
    rwa [LieModuleHom.sub_apply, LieModuleHom.smul_apply, sub_eq_zero] at this⟩
universe u_vm in

/--
[IsVermaModule.universal_map'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma IsVermaModule.universal_map'
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_vm}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {V : Type u_vm}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  {v : V}
-- given
  (hM : IsVermaModule Δ M wt)
  (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v)
  (hv_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) :
-- imply
  ∃ (η : M →ₗ⁅R, 𝔤⁆ V), η hM.highestWeightVec = v :=
-- proof
  hM.universal_map V v hv_wt hv_npos
universe u_vhsw in

/--
[verma_hom_same_weight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma verma_hom_same_weight
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {Mmu : Type u_vhsw}
  [AddCommGroup Mmu]
  [Module R Mmu]
  [LieRingModule 𝔤 Mmu]
  [LieModule R 𝔤 Mmu]
  {Mlam : Type u_vhsw}
  [AddCommGroup Mlam]
  [Module R Mlam]
  [LieRingModule 𝔤 Mlam]
  [LieModule R 𝔤 Mlam]
  {wt : Δ.𝔥 →ₗ[R] R}
-- given
  (hMmu : IsVermaModule Δ Mmu wt)
  (hMlam : IsVermaModule Δ Mlam wt) :
-- imply
  ∃ (eta : Mmu →ₗ⁅R, 𝔤⁆ Mlam), eta ≠ 0 := by
-- proof
  obtain ⟨η, hη⟩ := hMmu.universal_map' hMlam.highestWeightVec
    hMlam.cartan_action hMlam.npos_action
  exact ⟨η, fun h => hMlam.hwv_ne_zero (by rw [← hη]; simp [h])⟩

/--
[IsInQPlus_antisymm_catO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma IsInQPlus_antisymm_catO
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {μ : Δ.𝔥 →ₗ[R] R}
-- given
  (hpos : rd.IsInQPlus μ)
  (hneg : rd.IsInQPlus (-μ)) :
-- imply
  μ = 0 := by
-- proof
  classical
  obtain ⟨c, hc⟩ := hpos
  obtain ⟨d, hd⟩ := hneg
  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hμ (by rw [hc]; exact Finset.sum_eq_zero fun β hβ => by simp [hall β hβ])
  obtain ⟨β, hβ, hcβ⟩ := hne
  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _; rw [add_nsmul]
  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract
  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ
  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
    ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp [Finset.ne_of_mem_erase hγ]
  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]
  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ; omega
  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩

/--
[CategoryO.exists_maximal_weight_vector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.exists_maximal_weight_vector
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [Nontrivial M]
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  ∃ (v : M) (μ : Δ.𝔥 →ₗ[R] R), v ≠ 0 ∧ (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = μ h • v) ∧ (∀ (ν : Δ.𝔥 →ₗ[R] R) (w : M), (∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = ν h • w) → rd.IsInQPlus (ν - μ) → ν ≠ μ → w = 0) := by
-- proof
  classical
  obtain ⟨m, hm_ne⟩ := exists_ne (0 : M)
  obtain ⟨S, wv, hm_decomp⟩ := hM.weight_decomp m
  have hS_ne : ∃ μ₀ ∈ S, (wv μ₀ : M) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hm_ne
    rw [hm_decomp]
    exact Finset.sum_eq_zero fun μ hμ => hall μ hμ
  obtain ⟨μ₀, hμ₀_mem, hv₀_ne⟩ := hS_ne
  have hμ₀_wt : μ₀ ∈ weights Δ M := by
    rw [weights, Set.mem_setOf_eq]
    intro h
    apply hv₀_ne
    rw [Submodule.eq_bot_iff] at h
    exact h _ (wv μ₀).prop
  obtain ⟨bds, hbds⟩ := hM.weight_bound
  have hcontain : ∀ μ ∈ weights Δ M,
    ∃ wt ∈ bds, rd.IsInQPlus (wt - μ) := hbds
  let T_map : (Δ.𝔥 →ₗ[R] R) → Finset (Δ.𝔥 →ₗ[R] R) :=
    fun wt => (rd.cone_inter_finite wt wt).choose
  have hT_map_spec : ∀ wt, ∀ γ,
    (∃ c : _ → ℕ, wt - γ = ∑ α ∈ rd.posRoots, (c α) • α) →
    (∃ c : _ → ℕ, wt - γ = ∑ α ∈ rd.posRoots, (c α) • α) →
    γ ∈ T_map wt :=
    fun wt => (rd.cone_inter_finite wt wt).choose_spec
  let T : Finset (Δ.𝔥 →ₗ[R] R) := bds.biUnion (fun wt => T_map wt)
  have hweights_in_T : ∀ μ ∈ weights Δ M, μ ∈ T := by
    intro μ hμ
    obtain ⟨wt, hwt_mem, hwt_bound⟩ := hcontain μ hμ
    obtain ⟨c, hc⟩ := hwt_bound
    have hγ_in : μ ∈ T_map wt := by
      exact hT_map_spec wt μ ⟨c, hc⟩ ⟨c, hc⟩
    exact Finset.mem_biUnion.mpr ⟨wt, hwt_mem, hγ_in⟩
  let T_wt : Finset (Δ.𝔥 →ₗ[R] R) := T.filter (fun μ => μ ∈ weights Δ M)
  have hT_wt_ne : T_wt.Nonempty := by
    exact ⟨μ₀, Finset.mem_filter.mpr ⟨hweights_in_T μ₀ hμ₀_wt, hμ₀_wt⟩⟩
  letI : LE (Δ.𝔥 →ₗ[R] R) := ⟨fun μ ν => rd.IsInQPlus (ν - μ)⟩
  letI : IsTrans (Δ.𝔥 →ₗ[R] R) LE.le := ⟨by
    intro μ ν ξ hμν hνξ
    show rd.IsInQPlus (ξ - μ)
    exact rd.IsInQPlus_trans ξ ν μ hνξ hμν⟩
  obtain ⟨μ, hμ_mem, hμ_max⟩ := Finset.exists_maximal hT_wt_ne
  rw [Finset.mem_filter] at hμ_mem
  have hμ_wt : μ ∈ weights Δ M := hμ_mem.2
  rw [weights, Set.mem_setOf_eq] at hμ_wt
  rw [Submodule.ne_bot_iff] at hμ_wt
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ_wt
  have hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = μ h • v := hv_mem
  refine ⟨v, μ, hv_ne, hv_wt, ?_⟩
  intro ν w hw_wt hν_above hν_ne
  by_contra hw_ne
  push_neg at hw_ne
  have hν_wt : ν ∈ weights Δ M := by
    rw [weights, Set.mem_setOf_eq]
    intro h
    apply hw_ne
    rw [Submodule.eq_bot_iff] at h
    exact h _ hw_wt
  have hν_in_T : ν ∈ T := hweights_in_T ν hν_wt
  have hν_in_T_wt : ν ∈ T_wt := Finset.mem_filter.mpr ⟨hν_in_T, hν_wt⟩
  have hμ_le_ν : (μ : Δ.𝔥 →ₗ[R] R) ≤ ν := hν_above
  have hν_le_μ : (ν : Δ.𝔥 →ₗ[R] R) ≤ μ := hμ_max hν_in_T_wt hμ_le_ν
  have hνμ_zero : ν - μ = 0 := by
    exact IsInQPlus_antisymm_catO rd (ν - μ) hν_above (by rwa [neg_sub])
  have : ν = μ := sub_eq_zero.mp hνμ_zero
  exact hν_ne this

/--
[root_vec_raises_weight_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma root_vec_raises_weight_local
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {α : Δ.𝔥 →ₗ[R] R}
  {μ : Δ.𝔥 →ₗ[R] R}
  {w : M}
-- given
  (hα : α ∈ rd.posRoots)
  (hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) :
-- imply
  ∀ (h : Δ.𝔥), ⁅(h : 𝔤), (⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ : M)⁆ = (α + μ) h • ⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ := by
-- proof
  intro h
  have hleibniz := leibniz_lie (h : 𝔤) (↑(rd.posRootVec α hα) : 𝔤) w
  have hroot := rd.posRootVec_weight α hα h
  have hwt := hw_wt h
  rw [hroot, hwt] at hleibniz
  rw [smul_lie, LieModule.lie_smul] at hleibniz
  rw [hleibniz]
  simp only [LinearMap.add_apply]
  rw [← add_smul]

/--
[CategoryO.exists_singular_vector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.exists_singular_vector
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [Nontrivial M]
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  ∃ (v : M) (lam : Δ.𝔥 →ₗ[R] R), v ≠ 0 ∧ (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = lam h • v) ∧ (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) := by
-- proof
  classical
  obtain ⟨v, μ, hv_ne, hv_wt, hμ_max⟩ := CategoryO.exists_maximal_weight_vector hM
  refine ⟨v, μ, hv_ne, hv_wt, ?_⟩
  intro e
  obtain ⟨c, hc⟩ := rd.npos_span e
  have hew : (⁅(e : 𝔤), v⁆ : M) =
    ∑ x ∈ rd.posRoots.attach, c x.1 x.2 • ⁅(↑(rd.posRootVec x.1 x.2) : 𝔤), v⁆ := by
    conv_lhs => rw [show (e : 𝔤) = ∑ x ∈ rd.posRoots.attach,
      c x.1 x.2 • (↑(rd.posRootVec x.1 x.2) : 𝔤) from hc]
    rw [sum_lie]
    congr 1
    ext x
    rw [smul_lie]
  have hzero : ∀ (x : { x // x ∈ rd.posRoots }),
    ⁅(↑(rd.posRootVec x.1 x.2) : 𝔤), v⁆ = (0 : M) := by
    intro ⟨α, hα⟩
    apply hμ_max (α + μ)
    · exact root_vec_raises_weight_local α hα μ v hv_wt
    · show rd.IsInQPlus (α + μ - μ)
      rw [add_sub_cancel_right]
      exact ⟨fun β => if β = α then 1 else 0, by simp [Finset.sum_ite_eq', hα]⟩
    · intro heq
      apply rd.posRoots_ne_zero α hα
      have : α + μ - μ = μ - μ := by rw [heq]
      simp [add_sub_cancel_right, sub_self] at this
      exact this
  rw [hew]
  simp only [hzero, smul_zero, Finset.sum_const_zero]

/--
[CategoryO.simple_objects_are_highest_weight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma CategoryO.simple_objects_are_highest_weight
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
-- given
  (hM : IsCategoryO Δ rd M)
  (hirr : LieModule.IsIrreducible R 𝔤 M) :
-- imply
  ∃ (lam : Δ.𝔥 →ₗ[R] R), Nonempty (IsHighestWeightModule Δ M lam) := by
-- proof
  haveI : LieModule.IsIrreducible R 𝔤 M := hirr
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible R 𝔤 M
  obtain ⟨v, lam, hv_ne, hv_weight, hv_killed⟩ :=
    CategoryO.exists_singular_vector hM (M := M)
  have hgen : LieSubmodule.lieSpan R 𝔤 {v} = ⊤ := by
    have hspan_ne_bot : LieSubmodule.lieSpan R 𝔤 {v} ≠ ⊥ := by
      intro h
      have := (LieSubmodule.lieSpan_eq_bot_iff R 𝔤 M).mp h v (Set.mem_singleton v)
      exact hv_ne this
    exact (hirr.eq_bot_or_eq_top _).resolve_left hspan_ne_bot
  exact ⟨lam, ⟨{
    highestWeightVec := v
    hwv_ne_zero := hv_ne
    cartan_action := hv_weight
    npos_action := hv_killed
    generates := hgen
  }⟩⟩

/--
[WeylStabilizer_mul_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma WeylStabilizer_mul_closed
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {x : Δ.𝔥 →ₗ[R] R}
  {w₁ w₂ : wg.W}
-- given
  (h₁ : w₁ ∈ WeylStabilizer rd wg x)
  (h₂ : w₂ ∈ WeylStabilizer rd wg x) :
-- imply
  w₁ * w₂ ∈ WeylStabilizer rd wg x := by
-- proof
  show wg.dualAction (w₁ * w₂) x = x
  rw [wg.dualAction_mul, h₂, h₁]

/--
[RootSystemWithReflections.dualAction_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma RootSystemWithReflections.dualAction_mul
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {_rs : RootSystemWithReflections rd wg}
  {w₁ w₂ : wg.W}
  {μ : Δ.𝔥 →ₗ[R] R} :
-- imply
  wg.dualAction (w₁ * w₂) μ = wg.dualAction w₁ (wg.dualAction w₂ μ) :=
-- proof
  wg.dualAction_mul w₁ w₂ μ

/--
[WeylStabilizerModQ_mul_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma WeylStabilizerModQ_mul_closed
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {rs : RootSystemWithReflections rd wg}
  {x : Δ.𝔥 →ₗ[R] R}
  {w₁ w₂ : wg.W}
-- given
  (h₁ : w₁ ∈ WeylStabilizerModQ rd wg x)
  (h₂ : w₂ ∈ WeylStabilizerModQ rd wg x) :
-- imply
  w₁ * w₂ ∈ WeylStabilizerModQ rd wg x := by
-- proof
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  obtain ⟨c₂', hc₂'⟩ := rs.dualAction_rootLattice w₁ c₂
  refine ⟨fun α => c₁ α + c₂' α, ?_⟩
  have hmul := rs.dualAction_mul w₁ w₂ x
  have hsub := rs.dualAction_sub w₁ (wg.dualAction w₂ x) x
  have hkey : wg.dualAction w₁ (wg.dualAction w₂ x - x) =
    wg.dualAction w₁ (wg.dualAction w₂ x) - wg.dualAction w₁ x := hsub
  rw [hc₂] at hkey
  rw [hc₂'] at hkey
  have : wg.dualAction (w₁ * w₂) x - x =
    (wg.dualAction w₁ (wg.dualAction w₂ x) - wg.dualAction w₁ x) +
    (wg.dualAction w₁ x - x) := by
    rw [hmul]
    abel
  rw [this, ← hkey, hc₁, ← Finset.sum_add_distrib]
  congr 1
  funext α
  show c₂' α • α + c₁ α • α = (c₁ α + c₂' α) • α
  rw [add_comm (c₁ α) (c₂' α), add_zsmul]

/--
[weyl_generated_by_root_reflections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma weyl_generated_by_root_reflections
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {rs : RootSystemWithReflections rd wg} :
-- imply
  ∀ w : wg.W, ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R), (∀ i, αs i ∈ rs.allRoots) ∧ w = (List.ofFn (fun i => rs.reflection (αs i))).prod :=
-- proof
  fun w => rs.generated_by_reflections w

/--
[Wx_roots_form_root_system](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma Wx_roots_form_root_system
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {rs : RootSystemWithReflections rd wg}
  {x : Δ.𝔥 →ₗ[R] R} :
-- imply
  IsRootSubsystem rd wg rs (rootsOfStabilizer rd wg rs x) := by
-- proof
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro α hα
    exact hα.1
  ·
    intro h0
    have h0_in : (0 : Δ.𝔥 →ₗ[R] R) ∈ rs.allRoots := h0.1
    obtain hp | hn := rs.roots_pos_or_neg 0 h0_in
    · exact absurd rfl (rd.posRoots_ne_zero 0 hp)
    · simp at hn
      exact absurd rfl (rd.posRoots_ne_zero 0 hn)
  ·
    intro α hα
    refine ⟨rs.allRoots_neg_closed α hα.1, ?_⟩
    rwa [rs.reflection_neg α hα.1]
  ·
    intro α hα β hβ
    have h_root : wg.dualAction (rs.reflection α) β ∈ rs.allRoots :=
      rs.allRoots_reflection_closed α hα.1 β hβ.1
    refine ⟨h_root, ?_⟩
    rw [← rs.reflection_conjugation α hα.1 β hβ.1]
    exact WeylStabilizerModQ_mul_closed rd wg rs x
      (WeylStabilizerModQ_mul_closed rd wg rs x hα.2 hβ.2)
      hα.2

/--
[Rx_dual_is_root_subsystem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean)
-/
@[path]
private lemma Rx_dual_is_root_subsystem
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {rs : RootSystemWithReflections rd wg}
  {x : Δ.𝔥 →ₗ[R] R} :
-- imply
  ∀ h : Δ.𝔥, h ∈ corootsOf rs (rootsOfStabilizer rd wg rs x) ↔ (h ∈ Submodule.span ℤ (corootsOf rs (rootsOfStabilizer rd wg rs x)) ∧ h ∈ corootsOf rs (↑rs.allRoots : Set (Δ.𝔥 →ₗ[R] R))) := by
-- proof
  intro h
  constructor
  ·
    intro hh
    constructor
    · exact Submodule.subset_span hh
    · obtain ⟨α, hα_mem, hα_eq⟩ := hh
      refine ⟨α, ?_, hα_eq⟩
      simp only [Finset.mem_coe]
      exact hα_mem.1
  ·
    intro ⟨h_span, h_all⟩
    obtain ⟨β, hβ_all, hβ_eq⟩ := h_all
    simp only [Finset.mem_coe] at hβ_all
    refine ⟨β, ⟨hβ_all, ?_⟩, hβ_eq⟩
    have h_int_stab : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ rootsOfStabilizer rd wg rs x →
      ∃ (n : ℤ), x (rs.coroot α) = (n : R) := by
      intro α hα
      apply rs.pairing_integral α hα.1 x
      obtain ⟨c, hc⟩ := hα.2
      have hrefl := rs.reflection_formula α hα.1 x
      have : wg.dualAction (rs.reflection α) x - x = -(x (rs.coroot α)) • α := by
        rw [hrefl]
        simp [sub_sub_cancel_left]
      rw [← this]
      exact ⟨c, hc⟩
    have h_int_beta : ∃ (N : ℤ), x (rs.coroot β) = (N : R) := by
      let S : Submodule ℤ Δ.𝔥 :=
        { carrier := {v : Δ.𝔥 | ∃ (n : ℤ), x v = (n : R)}
          add_mem' := by
            intro a b ⟨na, ha⟩ ⟨nb, hb⟩
            exact ⟨na + nb, by rw [map_add, ha, hb, Int.cast_add]⟩
          zero_mem' := ⟨0, by simp⟩
          smul_mem' := by
            intro m v ⟨n, hn⟩
            refine ⟨m * n, ?_⟩
            show x ((m : ℤ) • v) = ((m * n : ℤ) : R)
            rw [← Int.cast_smul_eq_zsmul R m v, map_smul, hn, Int.cast_mul, smul_eq_mul] }
      have h_sub : corootsOf rs (rootsOfStabilizer rd wg rs x) ⊆ S := by
        intro v hv
        obtain ⟨α, hα_mem, hα_eq⟩ := hv
        rw [hα_eq]
        exact h_int_stab α hα_mem
      rw [hβ_eq] at h_span
      exact Submodule.span_le.mpr h_sub h_span
    obtain ⟨N, hN⟩ := h_int_beta
    show rs.reflection β ∈ WeylStabilizerModQ rd wg x
    rw [WeylStabilizerModQ]
    simp only [Set.mem_setOf_eq]
    have hreflβ := rs.reflection_formula β hβ_all x
    have hdiff : wg.dualAction (rs.reflection β) x - x = -(x (rs.coroot β)) • β := by
      rw [hreflβ]
      simp [sub_sub_cancel_left]
    rw [hdiff, hN]
    have h_zsmul : -((N : R)) • β = (-N : ℤ) • β := by
      rw [← Int.cast_neg, Int.cast_smul_eq_zsmul R]
    rw [h_zsmul]
    obtain h_pos | h_neg := rs.roots_pos_or_neg β hβ_all
    ·
      classical
      refine ⟨fun γ => if γ = β then -N else 0, ?_⟩
      rw [Finset.sum_eq_single β
        (fun γ _ hγ => by simp [hγ])
        (fun hβ => absurd h_pos hβ)]
      simp
    ·
      classical
      refine ⟨fun γ => if γ = -β then N else 0, ?_⟩
      rw [Finset.sum_eq_single (-β)
        (fun γ _ hγ => by simp [hγ])
        (fun hβ => absurd h_neg hβ)]
      simp


-- created on 2026-10-23
-- updated on 2026-10-24
