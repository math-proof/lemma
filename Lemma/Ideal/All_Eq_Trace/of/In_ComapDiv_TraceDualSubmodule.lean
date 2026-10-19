import Mathlib
import sympy.Basic
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open scoped TensorProduct nonZeroDivisors


private lemma span_mk_image_eq_top
  [CommRing R] [CommRing S] [Algebra R S]
  {I : Ideal R} {s : Set S}
-- given
  (hs : Submodule.span R s = ⊤) :
-- imply
  Submodule.span (R ⧸ I) ((Ideal.Quotient.mk (I.map (algebraMap R S))) '' s) = ⊤ := by
-- proof
  have hcoe : ⇑((IsScalarTower.toAlgHom R S (S ⧸ I.map (algebraMap R S))).toLinearMap) =
      ⇑(Ideal.Quotient.mk (I.map (algebraMap R S))) := by
    rw [AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq]
  have H : (Submodule.span (R ⧸ I) ((Ideal.Quotient.mk (I.map (algebraMap R S))) '' s)).restrictScalars R =
      (Submodule.span R s).map (IsScalarTower.toAlgHom R S (S ⧸ I.map (algebraMap R S))).toLinearMap := by
    rw [Submodule.map_span, ← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, hcoe]
  rwa [hs, Submodule.map_top, LinearMap.range_eq_top.mpr, Submodule.restrictScalars_eq_top_iff] at H
  rw [hcoe]
  apply Ideal.Quotient.mk_surjective

private lemma linearIndependent_mk_comp
  [CommRing R] [CommRing S] [Algebra R S]
  {I : Ideal R} {b : Module.Basis ι R S} :
-- imply
  LinearIndependent (R ⧸ I) (Ideal.Quotient.mk (I.map (algebraMap R S)) ∘ b) := by
-- proof
  classical
  rw [linearIndependent_iff']
  intro t g hg i hi
  choose g' hg' using fun j => Ideal.Quotient.mk_surjective (g j)
  have hsum : Ideal.Quotient.mk (I.map (algebraMap R S)) (∑ j ∈ t, g' j • b j) = 0 := by
    rw [map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.comp_apply, ← hg' j, Algebra.smul_def, map_mul,
      Ideal.Quotient.mk_smul_mk_quotient_map_quotient, map_mul, Ideal.Quotient.mk_algebraMap]
  rw [Ideal.Quotient.eq_zero_iff_mem] at hsum
  have hsmul : (∑ j ∈ t, g' j • b j) ∈ I • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map]
    apply hsum
  rw [← b.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum] at hsmul
  obtain ⟨a, ha, hax⟩ := hsmul
  have hcoord : b.repr (∑ j ∈ t, g' j • b j) i = g' i := by
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_eq_left hi]
  have hcoord' : b.repr (a.sum fun j c => c • b j) i = a i := by
    have : (a.sum fun j c => c • b j) = Finsupp.linearCombination R b a := rfl
    rw [this, b.repr_linearCombination]
  have hgi : g' i = a i := by rw [← hcoord, ← hcoord', hax]
  rw [← hg' i, hgi, Ideal.Quotient.eq_zero_iff_mem]
  apply ha i

private noncomputable def basisQuot
  {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {I : Ideal R} {ι : Type*} (b : Module.Basis ι R S) : Module.Basis ι (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Module.Basis.mk (linearIndependent_mk_comp (I := I) (b := b)) (by rw [Set.range_comp]; apply (span_mk_image_eq_top (I := I) (s := Set.range b) b.span_eq).ge)

private lemma basisQuot_apply
  [CommRing R] [CommRing S] [Algebra R S]
  {I : Ideal R} {b : Module.Basis ι R S} {i : ι} :
-- imply
  basisQuot (I := I) b i = Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) := by
-- proof
  rw [basisQuot, Module.Basis.coe_mk, Function.comp_apply]

private lemma basisQuot_repr
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι]
  {I : Ideal R} {b : Module.Basis ι R S} {x : S} {i : ι} :
-- imply
  (basisQuot (I := I) b).repr (Ideal.Quotient.mk (I.map (algebraMap R S)) x) i =
    Ideal.Quotient.mk I (b.repr x i) := by
-- proof
  classical
  refine congr_fun (g := Ideal.Quotient.mk I ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ I) _ _).symm.injective
  apply (basisQuot (I := I) b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply, Module.Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply (R ⧸ I), Fintype.linearCombination_apply]
  simp only [Function.comp_apply, basisQuot_apply, Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← Algebra.smul_def]
  rw [← map_sum, Module.Basis.sum_repr b x]

private lemma trace_quot_mk
  [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
  {I : Ideal R} {x : S} :
-- imply
  Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
    Ideal.Quotient.mk I (Algebra.trace R S x) := by
-- proof
  classical
  let ιb := Module.Free.ChooseBasisIndex R S
  let b : Module.Basis ιb R S := Module.Free.chooseBasis R S
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace (basisQuot (I := I) b), AddMonoidHom.map_trace]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply, basisQuot_apply, LinearMap.mul_apply', Matrix.map_apply, ← map_mul, basisQuot_repr]


/--
[Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {S : Type u} [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
  {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F] [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
  {I : Ideal R} {s : S}
-- given
  (hs : s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap
    (Algebra.linearMap S F))) :
-- imply
  ∀ φ : Module.Dual (R ⧸ I) (S ⧸ I.map (algebraMap R S)),
    ∃ x : S ⧸ I.map (algebraMap R S), ∀ y : S ⧸ I.map (algebraMap R S),
      φ (Ideal.Quotient.mk (I.map (algebraMap R S)) s * y) =
        Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (x * y) := by
-- proof
  classical
  intro φb
  let _ : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) F := IsIntegralClosure.isLocalization R K F S
  let _ : FiniteDimensional K F := Module.Finite.of_isLocalization R S R⁰
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let b := Module.Free.chooseBasis R S
  choose g hg using fun i =>
    Ideal.Quotient.mk_surjective (φb (Ideal.Quotient.mk (I.map (algebraMap R S)) (b i)))
  let φ : S →ₗ[R] R := b.constr R g
  have hφb : ∀ i, φ (b i) = g i := fun i => b.constr_basis R g i
  have hφ : ∀ y : S, Ideal.Quotient.mk I (φ y) =
      φb (Ideal.Quotient.mk (I.map (algebraMap R S)) y) := by
    intro y
    let L1 : S →ₗ[R] (R ⧸ I) := LinearMap.comp (Ideal.Quotient.mkₐ R I).toLinearMap φ
    let L2 : S →ₗ[R] (R ⧸ I) :=
      LinearMap.comp (φb.restrictScalars R) (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))).toLinearMap
    apply LinearMap.congr_fun (show L1 = L2 from b.ext fun i => by simp only [L1, L2, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, LinearMap.restrictScalars_apply, hφb, hg]) y
  let bF := b.localizationLocalization K R⁰ F
  have hbF : ∀ i, bF i = algebraMap S F (b i) := fun i => Module.Basis.localizationLocalization_apply K R⁰ F b i
  let ψ : F →ₗ[K] K := bF.constr K (fun i => algebraMap R K (g i))
  have hψ : ∀ y : S, ψ (algebraMap S F y) = algebraMap R K (φ y) := by
    intro y
    let M1 : S →ₗ[R] K := LinearMap.comp (ψ.restrictScalars R) (IsScalarTower.toAlgHom R S F).toLinearMap
    let M2 : S →ₗ[R] K := LinearMap.comp (Algebra.linearMap R K) φ
    apply LinearMap.congr_fun (show M1 = M2 from b.ext fun i => by simp only [M1, M2, LinearMap.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', LinearMap.restrictScalars_apply, Algebra.linearMap_apply, hφb, ← hbF, ψ, Module.Basis.constr_basis]) y
  have hnd := traceForm_nondegenerate K F
  let z : F := ((Algebra.traceForm K F).toDual hnd).symm ψ
  have hz : ∀ w : F, Algebra.traceForm K F z w = ψ w := fun w => by
    rw [← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  have hzd : z ∈ Submodule.traceDual R K (1 : Submodule S F) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
    rw [hz, hψ]
    refine ⟨_, rfl⟩
  have hs' : algebraMap S F s * z ∈ (1 : Submodule S F) := by
    rw [Submodule.mem_comap, Algebra.linearMap_apply, Submodule.mem_div_iff_forall_mul_mem] at hs
    apply hs z hzd
  obtain ⟨x, hx⟩ := Submodule.mem_one.mp hs'
  have key : ∀ y : S, φ (s * y) = Algebra.trace R S (x * y) := by
    intro y
    apply hinjK
    rw [← hψ, ← Algebra.trace_localization R R⁰ (Rₘ := K) (Sₘ := F), RingHom.map_mul (algebraMap S F),
      RingHom.map_mul (algebraMap S F), hx, ← hz, Algebra.traceForm_apply]
    congr 1
    ring
  refine ⟨Ideal.Quotient.mk _ x, fun yb => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  rw [← map_mul, ← hφ, key, ← map_mul, trace_quot_mk]


-- created on 2026-10-13
