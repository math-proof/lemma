import Mathlib
import sympy.Basic
import Class.v1.Atlas.FourierAnalysis.code.OrthonormalBases
open Filter Topology Submodule OrthonormalBases HilbertSpace
open scoped InnerProductSpace ComplexConjugate


/--
[IsOrthonormalSequence.norm_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean)
-/
@[path]
private lemma IsOrthonormalSequence.norm_eq_one
  [RCLike 𝕜]
  [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  {φ : ℕ → E}
  {n : ℕ}
-- given
  (h : IsOrthonormalSequence 𝕜 φ) :
-- imply
  ‖φ n‖ = 1 :=
-- proof
  h.1 n

/--
[IsOrthonormalSequence.inner_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean)
-/
@[path]
private lemma IsOrthonormalSequence.inner_eq_zero
  [RCLike 𝕜]
  [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  {φ : ℕ → E}
  {n m : ℕ}
-- given
  (h : IsOrthonormalSequence 𝕜 φ)
  (hne : n ≠ m) :
-- imply
  ⟪φ n, φ m⟫_𝕜 = 0 :=
-- proof
  h.2 hne

/--
[inner_tendsto_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean)
-/
@[path]
private lemma inner_tendsto_of_tendsto
  [RCLike 𝕜]
  [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  {l : Filter α}
  {u v : α → E}
  {a b : E}
-- given
  (hu : Tendsto u l (𝓝 a))
  (hv : Tendsto v l (𝓝 b)) :
-- imply
  Tendsto (fun n => ⟪u n, v n⟫_𝕜) l (𝓝 ⟪a, b⟫_𝕜) :=
-- proof
  hu.inner hv

/--
[hasSum_inner_smul_of_dense_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean)
-/
@[path]
private lemma hasSum_inner_smul_of_dense_span
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {φ : ℕ → E}
  {f : E}
-- given
  (hφ : Orthonormal 𝕜 φ)
  (ha : (span 𝕜 (Set.range φ)).topologicalClosure = ⊤) :
-- imply
  HasSum (fun n => @inner 𝕜 _ _ (φ n) f • φ n) f := by
-- proof
  let b := HilbertBasis.mk hφ ha.ge
  have hb : (b : ℕ → E) = φ := HilbertBasis.coe_mk hφ ha.ge
  have := b.hasSum_repr f
  simp only [b.repr_apply_apply] at this
  rwa [hb] at this

/--
[parseval_of_dense_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean)
-/
@[path]
private lemma parseval_of_dense_span
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {φ : ℕ → E}
  {f : E}
-- given
  (hφ : Orthonormal 𝕜 φ)
  (ha : (span 𝕜 (Set.range φ)).topologicalClosure = ⊤) :
-- imply
  HasSum (fun n => ‖@inner 𝕜 _ _ (φ n) f‖ ^ 2) (‖f‖ ^ 2) := by
-- proof
  let b := HilbertBasis.mk hφ ha.ge
  have hb : (b : ℕ → E) = φ := HilbertBasis.coe_mk hφ ha.ge
  have h1 := b.hasSum_inner_mul_inner f f
  have h2 := (RCLike.reCLM (K := 𝕜)).hasSum h1
  simp only [RCLike.reCLM_apply] at h2
  simp_rw [show ∀ n, RCLike.re (@inner 𝕜 _ _ f (b n) * @inner 𝕜 _ _ (b n) f) =
    ‖@inner 𝕜 _ _ (b n) f‖ ^ 2 from fun n => by
    rw [inner_mul_symm_re_eq_norm, norm_mul, sq]
    congr 1
    rw [← RCLike.norm_conj (@inner 𝕜 _ _ f (b n))]
    congr 1
    exact inner_conj_symm (𝕜 := 𝕜) (b n) f, hb] at h2
  rwa [inner_self_eq_norm_sq (𝕜 := 𝕜)] at h2

/--
[dense_span_of_hasSum_inner_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean)
-/
@[path]
private lemma dense_span_of_hasSum_inner_smul
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {φ : ℕ → E}
-- given
  (hc : ∀ f : E, HasSum (fun n => @inner 𝕜 _ _ (φ n) f • φ n) f) :
-- imply
  (span 𝕜 (Set.range φ)).topologicalClosure = ⊤ := by
-- proof
  rw [eq_top_iff]
  intro f _
  apply mem_closure_of_tendsto (hc f)
  apply Filter.Eventually.of_forall
  intro s
  apply sum_mem
  intro n _
  apply smul_mem
  exact subset_span ⟨n, rfl⟩

/--
[dense_span_of_parseval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean)
-/
@[path]
private lemma dense_span_of_parseval
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {φ : ℕ → E}
-- given
  (hb : ∀ f : E, HasSum (fun n => ‖@inner 𝕜 _ _ (φ n) f‖ ^ 2) (‖f‖ ^ 2)) :
-- imply
  (span 𝕜 (Set.range φ)).topologicalClosure = ⊤ := by
-- proof
  rw [← orthogonal_orthogonal_eq_closure, orthogonal_eq_top_iff, eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  have h_inner_zero : ∀ n, @inner 𝕜 _ _ (φ n) f = 0 := fun n =>
    hf (φ n) (subset_span ⟨n, rfl⟩)
  have h_parseval := hb f
  simp only [h_inner_zero, norm_zero, sq, mul_zero] at h_parseval
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg f, h_parseval.unique hasSum_zero])

/--
[inner_hasSum_of_orthonormal_series](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean)
-/
@[path]
private lemma inner_hasSum_of_orthonormal_series
  [RCLike 𝕜]
  [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  {φ : ℕ → E}
  {a b : ℕ → 𝕜}
  {u v : E}
-- given
  (hφ : Orthonormal 𝕜 φ)
  (hu : HasSum (fun n => a n • φ n) u)
  (hv : HasSum (fun n => b n • φ n) v) :
-- imply
  HasSum (fun n => @starRingEnd 𝕜 _ (@RCLike.toStarRing 𝕜 _) (a n) * b n) (⟪u, v⟫_𝕜) := by
-- proof
  apply (hu.inner hv).congr
  intro s
  apply hφ.inner_sum a b s


-- created on 2026-10-23
-- updated on 2026-10-24
