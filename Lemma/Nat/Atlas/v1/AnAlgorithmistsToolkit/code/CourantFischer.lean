import Mathlib
import sympy.Basic
open Matrix Finset BigOperators


namespace CourantFischer

/--
[eucl_inner_eq_dotProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma eucl_inner_eq_dotProduct
  [Fintype V]
  {a b : EuclideanSpace ℝ V} :
-- imply
  @inner ℝ _ _ a b = dotProduct a.ofLp b.ofLp := by
-- proof
  have h := EuclideanSpace.inner_eq_star_dotProduct a b
  rw [star_trivial] at h
  rw [dotProduct_comm a.ofLp b.ofLp]; exact h

end CourantFischer

namespace CourantFischer

/--
[rayleigh_spectral_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma rayleigh_spectral_expansion
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  {x : Fin m → ℝ}
-- given
  (hA : A.IsHermitian) :
-- imply
  dotProduct x (A.mulVec x) = ∑ i : Fin m, hA.eigenvalues i * (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 := by
-- proof
  have htrans : Aᵀ = A := by
    ext i j
    have := congr_fun (congr_fun hA i) j
    simp [conjTranspose, star] at this
    exact this
  have key : dotProduct x (A.mulVec x) =
    ∑ i, dotProduct x (⇑(hA.eigenvectorBasis i)) *
      dotProduct (⇑(hA.eigenvectorBasis i)) (A.mulVec x) := by
    have h := hA.eigenvectorBasis.sum_inner_mul_inner
      (WithLp.toLp (p := 2) x) (WithLp.toLp (p := 2) (A.mulVec x))
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
    simpa [dotProduct_comm] using h.symm
  rw [key]
  congr 1
  ext i
  have hmul : dotProduct (⇑(hA.eigenvectorBasis i)) (A.mulVec x) =
    hA.eigenvalues i * dotProduct (⇑(hA.eigenvectorBasis i)) x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, htrans, hA.mulVec_eigenvectorBasis i]
    simp only [smul_dotProduct, smul_eq_mul]
  rw [hmul, dotProduct_comm x]
  ring

end CourantFischer

namespace CourantFischer

/--
[parseval_eigenvectors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma parseval_eigenvectors
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  {x : Fin m → ℝ}
-- given
  (hA : A.IsHermitian) :
-- imply
  ∑ i : Fin m, (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 = dotProduct x x := by
-- proof
  let b := hA.eigenvectorBasis
  let x' : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x
  have parseval := OrthonormalBasis.sum_sq_norm_inner_right b x'
  have h_inner : ∀ i : Fin m, @inner ℝ _ _ (b i) x' = (b i).ofLp ⬝ᵥ x := by
    intro i
    show x ⬝ᵥ star (b i).ofLp = (b i).ofLp ⬝ᵥ x
    simp [star_trivial, dotProduct_comm]
  have h_norm_sq : ∀ i : Fin m, ‖@inner ℝ _ _ (b i) x'‖ ^ 2 = ((b i).ofLp ⬝ᵥ x) ^ 2 := by
    intro i
    rw [h_inner i, Real.norm_eq_abs, sq_abs]
  have h_norm_x : ‖x'‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Fintype.sum_nonneg (fun j => ?_))]
    · simp only [dotProduct]
      congr 1
      ext j
      show ‖x j‖ ^ 2 = x j * x j
      rw [Real.norm_eq_abs, sq_abs, sq]
    · positivity
  rw [h_norm_x] at parseval
  convert parseval using 1
  congr 1
  ext i
  exact (h_norm_sq i).symm
omit [NeZero m] in
section LaplacianRayleigh

end CourantFischer

namespace CourantFischer

/--
[rayleigh_spectral_expansion_V](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma rayleigh_spectral_expansion_V
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  {L : Matrix V V ℝ}
  {x : V → ℝ}
-- given
  (hA : A.IsHermitian)
  (hL : L.IsHermitian) :
-- imply
  dotProduct x (L.mulVec x) = ∑ i : V, hL.eigenvalues i * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
-- proof
  set b := hL.eigenvectorBasis
  set x' : EuclideanSpace ℝ V := WithLp.toLp (p := 2) x
  set Lx' : EuclideanSpace ℝ V := WithLp.toLp (p := 2) (L *ᵥ x)
  have hlhs : dotProduct x (L *ᵥ x) = @inner ℝ _ _ x' Lx' := by
    rw [eucl_inner_eq_dotProduct]
  have hrhs_term : ∀ i : V, dotProduct (⇑(b i)) x = @inner ℝ _ _ (b i) x' := by
    intro i; rw [eucl_inner_eq_dotProduct]
  rw [hlhs]
  simp_rw [hrhs_term]
  rw [show @inner ℝ _ _ x' Lx' = ∑ i, @inner ℝ _ _ x' (b i) * @inner ℝ _ _ (b i) Lx' from
    (b.sum_inner_mul_inner x' Lx').symm]
  congr 1; ext i
  have h_eigval : @inner ℝ _ _ (b i) Lx' = hL.eigenvalues i * @inner ℝ _ _ (b i) x' := by
    rw [eucl_inner_eq_dotProduct, eucl_inner_eq_dotProduct]
    rw [dotProduct_mulVec]
    have hvecmul : (b i).ofLp ᵥ* L = hL.eigenvalues i • (b i).ofLp := by
      conv_lhs => rw [show L = Lᴴ from hL.symm]
      rw [vecMul_conjTranspose, star_trivial, star_trivial]
      exact hL.mulVec_eigenvectorBasis i
    rw [hvecmul, smul_dotProduct, smul_eq_mul]
  rw [h_eigval, real_inner_comm x' (b i), sq]
  ring

end CourantFischer

namespace CourantFischer

/--
[parseval_eigenvectors_V](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma parseval_eigenvectors_V
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  {L : Matrix V V ℝ}
  {x : V → ℝ}
-- given
  (hA : A.IsHermitian)
  (hL : L.IsHermitian) :
-- imply
  ∑ i : V, (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 = dotProduct x x := by
-- proof
  set b := hL.eigenvectorBasis
  set x' : EuclideanSpace ℝ V := WithLp.toLp (p := 2) x
  have hrhs : dotProduct x x = @inner ℝ _ _ x' x' := by rw [eucl_inner_eq_dotProduct]
  have hlhs_term : ∀ i : V, dotProduct (⇑(b i)) x = @inner ℝ _ _ (b i) x' := by
    intro i; rw [eucl_inner_eq_dotProduct]
  rw [hrhs]
  simp_rw [hlhs_term]
  trans (∑ i : V, @inner ℝ _ _ x' (b i) * @inner ℝ _ _ (b i) x')
  · apply Finset.sum_congr rfl
    intro i _
    rw [sq, ← real_inner_comm x' (b i)]
  · exact b.sum_inner_mul_inner x' x'

end CourantFischer

namespace CourantFischer

/--
[eigenvalue_eq_rayleigh_eigenvector_V](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma eigenvalue_eq_rayleigh_eigenvector_V
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  {L : Matrix V V ℝ}
  {k : V}
-- given
  (hA : A.IsHermitian)
  (hL : L.IsHermitian) :
-- imply
  dotProduct (⇑(hL.eigenvectorBasis k)) (L.mulVec (⇑(hL.eigenvectorBasis k))) = hL.eigenvalues k := by
-- proof
  rw [hL.mulVec_eigenvectorBasis k]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  have hkey : ∀ x : V,
    (hL.eigenvectorBasis k).ofLp x * (hL.eigenvalues k * (hL.eigenvectorBasis k).ofLp x) =
    hL.eigenvalues k * ((hL.eigenvectorBasis k).ofLp x) ^ 2 := by
    intro x; ring
  simp_rw [hkey, ← Finset.mul_sum]
  have hnorm : ‖hL.eigenvectorBasis k‖ = 1 := hL.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq] at hnorm
  have hsum : ∑ x : V, ((hL.eigenvectorBasis k).ofLp x) ^ 2 = 1 := by
    have h1 := Real.sqrt_eq_one.mp hnorm
    convert h1 using 1
    congr 1
    simp [Real.norm_eq_abs, sq_abs]
  rw [hsum, mul_one]

end CourantFischer

namespace CourantFischer

/--
[eigenvector_dotProduct_one_V](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma eigenvector_dotProduct_one_V
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  {L : Matrix V V ℝ}
  {k : V}
-- given
  (hA : A.IsHermitian)
  (hL : L.IsHermitian) :
-- imply
  dotProduct (⇑(hL.eigenvectorBasis k)) (⇑(hL.eigenvectorBasis k)) = 1 := by
-- proof
  have hn : ‖hL.eigenvectorBasis k‖ = 1 := hL.eigenvectorBasis.orthonormal.1 k
  have h1 : ‖hL.eigenvectorBasis k‖ ^ 2 = 1 := by rw [hn, one_pow]
  rw [EuclideanSpace.norm_eq] at h1
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => by positivity))] at h1
  simp only [dotProduct]
  convert h1 using 1
  congr 1
  ext j
  rw [Real.norm_eq_abs, sq_abs, sq]

end CourantFischer

namespace CourantFischer

/--
[rayleighQuotient_orthogonal_isLeast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma rayleighQuotient_orthogonal_isLeast
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  {L : Matrix V V ℝ}
  {k : V}
-- given
  (hA : A.IsHermitian)
  (hL : L.IsHermitian) :
-- imply
  IsLeast {r | ∃ x : V → ℝ, x ≠ 0 ∧ (∀ j : V, hL.eigenvalues j < hL.eigenvalues k → dotProduct (⇑(hL.eigenvectorBasis j)) x = 0) ∧ dotProduct x (L.mulVec x) / dotProduct x x = r} (hL.eigenvalues k) := by
-- proof
  constructor
  ·
    refine ⟨⇑(hL.eigenvectorBasis k), ?_, ?_, ?_⟩
    ·
      intro h
      have hn := hL.eigenvectorBasis.orthonormal.1 k
      simp only [EuclideanSpace.norm_eq] at hn
      have : (∑ i, ‖(hL.eigenvectorBasis k).ofLp i‖ ^ 2) = 0 :=
        Finset.sum_eq_zero (fun j _ => by simp [congr_fun h j])
      rw [this, Real.sqrt_zero] at hn
      exact zero_ne_one hn
    ·
      intro j hj
      have hjk : j ≠ k := ne_of_apply_ne hL.eigenvalues (ne_of_lt hj)
      have h := orthonormal_iff_ite.mp hL.eigenvectorBasis.orthonormal j k
      simp only [hjk, ite_false] at h
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
      simp only [dotProduct]
      convert h using 1
      congr 1; ext i; ring
    ·
      rw [eigenvector_dotProduct_one_V hL k, div_one]
      exact eigenvalue_eq_rayleigh_eigenvector_V hL k
  ·
    intro r ⟨x, hx, horth, hxr⟩
    rw [← hxr]
    have hpos : (0 : ℝ) < dotProduct x x := by
      have : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
      obtain ⟨i, hi⟩ := this
      calc (0 : ℝ) < x i * x i := mul_self_pos.mpr hi
        _ ≤ ∑ j : V, x j * x j := Finset.single_le_sum
          (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (a := x j)) (Finset.mem_univ i)
        _ = dotProduct x x := by simp [dotProduct]
    rw [le_div_iff₀ hpos]
    rw [rayleigh_spectral_expansion_V hL x]
    calc hL.eigenvalues k * dotProduct x x
      = hL.eigenvalues k * ∑ i, (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
        rw [parseval_eigenvectors_V hL x]
      _ = ∑ i, hL.eigenvalues k * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i, hL.eigenvalues i * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : hL.eigenvalues i < hL.eigenvalues k
        · simp [horth i hi]
        · push Not at hi
          exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)

end CourantFischer

namespace CourantFischer

/--
[laplacian_quadratic_form_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma laplacian_quadratic_form_eq
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V → ℝ}
-- given
  (hA : A.IsHermitian) :
-- imply
  dotProduct x ((G.lapMatrix ℝ).mulVec x) = (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
-- proof
  have h := lapMatrix_toLinearMap₂' ℝ G x
  rwa [toLinearMap₂'_apply'] at h

end CourantFischer

namespace CourantFischer

/--
[laplacian_edge_sum_min_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma laplacian_edge_sum_min_characterization
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (hA : A.IsHermitian)
  (hL : (G.lapMatrix ℝ).IsHermitian) :
-- imply
  IsLeast {r | ∃ x : V → ℝ, x ≠ 0 ∧ (∀ j : V, hL.eigenvalues j < hL.eigenvalues k → dotProduct (⇑(hL.eigenvectorBasis j)) x = 0) ∧ (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 / dotProduct x x = r} (hL.eigenvalues k) := by
-- proof
  constructor
  ·
    refine ⟨⇑(hL.eigenvectorBasis k), ?_, ?_, ?_⟩
    ·
      intro h
      have hn := hL.eigenvectorBasis.orthonormal.1 k
      simp only [EuclideanSpace.norm_eq] at hn
      have : (∑ i, ‖(hL.eigenvectorBasis k).ofLp i‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [show (hL.eigenvectorBasis k).ofLp j = 0 from congr_fun h j]
      rw [this, Real.sqrt_zero] at hn
      exact zero_ne_one hn
    ·
      intro j hj
      have hjk : j ≠ k := by intro heq; rw [heq] at hj; exact lt_irrefl _ hj
      have h := orthonormal_iff_ite.mp hL.eigenvectorBasis.orthonormal j k
      simp only [hjk, ite_false] at h
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
      simp only [dotProduct]
      convert h using 1
      congr 1; ext i; ring
    ·
      rw [eigenvector_dotProduct_one_V hL k, div_one]
      rw [← laplacian_quadratic_form_eq]
      exact eigenvalue_eq_rayleigh_eigenvector_V hL k
  ·
    intro r ⟨x, hx, horth, hxr⟩
    rw [← hxr]
    have hpos : (0 : ℝ) < dotProduct x x := by
      have : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
      obtain ⟨i, hi⟩ := this
      calc (0 : ℝ) < x i * x i := mul_self_pos.mpr hi
        _ ≤ ∑ j : V, x j * x j := Finset.single_le_sum
          (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (a := x j)) (Finset.mem_univ i)
        _ = dotProduct x x := by simp [dotProduct]
    rw [← laplacian_quadratic_form_eq]
    rw [le_div_iff₀ hpos]
    rw [rayleigh_spectral_expansion_V hL x]
    calc hL.eigenvalues k * dotProduct x x
      = hL.eigenvalues k * ∑ i, (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
        rw [parseval_eigenvectors_V hL x]
      _ = ∑ i, hL.eigenvalues k * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i, hL.eigenvalues i * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : hL.eigenvalues i < hL.eigenvalues k
        · simp [horth i hi]
        · push Not at hi
          exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)

end CourantFischer

namespace CourantFischer

/--
[laplacian_edge_sum_max_quotient_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma laplacian_edge_sum_max_quotient_characterization
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i₀ : V}
-- given
  (hA : A.IsHermitian)
  (hL : (G.lapMatrix ℝ).IsHermitian)
  (hi₀ : ∀ j : V, hL.eigenvalues j ≤ hL.eigenvalues i₀) :
-- imply
  IsGreatest {r | ∃ x : V → ℝ, x ≠ 0 ∧ (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 / dotProduct x x = r} (hL.eigenvalues i₀) := by
-- proof
  constructor
  ·
    refine ⟨⇑(hL.eigenvectorBasis i₀), ?_, ?_⟩
    ·
      intro h
      have hn := hL.eigenvectorBasis.orthonormal.1 i₀
      simp only [EuclideanSpace.norm_eq] at hn
      have : (∑ i, ‖(hL.eigenvectorBasis i₀).ofLp i‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [show (hL.eigenvectorBasis i₀).ofLp j = 0 from congr_fun h j]
      rw [this, Real.sqrt_zero] at hn
      exact zero_ne_one hn
    ·
      rw [eigenvector_dotProduct_one_V hL i₀, div_one]
      rw [← laplacian_quadratic_form_eq]
      exact eigenvalue_eq_rayleigh_eigenvector_V hL i₀
  ·
    intro r ⟨x, hx, hxr⟩
    rw [← hxr]
    have hpos : (0 : ℝ) < dotProduct x x := by
      have : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
      obtain ⟨i, hi⟩ := this
      calc (0 : ℝ) < x i * x i := mul_self_pos.mpr hi
        _ ≤ ∑ j : V, x j * x j := Finset.single_le_sum
          (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (a := x j)) (Finset.mem_univ i)
        _ = dotProduct x x := by simp [dotProduct]
    rw [← laplacian_quadratic_form_eq]
    rw [div_le_iff₀ hpos]
    rw [rayleigh_spectral_expansion_V hL x]
    calc ∑ i, hL.eigenvalues i * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2
      ≤ ∑ i, hL.eigenvalues i₀ * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hi₀ i) (sq_nonneg _)
      _ = hL.eigenvalues i₀ * ∑ i, (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
        rw [Finset.mul_sum]
      _ = hL.eigenvalues i₀ * dotProduct x x := by
        rw [parseval_eigenvectors_V hL x]

end CourantFischer

namespace CourantFischer

/--
[ones_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma ones_ne_zero
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hA : A.IsHermitian) :
-- imply
  (fun _ : V => (1 : ℝ)) ≠ 0 := by
-- proof
  intro h
  have := congr_fun h (Classical.arbitrary V)
  simp at this

end CourantFischer

namespace CourantFischer

/--
[laplacian_quadform_ones_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma laplacian_quadform_ones_eq_zero
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hA : A.IsHermitian) :
-- imply
  dotProduct (fun _ : V => (1 : ℝ)) ((G.lapMatrix ℝ).mulVec (fun _ => 1)) = 0 := by
-- proof
  rw [lapMatrix_mulVec_const_eq_zero]
  simp [dotProduct]

end CourantFischer

namespace CourantFischer

/--
[laplacian_rayleigh_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma laplacian_rayleigh_nonneg
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V → ℝ}
-- given
  (hA : A.IsHermitian)
  (hx : x ≠ 0) :
-- imply
  0 ≤ dotProduct x ((G.lapMatrix ℝ).mulVec x) / dotProduct x x := by
-- proof
  apply div_nonneg
  · have h := lapMatrix_toLinearMap₂' ℝ G x
    rw [toLinearMap₂'_apply'] at h
    rw [h]
    apply div_nonneg
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    · norm_num
  · have : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
    obtain ⟨i, hi⟩ := this
    apply le_of_lt
    calc (0 : ℝ) < x i * x i := mul_self_pos.mpr hi
      _ ≤ ∑ j : V, x j * x j := Finset.single_le_sum
        (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (a := x j)) (Finset.mem_univ i)
      _ = dotProduct x x := by simp [dotProduct]

end CourantFischer

namespace CourantFischer

/--
[laplacian_rayleigh_ones_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma laplacian_rayleigh_ones_eq_zero
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hA : A.IsHermitian) :
-- imply
  dotProduct (fun _ : V => (1 : ℝ)) ((G.lapMatrix ℝ).mulVec (fun _ => 1)) / dotProduct (fun _ : V => (1 : ℝ)) (fun _ : V => (1 : ℝ)) = 0 := by
-- proof
  rw [laplacian_quadform_ones_eq_zero]
  simp

end CourantFischer

namespace CourantFischer

/--
[laplacian_rayleighQuotient_min_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma laplacian_rayleighQuotient_min_eq_zero
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hA : A.IsHermitian) :
-- imply
  IsLeast {r | ∃ x : V → ℝ, x ≠ 0 ∧ dotProduct x ((G.lapMatrix ℝ).mulVec x) / dotProduct x x = r} 0 := by
-- proof
  constructor
  ·
    exact ⟨fun _ => 1, ones_ne_zero, laplacian_rayleigh_ones_eq_zero G⟩
  ·
    intro r ⟨x, hx, hxr⟩
    rw [← hxr]
    exact laplacian_rayleigh_nonneg G x hx

end CourantFischer

namespace CourantFischer

/--
[corollary24_rayleighQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CourantFischer.lean)
-/
@[path]
lemma corollary24_rayleighQuotient
  {m : ℕ}
  [NeZero m]
  {A : Matrix (Fin m) (Fin m) ℝ}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
  {i₀ : V}
-- given
  (hA : A.IsHermitian)
  (hL : (G.lapMatrix ℝ).IsHermitian)
  (hk : ∀ x : V → ℝ, (∀ j : V, hL.eigenvalues j < hL.eigenvalues k → dotProduct (⇑(hL.eigenvectorBasis j)) x = 0) ↔ (∑ i, x i = 0))
  (hi₀ : ∀ j : V, hL.eigenvalues j ≤ hL.eigenvalues i₀) :
-- imply
  IsLeast {r | ∃ x : V → ℝ, x ≠ 0 ∧ dotProduct x ((G.lapMatrix ℝ).mulVec x) / dotProduct x x = r} 0 ∧ IsLeast {r | ∃ x : V → ℝ, x ≠ 0 ∧ (∑ i, x i = 0) ∧ (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 / dotProduct x x = r} (hL.eigenvalues k) ∧ IsGreatest {r | ∃ x : V → ℝ, x ≠ 0 ∧ (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 / dotProduct x x = r} (hL.eigenvalues i₀) := by
-- proof
  refine ⟨laplacian_rayleighQuotient_min_eq_zero G, ?_, laplacian_edge_sum_max_quotient_characterization G hL i₀ hi₀⟩
  have h := laplacian_edge_sum_min_characterization G hL k
  have hset : {r | ∃ x : V → ℝ, x ≠ 0 ∧
    (∀ j : V, hL.eigenvalues j < hL.eigenvalues k →
      dotProduct (⇑(hL.eigenvectorBasis j)) x = 0) ∧
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 /
      dotProduct x x = r} =
    {r | ∃ x : V → ℝ, x ≠ 0 ∧
      (∑ i, x i = 0) ∧
      (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 /
        dotProduct x x = r} := by
    ext r
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hne, horth, hval⟩
      exact ⟨x, hne, (hk x).mp horth, hval⟩
    · rintro ⟨x, hne, hsum, hval⟩
      exact ⟨x, hne, (hk x).mpr hsum, hval⟩
  rwa [← hset]

end CourantFischer


-- created on 2026-10-23
