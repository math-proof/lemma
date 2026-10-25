/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Def.Analysis.NormedSpace.LocalReflexivity.Part5


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- Application formula for `plr_T'`. -/
theorem plr_T'_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E) (u : ↥Mp) :
    plr_T' Mp C hC y u = plr_S0 Mp (plr_pi0 Mp C hC u)
      + ∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j • y j :=
  rfl

/-- Values of `T'` at the net points, with two-sided norm bounds. -/
theorem plr_T'_net {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E)
    {ι : Type*}
    (a : ι → E) (c : ι → Fin (Module.finrank 𝕜 ↥C) → 𝕜)
    (g : ι → StrongDual 𝕜 E) (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (mk : ι → ↥Mp)
    (ha : ∀ k, a k = plr_S0 Mp (plr_pi0 Mp C hC (mk k)))
    (hc : ∀ k j, c k j
      = (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC (mk k)) j)
    (hg : ∀ k, ‖g k‖ ≤ 1)
    {δ : ℝ}
    (hgnorm : ∀ k, 1 - δ ≤ RCLike.re (m k (g k)))
    (hN6g : ∀ k, g k (a k + ∑ j, c k j • y j) = m k (g k))
    (hN6n : ∀ k, ‖a k + ∑ j, c k j • y j‖ < 1 + δ) :
    ∀ k, 1 - δ ≤ ‖plr_T' Mp C hC y (mk k)‖
      ∧ ‖plr_T' Mp C hC y (mk k)‖ ≤ 1 + δ := by
  intro k
  have hTeq : plr_T' Mp C hC y (mk k) = a k + ∑ j, c k j • y j := by
    rw [plr_T'_apply, ← ha k]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [hc k j])
  refine ⟨?_, ?_⟩
  · calc 1 - δ ≤ RCLike.re (m k (g k)) := hgnorm k
      _ = RCLike.re (g k (plr_T' Mp C hC y (mk k))) := by
        rw [hTeq, hN6g k]
      _ ≤ ‖g k (plr_T' Mp C hC y (mk k))‖ := RCLike.re_le_norm _
      _ ≤ ‖plr_T' Mp C hC y (mk k)‖ := by
        calc ‖g k (plr_T' Mp C hC y (mk k))‖
            ≤ ‖g k‖ * ‖plr_T' Mp C hC y (mk k)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖plr_T' Mp C hC y (mk k)‖ :=
            mul_le_mul_of_nonneg_right (hg k) (norm_nonneg _)
          _ = ‖plr_T' Mp C hC y (mk k)‖ := one_mul _
  · rw [hTeq]
    exact le_of_lt (hN6n k)

set_option maxHeartbeats 800000 in
-- The two finite-basis expansions exceed the default elaboration heartbeat limit.
/-- `T'` preserves all dual pairings. -/
theorem plr_T'_pair {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E)
    {q : ℕ} (f : Fin q → StrongDual 𝕜 E)
    (b : Fin (Module.finrank 𝕜 ↥C) → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hfy : ∀ i j, f i (y j) = b j (f i))
    (hb : ∀ j, Mp.subtype (C.subtype ((Module.finBasis 𝕜 ↥C) j)) = b j)
    (u : ↥Mp) (i : Fin q) :
    f i (plr_T' Mp C hC y u) = (Mp.subtype u) (f i) := by
  have e1 : (Mp.subtype u) (f i)
      = f i (plr_S0 Mp (plr_pi0 Mp C hC u))
        + ∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j
          * b j (f i) := by
    have h := congrArg (· (f i)) (plr_decomp Mp C hC u)
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul,
      NormedSpace.dual_def] at h
    have h2 : (∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j
          * (Mp.subtype (C.subtype ((Module.finBasis 𝕜 ↥C) j))) (f i))
        = (∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j
          * b j (f i)) :=
      Finset.sum_congr rfl (fun j _ => by rw [hb j])
    rw [h2] at h
    exact h
  have e2 : f i (plr_T' Mp C hC y u)
      = f i (plr_S0 Mp (plr_pi0 Mp C hC u))
        + ∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j
          * b j (f i) := by
    rw [plr_T'_apply, map_add, map_sum]
    congr 1
    exact Finset.sum_congr rfl
      (fun j _ => by rw [map_smul, smul_eq_mul, hfy i j])
  exact e2.trans e1.symm

/-- `T'` fixes the `J(E)` part. -/
theorem plr_T'_fix {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E)
    (u : ↥Mp) (x : E)
    (hx : Mp.subtype u
      = NormedSpace.inclusionInDoubleDual 𝕜 E x) :
    plr_T' Mp C hC y u = x := by
  have hmem : u ∈ plr_M0 Mp := ⟨x, hx.symm⟩
  have hpi0 : plr_pi0 Mp C hC u = ⟨u, hmem⟩ :=
    plr_pi0_mem Mp C hC ⟨u, hmem⟩
  have hpi1 : plr_pi1 Mp C hC u = 0 :=
    plr_pi1_mem Mp C hC ⟨u, hmem⟩
  have hSx : plr_S0 Mp ⟨u, hmem⟩ = x := by
    apply plr_J_inj (𝕜 := 𝕜)
    change (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap
        (plr_S0 Mp ⟨u, hmem⟩)
      = (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap x
    rw [plr_S0_mem]
    exact hx
  rw [plr_T'_apply, hpi0, hpi1, hSx]
  simp only [map_zero, Finsupp.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

/-- The choice `δ = ε / (8 + 4ε)` has the numerical bounds needed by N8. -/
theorem plr_delta_estimates (ε : ℝ) (hε : 0 < ε) :
    let δ := ε / (8 + 4 * ε)
    0 < δ ∧ δ < 1
      ∧ (1 + δ) / (1 - δ) ≤ 1 + ε
      ∧ (1 + ε)⁻¹ ≤ (1 - 3 * δ) / (1 - δ) := by
  let δ := ε / (8 + 4 * ε)
  have hden : 0 < 8 + 4 * ε := by linarith
  have hδ0 : 0 < δ := div_pos hε hden
  have hδeq : δ * (8 + 4 * ε) = ε := by
    rw [show δ = ε / (8 + 4 * ε) from rfl, div_mul_cancel₀]
    exact ne_of_gt hden
  have hδ1 : δ < 1 := by
    rw [show δ = ε / (8 + 4 * ε) from rfl, div_lt_one hden]
    linarith
  have hsub : 0 < 1 - δ := by linarith
  have hup : (1 + δ) / (1 - δ) ≤ 1 + ε := by
    rw [div_le_iff₀ hsub]
    nlinarith
  have he : 0 < 1 + ε := by linarith
  have hlow : (1 + ε)⁻¹ ≤ (1 - 3 * δ) / (1 - δ) := by
    rw [le_div_iff₀ hsub, inv_mul_eq_div, div_le_iff₀ he]
    nlinarith
  exact ⟨hδ0, hδ1, hup, hlow⟩

/-- The net-point estimates imply the required global norm bounds. -/
theorem plr_norm_bounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : V →L[𝕜] E) {n : ℕ} (mk : Fin n → V) (ε : ℝ) (hε : 0 < ε)
    (hcover : ∀ u : V, ‖u‖ = 1 →
      ∃ k, ‖u - mk k‖ < ε / (8 + 4 * ε))
    (hnet : ∀ k,
      1 - ε / (8 + 4 * ε) ≤ ‖T (mk k)‖
        ∧ ‖T (mk k)‖ ≤ 1 + ε / (8 + 4 * ε)) :
    ∀ u : V,
      (1 + ε)⁻¹ * ‖u‖ ≤ ‖T u‖ ∧ ‖T u‖ ≤ (1 + ε) * ‖u‖ := by
  classical
  let δ := ε / (8 + 4 * ε)
  obtain ⟨hδ0, hδ1, hupRatio, hlowRatio⟩ := plr_delta_estimates ε hε
  let t : Finset V := Finset.univ.image mk
  have hcover' : ∀ u : V, ‖u‖ = 1 → ∃ k ∈ t, ‖u - k‖ < δ := by
    intro u hu
    obtain ⟨k, hk⟩ := hcover u hu
    refine ⟨mk k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, ?_⟩
    simpa [δ] using hk
  have hup : ∀ k ∈ t, ‖T k‖ ≤ 1 + δ := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    simpa [δ] using (hnet i).2
  have hlow : ∀ k ∈ t, 1 - δ ≤ ‖T k‖ := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    simpa [δ] using (hnet i).1
  have hTop : ‖T‖ ≤ (1 + δ) / (1 - δ) :=
    plr_opNorm_of_net T hδ0 hδ1 hcover' hup
  have hLow : ∀ u : V, ((1 - 3 * δ) / (1 - δ)) * ‖u‖ ≤ ‖T u‖ :=
    plr_lower_of_net T hδ0 hδ1 hcover' hlow hTop
  intro u
  constructor
  · exact (mul_le_mul_of_nonneg_right hlowRatio (norm_nonneg u)).trans (hLow u)
  · calc
      ‖T u‖ ≤ ‖T‖ * ‖u‖ := ContinuousLinearMap.le_opNorm T u
      _ ≤ ((1 + δ) / (1 - δ)) * ‖u‖ :=
        mul_le_mul_of_nonneg_right hTop (norm_nonneg u)
      _ ≤ (1 + ε) * ‖u‖ :=
        mul_le_mul_of_nonneg_right hupRatio (norm_nonneg u)

/-- Pairing equality on the canonical finite basis extends to the whole space. -/
theorem plr_pair_from_finBasis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    [FiniteDimensional 𝕜 N]
    (iN : N →L[𝕜] StrongDual 𝕜 E) (z : StrongDual 𝕜 (StrongDual 𝕜 E)) (x : E)
    (hpair : ∀ i, (iN ((Module.finBasis 𝕜 N) i)) x
      = z (iN ((Module.finBasis 𝕜 N) i))) :
    ∀ n : N, (iN n) x = z (iN n) := by
  intro n
  rw [show n = ∑ i, (Module.finBasis 𝕜 N).repr n i
      • (Module.finBasis 𝕜 N) i from (Module.finBasis 𝕜 N).sum_repr n |>.symm]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by rw [hpair i])

/-- Assembly of N1--N8 on the range of `iM`. -/
theorem plr_assemble
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    [FiniteDimensional 𝕜 M]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    [FiniteDimensional 𝕜 N]
    (iM : M →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (iN : N →L[𝕜] StrongDual 𝕜 E)
    (hM_inj : Function.Injective iM) (hN_inj : Function.Injective iN)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : M →L[𝕜] E),
      (∀ u : M, (1 + ε)⁻¹ * ‖iM u‖ ≤ ‖T u‖
        ∧ ‖T u‖ ≤ (1 + ε) * ‖iM u‖)
      ∧ (∀ (u : M) (n : N), (iN n) (T u) = (iM u) (iN n))
      ∧ (∀ (u : M) (x : E),
        iM u = NormedSpace.inclusionInDoubleDual 𝕜 E x → T u = x) := by
  let Mp := LinearMap.range iM.toLinearMap
  let _ : NormedAddCommGroup ↥Mp := plrNACG_Mp Mp
  let _ : NormedSpace 𝕜 ↥Mp := plrNS_Mp Mp
  let iMr : M →L[𝕜] ↥Mp := iM.rangeRestrict
  let iMEquiv : M ≃ₗ[𝕜] ↥Mp :=
    LinearEquiv.ofBijective iMr.toLinearMap ⟨(by
      intro u v huv
      apply hM_inj
      exact congrArg Subtype.val huv), (by
      intro u
      obtain ⟨v, hv⟩ := u.prop
      exact ⟨v, Subtype.ext hv⟩)⟩
  let _ : FiniteDimensional 𝕜 ↥Mp :=
    FiniteDimensional.of_surjective iMEquiv.toLinearMap iMEquiv.surjective
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (plr_M0 Mp)
  let _ : NormedAddCommGroup ↥C := plrNACG_C Mp C
  let b : Fin (Module.finrank 𝕜 ↥C) → StrongDual 𝕜 (StrongDual 𝕜 E) :=
    fun j => Mp.subtype (C.subtype ((Module.finBasis 𝕜 ↥C) j))
  let Np := LinearMap.range iN.toLinearMap
  let iNr : N →ₗ[𝕜] ↥Np := iN.toLinearMap.rangeRestrict
  let iNEquiv : N ≃ₗ[𝕜] ↥Np :=
    LinearEquiv.ofBijective iNr ⟨(by
      intro u v huv
      apply hN_inj
      exact congrArg Subtype.val huv), (by
      intro u
      obtain ⟨v, hv⟩ := u.prop
      exact ⟨v, Subtype.ext hv⟩)⟩
  let f : Fin (Module.finrank 𝕜 N) → StrongDual 𝕜 E :=
    fun i => Np.subtype (iNEquiv ((Module.finBasis 𝕜 N) i))
  let δ := ε / (8 + 4 * ε)
  have hδ0 : 0 < δ := by
    simpa [δ] using (plr_delta_estimates ε hε).1
  obtain ⟨card, mk, hmknorm, hcover⟩ := plr_net_exists Mp hδ0
  have hexg : ∀ k : Fin card, ∃ g : StrongDual 𝕜 E,
      ‖g‖ ≤ 1 ∧ 1 - δ ≤ RCLike.re ((Mp.subtype (mk k)) g) := by
    intro k
    apply plr_norming (Mp.subtype (mk k))
    · exact hmknorm k
    · exact hδ0
  choose g hg hgnorm using hexg
  let a : Fin card → E :=
    fun k => plr_S0 Mp (plr_pi0 Mp C hC (mk k))
  let c : Fin card → Fin (Module.finrank 𝕜 ↥C) → 𝕜 :=
    fun k j => (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC (mk k)) j
  let mBid : Fin card → StrongDual 𝕜 (StrongDual 𝕜 E) :=
    fun k => Mp.subtype (mk k)
  have hm : ∀ k (h : StrongDual 𝕜 E),
      mBid k h = h (a k) + ∑ j, c k j * b j h := by
    intro k h
    have hd := congrArg (fun z : StrongDual 𝕜 (StrongDual 𝕜 E) => z h)
      (plr_decomp Mp C hC (mk k))
    simpa only [mBid, a, c, b, add_apply, sum_apply, smul_apply, smul_eq_mul,
      NormedSpace.dual_def] using hd
  have hmnorm : ∀ k, ‖mBid k‖ = 1 := by
    intro k
    exact hmknorm k
  obtain ⟨y, hfy, hyg, hynorm⟩ := plr_solve
    (inferInstance : Fintype (Fin card)) a c f g b mBid hm hmnorm hδ0
  let Tp : ↥Mp →L[𝕜] E := plr_T' Mp C hC y
  have hnet : ∀ k, 1 - δ ≤ ‖Tp (mk k)‖ ∧ ‖Tp (mk k)‖ ≤ 1 + δ :=
    plr_T'_net Mp C hC y a c g mBid mk (fun _ => rfl) (fun _ _ => rfl)
      hg hgnorm hyg hynorm
  have hbounds : ∀ u : ↥Mp,
      (1 + ε)⁻¹ * ‖u‖ ≤ ‖Tp u‖ ∧ ‖Tp u‖ ≤ (1 + ε) * ‖u‖ := by
    apply plr_norm_bounds Tp mk ε hε
    · simpa [δ] using hcover
    · simpa [δ] using hnet
  let T : M →L[𝕜] E := Tp.comp iMr
  refine ⟨T, ?_, ?_, ?_⟩
  · intro u
    change (1 + ε)⁻¹ * ‖iMr u‖ ≤ ‖Tp (iMr u)‖
      ∧ ‖Tp (iMr u)‖ ≤ (1 + ε) * ‖iMr u‖
    exact hbounds (iMr u)
  · intro u n
    apply plr_pair_from_finBasis iN (iM u) (T u)
    intro i
    change f i (Tp (iMr u)) = (Mp.subtype (iMr u)) (f i)
    exact plr_T'_pair Mp C hC y f b hfy (fun _ => rfl) (iMr u) i
  · intro u x hux
    change Tp (iMr u) = x
    apply plr_T'_fix Mp C hC y (iMr u) x
    exact hux

/--
For a Banach space `E` over `𝕜 = ℝ` or `ℂ`, finite-dimensional `M ↪ E**` via `iM`, `N ↪ E*` via
`iN`, and `ε > 0`, there exists `T : M →L[𝕜] E` that is `(1+ε)`-almost isometric, preserves dual
pairings `(iN n)(T m) = (iM m)(iN n)`, and fixes `J(E)`: `iM m = J x → T m = x`. Source: J.
Lindenstrauss and H. Rosenthal, Israel J. Math. 7 (1969) 325-349, principle of local reflexivity;
Johnson-Rosenthal-Zippin 1971 refinements; Albiac and Kalton, Topics in Banach Space Theory; Lean
states `RCLike` Banach finite- dimensional `M, N` version with `(1+ε)`-isometry and pairing
preservation.

Proves `Wanted` entry `principle_of_local_reflexivity`.

Proof: Helly's lemma applied to finitely many linear conditions plus one norm bound, then a finite
δ-net of the unit sphere of `range iM` turns net-point bounds into the `(1+ε)` bounds (the
elementary proof in Albiac–Kalton, *Topics in Banach Space Theory*).
-/
theorem principle_of_local_reflexivity
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M] [FiniteDimensional 𝕜 M]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N] [FiniteDimensional 𝕜 N]
    (iM : M →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (iN : N →L[𝕜] StrongDual 𝕜 E)
    (hM_inj : Function.Injective iM)
    (hN_inj : Function.Injective iN)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : M →L[𝕜] E),
      (∀ m : M, (1 + ε)⁻¹ * ‖iM m‖ ≤ ‖T m‖ ∧ ‖T m‖ ≤ (1 + ε) * ‖iM m‖)
      ∧ (∀ (m : M) (n : N), (iN n) (T m) = (iM m) (iN n))
      ∧ (∀ (m : M) (x : E), iM m = NormedSpace.inclusionInDoubleDual 𝕜 E x → T m = x) := by
  exact plr_assemble iM iN hM_inj hN_inj ε hε

end
end FunctionalAnalysis.LocalReflexivityWanted
