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
import Def.Analysis.NormedSpace.LocalReflexivity.Part3


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- Application formula for `plr_L`. -/
theorem plr_L_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜) (z : 𝕜 × (Fin p → E)) (k : ι) :
    plr_L a c z k = z.1 • a k + ∑ j, c k j • z.2 j := by
  simp only [plr_L, Pi.add_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.id_apply,
    FunLike.coe_sum, Finset.sum_apply]

/-- Application formula for `plr_Phi`. -/
theorem plr_Phi_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (z : 𝕜 × (Fin p → E)) :
    plr_Phi a c f g z
      = (z.1, (fun i j => f i (z.2 j)),
        (fun k => g k (plr_L a c z k))) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [plr_Phi, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst']
  · funext i j
    simp only [plr_Phi, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply]
  · funext k
    simp only [plr_Phi, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]

/-- A continuous linear functional on `𝕜` is determined by its value at `1`. -/
theorem plr_clm_smul_apply (f : 𝕜 →L[𝕜] 𝕜) (x : 𝕜) :
    f x = x * f 1 := by
  have hx : x = x • (1 : 𝕜) := by rw [smul_eq_mul, mul_one]
  conv_lhs => rw [hx, map_smul, smul_eq_mul]

/-- The first-coordinate part of the `λ`-expansion on `V`. -/
theorem plr_lam_fst {p q : ℕ} {ι : Type*}
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜) (s : 𝕜) :
    lam (s, 0, 0) = s * lam (1, 0, 0) := by
  have e : ((s, 0, 0) : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜))
      = s • ((1, 0, 0) : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) := by
    ext <;> simp
  rw [e, map_smul, smul_eq_mul]

/-- The third-coordinate part of the `λ`-expansion on `V`. -/
theorem plr_lam_last {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜) (h : ι → 𝕜) :
    lam (0, 0, h) = ∑ k, h k * lam (0, 0, Pi.single k 1) := by
  have hg : ∀ x : ι → 𝕜,
      lam.comp ((ContinuousLinearMap.inr 𝕜 𝕜
        ((Fin q → Fin p → 𝕜) × (ι → 𝕜))).comp
        (ContinuousLinearMap.inr 𝕜 (Fin q → Fin p → 𝕜) (ι → 𝕜))) x
        = lam (0, 0, x) := fun x => rfl
  rw [← hg h, plr_clm_pi_sum _ h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [plr_clm_smul_apply]
  congr 1

/-- The middle-coordinate part of the `λ`-expansion on `V`, by applying the
one-index expansion twice. -/
theorem plr_lam_mid {p q : ℕ} {ι : Type*}
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜)
    (r : Fin q → Fin p → 𝕜) :
    lam (0, r, 0)
      = ∑ i, ∑ j, r i j * lam (0, Pi.single i (Pi.single j 1), 0) := by
  have hg : ∀ x : Fin q → Fin p → 𝕜,
      lam.comp ((ContinuousLinearMap.inr 𝕜 𝕜
        ((Fin q → Fin p → 𝕜) × (ι → 𝕜))).comp
        (ContinuousLinearMap.inl 𝕜 (Fin q → Fin p → 𝕜) (ι → 𝕜))) x
        = lam (0, x, 0) := fun x => rfl
  rw [← hg r, plr_clm_pi_sum _ r]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [plr_clm_pi_sum _ (r i)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [plr_clm_smul_apply]
  congr 1

/-- Full `λ`-expansion on `V = 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)`. -/
theorem plr_lam_expand {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜)
    (v : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) :
    lam v = v.1 * lam (1, 0, 0)
      + (∑ i, ∑ j, v.2.1 i j * lam (0, Pi.single i (Pi.single j 1), 0))
      + ∑ k, v.2.2 k * lam (0, 0, Pi.single k 1) := by
  have hsplit : v = (v.1, 0, 0) + (0, v.2.1, 0) + (0, 0, v.2.2) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  conv_lhs => rw [hsplit]
  rw [map_add, map_add, plr_lam_fst, plr_lam_mid, plr_lam_last]

/-- The value of `plr_Phi` at `(1, 0)`. -/
theorem plr_Phi10 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E) :
    plr_Phi a c f g (1, 0) = (1, 0, fun k => g k (a k)) := by
  have hL10 : ∀ k, plr_L a c (1, 0) k = a k := by
    intro k
    rw [plr_L_apply]
    simp
  rw [plr_Phi_apply]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext i j
    simp
  · funext k
    exact congrArg (g k) (hL10 k)

/-- The value of `plr_Phi` at `(0, s)`. -/
theorem plr_Phi0 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (s : Fin p → E) :
    plr_Phi a c f g (0, s)
      = (0, (fun i j' => f i (s j')),
        (fun k => g k (∑ j', c k j' • s j'))) := by
  have hL0 : ∀ k, plr_L a c (0, s) k = ∑ j', c k j' • s j' := by
    intro k
    rw [plr_L_apply]
    simp
  rw [plr_Phi_apply]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext k
  exact congrArg (g k) (hL0 k)

/-- A coefficient-weighted point-mass sum collapses. -/
theorem plr_single_smul_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ} (c : Fin p → 𝕜) (y : E) (j : Fin p) :
    (∑ j', c j' • Pi.single (M := fun _ => E) j y j') = c j • y := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hne
    simp [hne]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end
end FunctionalAnalysis.LocalReflexivityWanted
