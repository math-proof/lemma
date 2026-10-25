/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Algebra.Monoid
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Def.Topology.Algebra.PeterWeyl.Part6


noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory

open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

section PWHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- `S` is compact. -/
theorem pwS_compact (k : C(G, ℂ)) :
    IsCompactOperator ⇑(pwS (G := G) k) := by
  have h := (pwT_compact (G := G) k).clm_comp
    (ContinuousLinearMap.adjoint (pwT (G := G) k))
  have hfun : (⇑(ContinuousLinearMap.adjoint (pwT (G := G) k)) ∘ ⇑(pwT (G := G) k))
      = ⇑(pwS (G := G) k) :=
    funext fun _ => rfl
  rwa [hfun] at h

/-- The adjoint of `T` commutes with every translation. -/
theorem pwAdj_comm (k : C(G, ℂ)) (a : G) (u : Lp ℂ 2 (pwHaar G)) :
    (ContinuousLinearMap.adjoint (pwT (G := G) k)) (pwTransl (G := G) a u)
      = pwTransl (G := G) a
        ((ContinuousLinearMap.adjoint (pwT (G := G) k)) u) := by
  apply ext_inner_right ℂ
  intro v
  calc ⟪(ContinuousLinearMap.adjoint (pwT (G := G) k)) (pwTransl (G := G) a u), v⟫
        = ⟪pwTransl (G := G) a u, (pwT (G := G) k) v⟫ :=
          ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = ⟪u, pwTransl (G := G) a⁻¹ ((pwT (G := G) k) v)⟫ :=
          pwTransl_inner (G := G) a _ _
      _ = ⟪u, (pwT (G := G) k) (pwTransl (G := G) a⁻¹ v)⟫ := by
          rw [pwT_comm]
      _ = ⟪(ContinuousLinearMap.adjoint (pwT (G := G) k)) u,
            pwTransl (G := G) a⁻¹ v⟫ :=
          (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
      _ = ⟪pwTransl (G := G) a
            ((ContinuousLinearMap.adjoint (pwT (G := G) k)) u), v⟫ :=
          (pwTransl_inner (G := G) a _ _).symm

/-- `S` commutes with every translation. -/
theorem pwS_comm (k : C(G, ℂ)) (a : G) (f : Lp ℂ 2 (pwHaar G)) :
    (pwS (G := G) k) (pwTransl (G := G) a f)
      = pwTransl (G := G) a ((pwS (G := G) k) f) := by
  unfold pwS
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    pwT_comm, pwAdj_comm]

/-- Eigenspaces of `S` are invariant under every translation. -/
theorem pwEigen_invariant (k : C(G, ℂ)) (c : ℂ) (a : G)
    (v : Lp ℂ 2 (pwHaar G))
    (hv : v ∈ Module.End.eigenspace ((pwS (G := G) k) :
      Module.End ℂ (Lp ℂ 2 (pwHaar G))) c) :
    pwTransl (G := G) a v ∈ Module.End.eigenspace ((pwS (G := G) k) :
      Module.End ℂ (Lp ℂ 2 (pwHaar G))) c := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hcomm : ((pwS (G := G) k) : Module.End ℂ (Lp ℂ 2 (pwHaar G)))
        (pwTransl (G := G) a v)
      = pwTransl (G := G) a (((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) v) :=
    pwS_comm (G := G) k a v
  rw [hcomm, hv, map_smul]

/-- Matrix coefficients on a nonzero eigenspace are continuous in `g`
(`u` is arbitrary; only `v`'s eigenvalue equation is used). -/
theorem pwEigen_coeff_continuous (k : C(G, ℂ)) (c : ℂ) (hc : c ≠ 0)
    (u v : Lp ℂ 2 (pwHaar G))
    (hv : v ∈ Module.End.eigenspace ((pwS (G := G) k) :
      Module.End ℂ (Lp ℂ 2 (pwHaar G))) c) :
    Continuous (fun g => ⟪u, pwTransl (G := G) g v⟫) := by
  rw [Module.End.mem_eigenspace_iff] at hv
  have hv' : (pwS (G := G) k) v = c • v := hv
  have hvc : v = c⁻¹ • ((pwS (G := G) k) v) := by
    rw [hv', smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hSv : (pwS (G := G) k) v
      = (ContinuousLinearMap.adjoint (pwT (G := G) k)) ((pwT (G := G) k) v) :=
    rfl
  have hfun : (fun g => ⟪u, pwTransl (G := G) g v⟫)
      = fun g => c⁻¹ * ⟪(pwT (G := G) k) u,
        pwTransl (G := G) g ((pwT (G := G) k) v)⟫ := by
    funext g
    conv_lhs => rw [hvc, map_smul, inner_smul_right, hSv, ← pwAdj_comm,
      ContinuousLinearMap.adjoint_inner_right]
  have hTvc : (pwT (G := G) k) v
      = ContinuousMap.toLp 2 (pwHaar G) ℂ ((pwT0 (G := G) k) v) := rfl
  rw [hfun, hTvc]
  exact continuous_const.mul
    (continuous_const.inner (pwTransl_toLp_continuous (G := G) _))

/-- (helper) If `z` fixes every vector of every eigenspace of `S`,
then `z` fixes every value of `S`. -/
theorem pwSep_fixS (z : G) (k : C(G, ℂ))
    (hall : ∀ (c : ℂ), c ≠ 0 → ∀ (v : Lp ℂ 2 (pwHaar G)),
      v ∈ Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) c →
      pwTransl (G := G) z v = v) :
    ∀ w : Lp ℂ 2 (pwHaar G),
      pwTransl (G := G) z ((pwS (G := G) k) w) = (pwS (G := G) k) w := by
  set B : (Lp ℂ 2 (pwHaar G)) →L[ℂ] Lp ℂ 2 (pwHaar G) :=
    ((pwTransl (G := G) z).toContinuousLinearMap - ContinuousLinearMap.id ℂ _) ∘L
      (pwS (G := G) k) with hBdef
  have eLz : ∀ x : Lp ℂ 2 (pwHaar G),
      ((pwTransl (G := G) z).toContinuousLinearMap) ((pwS (G := G) k) x)
        = (pwTransl (G := G) z) ((pwS (G := G) k) x) := fun _ => rfl
  have hBv : ∀ v : Lp ℂ 2 (pwHaar G), B v
      = (pwTransl (G := G) z) ((pwS (G := G) k) v)
        - ((pwS (G := G) k) v) := by
    intro v
    rw [hBdef, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, eLz]
  have hsub : ∀ μ : ℂ, Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) μ ≤ LinearMap.ker
        ((B : Lp ℂ 2 (pwHaar G) →ₗ[ℂ] Lp ℂ 2 (pwHaar G))) := by
    intro μ v hv
    have hvmem := hv
    rw [Module.End.mem_eigenspace_iff] at hv
    have hv' : (pwS (G := G) k) v = μ • v := hv
    rw [LinearMap.mem_ker]
    change B v = 0
    rw [hBv, hv']
    by_cases hμ : μ = 0
    · subst hμ
      simp
    · rw [map_smul, hall μ hμ v hvmem, sub_self]
  have hiSup : (⨆ μ, Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) μ) ≤ LinearMap.ker
      ((B : Lp ℂ 2 (pwHaar G) →ₗ[ℂ] Lp ℂ 2 (pwHaar G))) :=
    iSup_le hsub
  have hclosed : IsClosed ((LinearMap.ker
      ((B : Lp ℂ 2 (pwHaar G) →ₗ[ℂ] Lp ℂ 2 (pwHaar G))) : Submodule ℂ _) :
      Set (Lp ℂ 2 (pwHaar G))) :=
    ContinuousLinearMap.isClosed_ker B
  have htop : ((⨆ μ, Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) μ)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff]
    exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      (pwS_compact (G := G) k) (pwS_symmetric (G := G) k)
  intro w
  have hmem : w ∈ ((⨆ μ, Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) μ)).topologicalClosure := by
    rw [htop]
    exact Submodule.mem_top
  have hkerw := Submodule.topologicalClosure_minimal _ hiSup hclosed hmem
  have hkerw' : B w = 0 := hkerw
  rw [hBv, sub_eq_zero] at hkerw'
  exact hkerw'

/-- Some nonzero eigenspace of `S` moves under translation by `z`. -/
theorem pwSeparation (z : G) (k : C(G, ℂ))
    (hi : ∫ h, k h * k (h⁻¹) ∂(pwHaar G) ≠ 0)
    (hii : ∀ h : G, k h * k (h⁻¹ * z⁻¹) = 0) :
    ∃ (c : ℂ) (_hc : c ≠ 0) (v : Lp ℂ 2 (pwHaar G)),
      v ∈ Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) c ∧ pwTransl (G := G) z v ≠ v := by
  by_contra hall
  have hall' : ∀ (c : ℂ), c ≠ 0 → ∀ (v : Lp ℂ 2 (pwHaar G)),
      v ∈ Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) c →
      pwTransl (G := G) z v = v := by
    intro c hc v hvmem
    by_contra hne
    exact hall ⟨c, hc, v, hvmem, hne⟩
  have hfixS := pwSep_fixS (G := G) z k hall'
  have hS0 : ∀ w : Lp ℂ 2 (pwHaar G),
      (pwS (G := G) k) (pwTransl (G := G) z w - w) = 0 := by
    intro w
    rw [map_sub, pwS_comm, hfixS, sub_self]
  set ψ : Lp ℂ 2 (pwHaar G) := ContinuousMap.toLp 2 (pwHaar G) ℂ k with hψdef
  have hw0 := hS0 ψ
  have hnorm : ‖(pwT (G := G) k) (pwTransl (G := G) z ψ - ψ)‖ ^ 2 = 0 := by
    have h := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left
      (pwT (G := G) k) (pwTransl (G := G) z ψ - ψ)
    have e : ((ContinuousLinearMap.adjoint (pwT (G := G) k)) ∘L
        (pwT (G := G) k)) (pwTransl (G := G) z ψ - ψ)
        = (pwS (G := G) k) (pwTransl (G := G) z ψ - ψ) := rfl
    rw [e, hw0, inner_zero_left] at h
    simpa using h
  have hT0 : (pwT (G := G) k) (pwTransl (G := G) z ψ - ψ) = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hnorm)
  have hTeq : (pwT (G := G) k) (pwTransl (G := G) z ψ)
      = (pwT (G := G) k) ψ := by
    have hms := map_sub (pwT (G := G) k) (pwTransl (G := G) z ψ) ψ
    rw [hT0] at hms
    exact sub_eq_zero.mp hms.symm
  have hLz : pwTransl (G := G) z ((pwT (G := G) k) ψ)
      = (pwT (G := G) k) ψ := by
    rw [← pwT_comm]
    exact hTeq
  have hTTψ : (pwT (G := G) k) ψ
      = ContinuousMap.toLp 2 (pwHaar G) ℂ ((pwT0 (G := G) k) ψ) := rfl
  have hT0ψ : (pwT0 (G := G) k) ψ = pwT0Map (G := G) k ψ :=
    LinearMap.mkContinuousOfExistsBound_apply _ _ _
  rw [hTTψ, hT0ψ, pwTransl_toLp] at hLz
  have hCeq := (ContinuousMap.toLp_inj (pwHaar G)).mp hLz
  have h1 := congrArg (fun F : C(G, ℂ) => F 1) hCeq
  rw [ContinuousMap.comp_apply] at h1
  change (pwT0Map (G := G) k ψ) (z⁻¹ * 1) = (pwT0Map (G := G) k ψ) 1 at h1
  rw [mul_one, hψdef, pwT0_toLp_apply, pwT0_toLp_apply] at h1
  have hz : (∫ h, k h * k (h⁻¹ * z⁻¹) ∂(pwHaar G)) = 0 := by
    simp only [hii, integral_zero]
  have h1' : (∫ h, k h * k (h⁻¹ * 1) ∂(pwHaar G))
      = ∫ h, k h * k h⁻¹ ∂(pwHaar G) := by
    apply integral_congr_ae
    filter_upwards with h
    rw [mul_one]
  rw [hz, h1'] at h1
  exact hi h1.symm

end PWHelpers
end MathlibExt.Topology.Algebra.PeterWeylWanted
end
