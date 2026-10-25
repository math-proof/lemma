import Mathlib
import Lemma.ModularCurve.X1
import Def.CohCarrier_Level
import Lemma.EllipticCurve.TateModule
import Abbrev.ModularCurve_XH

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section Groups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem translation_mem_GammaH : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    simp [CohCarrier.gamma0Units, Gamma0Map, ModularGroup.T]
  rw [this]
  exact one_mem H

theorem Gamma1_le_GammaH : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨_, h11, h10⟩ := hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA0 : A ∈ Gamma0 M := Gamma0_mem.mpr h10
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [this]
  exact one_mem H

theorem GammaH_bot : CohCarrier.GammaH M ⊥ = Gamma1 M := by
  refine le_antisymm ?_ (Gamma1_le_GammaH M ⊥)
  intro A hA
  obtain ⟨hA0, hAH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  rw [Subgroup.mem_bot] at hAH
  have h11 : ((A 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hAH
    simpa [CohCarrier.gamma0Units, Gamma0Map] using this
  have h10 : ((A 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hA0
  rw [Gamma1_mem]
  refine ⟨?_, h11, h10⟩
  have hda := CohCarrier.Gamma0_d_mul_a M ⟨A, hA0⟩
  simp only at hda
  rw [h11, one_mul] at hda
  exact hda

variable {M} in

theorem GammaH_mono {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH M H' := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  exact CohCarrier.mem_GammaH_iff.mpr ⟨hA0, h hAH⟩

end Groups

section FunctionField

variable (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def xHFunctionFieldC : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH M H)

abbrev xHFunctionField : IntermediateField ℚ (LaurentSeries ℚ) :=
  xHFunctionFieldC ℚ M H

theorem xHFunctionFieldC_rat : xHFunctionFieldC ℚ M H = xHFunctionField M H := rfl

def xHTopFunctionFieldC (t : ℕ) : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 t)

theorem xHFunctionFieldC_le_top (t : ℕ) : xHFunctionFieldC K M H ≤ xHTopFunctionFieldC K M H t :=
  qExpFunctionFieldC_mono K inf_le_left

theorem xHTopFunctionFieldC_one : xHTopFunctionFieldC K M H 1 = xHFunctionFieldC K M H := by
  have : CohCarrier.GammaH M H ⊓ Gamma0 1 = CohCarrier.GammaH M H := by
    refine le_antisymm inf_le_left (le_inf le_rfl ?_)
    intro A _
    rw [Gamma0_mem]
    exact Subsingleton.elim _ _
  rw [xHTopFunctionFieldC, this, xHFunctionFieldC]

theorem xHFunctionFieldC_le_x1 : xHFunctionFieldC K M H ≤ x1FunctionFieldC K M :=
  qExpFunctionFieldC_mono K (Gamma1_le_GammaH M H)

theorem x0_le_xHFunctionFieldC : qExpFunctionFieldC K (Gamma0 M) ≤ xHFunctionFieldC K M H :=
  qExpFunctionFieldC_mono K (CohCarrier.GammaH_le_Gamma0 H)

variable {H} in

theorem xHFunctionFieldC_antitone {H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') :
    xHFunctionFieldC K M H' ≤ xHFunctionFieldC K M H :=
  qExpFunctionFieldC_mono K (GammaH_mono h)

theorem xHFunctionFieldC_top : xHFunctionFieldC K M ⊤ = qExpFunctionFieldC K (Gamma0 M) := by
  rw [xHFunctionFieldC, CohCarrier.GammaH_top]

theorem xHFunctionFieldC_bot : xHFunctionFieldC K M ⊥ = x1FunctionFieldC K M := by
  rw [xHFunctionFieldC, GammaH_bot]
  rfl

end FunctionField

section Jacobian

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)


def JH.torsionGaloisRep (n : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End (ZMod n) (Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n) :=
  (SemilinearAut.torsionRep _ _ n).comp (arithmeticGalois (xHFunctionField M H))

@[simp]
theorem JH.torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n) :
    JH.torsionGaloisRep M H n σ x = arithmeticGalois (xHFunctionField M H) σ • x :=
  rfl

theorem JH.coe_torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n) :
    ((JH.torsionGaloisRep M H n σ x : Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n) :
        JH M H) = σ • (x : JH M H) :=
  rfl

variable (p : ℕ) [Fact p.Prime]


theorem JH.tateGaloisRep_apply_coe (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : TateModule p (JH M H)) (n : ℕ) :
    ((JH.tateGaloisRep M H p σ x : TateModule p (JH M H)) : ℕ → JH M H) n = σ • (x : ℕ → JH M H) n :=
  rfl

theorem JH.tateEnd_apply_coe (f : AddMonoid.End (JH M H)) (x : TateModule p (JH M H)) (n : ℕ) :
    ((JH.tateEnd M H p f x : TateModule p (JH M H)) : ℕ → JH M H) n = f ((x : ℕ → JH M H) n) :=
  rfl

abbrev JHC (K : Type*) [Field K] : Type _ :=
  Pic0 K (xHFunctionFieldC K M H)

example (K : Type*) [Field K] : AddCommGroup (JHC M H K) := inferInstance

end Jacobian

end ModularCurve

end
