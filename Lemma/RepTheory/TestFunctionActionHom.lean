import Lemma.RepTheory.TestFunctionAction
import Abbrev.LanglandsTunnell_SchwartzBruhatSpace
import Lemma.RepTheory.SmoothAdmissibleSchurCommutant
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Abbrev.RepTheory_TestFunctionActionHom

set_option autoImplicit false

open MeasureTheory Set

namespace LevelMeasure

section Mass

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

theorem measure_ne_zero (K : Subgroup G) (hKo : IsOpen (K : Set G)) : μ (K : Set G) ≠ 0 :=
  hKo.measure_ne_zero μ ⟨1, K.one_mem⟩

theorem measure_ne_top (K : Subgroup G) (hKc : IsCompact (K : Set G)) : μ (K : Set G) ≠ ⊤ :=
  hKc.measure_lt_top.ne

end Mass

section Indicator

variable {G : Type} [Group G]

theorem indicator_mul_left (K : Subgroup G) (c : ℂ) {k : G} (hk : k ∈ K) (g : G) :
    (K : Set G).indicator (fun _ => c) (k * g) = (K : Set G).indicator (fun _ => c) g := by
  by_cases hg : g ∈ K
  · rw [indicator_of_mem (K.mul_mem hk hg), indicator_of_mem hg]
  · have : k * g ∉ K := fun h => hg (by simpa using K.mul_mem (K.inv_mem hk) h)
    rw [indicator_of_notMem this, indicator_of_notMem hg]

theorem indicator_mul_right (K : Subgroup G) (c : ℂ) {k : G} (hk : k ∈ K) (g : G) :
    (K : Set G).indicator (fun _ => c) (g * k) = (K : Set G).indicator (fun _ => c) g := by
  by_cases hg : g ∈ K
  · rw [indicator_of_mem (K.mul_mem hg hk), indicator_of_mem hg]
  · have : g * k ∉ K := fun h => hg (by simpa using K.mul_mem h (K.inv_mem hk))
    rw [indicator_of_notMem this, indicator_of_notMem hg]

end Indicator

end LevelMeasure

namespace ModuleAction

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ofHom_smul (π : G →* Module.End ℂ V) (g : G) (v : V) :
    letI := ofHom π
    g • v = π g v := rfl

theorem smulCommClass_ofHom (π : G →* Module.End ℂ V) :
    letI := ofHom π
    SMulCommClass G ℂ V := by
  letI := ofHom π
  exact ⟨fun g c v => ((π g).map_smul c v).symm ▸ rfl⟩

end ModuleAction

open MeasureTheory
open scoped Topology

namespace TestFunctionAction

section Smooth

open FLT.SmoothAdmissibleSchurCommutant

variable {G : Type} [Group G] [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : G →* Module.End ℂ V)

omit [TopologicalSpace G] in

theorem stabilizer_ofHom_eq (v : V) :
    letI := ModuleAction.ofHom π
    MulAction.stabilizer G v = repStabilizer π v := by
  letI := ModuleAction.ofHom π
  ext g
  rfl

theorem isSmoothRep_iff_forall_hasOpenStabilizer :
    letI := ModuleAction.ofHom π
    IsSmoothRep π ↔ ∀ v : V, HasOpenStabilizer G v := by
  letI := ModuleAction.ofHom π
  refine forall_congr' fun v => ?_
  show IsOpen _ ↔ IsOpen _
  rw [stabilizer_ofHom_eq]

theorem hasOpenStabilizer_of_isSmoothRep (hsm : IsSmoothRep π) (v : V) :
    letI := ModuleAction.ofHom π
    HasOpenStabilizer G v :=
  (isSmoothRep_iff_forall_hasOpenStabilizer π).mp hsm v

end Smooth

section Bundle

open FLT.SmoothAdmissibleSchurCommutant

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
  [OpensMeasurableSpace G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def heckeSmulHom (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] : SchwartzBruhatSpace.testSpace G →ₗ[ℂ] Module.End ℂ V :=
  letI := ModuleAction.ofHom π
  haveI := ModuleAction.smulCommClass_ofHom π
  have hsm' : ∀ v : V, HasOpenStabilizer G v := hasOpenStabilizer_of_isSmoothRep π hsm
  { toFun := fun φ =>
      { toFun := fun v => heckeSmul μ (φ : G → ℂ) v
        map_add' := fun v w => heckeSmul_add_right μ φ.2.1 φ.2.2 (hsm' v) (hsm' w)
        map_smul' := fun c v => heckeSmul_smul_right μ φ.2.1 φ.2.2 (hsm' v) c }
    map_add' := fun φ ψ => by
      ext v
      exact heckeSmul_add_left μ φ.2.1 φ.2.2 ψ.2.1 ψ.2.2 (hsm' v)
    map_smul' := fun c φ => by
      ext v
      exact heckeSmul_smul_left μ φ.2.1 φ.2.2 (hsm' v) c }

theorem heckeSmulHom_apply (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (φ : SchwartzBruhatSpace.testSpace G) (v : V) :
    heckeSmulHom π hsm μ φ v =
      (letI := ModuleAction.ofHom π; heckeSmul μ (φ : G → ℂ) v) :=
  rfl

end Bundle

end TestFunctionAction
