import Mathlib
import Instance.AlgebraicGeometry_ResolvedModelGlue

set_option autoImplicit false
set_option maxHeartbeats 200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue

structure GlueInput (X : Scheme.{0}) (N : Type) where

  x : N → X

  X0 : X.Opens
  mem_X0 : ∀ y : X, y ∈ X0 ↔ ∀ n, y ≠ x n

  U : N → X.Opens
  x_mem_U : ∀ n, x n ∈ U n
  x_not_mem_U : ∀ n m, m ≠ n → x m ∉ U n

  Y : N → Scheme.{0}
  q : ∀ n, Y n ⟶ (U n : Scheme.{0})

  j : ∀ n, ((U n ⊓ X0 : X.Opens) : Scheme.{0}) ⟶ Y n
  j_isOpenImmersion : ∀ n, IsOpenImmersion (j n)
  j_q : ∀ n, j n ≫ q n = X.homOfLE inf_le_left

attribute [instance] GlueInput.j_isOpenImmersion

namespace GlueInput

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)


variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq


end GlueInput

end V3Glue

namespace V3Glue

structure ChartInput (X : Scheme.{0}) (N : Type) where

  x : N → X
  X0 : X.Opens
  mem_X0 : ∀ y : X, y ∈ X0 ↔ ∀ n, y ≠ x n

  S : N → Scheme.{0}
  Vc : ∀ n, (S n).Opens
  Res : N → Scheme.{0}
  ρ : ∀ n, Res n ⟶ S n

  isIso_ρ_restrict : ∀ n, IsIso (ρ n ∣_ Vc n)

  isProper_ρ : ∀ n, IsProper (ρ n)

  thick : N → ℕ
  one_le_thick : ∀ n, 1 ≤ thick n

  U : N → X.Opens
  x_mem_U : ∀ n, x n ∈ U n
  x_not_mem_U : ∀ n m, m ≠ n → x m ∉ U n
  f : ∀ n, ((U n : X.Opens) : Scheme.{0}) ⟶ S n

  f_mem_Vc_iff : ∀ n (y : U n), (f n).base y ∈ Vc n ↔ (y : X) ≠ x n

  f_etale : ∀ n, Etale (f n)

  f_node : ∀ n, ((f n).stalkMap ⟨x n, x_mem_U n⟩).hom.Flat ∧
    Ideal.map ((f n).stalkMap ⟨x n, x_mem_U n⟩).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
    IsIso ((f n).residueFieldMap ⟨x n, x_mem_U n⟩)

  B : Scheme.{0}
  πX : X ⟶ B
  σ : ∀ n, S n ⟶ B
  f_over : ∀ n, f n ≫ σ n = (U n).ι ≫ πX

  flat_ρ_σ : ∀ n, Flat (ρ n ≫ σ n)
  isLocallyNoetherian_Res : ∀ n, IsLocallyNoetherian (Res n)

  interior_preimage_vertex : ∀ n, interior ((ρ n).base ⁻¹' (Vc n : Set (S n))ᶜ) = ∅

attribute [instance] ChartInput.isIso_ρ_restrict ChartInput.isProper_ρ ChartInput.f_etale
  ChartInput.flat_ρ_σ ChartInput.isLocallyNoetherian_Res

namespace ChartInput

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)


end ChartInput

structure RawChartInput (X : Scheme.{0}) (N : Type) where
  x : N → X
  x_injective : Function.Injective x
  isClosed_x : ∀ n, IsClosed ({x n} : Set X)
  S : N → Scheme.{0}
  Vc : ∀ n, (S n).Opens
  Res : N → Scheme.{0}
  ρ : ∀ n, Res n ⟶ S n
  isIso_ρ_restrict : ∀ n, IsIso (ρ n ∣_ Vc n)
  isProper_ρ : ∀ n, IsProper (ρ n)
  thick : N → ℕ
  one_le_thick : ∀ n, 1 ≤ thick n
  U₀ : N → X.Opens
  x_mem_U₀ : ∀ n, x n ∈ U₀ n
  f₀ : ∀ n, ((U₀ n : X.Opens) : Scheme.{0}) ⟶ S n
  f₀_mem_Vc_iff : ∀ n (y : U₀ n), (f₀ n).base y ∈ Vc n ↔ (y : X) ≠ x n

  f₀_node : ∀ n (y : U₀ n), (y : X) = x n →
    ((f₀ n).stalkMap y).hom.Flat ∧
      Ideal.map ((f₀ n).stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
      IsIso ((f₀ n).residueFieldMap y)

  f₀_lfp : ∀ n, LocallyOfFinitePresentation (f₀ n)
  B : Scheme.{0}
  πX : X ⟶ B
  σ : ∀ n, S n ⟶ B
  f₀_over : ∀ n, f₀ n ≫ σ n = (U₀ n).ι ≫ πX
  flat_ρ_σ : ∀ n, Flat (ρ n ≫ σ n)
  isLocallyNoetherian_Res : ∀ n, IsLocallyNoetherian (Res n)
  interior_preimage_vertex : ∀ n, interior ((ρ n).base ⁻¹' (Vc n : Set (S n))ᶜ) = ∅

attribute [instance] RawChartInput.isIso_ρ_restrict RawChartInput.isProper_ρ RawChartInput.f₀_lfp
  RawChartInput.flat_ρ_σ RawChartInput.isLocallyNoetherian_Res

namespace RawChartInput

variable {X : Scheme.{0}} {N : Type} [Finite N] (R : RawChartInput X N)


variable (hnbhd : ∀ n, ∃ V : ((R.U₀ n : X.Opens) : Scheme.{0}).Opens,
  (⟨R.x n, R.x_mem_U₀ n⟩ : R.U₀ n) ∈ V ∧ Etale (V.ι ≫ R.f₀ n))


end RawChartInput

end V3Glue

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

omit D in


variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq


end V3Glue.GlueInput

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

omit D in


variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq


end V3Glue.GlueInput

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)
variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq


end V3Glue.GlueInput

end
