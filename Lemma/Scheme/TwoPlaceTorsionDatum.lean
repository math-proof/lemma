import Def.CerednikDrinfeld_JPrimeTorsionDatum
import Lemma.Compat.Mathlib430
import Structure.CerednikDrinfeld_TwoPlaceTorsionDatum

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

namespace JPrimeTorsionDatum

variable {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {A : ValuationSubring (AlgebraicClosure ℚ)}

end JPrimeTorsionDatum

namespace TwoPlaceTorsionDatum

variable {p : ℕ} {E₁ V₁ E₂ V₂ : Type}
  [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
  {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
  {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}

@[simp] theorem fst_D (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.D = D₁ := rfl
@[simp] theorem snd_D (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.D = D₂ := rfl
@[simp] theorem fst_T (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.T = 𝒥.T := rfl
@[simp] theorem snd_T (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.T = 𝒥.T := rfl
@[simp] theorem fst_toric (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.toric = 𝒥.toric₁ := rfl
@[simp] theorem snd_toric (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.toric = 𝒥.toric₂ := rfl

end TwoPlaceTorsionDatum

end CerednikDrinfeld
