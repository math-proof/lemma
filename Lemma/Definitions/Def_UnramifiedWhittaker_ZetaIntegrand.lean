import Lemma.Definitions.Def_AdelicDock_LocalEmbedding
import Lemma.Definitions.Def_NumberField_TateGlobalZeta
import Lemma.Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Lemma.Definitions.Def_NumberField_IdeleBox

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Polynomial
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal
open AutomorphicForm AdelicDock

namespace UnramifiedWhittaker

def zetaIntegrand {F : Type} [Field F] [NumberField F] (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  W (diagOne a) * ((χ a : ℂˣ) : ℂ) * ((ideleNorm F a : ℝ) : ℂ) ^ (s - 1)

structure ProductMeasureData {F : Type} [Field F] [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (ν : Measure (AdeleRing (𝓞 F) F)ˣ) where

  c : ℝ
  c_pos : 0 < c

  νS : Measure (AdeleRing (𝓞 F) F)ˣ

  projS : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 F) F)ˣ

  ord : HeightOneSpectrum (𝓞 F) → (AdeleRing (𝓞 F) F)ˣ → ℤ
  projS_off : ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)), v ∉ S →
    ((projS a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1
  decomp : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    ∀ a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}),
      ∃ u : (AdeleRing (𝓞 F) F)ˣ, (u : AdeleRing (𝓞 F) F).1 = 1 ∧
        (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) ∧
        finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F ∧
        a = projS a * (L.map fun v => uniformizerIdele F v ^ ord v a).prod * u
  tonelli : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    ∀ (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℂ),
      Integrable f νS → (∀ v ∈ L, Summable fun m : ℤ => ‖φ v m‖) →
        IntegrableOn (fun a => f (projS a) * (L.map fun v => φ v (ord v a)).prod)
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ) ν ∧
        (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ),
            f (projS a) * (L.map fun v => φ v (ord v a)).prod ∂ν) =
          c * (∫ a, f a ∂νS) * (L.map fun v => ∑' m : ℤ, φ v m).prod

  measurableSet : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    MeasurableSet (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ)

end UnramifiedWhittaker

end
