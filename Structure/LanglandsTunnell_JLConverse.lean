import Structure.LanglandsTunnell_JLData
import Def.LanglandsTunnell_ArchEpsilon
import Def.UnramifiedWhittaker_HeckeRecursion
import Lemma.AutomorphicForm.ArithCuspRealization
import Def.LanglandsTunnell_StandardLocalConstantsAt

set_option autoImplicit false

open Complex

noncomputable section

namespace LanglandsTunnell.Converse

namespace ArchR

def diagOne (y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![y, 0; 0, 1]

def unip (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, x; 0, 1]

def weyl : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]


def glSet : Set (Fin 2 → Fin 2 → ℝ) := {M | (Matrix.of M).det ≠ 0}

def asPi (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (M : Fin 2 → Fin 2 → ℝ) : ℂ := W (Matrix.of M)

def diagOneMulCoords (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ := Matrix.of.symm (diagOne y * k)

def quasiChar (u : ℂ) (a : ZMod 2) (y : ℝ) : ℂ :=
  ((|y| : ℝ) : ℂ) ^ u * (if a = 0 then 1 else ((SignType.sign y : ℝ) : ℂ))

def centralChar (P : RealArchParam) (y : ℝ) : ℂ := quasiChar P.centralExponent P.centralSign y


def zetaIntegrand (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ)
    (y : ℝ) : ℂ :=
  W (diagOne y * g) * quasiChar u a y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹

end ArchR

open ArchR in

structure ArchDatumR (P : RealArchParam) where

  W : Matrix (Fin 2) (Fin 2) ℝ → ℂ

  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (asPi W) glSet

  unip_law : ∀ (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), W (unip x * g) = psi x * W g

  central_law : ∀ (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), z ≠ 0 →
    W (z • g) = centralChar P z * ((|z| : ℝ) : ℂ) * W g

  zetaEntire : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ZMod 2 → ℂ → ℂ
  zetaEntire_differentiable : ∀ g u a, Differentiable ℂ (zetaEntire g u a)

  zeta_abscissa : ℝ
  zeta_integrable : ∀ g u a s, g.det ≠ 0 → zeta_abscissa < s.re + u.re →
    MeasureTheory.Integrable (zetaIntegrand W g u a s)

  zeta_eq : ∀ g u a s, g.det ≠ 0 → zeta_abscissa < s.re + u.re →
    ∫ y : ℝ, zetaIntegrand W g u a s y = (P.twist u a).archFactor s * zetaEntire g u a s

  functional_equation : ∀ g u a s, g.det ≠ 0 →
    zetaEntire (weyl * g) (-(u + P.centralExponent)) (a + P.centralSign) (1 - s)
      = (P.twist u a).epsilonFactor * zetaEntire g u a s

  zetaEntire_finiteOrder : ∀ g u a (A B : ℝ), ∃ C D : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B →
    ‖zetaEntire g u a s‖ ≤ C * Real.exp (D * |s.im|)

  decay_top : ∀ (j N : ℕ), ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → 1 ≤ |y| →
    ‖iteratedFDerivWithin ℝ j (asPi W) glSet (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-(N : ℝ))

  decay_zero : ∀ j : ℕ, ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → y ≠ 0 → |y| ≤ 1 →
    ‖iteratedFDerivWithin ℝ j (asPi W) glSet (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-σ)

namespace ArchDatumR

variable {P : RealArchParam}


end ArchDatumR

namespace ArchC

def diagOne (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![z, 0; 0, 1]
def unip (x : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, x; 0, 1]

def weyl : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]


def glSet : Set (Fin 2 → Fin 2 → ℂ) := {M | (Matrix.of M).det ≠ 0}
def asPi (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (M : Fin 2 → Fin 2 → ℂ) : ℂ := W (Matrix.of M)
def diagOneMulCoords (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → Fin 2 → ℂ := Matrix.of.symm (diagOne z * k)

def quasiChar (u : ℂ) (k : ℤ) (z : ℂ) : ℂ := ((‖z‖ : ℝ) : ℂ) ^ (2 * u) * (z / ((‖z‖ : ℝ) : ℂ)) ^ k

def centralChar (P : ComplexArchParam) (z : ℂ) : ℂ := quasiChar P.centralExponent P.centralTwist z


def zetaIntegrand (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ) (s : ℂ)
    (z : ℂ) : ℂ :=
  W (diagOne z * g) * quasiChar u k z * (((‖z‖ ^ 2 : ℝ)) : ℂ) ^ (s - 1) * (((‖z‖ ^ 2 : ℝ)) : ℂ)⁻¹

end ArchC

open ArchC in

structure ArchDatumC (P : ComplexArchParam) where
  W : Matrix (Fin 2) (Fin 2) ℂ → ℂ

  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (asPi W) glSet
  unip_law : ∀ (x : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), W (unip x * g) = psi x * W g

  central_law : ∀ (z : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), z ≠ 0 →
    W (z • g) = centralChar P z * ((‖z‖ ^ 2 : ℝ) : ℂ) * W g
  zetaEntire : Matrix (Fin 2) (Fin 2) ℂ → ℂ → ℤ → ℂ → ℂ
  zetaEntire_differentiable : ∀ g u k, Differentiable ℂ (zetaEntire g u k)
  zeta_abscissa : ℝ
  zeta_integrable : ∀ g u k s, g.det ≠ 0 → zeta_abscissa < s.re + u.re →
    MeasureTheory.Integrable (zetaIntegrand W g u k s)
  zeta_eq : ∀ g u k s, g.det ≠ 0 → zeta_abscissa < s.re + u.re →
    ∫ z : ℂ, zetaIntegrand W g u k s z = (P.twist u k).archFactor s * zetaEntire g u k s

  functional_equation : ∀ g u k s, g.det ≠ 0 →
    zetaEntire (weyl * g) (-(u + P.centralExponent)) (-(k + P.centralTwist)) (1 - s)
      = (P.twist u k).epsilonFactor * zetaEntire g u k s
  zetaEntire_finiteOrder : ∀ g u k (A B : ℝ), ∃ C D : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B →
    ‖zetaEntire g u k s‖ ≤ C * Real.exp (D * |s.im|)
  decay_top : ∀ (j N : ℕ), ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), IsK k → 1 ≤ ‖z‖ →
    ‖iteratedFDerivWithin ℝ j (asPi W) glSet (diagOneMulCoords z k)‖ ≤ C * ‖z‖ ^ (-(N : ℝ))
  decay_zero : ∀ j : ℕ, ∃ (C σ : ℝ), ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), IsK k → z ≠ 0 → ‖z‖ ≤ 1 →
    ‖iteratedFDerivWithin ℝ j (asPi W) glSet (diagOneMulCoords z k)‖ ≤ C * ‖z‖ ^ (-σ)

namespace ArchDatumC

variable {P : ComplexArchParam}


end ArchDatumC

end LanglandsTunnell.Converse

end

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SmoothCusp
open UnramifiedWhittaker

namespace LanglandsTunnell.Converse

variable (K : Type) [Field K] [NumberField K]

structure FinWhittakerDatum (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ) where

  Wf : AdelicGL2 (𝓞 K) K → ℂ

  finite_dependent : ∀ g g' : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g' → Wf g = Wf g'

  blind_at : ∀ v ∈ S, ∀ (h : GL (Fin 2) (v.adicCompletion K)) (g : AdelicGL2 (𝓞 K) K),
    Wf (g * placeEmbed K v h) = Wf g

  unipotent_left : ∀ v ∉ S, ∀ (x : v.adicCompletion K) (g : AdelicGL2 (𝓞 K) K),
    Wf (placeEmbed K v (unipotent x) * g) = StandardAddChar.psiLocal K v x * Wf g

  integral_right : ∀ v ∉ S, ∀ (k : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
    Wf (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k)) = Wf g

  hecke_eigen : ∀ v ∉ S, ∀ M : Ideal (𝓞 K), ¬ v.asIdeal ∣ M →
    IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
      (heckeGen (𝓞 K) K v) v Wf (Pi.a v)

  central_eigen : ∀ v ∉ S, ∀ g : AdelicGL2 (𝓞 K) K,
    Wf (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g)
      = Pi.toRawCentral.b v * Wf g

  level_right : ∃ N₀ : Ideal (𝓞 K), N₀ ≠ ⊥ ∧ ∀ (g : AdelicGL2 (𝓞 K) K),
    ∀ u ∈ levelOne (𝓞 K) K N₀ ⊓ finiteAdelicGL2Subgroup K, Wf (g * u) = Wf g

variable {K}


end LanglandsTunnell.Converse

end

noncomputable section

namespace LanglandsTunnell.Converse

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]


namespace JLData

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

open Classical in


end JLData

end LanglandsTunnell.Converse

end

noncomputable section

namespace LanglandsTunnell.Converse

section Wiring

variable {K : Type} [Field K] [NumberField K]

open NumberField NumberField.InfinitePlace NumberField.AdelicLevel AutomorphicForm


open scoped Classical in


variable {S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
  {ω : (NumberField.AdeleRing (𝓞 K) K)ˣ →* ℂˣ}


end Wiring

end LanglandsTunnell.Converse

end
