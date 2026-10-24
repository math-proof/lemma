import Lemma.Definitions.Def_LanglandsTunnell_JLData
import Lemma.Definitions.Def_LanglandsTunnell_ArchEpsilon
import Lemma.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Lemma.Definitions.Def_AutomorphicForm_ArithCuspRealization
import Lemma.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option autoImplicit false

open Complex

noncomputable section

namespace LanglandsTunnell.Converse

namespace ArchR

def diagOne (y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![y, 0; 0, 1]

def unip (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, x; 0, 1]

def weyl : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

def psi (x : ℝ) : ℂ := exp (2 * (Real.pi : ℂ) * I * x)

def glSet : Set (Fin 2 → Fin 2 → ℝ) := {M | (Matrix.of M).det ≠ 0}

def asPi (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (M : Fin 2 → Fin 2 → ℝ) : ℂ := W (Matrix.of M)

def diagOneMulCoords (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ := Matrix.of.symm (diagOne y * k)

def quasiChar (u : ℂ) (a : ZMod 2) (y : ℝ) : ℂ :=
  ((|y| : ℝ) : ℂ) ^ u * (if a = 0 then 1 else ((SignType.sign y : ℝ) : ℂ))

def centralChar (P : RealArchParam) (y : ℝ) : ℂ := quasiChar P.centralExponent P.centralSign y

def IsK (k : Matrix (Fin 2) (Fin 2) ℝ) : Prop := k ∈ Matrix.orthogonalGroup (Fin 2) ℝ

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

def dualFun (D : ArchDatumR P) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (ArchR.centralChar P g.det)⁻¹ * D.W g

end ArchDatumR

namespace ArchC

def diagOne (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![z, 0; 0, 1]
def unip (x : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, x; 0, 1]

def weyl : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

def psi (z : ℂ) : ℂ := exp (2 * (Real.pi : ℂ) * I * (2 * z.re : ℝ))

def glSet : Set (Fin 2 → Fin 2 → ℂ) := {M | (Matrix.of M).det ≠ 0}
def asPi (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (M : Fin 2 → Fin 2 → ℂ) : ℂ := W (Matrix.of M)
def diagOneMulCoords (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → Fin 2 → ℂ := Matrix.of.symm (diagOne z * k)

def quasiChar (u : ℂ) (k : ℤ) (z : ℂ) : ℂ := ((‖z‖ : ℝ) : ℂ) ^ (2 * u) * (z / ((‖z‖ : ℝ) : ℂ)) ^ k

def centralChar (P : ComplexArchParam) (z : ℂ) : ℂ := quasiChar P.centralExponent P.centralTwist z

def IsK (k : Matrix (Fin 2) (Fin 2) ℂ) : Prop := k ∈ Matrix.unitaryGroup (Fin 2) ℂ

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

def dualFun (D : ArchDatumC P) (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := (ArchC.centralChar P g.det)⁻¹ * D.W g

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

def whittakerSeries (a : Kˣ → ℂ) (ε Winf Wf : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∑' α : Kˣ,
    a α * ε g * Winf (globalPoints (𝓞 K) K (diagOne α) * g) * Wf (globalPoints (𝓞 K) K (diagOne α) * g)

def detTwist (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (W : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W g

def extendByRationalPoints (D : Set (AdelicGL2 (𝓞 K) K))
    (hD : ∀ g : AdelicGL2 (𝓞 K) K, ∃ γ : GL (Fin 2) K, globalPoints (𝓞 K) K γ * g ∈ D)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  f (globalPoints (𝓞 K) K (Classical.choose (hD g)) * g)

end LanglandsTunnell.Converse

end

noncomputable section

namespace LanglandsTunnell.Converse

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

def componentMatrix (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion K) :=
  ((AdelicLevel.finComponent (𝓞 K) K v) (AdelicLevel.glFin (𝓞 K) K g) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))

def MemZK0At (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Prop :=
  Valued.v (componentMatrix v g 1 1) ≠ 0 ∧
    Valued.v (componentMatrix v g 0 0) = Valued.v (componentMatrix v g 1 1) ∧
    Valued.v (componentMatrix v g 0 1) ≤ Valued.v (componentMatrix v g 1 1) ∧
    Valued.v (componentMatrix v g 1 0) ≤ Valued.v (componentMatrix v g 1 1) * WithZero.exp (-(m : ℤ))

namespace JLData

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

open Classical in

def epsChar (d : JLData K S epsS ω) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) : ℂ :=
  if ∀ v : ↥S, MemZK0At v.1 (d.m v) g then
    ∏ v : ↥S,
      TateLocal.charExt (TateGlobal.localChar ω v.1) (componentMatrix v.1 g 1 1) *
        TateLocal.charExt (epsS v.1) (componentMatrix v.1 g 0 0 / componentMatrix v.1 g 1 1)
  else 0

end JLData

end LanglandsTunnell.Converse

end

noncomputable section

namespace LanglandsTunnell.Converse

section Wiring

variable {K : Type} [Field K] [NumberField K]

open NumberField NumberField.InfinitePlace NumberField.AdelicLevel AutomorphicForm

def realComponent (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((glArch (𝓞 K) K g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
    fun x => Completion.ringEquivRealOfIsReal hw ((show ((v : InfinitePlace K) → v.Completion) from x) w)

def complexComponent (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((glArch (𝓞 K) K g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
    fun x => Completion.ringEquivComplexOfIsComplex hw ((show ((v : InfinitePlace K) → v.Completion) from x) w)

open scoped Classical in

def archW (archR : (w : InfinitePlace K) → w.IsReal → RealArchParam)
    (archC : (w : InfinitePlace K) → w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∏ w : InfinitePlace K,
    if hw : w.IsReal then (dR w hw).W (realComponent w hw g)
    else (dC w (not_isReal_iff_isComplex.mp hw)).W (complexComponent w (not_isReal_iff_isComplex.mp hw) g)

variable {S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
  {ω : (NumberField.AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

def jlSeries (d : JLData K S epsS ω)
    (archR : (w : InfinitePlace K) → w.IsReal → RealArchParam)
    (archC : (w : InfinitePlace K) → w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) : AdelicGL2 (𝓞 K) K → ℂ :=
  whittakerSeries d.a d.epsChar (archW archR archC dR dC) dF.Wf

def jlForm (D : Set (AdelicGL2 (𝓞 K) K))
    (hD : ∀ g : AdelicGL2 (𝓞 K) K, ∃ γ : GL (Fin 2) K, globalPoints (𝓞 K) K γ * g ∈ D)
    (d : JLData K S epsS ω)
    (archR : (w : InfinitePlace K) → w.IsReal → RealArchParam)
    (archC : (w : InfinitePlace K) → w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) : AdelicGL2 (𝓞 K) K → ℂ :=
  extendByRationalPoints D hD (jlSeries d archR archC dR dC dF)

end Wiring

end LanglandsTunnell.Converse

end
