import Def.LanglandsTunnell_JLData
import Lemma.LanglandsTunnell.ArchEpsilon
import Def.UnramifiedWhittaker_HeckeRecursion
import Lemma.AutomorphicForm.ArithCuspRealization
import Lemma.LanglandsTunnell.StandardLocalConstantsAt
import Structure.LanglandsTunnell_JLConverse

set_option autoImplicit false

open Complex

noncomputable section

namespace LanglandsTunnell.Converse

namespace ArchR


def psi (x : ℝ) : ℂ := exp (2 * (Real.pi : ℂ) * I * x)


def IsK (k : Matrix (Fin 2) (Fin 2) ℝ) : Prop := k ∈ Matrix.orthogonalGroup (Fin 2) ℝ


end ArchR

open ArchR in


namespace ArchDatumR

variable {P : RealArchParam}

def dualFun (D : ArchDatumR P) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (ArchR.centralChar P g.det)⁻¹ * D.W g

end ArchDatumR

namespace ArchC


def psi (z : ℂ) : ℂ := exp (2 * (Real.pi : ℂ) * I * (2 * z.re : ℝ))


def IsK (k : Matrix (Fin 2) (Fin 2) ℂ) : Prop := k ∈ Matrix.unitaryGroup (Fin 2) ℂ


end ArchC

open ArchC in


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
