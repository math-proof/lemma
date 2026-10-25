import Lemma.AutomorphicForm.ProductionPinsGeneral
import Def.LanglandsTunnell_JLConverse
import Def.AutomorphicForm_ConstantTerm
import Lemma.AutomorphicForm.CarrierPins
import Def.NumberField_AdelicBox
import Lemma.NumberField.NormPowChar
import Lemma.LocalLanglands.HeckeCosetLocal
import Def.M4aHerbrand_IdeleClassVocab
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ConditionalProbability
import Lemma.AutomorphicForm.WhittakerCoefficient
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Lemma.NumberField.IdeleProductMeasure
import Lemma.AutomorphicForm.ArchType
import Lemma.AutomorphicForm.ArchWeightChar
import Lemma.AutomorphicForm.ViaCompactCuspNotion
import Def.LanglandsTunnell_JLSynthesis
import Abbrev.LanglandsTunnell_TorusTransform
import Notation.LanglandsTunnell_TorusTransform

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell.Converse

noncomputable section

section
open scoped WithZero
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology
namespace LanglandsTunnell.Converse.Ideles
variable {K : Type} [Field K] [NumberField K]
open scoped LanglandsTunnell_TorusTransform
theorem val_mul_inv_snd_apply (z : 𝔸ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (z : 𝔸).2 v * ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v = 1 :=
  congrArg (fun x : 𝔸 => x.2 v) z.mul_inv
end LanglandsTunnell.Converse.Ideles
end
end

section
open scoped WithZero
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology
namespace LanglandsTunnell.Converse.Ideles
variable {K : Type} [Field K] [NumberField K]
open scoped LanglandsTunnell_TorusTransform
theorem val_inv_mul_snd_apply (z : 𝔸ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v * (z : 𝔸).2 v = 1 :=
  congrArg (fun x : 𝔸 => x.2 v) z.inv_mul
end LanglandsTunnell.Converse.Ideles
end
end

section
open scoped WithZero
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology
namespace LanglandsTunnell.Converse.Ideles
variable {K : Type} [Field K] [NumberField K]
open scoped LanglandsTunnell_TorusTransform

def archProd (a : ∀ w : InfinitePlace K, (w.Completion)ˣ) (T : Finset (InfinitePlace K)) : 𝔸ˣ :=
  ∏ w ∈ T, archUnitHom w (a w)
end LanglandsTunnell.Converse.Ideles
end
end

section
open scoped WithZero
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology
namespace LanglandsTunnell.Converse.Ideles
variable {K : Type} [Field K] [NumberField K]
open scoped LanglandsTunnell_TorusTransform

def unitAt (v : HeightOneSpectrum (𝓞 K)) (z : 𝔸ˣ) : (v.adicCompletion K)ˣ where
  val := (z : 𝔸).2 v
  inv := ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v
  val_inv := val_mul_inv_snd_apply z v
  inv_val := val_inv_mul_snd_apply z v
end LanglandsTunnell.Converse.Ideles
end
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]

noncomputable def expAt (w : InfinitePlace K) (s : ℝ) : w.Completion :=
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm (Real.exp s)
  else (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (Complex.exp s)
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]
theorem norm_expAt (w : InfinitePlace K) (s : ℝ) : ‖expAt w s‖ = Real.exp s := by
  unfold expAt
  split_ifs with hw
  · have h := (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)
      ((ringEquivRealOfIsReal hw).symm (Real.exp s))
    rw [← h]
    change ‖ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm (Real.exp s))‖ = _
    rw [RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  · set hc := not_isReal_iff_isComplex.mp hw
    have h := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
      ((ringEquivComplexOfIsComplex hc).symm (Complex.exp s))
    rw [← h]
    change ‖ringEquivComplexOfIsComplex hc ((ringEquivComplexOfIsComplex hc).symm (Complex.exp s))‖ = _
    rw [RingEquiv.apply_symm_apply, Complex.norm_exp_ofReal]
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]
theorem expAt_ne_zero (w : InfinitePlace K) (s : ℝ) : expAt w s ≠ 0 := by
  intro h
  have := norm_expAt w s
  rw [h, norm_zero] at this
  exact (Real.exp_pos s).ne this
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]

noncomputable def expUnitAt (w : InfinitePlace K) (s : ℝ) : (w.Completion)ˣ := Units.mk0 _ (expAt_ne_zero w s)
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]
variable [NumberField K]
variable (K) in

noncomputable def archScale (t : ℝ) : (AdeleRing (𝓞 K) K)ˣ :=
  archProd (fun w => expUnitAt w (t / Module.finrank ℚ K)) Finset.univ
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles
theorem unitAt_mul (v : HeightOneSpectrum (𝓞 K)) (a b : (AdeleRing (𝓞 K) K)ˣ) :
    unitAt v (a * b) = unitAt v a * unitAt v b := Units.ext rfl
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles
theorem unitAt_one (v : HeightOneSpectrum (𝓞 K)) : unitAt v (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := Units.ext rfl
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles
theorem unitAt_inv (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ) : unitAt v a⁻¹ = (unitAt v a)⁻¹ :=
  Units.ext rfl
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles

def unitIdelesAt (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (AdeleRing (𝓞 K) K)ˣ where
  carrier := {a | ∀ v : ↥S, Valued.v (unitAt v.1 a : v.1.adicCompletion K) = 1}
  mul_mem' {a b} ha hb v := by
    show Valued.v (unitAt v.1 (a * b) : v.1.adicCompletion K) = 1
    rw [unitAt_mul, Units.val_mul, map_mul, ha v, hb v, one_mul]
  one_mem' v := by
    show Valued.v (unitAt v.1 1 : v.1.adicCompletion K) = 1
    rw [unitAt_one, Units.val_one, map_one]
  inv_mem' {a} ha v := by
    show Valued.v (unitAt v.1 a⁻¹ : v.1.adicCompletion K) = 1
    rw [unitAt_inv, Units.val_inv_eq_inv_val, map_inv₀, ha v, inv_one]
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

noncomputable def torusClass (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (NormOneQuot K) :=
  ((unitIdelesAt S).subgroupOf (normOneIdeles K)).map (QuotientGroup.mk' _)
end TorusClass
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal
theorem mem_torusClass_iff {S : Finset (HeightOneSpectrum (𝓞 K))} {q : NormOneQuot K} :
    q ∈ torusClass S ↔
      ∃ x : ↥(normOneIdeles K), (x : (AdeleRing (𝓞 K) K)ˣ) ∈ unitIdelesAt S ∧ QuotientGroup.mk x = q := by
  simp only [torusClass, Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply]
end TorusClass
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

noncomputable def torusLift {S : Finset (HeightOneSpectrum (𝓞 K))} (q : ↥(torusClass (K := K) S)) :
    ↥(normOneIdeles K) :=
  Classical.choose (mem_torusClass_iff.1 q.2)
end TorusClass
end
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section
namespace LanglandsTunnell.Converse.CuspSynthesis
open MeasureTheory Topology
section TorusMeasure
variable {K : Type} [Field K] [NumberField K]

@[reducible] def torusBorel (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSpace ↥(torusClass (K := K) S) :=
  borel _
end TorusMeasure
end LanglandsTunnell.Converse.CuspSynthesis
end

noncomputable section
namespace LanglandsTunnell.Converse.CuspSynthesis
open MeasureTheory Topology
section TorusMeasure
variable {K : Type} [Field K] [NumberField K]
theorem borelSpace_torusBorel (S : Finset (HeightOneSpectrum (𝓞 K))) :
    @BorelSpace ↥(torusClass (K := K) S) _ (torusBorel S) :=
  @BorelSpace.mk _ _ (torusBorel S) rfl
end TorusMeasure
end LanglandsTunnell.Converse.CuspSynthesis
end

noncomputable section
namespace LanglandsTunnell.Converse.CuspSynthesis
open MeasureTheory Topology
section TorusMeasure
variable {K : Type} [Field K] [NumberField K]

def torusPoint {S : Finset (HeightOneSpectrum (𝓞 K))} (g : AdelicGL2 (𝓞 K) K)
    (p : ↥(torusClass (K := K) S) × ℝ) : AdelicGL2 (𝓞 K) K :=
  diagOne (((torusLift p.1 : ↥(normOneIdeles K)) : (AdeleRing (𝓞 K) K)ˣ) * Ideles.archScale K p.2) * g
end TorusMeasure
end LanglandsTunnell.Converse.CuspSynthesis
end

namespace LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

section DualSeries

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
variable {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

open scoped Classical
open scoped WithZero
open LanglandsTunnell.TateLocal NumberField.StandardAddChar NumberField.InfinitePlace UnramifiedWhittaker

variable (K) in

def weylGL2 : GL (Fin 2) K where
  val := !![0, 1; -1, 0]
  inv := !![0, -1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NumberField K] in
theorem weylGL2_coe : ((weylGL2 K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

def weylA (d : JLData K S epsS ω) : GL (Fin 2) K := weylGL2 K * diagOne (-d.A)

theorem weylA_coe (d : JLData K S epsS ω) :
    ((weylA d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; (d.A : K), 0] := by
  refine Matrix.ext fun i j => ?_
  simp only [weylA, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, weylGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

def dualSeriesTerm (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) (α : Kˣ) : ℂ :=
  d.ad α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α * weylA d) * g)
    * dF.Wf (globalPoints (𝓞 K) K (diagOne α * weylA d) * g)

def dualSeries' (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∑' α : Kˣ, dualSeriesTerm d archR archC dR dC dF g α

end DualSeries

end

end LanglandsTunnell.Converse.CuspSynthesis
