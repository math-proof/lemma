module

public import Theorem.Matrix.CubicInduction_Carrier
public import Def.LanglandsTunnell_CubicInduction_HeckeDatum
public import Theorem.Matrix.CubicInduction_Growth
public import Theorem.Matrix.CubicInduction_IotaTorus
public import Theorem.Matrix.CubicInduction_Congruence
public import Theorem.Matrix.CubicInduction_TorusValues
public import Theorem.Measure.WhittakerCoefficient
public import Theorem.Measure.TateGlobalZeta
public import Theorem.Matrix.SmoothingKernel
public import Structure.LanglandsTunnell_CubicInduction_Structure

public noncomputable section

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory Measure

noncomputable section

namespace LanglandsTunnell.CubicInduction

export AutomorphicForm (transposeInvN coe_transposeInvN)

universe u v w

section LocalWhittaker

variable {F : Type u} [CommRing F] {R : Type v} [CommRing R]


public theorem mem_gl3PsiWhittakerFnSpace_iff (ψ : AddChar F R) (W : GL (Fin 3) F → R) :
    W ∈ gl3PsiWhittakerFnSpace F R ψ ↔ IsGL3PsiWhittakerFn ψ W := Iff.rfl


public theorem rightTranslate_mem_gl3PsiWhittakerFnSpace (ψ : AddChar F R) (g : GL (Fin 3) F)
    {W : GL (Fin 3) F → R} (hW : W ∈ gl3PsiWhittakerFnSpace F R ψ) :
    gl3AmbientRightTranslate g W ∈ gl3PsiWhittakerFnSpace F R ψ := by
  refine (mem_gl3PsiWhittakerFnSpace_iff ψ _).mpr ?_
  intro x y z h
  show W (upperUnipotent3 x y z * h * g) = ψ (x + y) * W (h * g)
  rw [mul_assoc]
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ W).mp hW x y z (h * g)

variable {V : Type w} [AddCommGroup V] [Module R V]


end LocalWhittaker

section Cyclic

variable {F : Type u} [CommRing F] {R : Type v} [CommRing R]


public theorem gl3CyclicSubspace_zero : gl3CyclicSubspace (0 : GL (Fin 3) F → R) = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact map_zero _


public theorem hasWhittakerMultOne_zero [Nontrivial R] (ψ : AddChar F R) :
    HasWhittakerMultOne ψ (0 : GL (Fin 3) F → R) := by
  have hV : ∀ v : gl3CyclicSubspace (0 : GL (Fin 3) F → R), v = 0 := fun v =>
    Subtype.ext ((Submodule.eq_bot_iff _).mp gl3CyclicSubspace_zero _ v.2)
  haveI : Subsingleton (gl3WhittakerFunctionalSpace (gl3CyclicRep (0 : GL (Fin 3) F → R)) ψ) :=
    ⟨fun a b => Subtype.ext (LinearMap.ext fun v => by rw [hV v, map_zero, map_zero])⟩
  unfold HasWhittakerMultOne GL3WhittakerUniquenessStatement
  rw [rank_subsingleton']
  exact zero_le_one


end Cyclic

section Global

open AutomorphicForm Measure Matrix

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]


open scoped Classical in


attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel


public theorem not_isCuspidalAlongP21_one (pins : CarrierPins ℚ)
    (h : @IsProbabilityMeasure _ pins.nS pins.ν) :
    ¬ IsCuspidalAlongP21 pins (fun _ => (1 : ℂ)) := by
  letI := pins.nS
  haveI := h
  intro hc
  have h1 := hc 1
  simp at h1

