import Lemma.AutomorphicForm.AutomorphicFnAt
import Lemma.LocalNewvector.ConductorDatum
import Lemma.AdelicDock.LocalEmbedding

open NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LocalNewvector

variable (F : Type*) [Field F] [NumberField F]

def AdelicFnCarrier : Type _ :=
  AdelicGL2 (𝓞 F) F → ℂ

namespace AdelicFnCarrier

variable {F}

def mk (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicFnCarrier F := φ

def toFn (φ : AdelicFnCarrier F) : AdelicGL2 (𝓞 F) F → ℂ := φ

@[simp] theorem toFn_mk (φ : AdelicGL2 (𝓞 F) F → ℂ) : (mk φ).toFn = φ := rfl

@[simp] theorem mk_toFn (φ : AdelicFnCarrier F) : mk φ.toFn = φ := rfl

@[ext] theorem ext {φ ψ : AdelicFnCarrier F} (h : ∀ g, φ.toFn g = ψ.toFn g) : φ = ψ :=
  funext h


@[simp] theorem toFn_zero : (0 : AdelicFnCarrier F).toFn = 0 := rfl

@[simp] theorem toFn_add (φ ψ : AdelicFnCarrier F) : (φ + ψ).toFn = φ.toFn + ψ.toFn := rfl

@[simp] theorem toFn_csmul (c : ℂ) (φ : AdelicFnCarrier F) : (c • φ).toFn = c • φ.toFn := rfl


@[simp] theorem toFn_smul (g : AdelicGL2 (𝓞 F) F) (φ : AdelicFnCarrier F) (x : AdelicGL2 (𝓞 F) F) :
    (g • φ).toFn x = φ.toFn (x * g) := rfl


theorem mk_ne_zero_of_ne_zero {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ≠ 0) : mk φ ≠ 0 :=
  fun h => hφ (congrArg toFn h)

end AdelicFnCarrier

variable {F}

def AdelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicFnCarrier F) :=
  Submodule.span ℂ {ψ | ∃ g : AdelicGL2 (𝓞 F) F, ψ = g • AdelicFnCarrier.mk φ}

theorem mk_mem_adelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicFnCarrier.mk φ ∈ AdelicSpanSubmodule φ :=
  Submodule.subset_span ⟨1, (one_smul _ _).symm⟩

theorem smul_mem_adelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    {ψ : AdelicFnCarrier F} (hψ : ψ ∈ AdelicSpanSubmodule φ) :
    g • ψ ∈ AdelicSpanSubmodule φ := by
  refine Submodule.span_induction
    (fun x ⟨h, hh⟩ => Submodule.subset_span ⟨g * h, by rw [hh, mul_smul]⟩)
    (by rw [smul_zero]; exact zero_mem _)
    (fun x y _ _ hx hy => by rw [smul_add]; exact add_mem hx hy)
    (fun c x _ hx => by rw [smul_comm]; exact Submodule.smul_mem _ c hx) hψ

def AdelicSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) : Type _ :=
  AdelicSpanSubmodule φ

namespace AdelicSpan

variable (φ : AdelicGL2 (𝓞 F) F → ℂ)

def mk (ψ : AdelicFnCarrier F) (hψ : ψ ∈ AdelicSpanSubmodule φ) : AdelicSpan φ :=
  ⟨ψ, hψ⟩

def toFn (ψ : AdelicSpan φ) : AdelicFnCarrier F :=
  (ψ : AdelicSpanSubmodule φ).val

@[ext] theorem ext {ψ₁ ψ₂ : AdelicSpan φ} (h : toFn φ ψ₁ = toFn φ ψ₂) : ψ₁ = ψ₂ :=
  Subtype.ext h


@[simp] theorem toFn_smul (g : AdelicGL2 (𝓞 F) F) (ψ : AdelicSpan φ) :
    toFn φ (g • ψ) = g • toFn φ ψ := rfl


def self : AdelicSpan φ :=
  mk φ (AdelicFnCarrier.mk φ) (mk_mem_adelicSpanSubmodule φ)

@[simp] theorem toFn_self : toFn φ (self φ) = AdelicFnCarrier.mk φ := rfl

theorem self_ne_zero_of_ne_zero (hφ : φ ≠ 0) : self φ ≠ 0 := by
  intro h
  exact AdelicFnCarrier.mk_ne_zero_of_ne_zero hφ (congrArg (toFn φ) h)

end AdelicSpan

variable (F)

theorem adelicSpan_self_one_ne_zero :
    AdelicSpan.self (F := F) (fun _ => (1 : ℂ)) ≠ 0 :=
  AdelicSpan.self_ne_zero_of_ne_zero _ (by intro h; exact one_ne_zero (congrFun h 1))

section PadicAction

variable (p : ℕ) [Fact p.Prime]


theorem AdelicFnCarrier.padic_smul_def (g : GL (Fin 2) ℚ_[p]) (φ : AdelicFnCarrier ℚ) :
    g • φ = (AdelicDock.padicToAdelic p g : AdelicGL2 (𝓞 ℚ) ℚ) • φ := rfl


theorem AdelicSpan.padic_smul_def (g : GL (Fin 2) ℚ_[p]) (ψ : AdelicSpan φ) :
    g • ψ = (AdelicDock.padicToAdelic p g : AdelicGL2 (𝓞 ℚ) ℚ) • ψ := rfl


theorem AdelicSpan.typeOf_hasNewvectorConductor (c : ℕ) :
    (HasNewvectorConductor p (AdelicSpan φ) c) = (HasNewvectorConductor p (AdelicSpan φ) c) := rfl

theorem AdelicSpan.typeOf_fixedSubmodule_padicK1 (n : ℕ) :
    (fixedSubmodule (padicK1 p n) (AdelicSpan φ) : Submodule ℂ (AdelicSpan φ))
      = fixedSubmodule (padicK1 p n) (AdelicSpan φ) := rfl

end PadicAction

end LocalNewvector

end
