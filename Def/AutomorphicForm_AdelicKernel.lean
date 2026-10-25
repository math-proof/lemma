import Def.AutomorphicForm_GL2ConjugacyCells
import Def.AutomorphicForm_AdelicLsXi

set_option autoImplicit false

open Matrix

open scoped NumberField

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

section Kernel

variable {M : Type*} [AddCommMonoid M]

def adelicKernel (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ : GL (Fin 2) F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

def adelicKernelCentralPart (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ ∈ centralCell F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

def adelicKernelUnipotentPart (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ ∈ unipotentCell F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

def adelicKernelHyperbolicPart (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ ∈ hyperbolicCell F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

def adelicKernelEllipticPart (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ ∈ ellipticCell F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

end Kernel

def AdelicKernelLocalFiniteness : Prop :=
  ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C → ∀ x y : AdelicGL2 (𝓞 F) F,
    {γ : GL (Fin 2) F | x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ C}.Finite

end AutomorphicForm
