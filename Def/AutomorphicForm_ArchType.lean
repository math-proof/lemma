import Def.AutomorphicForm_RowIsometryInvariance
import Abbrev.AutomorphicForm_ArchType

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField AdelicLevel IsDedekindDomain Matrix

open scoped Classical

namespace AutomorphicForm

section MatrixFurniture

variable (F : Type) [Field F]

noncomputable section

def archMatrixUpdate (w : InfinitePlace F) (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  (archMatrixPiEquiv F).symm (Function.update 1 w m)

def archMatrixInclHom (w : InfinitePlace F) :
    Matrix (Fin 2) (Fin 2) w.Completion →* Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) where
  toFun := archMatrixUpdate F w
  map_one' := archMatrixUpdate_one F w
  map_mul' := archMatrixUpdate_mul F w

def archGLIncl (w : InfinitePlace F) :
    GL (Fin 2) w.Completion →* GL (Fin 2) (InfiniteAdeleRing F) :=
  Units.map (archMatrixInclHom F w)

end

end MatrixFurniture


section AdelicInclusion

variable (F : Type) [Field F] [NumberField F]

noncomputable section

def adelicMatrixProdEquiv :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) ≃+*
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) ×
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) where
  toFun M := ((RingHom.fst _ _).mapMatrix M, (RingHom.snd _ _).mapMatrix M)
  invFun p := Matrix.of fun i j => (p.1 i j, p.2 i j)
  left_inv M := by ext i j; rfl
  right_inv p := by ext i j <;> rfl
  map_mul' M N := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]; exact map_mul _ M N
    · simp only [Prod.snd_mul]; exact map_mul _ M N
  map_add' M N := rfl

def adelicArchGLIncl : GL (Fin 2) (InfiniteAdeleRing F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (MonoidHom.id _) (1 : _ →* GL (Fin 2) _)

def adelicArchGLInclAt (w : InfinitePlace F) :
    GL (Fin 2) w.Completion →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (archGLIncl F w)

end

end AdelicInclusion

section Predicate

variable (F : Type) [Field F] [NumberField F]

noncomputable def archRowIsometryAt (w : InfinitePlace F) : Subgroup (GL (Fin 2) (InfiniteAdeleRing F)) :=
  (rowIsometrySubgroup w.Completion).map (archGLIncl F w)

def HasArchCharacterAt (w : InfinitePlace F) (χ : rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ k : rowIsometrySubgroup w.Completion, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
      = (χ k : ℂ) * φ g

def HasArchType (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, HasArchCharacterAt F w (χ w) φ

end Predicate

end AutomorphicForm
