module
public import Theorem.Matrix.CentreCutSiegelSet
public import Theorem.Measure.ContractionDecay
public import Theorem.Matrix.SiegelCoordinates
public import Def.Measure_AdelicHaar
open MeasureTheory Set IsDedekindDomain NumberField Matrix Measure
open scoped ENNReal


public section

noncomputable section

namespace NumberField

namespace SiegelVolume

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates Matrix
  Matrix.AdelicLevel NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicCentre

variable (F : Type) [Field F]

section ArchEmbed

open scoped Classical in

def archPiMat (v₀ : InfinitePlace F) (g : Matrix (Fin 2) (Fin 2) v₀.Completion) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  Matrix.of fun i j =>
    (Function.update ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) v₀ (g i j) :
      InfiniteAdeleRing F)

end ArchEmbed

variable [NumberField F]

section AdelicEmbed

def infMat (M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((M i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
    AdeleRing (𝓞 F) F)

def archEmbed (v₀ : InfinitePlace F) : GL (Fin 2) v₀.Completion →* AdelicGL2 (𝓞 F) F where
  toFun g :=
    { val := infMat F (archPiMat F v₀ g)
      inv := infMat F (archPiMat F v₀ ((g⁻¹ : GL (Fin 2) v₀.Completion) : Matrix _ _ _))
      val_inv := by rw [← infMat_mul, ← archPiMat_mul, Units.mul_inv, archPiMat_one, infMat_one]
      inv_val := by rw [← infMat_mul, ← archPiMat_mul, Units.inv_mul, archPiMat_one, infMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; rw [archPiMat_one, infMat_one])
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; rw [archPiMat_mul, infMat_mul])

variable {F}

end AdelicEmbed

section Contraction

variable {F}

omit [NumberField F] in
def contraction (w : InfinitePlace F) (b : w.Completion) : AdelicGL2 (𝓞 F) F :=
  archEmbed F w (upperUnit (2⁻¹ : w.Completion) b 2 (inv_ne_zero (two_ne_zero_completion w))
    (two_ne_zero_completion w))

def xAt (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  xCoord (((archComponent F w (glArch (𝓞 F) F g) : GL (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) w.Completion).map (InfinitePlace.Completion.extensionEmbedding w))

end Contraction

section Capping

variable {F}

def capAt (c : ℝ) (P : Finset (InfinitePlace F)) (D : Set (AdelicGL2 (𝓞 F) F)) :
    Set (AdelicGL2 (𝓞 F) F) :=
  D ∩ {g | ∀ w ∈ P, localHeight (archComponent F w (glArch (𝓞 F) F g)) < 4 * c}


end Capping

end SiegelVolume

end NumberField

end
