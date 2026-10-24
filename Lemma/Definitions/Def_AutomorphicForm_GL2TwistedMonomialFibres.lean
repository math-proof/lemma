import Lemma.Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open MeasureTheory

noncomputable section

namespace AutomorphicForm.GL2Twisted

def invFrobSq (g : GL (Fin 2) ℂ) : ℝ :=
  (Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ))).re

def invTraceNorm (g : GL (Fin 2) ℂ) : ℂ :=
  Matrix.trace ((g * conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)

def invSecondRe (g : GL (Fin 2) ℂ) : ℝ :=
  (Matrix.trace (((g * conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
    ((g : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ)))).re

def invAbsDet (g : GL (Fin 2) ℂ) : ℝ :=
  ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ)‖

def invDifference (g : GL (Fin 2) ℂ) : ℝ :=
  (invSecondRe g - invFrobSq g * (invTraceNorm g).re + 2 * invAbsDet g ^ 2) / invAbsDet g

def monomialInput (i l : ℕ) (g : GL (Fin 2) ℂ) : ℝ :=
  ((invFrobSq g - (invTraceNorm g).re + invDifference g) / (2 * (invFrobSq g + 2 * invAbsDet g))) ^ i *
    ((invFrobSq g - (invTraceNorm g).re - invDifference g) / (2 * (invFrobSq g - 2 * invAbsDet g))) ^ l

def fibreMonomialFactor (i l : ℕ) (T d x : ℝ) : ℝ :=
  (T - x) ^ (i + l) / ((T + 2 * d) ^ i * (T - 2 * d) ^ l)

def fibreArcIntegral (i l : ℕ) (Ψ : ℝ) : ℝ :=
  ∫ ψ in (-(Ψ / 2))..(Ψ / 2), Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)

def ellipticArcLength (T r θ : ℝ) : ℝ :=
  Real.arccos ((2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ))

def ellipticFibreTerm (i l : ℕ) (T r θ : ℝ) : ℂ :=
  ((4 * Real.pi * Real.sin θ / r : ℝ) : ℂ) *
    ((fibreMonomialFactor i l T r (2 * r * Real.cos θ) * fibreArcIntegral i l (ellipticArcLength T r θ) : ℝ) : ℂ)

def splitFibreTerm (i l : ℕ) (T a₁ a₂ : ℝ) : ℂ :=
  ((1 / 2 * fibreMonomialFactor i l T (Real.sqrt (a₁ * a₂)) (a₁ + a₂) * fibreArcIntegral i l (2 * Real.pi) : ℝ) : ℂ)

def ellipticFibreSide (i l : ℕ) (c : ℝ → ℂ) (r θ : ℝ) : ℂ :=
  ∫ T in Set.Ioi (2 * r), c T * ellipticFibreTerm i l T r θ

def splitFibreSide (i l : ℕ) (c : ℝ → ℂ) (a₁ a₂ : ℝ) : ℂ :=
  ∫ T in Set.Ioi (a₁ + a₂), c T * splitFibreTerm i l T a₁ a₂

end AutomorphicForm.GL2Twisted

end
