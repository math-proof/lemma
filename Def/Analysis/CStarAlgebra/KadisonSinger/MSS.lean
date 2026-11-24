module
public import Def.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
public import Theorem.Real.CStarAlgebra.KadisonSinger.MixedCharPoly
public import Theorem.Complex.CStarAlgebra.KadisonSinger.Paving
public import Theorem.Polynomial.RealRooted
public import Theorem.Real.CStarAlgebra.KadisonSinger.Barrier
public import Theorem.Real.CStarAlgebra.KadisonSinger.RealStable
public import Theorem.Polynomial.Interlacing
public import Theorem.Matrix.Spectrum
public import Def.Analysis.CStarAlgebra.KadisonSinger.Paving
public import Def.Algebra.Polynomial.RealRooted.Part2
public import Def.Analysis.CStarAlgebra.KadisonSinger.Barrier
public import Def.Analysis.CStarAlgebra.KadisonSinger.RealStable
public import Def.Algebra.Polynomial.Interlacing
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MSS.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# The finite Marcus--Spielman--Srivastava bound

This file assembles interlacing families, mixed characteristic polynomials, and the barrier
estimate for finitely supported independent random vectors.
-/
namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

universe u

noncomputable def ksOuter {d : Type*} (u : d → ℂ) : Matrix d d ℂ :=
  Matrix.vecMulVec u (star u)

noncomputable def ksCovariance
    {m : ℕ} {d : Type*} [Fintype d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ) (i : Fin m) : Matrix d d ℂ :=
  ∑ a, p i a • ksOuter (v i a)

noncomputable def ksPartialMatrix
    {m : ℕ} {d : Type*} [Fintype d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ) (k : ℕ)
    (ω : (i : Fin m) → Fin (s i)) (i : Fin m) : Matrix d d ℂ :=
  if i.val < k then ksOuter (v i (ω i)) else ksCovariance p v i

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger
