/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MSS.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
import Lemma.Real.CStarAlgebra.KadisonSinger.MixedCharPoly
import Lemma.Complex.CStarAlgebra.KadisonSinger.Paving
import Lemma.Polynomial.RealRooted
import Lemma.Real.CStarAlgebra.KadisonSinger.Barrier
import Lemma.Real.CStarAlgebra.KadisonSinger.RealStable
import Lemma.Polynomial.Interlacing
import Lemma.Matrix.Spectrum
import Def.Analysis.CStarAlgebra.KadisonSinger.Paving
import Def.Algebra.Polynomial.RealRooted.Part2
import Def.Analysis.CStarAlgebra.KadisonSinger.Barrier
import Def.Analysis.CStarAlgebra.KadisonSinger.RealStable
import Def.Algebra.Polynomial.Interlacing
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

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
