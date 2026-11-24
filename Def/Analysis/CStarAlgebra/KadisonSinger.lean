module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Def.Analysis.CStarAlgebra.KadisonSinger.Paving
public import Theorem.Complex.CStarAlgebra.KadisonSinger.Paving
public import Theorem.Real.CStarAlgebra.KadisonSinger.MSS
public import Def.Analysis.CStarAlgebra.KadisonSinger.MSS
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
namespace MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/-- Diagonal `0-1` projection onto colour `j` of `c : Fin n → Fin r`. -/
noncomputable def pavingProj (n r : ℕ) (c : Fin n → Fin r) (j : Fin r) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => if c i = j then (1 : ℂ) else 0)

end MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted
