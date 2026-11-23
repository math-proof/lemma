/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Matrix/Spectrum.lean -/

module

public import Theorem.Matrix.Spectrum

@[expose] public section

open scoped ComplexOrder Matrix.Norms.L2Operator


namespace MathlibExtTest.Analysis.Matrix.Spectrum

def positiveDiagonal : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 : ℂ), 2]

end MathlibExtTest.Analysis.Matrix.Spectrum
