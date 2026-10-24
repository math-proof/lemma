/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Module/QuillenSuslin.lean -/


import sympy.atlas.Algebra.Module.QuillenSuslin

-- A finitely generated projective module over a two-variable rational polynomial ring is free.
example {M : Type*} [AddCommGroup M]
    [Module (MvPolynomial (Fin 2) ℚ) M]
    [Module.Finite (MvPolynomial (Fin 2) ℚ) M]
    [Module.Projective (MvPolynomial (Fin 2) ℚ) M] :
    Module.Free (MvPolynomial (Fin 2) ℚ) M :=
  MathlibExt.Algebra.Module.QuillenSuslinWanted.quillen_suslin
