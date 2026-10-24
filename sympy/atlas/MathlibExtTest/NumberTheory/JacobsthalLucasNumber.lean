/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/JacobsthalLucasNumber.lean -/


import sympy.atlas.NumberTheory.JacobsthalLucasNumber


namespace MetaMathlibExt

example : jacobsthalLucasNumber 0 = 2 := rfl
example : jacobsthalLucasNumber 1 = 1 := rfl
example : jacobsthalLucasNumber 2 = 5 := rfl
example : jacobsthalLucasNumber 3 = 7 := rfl
example : jacobsthalLucasNumber 4 = 17 := rfl
example : jacobsthalLucasNumber 5 = 31 := rfl

example (n : ℕ) :
    jacobsthalLucasNumber (n + 2) =
      jacobsthalLucasNumber (n + 1) + 2 * jacobsthalLucasNumber n := rfl

#print axioms MetaMathlibExt.jacobsthalLucasNumber

end MetaMathlibExt
