import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.SylvesterInertia
open MetaMathlibExt


/--
[sylvester_law_of_inertia](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SylvesterInertia.lean)
-/
@[path]
private lemma sylvester_law_of_inertia_eq
  [Fintype n] [DecidableEq n]
  {A B P : Matrix n n ℝ}
-- given
  (hA : A.IsHermitian)
  (hB : B.IsHermitian)
  (hP : IsUnit P.det)
  (hcong : B = P.transpose * A * P) :
-- imply
  (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card =
    (Finset.univ.filter (fun i => 0 < hB.eigenvalues i)).card ∧
    (Finset.univ.filter (fun i => hA.eigenvalues i < 0)).card =
    (Finset.univ.filter (fun i => hB.eigenvalues i < 0)).card ∧
    (Finset.univ.filter (fun i => hA.eigenvalues i = 0)).card =
    (Finset.univ.filter (fun i => hB.eigenvalues i = 0)).card := by
-- proof
  apply MetaMathlibExt.sylvester_law_of_inertia hA hB P hP hcong


-- created on 2026-10-20
