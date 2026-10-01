import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z w : ℂ} :
-- imply
  im z + im w = im (z + w) := by
-- proof
  exact (Complex.add_im z w).symm


-- created on 2023-06-03
