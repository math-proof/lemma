import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z w : ℂ} :
-- imply
  im (z + w) = im z + im w := by
-- proof
  exact Complex.add_im z w


-- created on 2023-06-03
