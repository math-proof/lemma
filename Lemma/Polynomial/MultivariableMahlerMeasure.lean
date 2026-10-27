import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Polynomial.MultivariableMahlerMeasure.Part5

open MultivariableMahlerMeasure.MetaMathlibExt

/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma real_sum_zero_eq
-- given
  (θ : Fin n → ℝ) :
-- imply
  realSum θ 0 = 0 := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.realSum_zero θ


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma real_sum_add_eq
-- given
  (θ : Fin n → ℝ) (a b : Fin n → ℤ) :
-- imply
  realSum θ (a + b) = realSum θ a + realSum θ b := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.realSum_add θ a b


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma torus_character_zero_eq
-- given
  (θ : Fin n → ℝ) :
-- imply
  torusCharacter θ 0 = 1 := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.torusCharacter_zero θ


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma torus_character_add_eq
-- given
  (θ : Fin n → ℝ) (a b : Fin n → ℤ) :
-- imply
  torusCharacter θ (a + b) = torusCharacter θ a * torusCharacter θ b := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.torusCharacter_add θ a b


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma torus_eval_single_zero_eq
-- given
  (θ : Fin n → ℝ) (c : ℂ) :
-- imply
  torusEval θ (AddMonoidAlgebra.single 0 c) = c := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.torusEval_single_zero θ c


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma torus_eval_single_eq
-- given
  (θ : Fin n → ℝ) (c : ℂ) (e : Fin n → ℤ) :
-- imply
  torusEval θ (AddMonoidAlgebra.single e c) = c * torusCharacter θ e := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.torusEval_single θ c e


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma logarithmic_mahler_measure_const_eq
-- given
  (c : ℂ) :
-- imply
  logarithmicMahlerMeasure (AddMonoidAlgebra.single (0 : Fin m → ℤ) c) = Real.log ‖c‖ := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.logarithmicMahlerMeasure_const c


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma logarithmic_mahler_measure_zero_eq :
-- imply
  logarithmicMahlerMeasure (0 : AddMonoidAlgebra ℂ (Fin m → ℤ)) = 0 := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.logarithmicMahlerMeasure_zero


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma bridge_laurent_single_eq
-- given
  (c : ℂ) (k : ℤ) :
-- imply
  bridgeLaurent (AddMonoidAlgebra.single (fun _ => k) c) = AddMonoidAlgebra.single k c := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.bridgeLaurent_single c k


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma bridge_laurent_C_eq
-- given
  (c : ℂ) :
-- imply
  bridgeLaurent (AddMonoidAlgebra.single (0 : Fin 1 → ℤ) c) = LaurentPolynomial.C c := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.bridgeLaurent_C c


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma bridge_laurent_T_eq
-- given
  (k : ℤ) :
-- imply
  bridgeLaurent (AddMonoidAlgebra.single (fun _ => k) 1) = LaurentPolynomial.T k := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.bridgeLaurent_T k


/--
[MultivariableMahlerMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/MultivariableMahlerMeasure.lean)
-/
@[path]
private lemma logarithmic_mahler_measure_one_eq :
-- imply
  logarithmicMahlerMeasure (1 : AddMonoidAlgebra ℂ (Fin m → ℤ)) = 0 := by
-- proof
  apply MultivariableMahlerMeasure.MetaMathlibExt.logarithmicMahlerMeasure_one


-- created on 2026-10-10
