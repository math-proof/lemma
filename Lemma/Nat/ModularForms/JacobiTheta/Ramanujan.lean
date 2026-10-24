import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ModularForms.JacobiTheta.Ramanujan
open MetaMathlibExt


namespace MetaMathlibExt

/--
[ramanujanThetaTerm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma ramanujanThetaTerm_zero
  {a b : ℂ} :
-- imply
  ramanujanThetaTerm a b 0 = 1 := by
-- proof
  simp [ramanujanThetaTerm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanThetaTerm_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma ramanujanThetaTerm_one
  {a b : ℂ} :
-- imply
  ramanujanThetaTerm a b 1 = a := by
-- proof
  simp [ramanujanThetaTerm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanThetaTerm_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma ramanujanThetaTerm_neg_one
  {a b : ℂ} :
-- imply
  ramanujanThetaTerm a b (-1) = b := by
-- proof
  simp [ramanujanThetaTerm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanThetaTerm_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma ramanujanThetaTerm_neg
  {a b : ℂ}
  {n : ℤ} :
-- imply
  ramanujanThetaTerm a b (-n) = ramanujanThetaTerm b a n := by
-- proof
  unfold ramanujanThetaTerm
  have h₁ : (-n) * (-n + 1) / (2 : ℤ) = n * (n - 1) / 2 := by
    rw [show (-n) * (-n + 1) = n * (n - 1) by ring]
  have h₂ : (-n) * (-n - 1) / (2 : ℤ) = n * (n + 1) / 2 := by
    rw [show (-n) * (-n - 1) = n * (n + 1) by ring]
  rw [h₁, h₂, mul_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanTheta_summable_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma ramanujanTheta_summable_symm
  {a b : ℂ} :
-- imply
  Summable (ramanujanThetaTerm a b) ↔ Summable (ramanujanThetaTerm b a) := by
-- proof
  constructor
  · intro hab
    have h := (Equiv.neg ℤ).summable_iff.mpr hab
    simpa [Function.comp_def, ramanujanThetaTerm_neg] using h
  · intro hba
    have h := (Equiv.neg ℤ).summable_iff.mpr hba
    simpa [Function.comp_def, ramanujanThetaTerm_neg] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanThetaRaw_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma ramanujanThetaRaw_symm
  {a b : ℂ} :
-- imply
  ramanujanThetaRaw a b = ramanujanThetaRaw b a := by
-- proof
  unfold ramanujanThetaRaw
  have h : ∀ n : ℤ, ramanujanThetaTerm a b n = ramanujanThetaTerm b a (-n) :=
    fun n => (ramanujanThetaTerm_neg b a n).symm
  calc
    ∑' n : ℤ, ramanujanThetaTerm a b n =
      ∑' n : ℤ, ramanujanThetaTerm b a (-n) := by simp_rw [h]
    _ = ∑' n : ℤ, ramanujanThetaTerm b a n :=
      Equiv.tsum_eq (Equiv.neg ℤ) (fun n => ramanujanThetaTerm b a n)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanTheta_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma ramanujanTheta_symm
  {a b : ℂ}
-- given
  (h : Summable (ramanujanThetaTerm a b)) :
-- imply
  ramanujanTheta a b h =
    ramanujanTheta b a ((ramanujanTheta_summable_symm a b).mp h) := by
-- proof
  simpa [ramanujanTheta] using ramanujanThetaRaw_symm a b

end MetaMathlibExt

namespace MetaMathlibExt

/--
[not_summable_ramanujanThetaTerm_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma not_summable_ramanujanThetaTerm_one_one
  :
-- imply
  ¬Summable (ramanujanThetaTerm 1 1) := by
-- proof
  intro h
  have hnorm : Summable (fun _ : ℤ => (1 : ℝ)) := by
    simpa [ramanujanThetaTerm] using h.norm
  exact @not_finite ℤ inferInstance (Finite.of_summable_const zero_lt_one hnorm)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanThetaRaw_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
lemma ramanujanThetaRaw_one_one
  :
-- imply
  ramanujanThetaRaw 1 1 = 0 := by
-- proof
  exact tsum_eq_zero_of_not_summable not_summable_ramanujanThetaTerm_one_one

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
