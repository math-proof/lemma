import sympy.sets.sets
import sympy.Basic
import Mathlib.Data.Real.Pointwise
import Lemma.Real.Inf.eq.Add
import Lemma.Real.Inf.eq.Mul.Sup.of.Lt_0
import Lemma.Real.EqSup.of.Lt


@[path]
private lemma main
  {a b m M : ℝ}
-- given
  (ha : a < 0)
  (h : m < M) :
-- imply
  sInf ((fun x => a * x + b) '' Set.Ioo m M) = a * M + b := by
-- proof
  have hne : (Set.Ioo m M).Nonempty := Set.nonempty_Ioo.mpr h
  have hb : BddBelow ((fun x : ℝ => x * a) '' Set.Ioo m M) :=
    ⟨M * a, fun z hz => by
      obtain ⟨x, hx, rfl⟩ := hz
      have h1 : 0 ≤ -a := by linarith
      have h2 : x * -a ≤ M * -a := mul_le_mul_of_nonneg_right hx.2.le h1
      simp only [mul_neg] at h2
      linarith⟩
  rw [show (fun x : ℝ => a * x + b) = (fun x : ℝ => x * a + b) from funext fun x => by rw [mul_comm a x]]
  have h1 : sInf ((fun x : ℝ => x * a + b) '' Set.Ioo m M)
      = sInf ((fun x : ℝ => x * a) '' Set.Ioo m M) + b :=
    Real.Inf.eq.Add (f := fun x : ℝ => x * a) hne hb
  have h2 : sInf ((fun x : ℝ => x * a) '' Set.Ioo m M)
      = a * sSup ((fun x : ℝ => x) '' Set.Ioo m M) :=
    Real.Inf.eq.Mul.Sup.of.Lt_0 (f := fun x : ℝ => x) ha
  have h3 : sSup ((fun x : ℝ => x) '' Set.Ioo m M) = sSup (Set.Ioo m M) := by
    rw [Set.image_id']
  rw [h1, h2, h3, Real.EqSup.of.Lt h]


-- created on 2020-01-22
