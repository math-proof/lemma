import sympy.sets.sets
import sympy.Basic
import Mathlib.Analysis.Real.Sqrt
import Lemma.Real.EqInf.of.Lt


@[path]
private lemma main
  {m M : ℝ}
-- given
  (hm : m ≥ 0)
  (h : m < M) :
-- imply
  sInf ((fun x => x ^ 2) '' Set.Ioo m M) = m ^ 2 := by
-- proof
  have hM : 0 ≤ M := hm.trans (le_of_lt h)
  have hkey : (fun x => x ^ 2) '' Set.Ioo m M = Set.Ioo (m ^ 2) (M ^ 2) := by
    ext y
    constructor
    ·
      rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨(sq_lt_sq₀ hm (by linarith : 0 ≤ x)).mpr hx1,
        (sq_lt_sq₀ (hm.trans (le_of_lt hx1)) hM).mpr hx2⟩
    ·
      rintro ⟨hy1, hy2⟩
      have hy0 : 0 ≤ y := (lt_of_le_of_lt (by positivity : 0 ≤ m ^ 2) hy1).le
      refine ⟨√y, ⟨Real.lt_sqrt hm |>.mpr hy1, ?_⟩, Real.sq_sqrt hy0⟩
      calc _ < √(M ^ 2) := Real.sqrt_lt_sqrt hy0 hy2
        _ = M := Real.sqrt_sq hM
  have h2 : m ^ 2 < M ^ 2 := (sq_lt_sq₀ hm hM).mpr h
  rw [hkey, Real.EqInf.of.Lt h2]


-- created on 2019-07-02
-- updated on 2023-05-20
