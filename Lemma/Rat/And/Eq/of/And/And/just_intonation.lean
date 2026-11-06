import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Initialize.Tactic.Attr.Basic


/--
Wavelengths `λ` (period ∼ 1/frequency) in just intonation: small-integer pitch
ratios as string-length ratios.

This is a consequence of the Pythagorean tuning law (equal-tension strings:
frequency inversely proportional to length), which is the equal-tension special
case of [Mersenne's law](?module=Hyperreal.Eq_Mul_SqrtDiv.of.All_EqMul_Deriv_SinArctan.All_Eq_MulMul_Sin_Cos) `f ∝ (1/L)√(T/μ)`.
-/

@[path]
private lemma main
  [NeZero («λ_1» : ℚ)] [NeZero («λ_{{^\#}1}» : ℚ)] [NeZero («λ_2» : ℚ)] [NeZero («λ_{{^\#}2}» : ℚ)] [NeZero («λ_3» : ℚ)]
  [NeZero («λ_4» : ℚ)] [NeZero («λ_{{^\#}4}» : ℚ)] [NeZero («λ_5» : ℚ)] [NeZero («λ_{{^\#}5}» : ℚ)] [NeZero («λ_6» : ℚ)]
  [NeZero («λ_{\underset{\mathbf{\Large{.}}}{7}}» : ℚ)]
-- given
  («λ_7» «λ_{{^\#}6}» «λ_{\overset{\mathbf{\Large{.}}}{1}}» «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» «λ_{\overset{\mathbf{\Large{.}}}{2}}» «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» «λ_{\overset{\mathbf{\Large{.}}}{3}}» : ℚ)
  (h₀ :
    «λ_7» / «λ_{\underset{\mathbf{\Large{.}}}{7}}» = «λ_{\overset{\mathbf{\Large{.}}}{1}}» / «λ_1» ∧
      «λ_{\overset{\mathbf{\Large{.}}}{1}}» / «λ_1» = «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» / «λ_{{^\#}1}» ∧
      «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» / «λ_{{^\#}1}» = «λ_{\overset{\mathbf{\Large{.}}}{2}}» / «λ_2» ∧
      «λ_{\overset{\mathbf{\Large{.}}}{2}}» / «λ_2» = «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» / «λ_{{^\#}2}» ∧
      «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» / «λ_{{^\#}2}» = «λ_{\overset{\mathbf{\Large{.}}}{3}}» / «λ_3» ∧
      «λ_{\overset{\mathbf{\Large{.}}}{3}}» / «λ_3» = (1 : ℚ) / 2)
  (h₁ :
    «λ_{{^\#}4}» / «λ_{\underset{\mathbf{\Large{.}}}{7}}» = «λ_5» / «λ_1» ∧
      «λ_5» / «λ_1» = «λ_{{^\#}5}» / «λ_{{^\#}1}» ∧
      «λ_{{^\#}5}» / «λ_{{^\#}1}» = «λ_6» / «λ_2» ∧
      «λ_6» / «λ_2» = «λ_{{^\#}6}» / «λ_{{^\#}2}» ∧
      «λ_{{^\#}6}» / «λ_{{^\#}2}» = «λ_7» / «λ_3» ∧
      «λ_7» / «λ_3» = «λ_{\overset{\mathbf{\Large{.}}}{1}}» / «λ_4» ∧
      «λ_{\overset{\mathbf{\Large{.}}}{1}}» / «λ_4» = «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» / «λ_{{^\#}4}» ∧
      «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» / «λ_{{^\#}4}» = «λ_{\overset{\mathbf{\Large{.}}}{2}}» / «λ_5» ∧
      «λ_{\overset{\mathbf{\Large{.}}}{2}}» / «λ_5» = «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» / «λ_{{^\#}5}» ∧
      «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» / «λ_{{^\#}5}» = «λ_{\overset{\mathbf{\Large{.}}}{3}}» / «λ_6» ∧
      «λ_{\overset{\mathbf{\Large{.}}}{3}}» / «λ_6» = (2 : ℚ) / 3) :
-- imply
  («λ_{{^\#}1}» / «λ_1» = «λ_{{^\#}2}» / «λ_2» ∧ «λ_{{^\#}2}» / «λ_2» = «λ_{{^\#}4}» / «λ_4» ∧ «λ_{{^\#}4}» / «λ_4» = «λ_{{^\#}5}» / «λ_5» ∧ «λ_{{^\#}5}» / «λ_5» = «λ_{{^\#}6}» / «λ_6» ∧
      «λ_{{^\#}6}» / «λ_6» = (2 : ℚ) ^ 11 / 3 ^ 7) ∧
    («λ_1» / «λ_{\underset{\mathbf{\Large{.}}}{7}}» = «λ_2» / «λ_{{^\#}1}» ∧ «λ_2» / «λ_{{^\#}1}» = «λ_3» / «λ_{{^\#}2}» ∧ «λ_3» / «λ_{{^\#}2}» = «λ_4» / «λ_3» ∧ «λ_4» / «λ_3» = «λ_5» / «λ_{{^\#}4}» ∧
      «λ_5» / «λ_{{^\#}4}» = «λ_6» / «λ_{{^\#}5}» ∧ «λ_6» / «λ_{{^\#}5}» = «λ_7» / «λ_{{^\#}6}» ∧ «λ_7» / «λ_{{^\#}6}» = (3 : ℚ) ^ 5 / 2 ^ 8) ∧
    «λ_2» / «λ_1» = 8 / 9 ∧
    «λ_4» / «λ_1» = 3 / 4 := by
-- proof
  have hl1 := NeZero.ne «λ_1»
  have hl1s := NeZero.ne «λ_{{^\#}1}»
  have hl2 := NeZero.ne «λ_2»
  have hl2s := NeZero.ne «λ_{{^\#}2}»
  have hl3 := NeZero.ne «λ_3»
  have hl4 := NeZero.ne «λ_4»
  have hl4s := NeZero.ne «λ_{{^\#}4}»
  have hl5 := NeZero.ne «λ_5»
  have hl5s := NeZero.ne «λ_{{^\#}5}»
  have hl6 := NeZero.ne «λ_6»
  have hl7l := NeZero.ne «λ_{\underset{\mathbf{\Large{.}}}{7}}»
  obtain ⟨o7, o1d, o1ds, o2d, o2ds, o3d⟩ := h₀
  obtain ⟨f4s, f5, f5s, f6, f6s, f7, f1d, f1ds, f2d, f2ds, f3d⟩ := h₁
  have e1d : 2 * «λ_{\overset{\mathbf{\Large{.}}}{1}}» = «λ_1» := by
    have : «λ_{\overset{\mathbf{\Large{.}}}{1}}» / «λ_1» = (1 : ℚ) / 2 := o1d.trans (o1ds.trans (o2d.trans (o2ds.trans o3d)))
    field_simp [hl1] at this
    linear_combination this
  have e1ds : 2 * «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» = «λ_{{^\#}1}» := by
    have : «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» / «λ_{{^\#}1}» = (1 : ℚ) / 2 := o1ds.trans (o2d.trans (o2ds.trans o3d))
    field_simp [hl1s] at this
    linear_combination this
  have e2d : 2 * «λ_{\overset{\mathbf{\Large{.}}}{2}}» = «λ_2» := by
    have : «λ_{\overset{\mathbf{\Large{.}}}{2}}» / «λ_2» = (1 : ℚ) / 2 := o2d.trans (o2ds.trans o3d)
    field_simp [hl2] at this
    linear_combination this
  have e2ds : 2 * «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» = «λ_{{^\#}2}» := by
    have : «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» / «λ_{{^\#}2}» = (1 : ℚ) / 2 := o2ds.trans o3d
    field_simp [hl2s] at this
    linear_combination this
  have e3d : 2 * «λ_{\overset{\mathbf{\Large{.}}}{3}}» = «λ_3» := by
    field_simp [hl3] at o3d
    linear_combination o3d
  have e7 : 2 * «λ_7» = «λ_{\underset{\mathbf{\Large{.}}}{7}}» := by
    have : «λ_7» / «λ_{\underset{\mathbf{\Large{.}}}{7}}» = (1 : ℚ) / 2 := o7.trans (o1d.trans (o1ds.trans (o2d.trans (o2ds.trans o3d))))
    field_simp [hl7l] at this
    linear_combination this
  have g5 : 3 * «λ_5» = 2 * «λ_1» := by
    have : «λ_5» / «λ_1» = (2 : ℚ) / 3 :=
      f5.trans (f5s.trans (f6.trans (f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d))))))))
    field_simp [hl1] at this
    linear_combination this
  have g5s : 3 * «λ_{{^\#}5}» = 2 * «λ_{{^\#}1}» := by
    have : «λ_{{^\#}5}» / «λ_{{^\#}1}» = (2 : ℚ) / 3 :=
      f5s.trans (f6.trans (f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d)))))))
    field_simp [hl1s] at this
    linear_combination this
  have g6 : 3 * «λ_6» = 2 * «λ_2» := by
    have : «λ_6» / «λ_2» = (2 : ℚ) / 3 :=
      f6.trans (f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d))))))
    field_simp [hl2] at this
    linear_combination this
  have g6s : 3 * «λ_{{^\#}6}» = 2 * «λ_{{^\#}2}» := by
    have : «λ_{{^\#}6}» / «λ_{{^\#}2}» = (2 : ℚ) / 3 :=
      f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d)))))
    field_simp [hl2s] at this
    linear_combination this
  have g7 : 3 * «λ_7» = 2 * «λ_3» := by
    have : «λ_7» / «λ_3» = (2 : ℚ) / 3 := f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d))))
    field_simp [hl3] at this
    linear_combination this
  have g1d4 : 3 * «λ_{\overset{\mathbf{\Large{.}}}{1}}» = 2 * «λ_4» := by
    have : «λ_{\overset{\mathbf{\Large{.}}}{1}}» / «λ_4» = (2 : ℚ) / 3 := f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d)))
    field_simp [hl4] at this
    linear_combination this
  have g1ds : 3 * «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» = 2 * «λ_{{^\#}4}» := by
    have : «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}» / «λ_{{^\#}4}» = (2 : ℚ) / 3 := f1ds.trans (f2d.trans (f2ds.trans f3d))
    field_simp [hl4s] at this
    linear_combination this
  have hl5' := NeZero.ne «λ_5»
  have g2d5 : 3 * «λ_{\overset{\mathbf{\Large{.}}}{2}}» = 2 * «λ_5» := by
    have : «λ_{\overset{\mathbf{\Large{.}}}{2}}» / «λ_5» = (2 : ℚ) / 3 := f2d.trans (f2ds.trans f3d)
    field_simp [hl5'] at this
    linear_combination this
  have hl5s' := NeZero.ne «λ_{{^\#}5}»
  have g2ds : 3 * «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» = 2 * «λ_{{^\#}5}» := by
    have : «λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}» / «λ_{{^\#}5}» = (2 : ℚ) / 3 := f2ds.trans f3d
    field_simp [hl5s'] at this
    linear_combination this
  have hl6' := NeZero.ne «λ_6»
  have g3d6 : 3 * «λ_{\overset{\mathbf{\Large{.}}}{3}}» = 2 * «λ_6» := by
    field_simp [hl6'] at f3d
    linear_combination f3d
  have g4s : 3 * «λ_{{^\#}4}» = 2 * «λ_{\underset{\mathbf{\Large{.}}}{7}}» := by
    have : «λ_{{^\#}4}» / «λ_{\underset{\mathbf{\Large{.}}}{7}}» = (2 : ℚ) / 3 :=
      f4s.trans (f5.trans (f5s.trans (f6.trans (f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d)))))))))
    field_simp [hl7l] at this
    linear_combination this
  have h4p : 4 * «λ_4» = 3 * «λ_1» := by
    linear_combination 3 * e1d - 2 * g1d4
  have h2p : 9 * «λ_2» = 8 * «λ_1» := by
    linear_combination -9 * e2d + 6 * g2d5 + 4 * g5
  have h21s : 9 * «λ_{{^\#}2}» = 8 * «λ_{{^\#}1}» := by
    linear_combination -9 * e2ds + 6 * g2ds + 4 * g5s
  have h32 : 9 * «λ_3» = 8 * «λ_2» := by
    linear_combination -9 * e3d + 6 * g3d6 + 4 * g6
  have h31 : 81 * «λ_3» = 64 * «λ_1» := by
    linear_combination 9 * h32 + 8 * h2p
  have h7l : 8 * «λ_{\underset{\mathbf{\Large{.}}}{7}}» = 9 * «λ_{{^\#}1}» := by
    linear_combination -4 * g4s - 6 * g1ds + 9 * e1ds
  have h37 : 4 * «λ_3» = 3 * «λ_{\underset{\mathbf{\Large{.}}}{7}}» := by
    linear_combination 3 * e7 - 2 * g7
  have h3s : 32 * «λ_3» = 27 * «λ_{{^\#}1}» := by
    linear_combination 8 * h37 + 3 * h7l
  have h4s : 4 * «λ_{{^\#}4}» = 3 * «λ_{{^\#}1}» := by
    linear_combination 3 * e1ds - 2 * g1ds
  have h63 : 4 * «λ_6» = 3 * «λ_3» := by
    linear_combination 3 * e3d - 2 * g3d6
  have hl6s : «λ_{{^\#}6}» ≠ 0 := by
    have h : 2 * «λ_{{^\#}2}» ≠ 0 := mul_ne_zero (by norm_num) hl2s
    rw [← g6s] at h
    exact right_ne_zero_of_mul h
  have hl7 : «λ_7» ≠ 0 := by
    have h : «λ_{\underset{\mathbf{\Large{.}}}{7}}» ≠ 0 := hl7l
    rw [← e7] at h
    exact right_ne_zero_of_mul h
  have hsharp : 2187 * «λ_{{^\#}1}» = 2048 * «λ_1» := by
    linear_combination 32 * h31 - 81 * h3s
  have h17 : 243 * «λ_{\underset{\mathbf{\Large{.}}}{7}}» = 256 * «λ_1» := by
    linear_combination ((2187 / 9) * h7l + hsharp) / 8
  have h4 : «λ_4» / «λ_1» = 3 / 4 := by
    field_simp [hl1, hl4]
    linear_combination h4p
  have h2 : «λ_2» / «λ_1» = 8 / 9 := by
    field_simp [hl1, hl2]
    linear_combination h2p
  have hs : «λ_{{^\#}1}» / «λ_1» = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    field_simp [hl1, hl1s]
    norm_num
    linear_combination hsharp
  have hs2 : «λ_{{^\#}2}» / «λ_2» = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    have h2v : «λ_2» = (8 / 9) * «λ_1» := by
      field_simp [hl2]
      linear_combination h2p
    have h2sv : «λ_{{^\#}2}» = (8 / 9) * «λ_{{^\#}1}» := by
      field_simp [hl2s]
      linear_combination h21s
    rw [h2v, h2sv]
    field_simp [hl1, hl1s]
    linear_combination hsharp
  have hs4 : «λ_{{^\#}4}» / «λ_4» = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    have h4v : «λ_4» = (3 / 4) * «λ_1» := by
      field_simp [hl4]
      linear_combination h4p
    have h4sv : «λ_{{^\#}4}» = (3 / 4) * «λ_{{^\#}1}» := by
      field_simp [hl4s]
      linear_combination h4s
    rw [h4v, h4sv]
    field_simp [hl1, hl1s]
    linear_combination hsharp
  have hs5 : «λ_{{^\#}5}» / «λ_5» = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    have h5v : «λ_5» = (2 / 3) * «λ_1» := by
      field_simp [hl5']
      linear_combination g5
    have h5sv : «λ_{{^\#}5}» = (2 / 3) * «λ_{{^\#}1}» := by
      field_simp [hl5s']
      linear_combination g5s
    rw [h5v, h5sv]
    field_simp [hl1, hl1s]
    linear_combination hsharp
  have hs6 : «λ_{{^\#}6}» / «λ_6» = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    have h6v : «λ_6» = (2 / 3) * «λ_2» := by
      field_simp [hl6']
      linear_combination g6
    have h6sv : «λ_{{^\#}6}» = (2 / 3) * «λ_{{^\#}2}» := by
      field_simp [hl6s]
      linear_combination g6s
    have h2v : «λ_2» = (8 / 9) * «λ_1» := by
      field_simp [hl2]
      linear_combination h2p
    have h2sv : «λ_{{^\#}2}» = (8 / 9) * «λ_{{^\#}1}» := by
      field_simp [hl2s]
      linear_combination h21s
    rw [h6v, h6sv, h2v, h2sv]
    field_simp [hl1, hl1s]
    linear_combination hsharp
  have hd1 : «λ_1» / «λ_{\underset{\mathbf{\Large{.}}}{7}}» = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    field_simp [hl1, hl7l]
    norm_num
    linear_combination -h17
  have hcross : (8 / 9) * «λ_1» / «λ_{{^\#}1}» = (3 : ℚ) ^ 5 / 2 ^ 8 := calc
    _ = (8 / 9) * (2048 * «λ_1») / (2048 * «λ_{{^\#}1}») := by
      field_simp
    _ = (8 / 9) * (2187 * «λ_{{^\#}1}») / (2048 * «λ_{{^\#}1}») := by
      rw [← hsharp]
    _ = (8 / 9) * (2187 / 2048) := by
      field_simp [hl1s]
    _ = (3 : ℚ) ^ 5 / 2 ^ 8 := by
      norm_num
  have hd2 : «λ_2» / «λ_{{^\#}1}» = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h2v : «λ_2» = (8 / 9) * «λ_1» := by
      field_simp [hl2]
      linear_combination h2p
    simpa [h2v] using hcross
  have hd3 : «λ_3» / «λ_{{^\#}2}» = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h3v : «λ_3» = (8 / 9) * «λ_2» := by
      field_simp [hl3]
      linear_combination h32
    have h2v : «λ_2» = (8 / 9) * «λ_1» := by
      field_simp [hl2]
      linear_combination h2p
    have h2sv : «λ_{{^\#}2}» = (8 / 9) * «λ_{{^\#}1}» := by
      field_simp [hl2s]
      linear_combination h21s
    rw [h3v, h2v, h2sv]
    field_simp [hl1, hl1s]
    linear_combination -hsharp
  have hd4 : «λ_4» / «λ_3» = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h4v : «λ_4» = (3 / 4) * «λ_1» := by
      field_simp [hl4]
      linear_combination h4p
    have h3v : «λ_3» = (64 / 81) * «λ_1» := by
      field_simp [hl3]
      linear_combination h31
    rw [h4v, h3v]
    field_simp [hl1, hl3]
    norm_num
  have hd5 : «λ_5» / «λ_{{^\#}4}» = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h5v : «λ_5» = (2 / 3) * «λ_1» := by
      field_simp [hl5']
      linear_combination g5
    have h4sv : «λ_{{^\#}4}» = (3 / 4) * «λ_{{^\#}1}» := by
      field_simp [hl4s]
      linear_combination h4s
    rw [h5v, h4sv]
    field_simp [hl1, hl1s]
    linear_combination -hsharp
  have hd6 : «λ_6» / «λ_{{^\#}5}» = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h6v : «λ_6» = (3 / 4) * «λ_3» := by
      field_simp [hl6']
      linear_combination h63
    have h3v : «λ_3» = (64 / 81) * «λ_1» := by
      field_simp [hl3]
      linear_combination h31
    have h5sv : «λ_{{^\#}5}» = (2 / 3) * «λ_{{^\#}1}» := by
      field_simp [hl5s']
      linear_combination g5s
    rw [h6v, h3v, h5sv]
    convert hcross using 1
    ring
  have hd7 : «λ_7» / «λ_{{^\#}6}» = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h7v : «λ_7» = (2 / 3) * «λ_3» := by
      field_simp [hl7]
      linear_combination g7
    have h3v : «λ_3» = (64 / 81) * «λ_1» := by
      field_simp [hl3]
      linear_combination h31
    have h6sv : «λ_{{^\#}6}» = (2 / 3) * «λ_{{^\#}2}» := by
      field_simp [hl6s]
      linear_combination g6s
    have h2sv : «λ_{{^\#}2}» = (8 / 9) * «λ_{{^\#}1}» := by
      field_simp [hl2s]
      linear_combination h21s
    rw [h7v, h3v, h6sv, h2sv]
    convert hcross using 1
    ring
  refine ⟨⟨?_, ?_, ?_, ?_, hs6⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, hd7⟩, h2, h4⟩
  · simp [hs, hs2]
  · simp [hs2, hs4]
  · simp [hs4, hs5]
  · simp [hs5, hs6]
  · simp [hd1, hd2]
  · simp [hd2, hd3]
  · simp [hd3, hd4]
  · simp [hd4, hd5]
  · simp [hd5, hd6]
  · simp [hd6, hd7]


-- created on 2018-11-24
-- updated on 2026-11-04
