/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MultipleBinomialTransform.lean -/

import sympy.atlas.Combinatorics.Enumerative.FallingKBinomialTransform
namespace MetaMathlibExt

/-- The `n`-fold binomial transform of an integer sequence, obtained by applying
`binomialTransform` successively `n` times. The zero-fold transform is the identity.

Sources:

* Jiaqiang Pan, *Multiple Binomial Transforms and Families of Integer Sequences*,
  Journal of Integer Sequences 13 (2010), lines 128–150:
  <https://cs.uwaterloo.ca/journals/JIS/VOL13/Pan/pan8.tex>.
* Jiaqiang Pan, *Some Properties of the Multiple Binomial Transform and the Hankel Transform of
  Shifted Sequences*, Journal of Integer Sequences 14 (2011), lines 104–118:
  <https://cs.uwaterloo.ca/journals/JIS/VOL14/Pan/pan12.tex>.

The archived sources have SHA-256 values
`1d0b3a962f3ebef6a30b664f7979f89bf9e80f8adddad71bfdbeef541daf0791` and
`b48df480b12f77923455a0db85c255217715a73eba7c7ad92ceb5855d434ef26`.

Concept `jis_term_c157679dc9eb88c4ba264101`; source statements
`jis_565fc7c3315ad99b5942cc67` and `jis_a569298bba80b28850af1658`.
-/
def multipleBinomialTransform : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, a => a
  | n + 1, a => binomialTransform (multipleBinomialTransform n a)

end MetaMathlibExt
