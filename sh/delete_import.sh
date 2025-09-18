modules=(
    'sympy.core.relational:^ +denote '
    'sympy.core.logic:^ +mpr? \['
    'sympy.functions.elementary.integers:\b(is even|is odd|fract|sign|IntegerRing)\b|//'
    'sympy.tensor.tensor:\b(Tensor|Zeros|Ones|Indexed|Sliced)\b'
    'sympy.sets.sets:\b(Ioo|Ico|Iio|Icc|Iic|Ioc|Ici|Ioi|range)\b'
    'stdlib.Slice:Slice'
    'stdlib.SEq:≃'
    'stdlib.List:\b(List|substr|slice|enumerate|is constant|swap)\b'
)

for entry in "${modules[@]}"; do
    # Split the entry into module and pattern
    module="${entry%%:*}"
    pattern="${entry#*:}"
    # Escape dots in the module name for regex
    escaped_module="${module//./\\.}"
    # Find files importing the module, then filter those not containing the pattern
    grep -rlZ --include='*.lean' --exclude='*.echo.lean' -E "^import $escaped_module$" Lemma \
    | xargs -0 grep -LZ -E "$pattern" \
    | while IFS= read -r -d $'\0' file; do
        echo "Processing file: $file"
        echo "The following line will be removed:"
        grep -nE "^import $escaped_module$" "$file"
        sed -i -E "/^import $escaped_module$/d" "$file"
    done
done
