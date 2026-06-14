"""Return the prefix of a parenthesized expression balanced from its opening '('."""
import sys
from pathlib import Path


def balanced_prefix(text: str, *, start: int = 0) -> str:
    """Return text[start : close+1] through the first ')' that balances text[start].

    Depth is counted from *start* (which must be '('). The first index where depth
    returns to zero is the closing parenthesis.
    """
    if start >= len(text) or text[start] != "(":
        raise ValueError("start position is not '('")

    depth = 0
    for i in range(start, len(text)):
        ch = text[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
            if depth < 0:
                raise ValueError(f"unbalanced ')' at index {i}")

    raise ValueError("no matching closing ')' found")


def search(text: str) -> str:
    """Return the balanced substring for input that starts with '('.

    Leading whitespace is skipped. Balancing begins at that first '('.
    """
    text = text.lstrip()
    if not text.startswith("("):
        raise ValueError("input must start with '(' after leading whitespace")
    return balanced_prefix(text)


def _read_input() -> str:
    if len(sys.argv) > 1:
        return Path(sys.argv[1]).read_text(encoding="utf-8")
    if not sys.stdin.isatty():
        return sys.stdin.read()
    raise SystemExit("usage: balanced_search.py <file>  (or pipe text on stdin)")


def main() -> None:
    sys.stdout.write(search(_read_input()))


if __name__ == "__main__":
    main()
