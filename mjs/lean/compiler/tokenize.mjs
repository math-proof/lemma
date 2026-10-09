/**
 * Mirrors `LeanParser::build` tokenization in `php/parser/lean.php`:
 *   $this->tokens = array_map(fn($args) => $args[0][0], std\matchAll('/\w+|\W/u', $text));
 */
export function tokenizeLeanSource(text) {
  let s = text;
  if (!s.endsWith('\n')) s += '\n';
  const re = /\w+|\W/gu;
  const out = [];
  let m;
  while ((m = re.exec(s)) !== null) {
    out.push(m[0]);
  }
  return out;
}
