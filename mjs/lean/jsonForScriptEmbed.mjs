/**
 * Serialize an object for embedding inside `<script>` so the browser does not
 * treat `</script>`, `<`, or line/paragraph separators as HTML/JS syntax breaks.
 */
export function jsonForScriptEmbed(obj) {
  return JSON.stringify(obj)
    .replace(/</g, '\\u003c')
    .replace(/\u2028/g, '\\u2028')
    .replace(/\u2029/g, '\\u2029');
}
