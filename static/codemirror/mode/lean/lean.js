// CodeMirror, copyright (c) by Marijn Haverbeke and others
// Distributed under an MIT license: https://codemirror.net/5/LICENSE
import { tactics } from "./tactics.js"

(function(mod) {
  if (typeof exports == 'object' && typeof module == 'object') // CommonJS
    mod(require("../../lib/codemirror"));
  else if (typeof define == 'function' && define.amd) // AMD
    define(["../../lib/codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {
  "use strict";

  function wordRegexp(words) {
    return new RegExp("^((" + words.join(")|(") + "))\\b");
  }

  var wordOperators = wordRegexp(['and', 'or', 'not', 'is']);
  var commonKeywords = [
    'assert', 'abs', 'eval', 'id', 'map', 'max', 'min', 'this', 'sorry'
  ];
  var commonBuiltins = [
    'import', 'open', 
    'def', 'else', 'catch', 'finally', 'then',
    'for', 'from', 'if', 'fun',
    'break', 'class', 'continue',
    'False', 'True', 'false', 'true', 
    'have', 'let', 'at', 'using', 'generalizing', 'by', 'show',
    'private', 'protected', 'public', 'noncomputable', 'unsafe', 'partial', 
    'return', 'try', 'with', 'in',
    'lemma', 'theorem', 'example', 'axiom',
    'constant', 'variable', 
    "isn't", 'calc',
    ...tactics
  ];
  CodeMirror.registerHelper('hintWords', 'lean', commonKeywords.concat(commonBuiltins).concat(['exec', 'print']));

  function top(state) {
    return state.scopes[state.scopes.length - 1];
  }

  CodeMirror.defineMode('lean', function(conf, parserConf) {
    var ERRORCLASS = 'error';
    var delimiters = parserConf.delimiters || parserConf.singleDelimiters || /^[\(\)\[\]\{\}@,:`=;\.\\⟨⟩·]/;
    var operators = [
      parserConf.singleOperators, 
      parserConf.doubleOperators, 
      parserConf.doubleDelimiters, 
      parserConf.tripleDelimiters,
      parserConf.operators || /^([-+*/%\/&|^]=?|[<>≤≥=≠↔≡≃≍∣←→↦∈∉∩∪⋂⋃⊓⊔∧∨∀∃×÷⊂⊃⊆⊇∘▸⊙⊕⊖⊗⊘⊚⊛⊜⊝∑∏]+|\/\/=?|\*\*=?|!=|[~!@]|\.\.\.)/
    ];
    for (var i = 0; i < operators.length; i++) 
      if (!operators[i]) 
        operators.splice(i--, 1)
    var hangingIndent = parserConf.hangingIndent || conf.indentUnit;
    var myKeywords = commonKeywords, myBuiltins = commonBuiltins;
    if (parserConf.extra_keywords != undefined)
      myKeywords = myKeywords.concat(parserConf.extra_keywords);

    if (parserConf.extra_builtins != undefined)
      myBuiltins = myBuiltins.concat(parserConf.extra_builtins);

    var identifiers = parserConf.identifiers || /^[_\p{L}][\p{L}\p{N}_'!?]+/u;
    myKeywords = myKeywords.concat(['nonrec', 'None', 'aiter', 'anext', 'async', 'await', 'match', 'case']);
    myBuiltins = myBuiltins.concat(['ascii', 'bytes', 'exec', 'print']);
    var stringPrefixes = new RegExp("^(([rbuf]|(br)|(rb)|(fr)|(rf))?('{3}|\"{3}|[\"]))", 'i');

    var keywords = wordRegexp(myKeywords);
    var builtins = wordRegexp(myBuiltins);

    // tokenizers
    function tokenBase(stream, state) {
      var sol = stream.sol() && state.lastToken != "\\"
      if (sol) state.indent = stream.indentation()
      // Handle scope changes
      if (sol && top(state).type == 'lean') {
        var scopeOffset = top(state).offset;
        if (stream.eatSpace()) {
          var lineOffset = stream.indentation();
          if (lineOffset > scopeOffset)
            pushPyScope(state);
          else if (lineOffset < scopeOffset && dedent(stream, state) && stream.peek() != "#")
            state.errorToken = true;
          return null;
        } else {
          var style = tokenBaseInner(stream, state);
          if (scopeOffset > 0 && dedent(stream, state))
            style += " " + ERRORCLASS;
          return style;
        }
      }
      return tokenBaseInner(stream, state);
    }

    function tokenBlockComment(stream, state) {
      var ch;
      while ((ch = stream.next()) != null) {
        if (ch === '-' && stream.eat('/')) {
          state.tokenize = tokenBase;
          break;
        }
      }
      return 'comment';
    }

    function tokenBaseInner(stream, state, inFormat) {
      if (stream.eatSpace()) return null;

      // Handle Comments
      if (!inFormat && stream.match(/^ *--.*/)) return 'comment';
      if (!inFormat && stream.match('/-')) {
        state.tokenize = tokenBlockComment;
        return "comment";
      }

      // Handle Number Literals
      if (stream.match(/^[0-9\.]/, false)) {
        var floatLiteral = false;
        // Floats
        if (stream.match(/^[\d_]*\.\d+(e[\+\-]?\d+)?/i)) { floatLiteral = true; }
        if (stream.match(/^[\d_]+\.\d*/)) { floatLiteral = true; }
        if (stream.match(/^\.\d+/)) { floatLiteral = true; }
        if (floatLiteral) {
          // Float literals may be 'imaginary'
          stream.eat(/J/i);
          return 'number';
        }
        // Integers
        var intLiteral = false;
        // Hex
        if (stream.match(/^0x[0-9a-f_]+/i)) intLiteral = true;
        // Binary
        if (stream.match(/^0b[01_]+/i)) intLiteral = true;
        // Octal
        if (stream.match(/^0o[0-7_]+/i)) intLiteral = true;
        // Decimal
        if (stream.match(/^[1-9][\d_]*(e[\+\-]?[\d_]+)?/)) {
          // Decimal literals may be 'imaginary'
          stream.eat(/J/i);
          // TODO - Can you have imaginary longs?
          intLiteral = true;
        }
        // Zero by itself with no other piece of number.
        if (stream.match(/^0(?![\dx])/i)) intLiteral = true;
        if (intLiteral) {
          // Integer literals may be 'long'
          stream.eat(/L/i);
          return 'number';
        }
      }

      // Handle Strings
      if (stream.match(stringPrefixes)) {
        var isFmtString = stream.current().toLowerCase().indexOf('f') !== -1;
        if (!isFmtString) {
          state.tokenize = tokenStringFactory(stream.current(), state.tokenize);
          return state.tokenize(stream, state);
        } else {
          state.tokenize = formatStringFactory(stream.current(), state.tokenize);
          return state.tokenize(stream, state);
        }
      }

      for (var i = 0; i < operators.length; i++)
        if (stream.match(operators[i])) return 'operator'

      if (stream.match(delimiters)) return 'punctuation';

      if (state.lastToken == "." && stream.match(identifiers))
        return 'property';

      if (stream.match(keywords) || stream.match(wordOperators))
        return 'keyword';

      if (stream.match(builtins))
        return 'builtin';

      if (stream.match(/^(self|cls)\b/))
        return "variable-2";

      if (stream.match(identifiers)) {
        if (state.lastToken == 'def' || state.lastToken == 'class')
          return 'def';
        return 'variable';
      }

      // Handle non-detected items
      stream.next();
      return inFormat ? null :ERRORCLASS;
    }

    function formatStringFactory(delimiter, tokenOuter) {
      while ('rubf'.indexOf(delimiter.charAt(0).toLowerCase()) >= 0)
        delimiter = delimiter.substr(1);

      var singleline = delimiter.length == 1;
      var OUTCLASS = 'string';

      function tokenNestedExpr(depth) {
        return function(stream, state) {
          var inner = tokenBaseInner(stream, state, true)
          if (inner == 'punctuation') {
            if (stream.current() == "{") {
              state.tokenize = tokenNestedExpr(depth + 1)
            } else if (stream.current() == "}") {
              if (depth > 1) state.tokenize = tokenNestedExpr(depth - 1)
              else state.tokenize = tokenString
            }
          }
          return inner
        }
      }

      function tokenString(stream, state) {
        while (!stream.eol()) {
          stream.eatWhile(/[^'"\{\}\\]/);
          if (stream.eat("\\")) {
            stream.next();
            if (singleline && stream.eol())
              return OUTCLASS;
          } else if (stream.match(delimiter)) {
            state.tokenize = tokenOuter;
            return OUTCLASS;
          } else if (stream.match('{{')) {
            // ignore {{ in f-str
            return OUTCLASS;
          } else if (stream.match('{', false)) {
            // switch to nested mode
            state.tokenize = tokenNestedExpr(0)
            if (stream.current()) return OUTCLASS;
            else return state.tokenize(stream, state)
          } else if (stream.match('}}')) {
            return OUTCLASS;
          } else if (stream.match('}')) {
            // single } in f-string is an error
            return ERRORCLASS;
          } else {
            stream.eat(/['"]/);
          }
        }
        if (singleline) {
          if (parserConf.singleLineStringErrors)
            return ERRORCLASS;
          else
            state.tokenize = tokenOuter;
        }
        return OUTCLASS;
      }
      tokenString.isString = true;
      return tokenString;
    }

    function tokenStringFactory(delimiter, tokenOuter) {
      while ('rubf'.indexOf(delimiter.charAt(0).toLowerCase()) >= 0)
        delimiter = delimiter.substr(1);

      var singleline = delimiter.length == 1;
      var OUTCLASS = 'string';

      function tokenString(stream, state) {
        while (!stream.eol()) {
          stream.eatWhile(/[^'"\\]/);
          if (stream.eat("\\")) {
            stream.next();
            if (singleline && stream.eol())
              return OUTCLASS;
          } else if (stream.match(delimiter)) {
            state.tokenize = tokenOuter;
            return OUTCLASS;
          } else {
            stream.eat(/['"]/);
          }
        }
        if (singleline) {
          if (parserConf.singleLineStringErrors)
            return ERRORCLASS;
          else
            state.tokenize = tokenOuter;
        }
        return OUTCLASS;
      }
      tokenString.isString = true;
      return tokenString;
    }

    function pushPyScope(state) {
      while (top(state).type != 'lean') state.scopes.pop()
      state.scopes.push({offset: top(state).offset + conf.indentUnit,
                         type: 'lean',
                         align: null})
    }

    function pushBracketScope(stream, state, type) {
      var align = stream.match(/^[\s\[\{\(]*(?:--|$)/, false) ? null : stream.column() + 1
      state.scopes.push({offset: state.indent + hangingIndent,
                         type: type,
                         align: align})
    }

    function dedent(stream, state) {
      var indented = stream.indentation();
      while (state.scopes.length > 1 && top(state).offset > indented) {
        if (top(state).type != 'lean') return true;
        state.scopes.pop();
      }
      return top(state).offset != indented;
    }

    function tokenLexer(stream, state) {
      if (stream.sol()) {
        state.beginningOfLine = true;
        state.dedent = false;
      }

      var style = state.tokenize(stream, state);
      var current = stream.current();

      // Handle decorators
      if (state.beginningOfLine && current == "@")
        return stream.match(identifiers, false) ? 'meta' : 'operator';

      if (/\S/.test(current)) state.beginningOfLine = false;

      if ((style == 'variable' || style == 'builtin')
          && state.lastToken == 'meta')
        style = 'meta';

      // Handle scope changes.
      if (current == 'pass' || current == 'return')
        state.dedent = true;

      if (current == 'lambda') state.lambda = true;
      if (current == ":" && !state.lambda && top(state).type == 'lean' && stream.match(/^\s*(?:--|$)/, false))
        pushPyScope(state);

      if (current.length == 1 && !/string|comment/.test(style)) {
        var delimiter_index = "[({".indexOf(current);
        if (delimiter_index != -1)
          pushBracketScope(stream, state, "])}".slice(delimiter_index, delimiter_index+1));

        delimiter_index = "])}".indexOf(current);
        if (delimiter_index != -1) {
          if (top(state).type == current) state.indent = state.scopes.pop().offset - hangingIndent
          else return ERRORCLASS;
        }
      }
      if (state.dedent && stream.eol() && top(state).type == 'lean' && state.scopes.length > 1)
        state.scopes.pop();

      return style;
    }

    var external = {
      startState: function(basecolumn) {
        return {
          tokenize: tokenBase,
          scopes: [{offset: basecolumn || 0, type: 'lean', align: null}],
          indent: basecolumn || 0,
          lastToken: null,
          lambda: false,
          dedent: 0
        };
      },

      token: function(stream, state) {
        var addErr = state.errorToken;
        if (addErr) state.errorToken = false;
        var style = tokenLexer(stream, state);

        if (style && style != 'comment')
          state.lastToken = (style == 'keyword' || style == 'punctuation') ? stream.current() : style;
        if (style == 'punctuation') style = null;

        if (stream.eol() && state.lambda)
          state.lambda = false;
        return addErr ? style + " " + ERRORCLASS : style;
      },

      indent: function(state, textAfter) {
        if (state.tokenize != tokenBase)
          return state.tokenize.isString ? CodeMirror.Pass : 0;

        var scope = top(state)
        var closing = scope.type == textAfter.charAt(0) ||
            scope.type == 'lean' && !state.dedent && /^(else:|elif |except |finally:)/.test(textAfter)
        if (scope.align != null)
          return scope.align - (closing ? 1 : 0)
        else
          return scope.offset - (closing ? hangingIndent : 0)
      },

      electricInput: /^\s*([\}\]\)]|else:|elif |except |finally:)$/,
      closeBrackets: {triples: "'\""},
      blockCommentStart: "/-",
      blockCommentEnd: "-/",
      lineComment: "--",
      fold: 'indent'
    };
    return external;
  });

  CodeMirror.defineMIME("text/x-lean", 'lean');
});
