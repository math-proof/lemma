const dotLookbehind = [
    '\\b([a-z]+|[A-Z][a-z]*)\\s+\\d+',
    '\\b[a-z]+',
    '((\\b[A-Z]?[a-z]+)*| +[A-Z]+\\.) +[A-Z][a-z]+', // The famous person is Martin Luther K.jr, JPR. Hendrikson
    '\\b[A-Z]?[a-z]+\\s+[A-Z]+', // Washington DC
    '\\w+ +(?:[A-Z]\\.)+[A-Z]', // U.S.A.
    '[;!?；！？…。"\\\\\'`’”\\da-zA-Z)₀-₉][)\\]}）】｝`]',  // even includes motivational expressions ("Three times the money, three times the fun!"). Today is a nice day
    '\\S/\\d+',// This lemma establishes that the sine of π divided by 9 is less than 1/2. The proof leverages the inequality
].join('|');


const dotLookahead = [
    '[A-Z][a-z]*(?: +\\w+\\b|[,\'`])',
    '[“‘"\'\\d]',
].join('|');


const dotNegativeLookbehind = [
    ' vs', //  vs. versus
    ' v',  //  v. versus
    's\\.t', //  subject to
    'etc', //  etc. et cetera
].join('|');

const englishSentenceRegex = new RegExp(`(?<=${dotLookbehind})(?<!${dotNegativeLookbehind})[.．]\\s+(?=${dotLookahead})`, 'g');

function merge_next_line(texts, nextLine) {
    if (texts.length) {
        var prevLine = texts.back();
        var match;
        if (match = prevLine.match(/(?<=\n)[ \t]+$/)) {
            var {index} = match;
            texts.back(prevLine.slice(0, index));
            return prevLine.slice(index) + nextLine;
        }
        else if (prevLine.match(/\b[a-z\d]! *$/) && nextLine.match(/ *[*-*/()]/)) {
            // deal with mathematical factorial expression n! / r!
            texts[texts.length - 1] += nextLine;
            return '';
        }
    }
}

export function sbd(text) {
    let m = text.match(/^[;!?；！？…。\s]+/);
    if (m) {
        var leadingDelimiters = m[0];
        text = text.slice(leadingDelimiters.length);
    }
    else
        var leadingDelimiters = '';

    const regex = /[^;!?；！？…。\r\n]+[;!?；！？…。\s]*/g;
    let texts = [];
    let hasContext = false;
    let match;
    while ((match = regex.exec(text)) !== null) {
        let line = match[0];
        // if the current sentence is correct, skipping processing!
        if (!line.match(/^[’”]/)) {
            // considering the following case:
            // ("Going once, going twice, gone!") and even includes motivational expressions
            var end = match.index + match[0].length;
            if (end < text.length && '")]}）】｝’”'.includes(text[end])) {
                if (hasContext)
                    texts[texts.length - 1] += line;
                else {
                    let newLine = merge_next_line(texts, line);
                    if (newLine)
                        texts.push(newLine);
                    else if (newLine === undefined)
                        texts.push(line);
                    hasContext = true;
                }
                continue;
            }
            // sentence boundary detected!
            let start = 0;
            let englishSentences = [];
            let englishSentenceMatch;
            // consider the following case: 1. firstly...  2. secondly... 3. thirdly...
            // the best answer is answer 1. Answer 2 is not correct.
            while ((englishSentenceMatch = englishSentenceRegex.exec(line)) !== null) {
                let end = englishSentenceMatch.index + englishSentenceMatch[0].length;
                englishSentences.push(line.slice(start, end));
                start = end;
            }

            englishSentences.push(start? line.slice(start): line);
            if (hasContext) {
                texts[texts.length - 1] += englishSentences[0];
                englishSentences = englishSentences.slice(1);
                hasContext = false;
            }
            if (texts.length && englishSentences[0]) {
                line = merge_next_line(texts, englishSentences[0]);
                if (line)
                    englishSentences[0] = line;
                else if (line === '')
                    englishSentences = englishSentences.slice(1);
            }
            texts.push(...englishSentences);
            continue;
        }

        hasContext = false;
        let boundaryIndex = 0;
        if (line.match(/^.[,)\]}，）】｝》、的]/)) {
            // for the following '的 ' case, this sentence should belong to be previous one:
            // ”的文字，以及选项“是”和“否”。
            if (line.slice(1, 3) === '的确')
                // for the following special case:
                // ”的确， GPS和其它基于卫星的定位系统为了商业、公共安全和国家安全的用 途而快速地发展。
                boundaryIndex = 1;
            else
                // for the following comma case:
                // ”,IEEE Jounalon Selected Areas in Communications,Vol.31,No.2,Feburary2013所述。
                if (texts.length)
                    texts[texts.length - 1] += line;
                else
                    texts.push(line);
        } else {
            m = line.match(/^.[;.!?:；。！？：…\r\n]+/);
            boundaryIndex = m ? m[0].length : 1;
            // considering the following complex case:
            // ”!!!然后可以通过家长控制功能禁止观看。
        }

        if (boundaryIndex) {
            if (!texts.length)
                texts.push('');
            texts[texts.length - 1] += line.slice(0, boundaryIndex); // sentence boundary detected! insert end of line here
            if (boundaryIndex < line.length) {
                let latter = line.slice(boundaryIndex);
                if (m = latter.match(/^\s+/)) {
                    texts[texts.length - 1] += m[0];
                    latter = latter.slice(m[0].length);
                    if (!latter)
                        continue;
                }
                texts.push(latter);
            }
        }
    }

    if (leadingDelimiters) {
        if (texts.length)
            texts[0] = leadingDelimiters + texts[0];
        else
            texts.push(leadingDelimiters);
    }
    // console.assert(texts.join('') == leadingDelimiters + text, 'Assertion failed: texts.join(\'\') !== leadingDelimiters + text');
    return texts;
}

console.log('import sbd.js');

