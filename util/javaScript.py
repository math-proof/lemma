from std.file import createNewFile
from os.path import dirname, basename, abspath, sep
import re
from std import computed
from util.search import yield_from_py
import std

workingDirectory = dirname(dirname(__file__)) + '/'

def has_unterminated_parantheses(statement):
    return statement.count("(") > statement.count(")")

def piece_together(input):
    code = "\n".join(input)
    input.clear()
    return code 

def is_latex_print(latex):
    res = []
    while matches := re.match(r'(Eq\.\w+|\((Eq\.\w+|\*Eq\[-\d+:\]) *(, *Eq\.\w+)+ *\)|Eq\[-(\d+:|1)\]|\*Eq\[-\d+:\]|\*\w+|\w+)', latex):
        res.append(matches[0])
        latex = latex[len(matches[0]):]
        if re.match(' *= *', latex):
            return res
        
        if matchComma := re.match(' *, *', latex):
            latex = latex[len(matchComma[0]):]
        else:    
            return []
    
    return []


def get_args_for_writing(module, latexStr):
    inputs = []
    input = []
    counterOfLengths = 0
    lengths = []
    m = re.search(r'([\w.]+)\.(of|given)\.', module)
    numOfRequisites = len(m[1].split(".")) - 1 if m else 0
    createdTime = updatedTime = None
    indexOfYield = -1
    for dict in yield_from_py(module):
        if 'statement' not in dict:
            continue

        statement = dict['statement']

        if 'module' in dict:
            module = dict['module']
            indexOfYield = counterOfLengths
            input.append(statement)
        elif 'a' in dict:
            if (not input) and inputs and inputs[-1][-1] == '\\':
                length = len(inputs)
                inputs[length - 1] += f"\n{statement}"
            else:
                input.append(statement)
            
        else:
            del dict['statement']
            if 'comment' in dict:
                del dict['comment']

                if 'unused' in dict:
                    ...
                elif inputs and has_unterminated_parantheses(inputs[-1]):
                    inputs[-1] += f"\n{statement}"
                    continue
                else:
                    if dict:
                        for key, value in dict.items():
                            match key:
                                case "created":
                                    createdTime = value
                                case "updated":
                                    updatedTime = value

                input.append(statement)
                continue

            if 'unused' in dict:
                input.append(statement)
                continue

            text = statement
            if statement.startswith('    ') and not input:
                # starting with more than 4 spaces indicates this line is a continuation of the previous line of code!
                inputs[-1] += f"\n{text}"
            else:
                input.append(text)
        
        if matches := re.match(r'Eq *(<<|\[ *(- *\d+ *)?(: *)?\] *=) *', statement):
            inputs.append(piece_together(input))

            counterOfLengths += 1
            lengths.append(1)
        elif matches := is_latex_print(statement):

            regexp = r'Eq\.\w+|Eq\[-(\d+:|1)\]'
            if 'module' in dict:
                count = len(matches)
                match count:
                    case 1:
                        lengthOfGiven = lengthOfWhere = 0                        
                    case 2:
                        if numOfRequisites:
                            matchGiven = re.findall(regexp, matches[0])
                            lengthOfGiven = len(matchGiven)
                            lengthOfWhere = 0
                        else:
                            matchWhere = re.findall(regexp, matches[0])
                            lengthOfWhere = len(matchWhere)
                            lengthOfGiven = 0
                    case 3:
                        matchGiven = re.findall(regexp, matches[0])
                        lengthOfGiven = len(matchGiven)

                        matchWhere = re.findall(regexp, matches[1])
                        lengthOfWhere = len(matchWhere)

                matchImply = re.findall(regexp, matches[count - 1])
                lengthOfImply = len(matchImply)
                lengths.append(lengthOfGiven + lengthOfWhere + lengthOfImply)
                
            elif assgnment_count := sum(len(re.findall(regexp, text)) for text in matches):
                lengths.append(assgnment_count)
            else:
                continue

            inputs.append(piece_together(input))
            counterOfLengths += 1

    if input:
        inputs.append(piece_together(input))
    
    if indexOfYield == -1:
        numOfReturnsFromApply = 1
    else:
        numOfReturnsFromApply = lengths[indexOfYield]
    
    i = 0
    latex = []
    where = statements = ''
    given = imply = None
    
    def is_latex_with_tabs(latex):
        if "\t" in latex:
            matches = []
            for tex in latex.split("\t"):
                if m := re.findall(r'\\\\\[.+?\\\\\]', tex):
                    matches.append(''.join(m))
                else:
                    return []
            return matches
        
        return re.findall(r'\\\\\[.+?\\\\\]', latex)
    
    resultsFromApply = []
    for statement in latexStr.split("\n"):
        if i == indexOfYield:
            if numOfReturnsFromApply == 1:
                lengths[i] -= 1
                if not lengths[i]:
                    if matches := is_latex_with_tabs(statement):
                        match len(matches):
                            case 3:
                                given, where, imply = matches
                            case 2:
                                if numOfRequisites:
                                    given, imply = matches
                                    where = ''
                                else:
                                    where, imply = matches
                                    given = ''
                            case 1:
                                where = ''
                                given = ''
                                imply, = matches
                    
                    given = {
                        'py' : inputs.pop(0),
                        'latex' : given
                    }
    
                    statements = ''
                    i += 1
            else:
                resultsFromApply.append(statement)
    
                lengths[i] -= 1
                if lengths[i] == 0:
                    given = resultsFromApply[:lengthOfGiven]
                    given = ''.join(given)
                    given = {
                        'py' : inputs[0],
                        'latex' : given
                    }
    
                    if lengthOfWhere:
                        where = resultsFromApply[lengthOfGiven:lengthOfWhere]
                        where = ''.join(where)
                    else:
                        where = ''
    
                    imply = resultsFromApply[lengthOfGiven + lengthOfWhere:]
                    imply = ''.join(imply)
    
                    statements = ''
                    inputs = inputs[1:]
                    i += 1
        else:
            statements += statement
            if i >= len(lengths):
                continue
    
            lengths[i] -= 1
            if not lengths[i]:
                latex.append(statements)
                statements = ''
                i += 1
    
    size = len(latex)
    unused = inputs[size:]
    prove = [{'py' : inputs[i], 'latex' : latex[i]} for i in range(size)]
    if imply is None:
        print(module, 'is eronuous!')
    return module, prove, given, imply, unused, createdTime, updatedTime

class LocalJsWriter:
    def __init__(self):
        ...
        
    def url_address(self, package):
        return f"{dirname(dirname(__file__))}/target/{package.replace('.', '/')}.html"

    def select_axiom_lapse_from_axiom(self):
        return {}

    @computed
    def targetFiles(self):
        targetFiles = []

        for file in std.listdir(workingDirectory + 'static/components', 'vue'):
            if basename(file) == 'codeMirror.vue':
                def transform(text):
                    return text.replace('//import CodeMirror', 'import CodeMirror') 
            else:
                transform = None
            generate_js(file, transform)
            targetFiles.append('vue/' + basename(file))
        
        parentPath = workingDirectory + 'static/'
        for file in std.listdir(workingDirectory + 'static/codemirror', 'js', recursive=True):
            file = abspath(file)
            if file.endswith('lib' + sep + 'codemirror.js'):
                def transform(text):
                    with open(parentPath + 'codemirror/mode/python/python.js', 'r', encoding='utf8') as file:
                        python = file.read()
                        python = re.search(r"function\(CodeMirror\) \{(.+)\}\);\s*$", python, re.S)[1]
                        
                    with open(parentPath + 'codemirror/addon/selection/active-line.js', 'r', encoding='utf8') as file:
                        active_line = file.read()
                        active_line = re.search(r"function\(CodeMirror\) \{(.+)\}\);\s*$", active_line, re.S)[1]
                        
                    with open(parentPath + 'codemirror/addon/hint/show-hint.js', 'r', encoding='utf8') as file:
                        show_hint = file.read()
                        show_hint = re.search(r"function\(CodeMirror\) \{(.+)\}\);\s*$", show_hint, re.S)[1]
                        
                    with open(parentPath + 'codemirror/addon/edit/matchbrackets.js', 'r', encoding='utf8') as file:
                        matchbrackets = file.read()
                        matchbrackets = re.search(r"function\(CodeMirror\) \{(.+)\}\);\s*$", matchbrackets, re.S)[1]
                        
                    text = re.sub(r"\(function\(global, factory\) \{.+\}\)\)\);\s*$", "export default CodeMirror\n", text, flags=re.S)
                    text += python + active_line + show_hint + matchbrackets
                    text = text.replace('"use strict";', '')
                    return text
            else:
                transform = None
            generate_js(file, transform, file[len(parentPath):-3].split(sep))
            targetFiles.append(abspath(file)[len(parentPath):])
        
        return targetFiles

    def load_data(self, table, data, **kwargs):
        from collections import defaultdict
        state_count_pairs = defaultdict(int)
        repertoire = defaultdict(dict)
        total = 0
        
        targetFiles = self.targetFiles
        for package, module, state, lapse, latex, *_ in data:
            state_count_pairs[state.name] += 1
            total += 1
            
            if state.name != 'proved':
                section = module.split('.', 1)[0]
                section = repertoire[section]
                if not state.name in section:
                    section[state.name] = []
                section[state.name].append(module)
                
            write_html(module, generate_theorem(*get_args_for_writing(module, latex), targetFiles))
            
        state_count_pairs['total'] = total
        state_count_pairs = [dict(state=state, count=count) for state, count in state_count_pairs.items()]
        write_js_object('target/js/axiomSummary.js', '', state_count_pairs=state_count_pairs, repertoire=repertoire)
        return len(targetFiles)
    
    def execute(self, sql):
        if m := re.match(r'update axiom set state = "\w+", lapse = \S+, latex = ("[\s\S]+") where user = "\w+" and axiom = "(\S+)"', sql):
            latex, module = m.groups()
            latex = eval(latex)
            html = write_html(module, generate_theorem(*get_args_for_writing(module, latex), self.targetFiles))
            print(html)
        return 1
        
instance = LocalJsWriter()
            
def write_js_object(path, namespace, **kwargs):
    
    texts = []
    for attr, value in kwargs.items():
        value = std.json_encode(value)
        if namespace:
            text = 'window.%s.%s = %s;' % (namespace, attr, value)
        else:
            text = 'window.%s = %s;' % (attr, value)
            
        texts.append(text)

    file = workingDirectory + path
    createNewFile(file)
    # Text(file).write('')
    with open(file, 'w', encoding='utf8') as file:
        for text in texts:
            print(text, file=file)


def generate_js(file, transform=None, attributes=None):
    name = basename(file)
    name, ext = std.split_filename(name)
    with open(file, 'r', encoding='utf8') as file:
        text = file.read()
        if transform:
            text = transform(text)

        text = text.replace('\\', '\\\\')
        text = text.replace('`', r"\`")
        text = text.replace('${', r"\${")
        
        if attributes:
            window = 'window.js'
            previousAssignments = []
            for attr in attributes[:-1]:
                attr = re.sub(r'\W', '_', attr)
                previousAssignments.append(f'if (!{window}.{attr}) {window}.{attr} = {{}};\n')
                window += "." + attr

            previousAssignments = ''.join(previousAssignments)
            assert '-' not in previousAssignments
            lastAttribute = re.sub(r'\W', '_', attributes[-1])
            text = previousAssignments + f"{window}.{lastAttribute} = `{text}`;"
            mjs = 'target/%s.js' % '/'.join(attributes)
        else:
            text = f'window.{ext}.{name} = `{text};`'
            mjs = 'target/%s/%s.%s' % (ext, name, ext)

    file = workingDirectory + mjs
    createNewFile(file)
    with open(file, 'w', encoding='utf8') as file:
        print(text, file=file)

    return mjs
    
def write_html(module, textContent):
    mjs = 'target/%s.html' % module.replace('.', '/')
    filePath = workingDirectory + mjs
    createNewFile(filePath)    
    with open(filePath, 'w', encoding='utf8') as file:
        print(textContent, file=file)

    return filePath
    
        
def generate_theorem(module, prove, given, imply, unused, createdTime, updatedTime, mjs):
    parentPath = '../' * (len(module.split('.')) - 1)
    mjs = '\n'.join([f"<script src='{parentPath}{mjs}'></script>" for mjs in mjs])
    parentPath += '../'
    imply = std.json_encode(imply)
    createdTime = std.json_encode(createdTime)
    updatedTime = std.json_encode(updatedTime)
    return f"""
<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="{parentPath}static/css/style.css">
<link rel="shortcut icon" type="image/x-icon" href="{parentPath}static/favicon.ico">
<title>{module}</title>
<link rel=stylesheet href="{parentPath}static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="{parentPath}static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="{parentPath}static/codemirror/addon/hint/show-hint.css">
<style>
div {{
    caret-color: transparent;
}}
</style>
<body></body>
<script src="{parentPath}static/unpkg.com/vue@3.2.47/dist/vue.global.prod.js"></script>
<script src="{parentPath}static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="{parentPath}static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="{parentPath}static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

<script src='{parentPath}static/js/std.js'></script>
<script src='{parentPath}static/js/utility.js'></script>
<script>
MathJax = InitMathJax(1000);
</script>
<script async src="{parentPath}static/unpkg.com/mathjax@3.2.0/es5/tex-chtml.js"></script>
<script>
window.vue = {{}};
window.js = {{}};
</script>
{mjs}
<script type=module>
createApp('render', {{
    error : [],
    logs : [],
    prove : {prove},
    unused : {unused},
    module: "{module}",
    given: {given},
    imply: {imply},
    where: "",
    createdTime: {createdTime},
    updatedTime: {updatedTime},
}});
</script>"""

    
if __name__ == '__main__':
    ...