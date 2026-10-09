import regex as re
from py.regexp import balancedParentheses, balancedBrackets, balancedBraces,\
    balancedGroups

def search(pairs, text, depth=16):
    if pairs == '()':
        return re.search(balancedParentheses(depth), text)
        
    if pairs == '[]':
        return re.search(balancedBrackets(depth), text)
    
    if pairs == '{}':
        return re.search(balancedBraces(depth), text)
        
    return re.search(balancedGroups(pairs, depth, multiple=''), text)

def findall(pairs, text, depth=16):
    if pairs == '()':
        return re.findall(balancedParentheses(depth), text)
        
    if pairs == '[]':
        return re.findall(balancedBrackets(depth), text)
    
    if pairs == '{}':
        return re.findall(balancedBraces(depth), text)
    
    return re.findall(balancedGroups(pairs, depth, multiple=''), text)
    
def finditer(pairs, text, depth=16):
    if pairs == '()':
        return re.finditer(balancedParentheses(depth), text)
        
    if pairs == '[]':
        return re.finditer(balancedBrackets(depth), text)
    
    if pairs == '{}':
        return re.finditer(balancedBraces(depth), text)

    return re.finditer(balancedGroups(pairs, depth, multiple=''), text)

if __name__ == '__main__':
    for pairedGroup in findall("（）", '（（1 + 2） * （3 * 4）） + （7 + 8） * [8 + 8]'):
        print(pairedGroup)
        
    for pairedGroup in findall("<>", '<<1 + 2> * <3 * 4>> + <7 + 8> * [8 + 8]'):
        print(pairedGroup)

    for pairedGroup in findall("‘’", '‘‘1 + 2’ * ‘3 * 4’’ + ‘7 + 8’ * [8 + 8]'):
        print(pairedGroup)
        
    for pairedGroup in findall("“”", '““1 + 2” * “3 * 4”” + “7 + 8” * [8 + 8]'):
        print(pairedGroup)
        
    for pairedGroup in findall("【】", '【【1 + 2】 * 【3 * 4】】 + 【7 + 8】 * [8 + 8]'):
        print(pairedGroup)
    
    for pairedGroup in findall("《》", '《《1 + 2》 * 《3 * 4》》 + 《7 + 8》 * [8 + 8]'):
        print(pairedGroup)
    
    for pairedGroup in findall("「」", '「「1 + 2」 * 「3 * 4」」 + 「7 + 8」 * [8 + 8]'):
        print(pairedGroup)
    
    for pairedGroup in findall("『』", '『『1 + 2』 * 『3 * 4』』 + 『7 + 8』 * [8 + 8]'):
        print(pairedGroup)
    
