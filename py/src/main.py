from py.cpp import repetition_penalty

def test():
    text='''这是一篇陈词滥调的文章[1]。This is a clichéd article [2]. C’est un article plein de clichés [3].
    这是一篇陈词滥调的文章[4]。C’est un article plein de clichés [6]. This is a clichéd article [5].
    C’est un article plein de clichés [9]. 这是一篇陈词滥调的文章[7]。This is a clichéd article [7].
    C’est un article plein de clichés [9]. This is a clichéd article [0]. 这是一篇陈词滥调的文章[7]。
    This is a clichéd article [1]. C’est un article plein de clichés [9]. 这是一篇陈词滥调的文章[7]。
    This is a clichéd article [8]. 这是一篇陈词滥调的文章[7]。C’est un article plein de clichés [9].'''
    print(repetition_penalty(text))

def main():
    from py.file import Text
    for i in range(27):
        file = f"std/src/hash/test/test-{i}.txt"
        text = Text(file).read()
        for info in repetition_penalty(text):
            error = info['text']
            print(error)
            index = info['index']
            scan_length = info['scan_length']
            assert scan_length == len(error.encode()), f'''
scan_length = {scan_length}
error.encode() = {error.encode()}
'''
            for start in index:
                assert error == text[start:start + len(error)], f'''
at index = {i}:\n{error}\n{text[start:start + len(error)]}
'''
    print('finish testing')



if __name__ == '__main__':
    # test()
    main()

