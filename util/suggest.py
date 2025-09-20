import os
from util import utility
os.environ['MYSQL_DATABASE'] = 'axiom'
from std import MySQL
from util.search import get_sections
sections = get_sections()

if __name__ == '__main__':
    
    data = []
    user = utility.user
    for axiom, *_ in MySQL.instance.query(f"select axiom from axiom where user = '{user}'"):
        phrases = axiom.split('.')
        size = len(phrases)
        phrases.append('apply')

        prefix = ''

        for i in range(0, size):
            prefix += phrases[i] + "."
            data.append([
                user,
                prefix,
                phrases[i + 1],
                1
            ])
            
            data.append([
                user,
                "Lemma." + prefix,
                phrases[i + 1],
                1
            ])

    for sec in sections:
        data.append([
            user,
            'Lemma.',
            sec,
            1
        ])
    
    MySQL.instance.execute(f"delete from suggest where user = '{user}'")    
    MySQL.instance.load_data('suggest', data)
