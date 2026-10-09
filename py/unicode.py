greeks = ('alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lamda', 'mu', 'nu', 'xi', 'omicron', 'pi', 'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega')

def ascii2greek(x):
    if x.lower() in greeks:
        if x[0].isupper():
            x = eval("'\\N{GREEK CAPITAL LETTER %s}'" % x)
        else:
            x = eval("'\\N{GREEK SMALL LETTER %s}'" % x)
    return x

from tqdm.utils import _text_width as strlen


if __name__ == '__main__':
    ...