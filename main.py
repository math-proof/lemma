from flask import Flask

from werkzeug.routing import BaseConverter
from sympy import MySQL
import sys
 
app = Flask(__name__)

from blueprint.system import system
app.register_blueprint(system)
 
from blueprint.debug import debug
app.register_blueprint(debug)

from blueprint.mysql import mysql
app.register_blueprint(mysql)


def tojson(obj):
    
    from jinja2.runtime import Undefined
    if isinstance(obj, Undefined):
        return 'null'
    
    from jinja2.utils import htmlsafe_json_dumps
    return htmlsafe_json_dumps(obj)


app.jinja_env.filters['tojson'] = tojson

    
class RegexConverter(BaseConverter):

    def __init__(self, url_map, *items):
        super(RegexConverter, self).__init__(url_map)
        self.regex = items[0]
 
 
app.url_map.converters['re'] = RegexConverter

    
def run(port):
    # from wsgiref import simple_server
    # httpd = simple_server.make_server('0.0.0.0', port, app)
    # httpd.serve_forever()
    from gevent import pywsgi
    server = pywsgi.WSGIServer(('0.0.0.0', port), app)
    server.serve_forever()


if __name__ == '__main__':
    from std import argparse
    args, kwargs = argparse()
    
    user = MySQL.user
    [[port]] = MySQL.instance.select(f"select port from login where user = '{user}'")
    port = kwargs.get('port', port)
    run(port)
