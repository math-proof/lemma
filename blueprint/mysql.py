from flask.blueprints import Blueprint
from sympy import MySQL
from flask.globals import request
from std import json_encode

mysql = Blueprint('mysql', __name__)


@mysql.route('/mysql/execute', methods=['POST', 'GET'])
def execute():    
    sql = request.form.get('sql')
    print('sql =', sql)
    rowcount = MySQL.instance.execute(sql)
    return str(rowcount)

@mysql.route('/mysql/select', methods=['POST', 'GET'])
def select():    
    sql = request.form.get('sql')
    print('sql =', sql)
    [*result] = MySQL.instance.select(sql)
    return json_encode(result)

