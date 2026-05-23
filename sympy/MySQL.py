import importlib.util, mysql.connector, std, re, random, time, os, json, pandas as pd, zipfile, tarfile, gzip, pandas
from tqdm import tqdm
from collections import defaultdict


def load_dataset(dataset_id, **ds_kw):
    """``MsDataset`` when ModelScope is installed; otherwise HuggingFace ``datasets``."""
    from datasets import load_dataset as hf_load_dataset

    if importlib.util.find_spec('modelscope') is None:
        return hf_load_dataset(dataset_id, **ds_kw)

    from modelscope import MsDataset
    import modelscope

    ms_kw = dict(ds_kw)
    subset_name = ms_kw.pop('name', 'default')
    revision = ms_kw.pop('revision', None)
    if revision == 'main':
        revision = 'master'
    streaming = ms_kw.pop('streaming', False)
    download_mode = ms_kw.pop('download_mode', 'reuse_dataset_if_exists')
    split_kw = ms_kw.pop('split', None)
    for noisy in ('num_proc', 'hub_token', 'cache_dir'):
        ms_kw.pop(noisy, None)

    extra = {'download_mode': download_mode, 'use_streaming': streaming}
    if revision is not None:
        extra['version'] = revision
    try:
        from packaging import version as pkg_version

        if pkg_version.parse(modelscope.__version__) >= pkg_version.parse('1.29.1'):
            extra['trust_remote_code'] = True
    except Exception:
        pass
    extra.update(ms_kw)

    def _to_hf(ds):
        return ds._hf_ds if hasattr(ds, '_hf_ds') else ds

    def _load_one(splt):
        return _to_hf(
            MsDataset.load(dataset_id, subset_name=subset_name, split=splt, **extra))

    if split_kw is not None:
        return _load_one(split_kw)

    out = {}
    for splt in ('train', 'validation', 'test', 'dev', 'val'):
        print(f'[load_dataset] ModelScope {dataset_id!r} split={splt!r} …', flush=True)
        try:
            ds = _load_one(splt)
            if hasattr(ds, '__len__') and len(ds) == 0:
                print(f'[load_dataset] split={splt!r} empty, skip', flush=True)
                continue
            print(f'[load_dataset] split={splt!r} rows={len(ds)}', flush=True)
            out[splt] = ds
        except Exception as e:
            print(f'[load_dataset] split={splt!r} failed: {e!r}', flush=True)
            continue
    if out:
        return out
    raise RuntimeError(
        'ModelScope MsDataset.load found no standard splits for %r (subset_name=%r). '
        'Try a ModelScope dataset id, pass split= / name=, or use an environment without '
        'modelscope to load from the Hugging Face Hub with datasets.' % (dataset_id, subset_name))


def format_table(table):
    if m := re.match(r'(\w+)\.(\S+)$', table):
        return "%s.`%s`" % m.groups()
    else:
        return "`%s`" % table
    
class Database:
    # usage:
    '''vim ~/.bashrc
export MYSQL_USER=yourName
export MYSQL_PWD=yourPassword
export MYSQL_HOST=yourIPAddress
    '''

    def create_database(self):
        cursor = self.cursor()
        try:
            cursor.execute("CREATE DATABASE {} DEFAULT CHARACTER SET '{}'".format(self.database, self.charset))
        except Exception as err:
            print("Failed creating database: {}".format(err))

    def __init__(self):
        self.user = os.environ.get('USERNAME') if os.name == 'nt' else os.environ.get('USER')
        self.password = os.environ.get('MYSQL_PWD')
        self.host = os.environ.get('MYSQL_HOST', '127.0.0.1')
        self.port = os.environ.get('MYSQL_PORT', '3306')
        self.database = os.environ.get('MYSQL_DATABASE', 'corpus')
        self.charset = os.environ.get('MYSQL_CHARSET', 'utf8mb4')
        try:
            self.conn = mysql.connector.connect(**self.kwargs)
        except mysql.connector.errors.ProgrammingError as err:
            print(err.msg)
            m = re.compile(r"Unknown database '(\w+)'").search(err.msg)
            assert m
            assert m[1] == self.database
            kwargs = self.kwargs
            kwargs['database'] = 'mysql'
            self.conn = mysql.connector.connect(**kwargs)
            self.execute("create database " + self.database)
            self.conn = mysql.connector.connect(**self.kwargs)

        self.execute('SET NAMES utf8mb4')
        self.execute('SET CHARACTER SET utf8mb4')

    @property
    def kwargs(self):
        return {
            'user': self.user,
            'password': self.password,
            'host': self.host,
            'database': self.database,
            'charset': self.charset,
            'port': self.port,
            'auth_plugin': 'mysql_native_password'
        }

    def cursor(self, **kwargs):
        return self.conn.cursor(**kwargs)

    @property
    def wait_timeout(self):
        cursor = self.cursor()
        cursor.execute("show global variables like 'wait_timeout'")
        for Variable_name, Value in cursor:
            assert Variable_name == 'wait_timeout'
            return Value

    @property
    def max_allowed_packet(self):
        cursor = self.cursor()
        cursor.execute("show global variables like 'max_allowed_packet'")
        for Variable_name, Value in cursor:
            assert Variable_name == 'max_allowed_packet'
            return Value

    def commit(self):
        self.conn.commit()

    def query(self, sql, order=None, limit=None, offset=0, dictionary=False):
        if order:
            sql += f" order by {order}"
            
        if limit:
            sql += ' limit %s' % limit
            
        if offset:
            sql += ' offset %s' % offset

        cursor = self.cursor(dictionary=dictionary)
        cursor.execute(sql)
        yield from cursor

    def execute(self, sql, *args):
        cursor = self.cursor()
        cursor.execute(sql, *args)
        self.commit()
        return cursor.rowcount

    def executemany(self, sql, seq_params, batch_size=1024, verbose=True):
        # seq_params must be a list of tuple
        cursor = self.cursor()
        
        if batch_size:
            [*batches] = std.batches(seq_params, batch_size)
            inner_verbose = True if verbose and len(batches) > 1 else False
            rowcount = 0
            for i, seq_params in enumerate(batches):
                if inner_verbose:
                    print("executing instances from", i * batch_size, 'to', (i + 1) * batch_size, "(excluded)")
                cursor.executemany(sql, seq_params)
                rowcount += cursor.rowcount
        else:
            cursor.executemany(sql, seq_params)
            rowcount = cursor.rowcount
            
        self.commit()
        if verbose:
            print(f"rowcount = {rowcount} from {sql}")
        return rowcount

    def show_create_table(self, table):
        for _, sql in self.query("show create table %s" % table):
            return sql

    def show_tables(self):
        tables = [table for table, *_ in self.query("show tables")]
#         tables.sort()
        return tables

    def show_create_table_oracle(self, table):
        for _, sql in self.query("select table_name, dbms_metadata.get_ddl('TABLE','%s') from dual,user_tables where table_name='%s'" % (table, table)):
            return sql

    def desc_oracle(self, table):
        return [args for args in self.query("select column_name,data_type,nullable from all_tab_columns where owner='%s' and table_name='%s'" % (self.conn._con._kwargs['user'], table))]

    def desc_table(self, table):
        return [*self.query("desc " + format_table(table))]

    def __enter__(self):
        if self.conn is None:
            self.conn = mysql.connector.connect(**self.kwargs)
        return self

    def __exit__(self, *args):
        self.conn.close()
        self.conn = None


class MySQLConnector(Database):

    def __init__(self):
        Database.__init__(self)

    def load_data_from_list(self, table, array, step=10000, ignore=True, delete=True, **kwargs):
        try:
            desc = self.desc_table(table)
        except mysql.connector.errors.ProgrammingError as err:
            print(err)
            m = re.search(r"1146 \(42S02\): Table '(\w+).(\S+)' doesn't exist", str(err))
            database, table = m.groups()
            print('database =', database)
            print('table =', table)
            
            keys = set()
            for obj in array:
                keys |= obj.keys()
            
            keys = [*keys]
            dtype = std.Object()
            for obj in array:
                for key in keys:
                    match val := obj.get(key):
                        case None:
                            ...
                    
                        case bool():
                            if dtype[key] is None:
                                dtype[key] = bool
                        
                        case int():
                            if dtype[key] is None or dtype[key] is bool:
                                dtype[key] = int

                        case float():
                            if dtype[key] is None or dtype[key] is bool or dtype[key] is int:
                                dtype[key] = float

                        case str():
                            if dtype[key] is None or dtype[key] is bool or dtype[key] is int or dtype[key] is float:
                                if re.fullmatch(r'\{.*\}', val) or re.fullmatch(r'\[.*\]', val):
                                    try:
                                        json.loads(val)
                                        dtype[key] = object
                                    except json.JSONDecodeError:
                                        dtype[key] = str
                                else:
                                    dtype[key] = str
            
                        case list() | tuple() | set() | dict():
                            if dtype[key] is None or dtype[key] is bool or dtype[key] is int or dtype[key] is float or dtype[key] is str:
                                dtype[key] = object
                                
                        case _:
                            raise _
            
            PRI = None

            def detect_primary_key(array, key):
                primary_keys = set()
                for obj in array:
                    if (pk := obj.get(key)) is None or pk in primary_keys:
                        break
                    primary_keys.add(pk)
                else:
                    return key
            desc = {}
            keys = [key for key in keys if dtype[key] is not None]
            for key in keys:
                match dtype[key].__name__:
                    case 'bool':
                        desc[key] = 'tinyint'
                    case 'int':
                        intvals = []
                        for obj in array:
                            if s := obj.get(key):
                                intvals.append(s)
                            else:
                                intvals.append(0)
                        if min(intvals) >= 0 and max(intvals) < 256:
                            desc[key] = 'tinyint'
                        else:
                            desc[key] = 'int'
                        if PRI is not None:
                            continue
                        PRI = detect_primary_key(array, key)
                    case 'float':
                        desc[key] = 'float'
                    case 'str':
                        length = 0
                        for obj in array:
                            if s := obj.get(key):
                                length = max(len(s), length)
                        if length >= 768:
                            desc[key] = 'text'
                        else:
                            desc[key] = f'varchar({length})'
                            if PRI is None:
                                PRI = detect_primary_key(array, key)
                            elif (m := re.match(r"varchar\((\d+)\)", desc[PRI])) and length < int(m[1]) and (_PRI := detect_primary_key(array, key)):
                                PRI = _PRI
                    case 'object':
                        desc[key] = 'json'
                    case _:
                        raise _

            if PRI is None:
                if 'id' not in keys:
                    PRI = 'id'
                elif 'uuid' not in keys:
                    PRI = 'uuid'
                elif '_id' not in keys:
                    PRI = '_id'

                for obj in array:
                    obj[PRI] = 0
                    
                keys.insert(0, PRI)
                desc[PRI] = 'int not null auto_increment'
            else:
                desc[PRI] += ' not null'

            def sort_key(key):
                if key == PRI:
                    return 0, len(key), key

                if key == 'training':
                    return 3, len(key), key
                
                if dtype[key] is str:
                    if desc[key] == 'text':
                        return 1, 65536, key

                    m = re.search(r'\d+', desc[key])
                    return 1, int(m[0]), key
                         
                return 2, len(key), key

            keys.sort(key=sort_key)
            print('keys =', keys)

            desc = ',\n'.join(map(lambda key : f"`{key}` {desc[key]}", keys))
            sql_create_table = f"CREATE TABLE `{database}`.`{table}` ({desc}, PRIMARY KEY (`{PRI}`)) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci PARTITION BY KEY() PARTITIONS 8"
            print(sql_create_table)
            try:
                self.execute(sql_create_table)
            except Exception as e:
                print(e)
                raise e
            desc = self.desc_table(table)
        
        has_training_field = False
        
        char_length = [256] * len(desc)
        dtype = [None] * len(desc)
        for i, (Field, Type, *_) in enumerate(desc):
            dtype[i] = Type = str(Type, encoding="utf-8")
            if Field == 'training':
                has_training_field = True
                
            if Type in ('text', 'json'):
                char_length[i] = 65535
                continue
            
            elif Type == 'mediumblob':
                char_length[i] = 16 * 1024 * 1024 - 1
                continue

            if m := re.compile(r"varchar\((\d+)\)").match(Type):
                char_length[i] = int(m[1])
                
        truncate = kwargs.get('truncate')
        def create_tsv(lines, step):
            import tempfile
            folder = tempfile.gettempdir()
                
            if '/' in table:
                from std.file import mkdir
                from os.path import dirname
                mkdir(dirname(folder + '/' + table))

            for i in range(0, len(lines), step):
                tsv = folder + '/%s-%d.tsv' % (table, i)
                with open(tsv, 'w', encoding='utf8') as file:
                    for args in lines[i:i + step]:
                        if isinstance(args, tuple):
                            args = [*args]
                        elif isinstance(args, dict):
                            args = [args.get(Field) for Field, *_ in desc]
                            
                        for i, arg in enumerate(args):
                            if isinstance(arg, set):
                                arg = [*arg]

                            if isinstance(arg, (list, tuple, dict)):
                                cbytes = std.json_encode(std.json_encode(arg))[1:-1]
                            elif isinstance(arg, str):
                                cbytes = std.json_encode(arg)[1:-1]
                            elif isinstance(arg, bytes):
                                if len(arg) > char_length[i]:
                                    print(args)
                                    print('args[%d] exceeds the allowable length %d' % (i, char_length[i]))
                                    arg = arg[:char_length[i]]
                                    
                                cbytes = arg.decode()
                            elif arg is None:
                                cbytes = 'null'
                            else:
                                cbytes = str(arg)

                            if not ignore:
                                if is_varchar(dtype[i]):
                                    if len(arg) > char_length[i]:
                                        if truncate:
                                            print('truncating the data to maximum length:', char_length[i], ", since its length is", len(arg))
                                            arg = arg[:char_length[i]]
                                            cbytes = std.json_encode(arg)[1:-1]
                                        else:
                                            print(args)
                                            print('args[%d] exceeds the allowable length %d, since its length is %d' % (i, char_length[i], len(arg)))
                                            args = None
                                            break
                                else:
                                    if len(cbytes) > char_length[i]:
                                        if truncate:
                                            print('truncating the data to maximum length:', char_length[i], ", since its length is", len(cbytes))
                                            cbytes = cbytes[:char_length[i]]
                                        else:
                                            print(args)
                                            print('args[%d] exceeds the allowable length %d' % (i, char_length[i]))
                                            args = None
                                            break
                            args[i] = cbytes
                        
                        if args:
                            if has_training_field and len(args) < len(desc):
                                args.append(str(random.randint(0, 1)))

                            for i, arg in enumerate(args):
                                if '\t' in arg or '\n' in arg:
                                    print(f'error detected: tab or newline found in Field: {desc[i][0]}')
                                    for (Field, Type, Null, Key, *_), arg in zip(desc, args):
                                        if Key:
                                            print(Field, '=', arg)
                                    print()
                                    break
                            else:
                                print('\t'.join(args), file=file)

                from std.file import eol_convert
                eol_convert(tsv)
                yield tsv
                
        rowcount = 0
        for tsv in create_tsv(array, step):
            rowcount += self.load_data_from_tsv(table, tsv, delete=delete, ignore=ignore, **kwargs)
        return rowcount

    def process_file(self, file, **kwargs):
        if file.endswith('.json'):
            with open(file, 'r', encoding='utf8') as f:
                yield json.loads(f.read())
        elif file.endswith('.jsonl'):
            with open(file, 'r', encoding='utf8') as f:
                for line in f:
                    yield json.loads(line)
        elif file.endswith('.parquet'):
            for _, row in pd.read_parquet(file).iterrows():
                yield json.loads(row.to_json())
        elif file.endswith('.zip'):
            with zipfile.ZipFile(file, 'r') as zip_ref:
                for file_name in zip_ref.namelist():
                    if file_name.endswith('.json'):
                        with zip_ref.open(file_name) as json_file:
                            yield json.loads(json_file.read().decode('utf-8'))
                    elif file_name.endswith('.jsonl'):
                        with zip_ref.open(file_name) as jsonl_file:
                            for line in jsonl_file:
                                yield json.loads(line.decode('utf-8'))
        elif file.endswith('.tar.gz'):
            with tarfile.open(file, 'r:gz') as tar:
                for member in tar.getmembers():
                    if not member.isfile():
                        continue
                    if member.name.endswith('.json'):
                        if f := tar.extractfile(member):
                            yield json.loads(f.read().decode('utf-8'))
                    elif member.name.endswith('.jsonl'):
                        if f := tar.extractfile(member):
                            for line in f:
                                yield json.loads(line.decode('utf-8'))
        elif file.endswith('.jsonl.gz'):
            with gzip.open(file, 'rt', encoding='utf-8') as f:
                for line in f:
                    yield json.loads(line)
        elif file.endswith('.json.gz'):
            with gzip.open(file, 'rt', encoding='utf-8') as f:
                yield json.loads(f.read())
        elif file.endswith('.xlsx'):
            map = kwargs.get('map', None)
            for _, row in pandas.read_excel(file).iterrows():
                obj = row.to_dict()
                if map:
                    if obj := map(obj):
                        yield obj
                else:
                    yield obj

    def load_data(self, table, *args, **kwargs):
        if args:
            data, = args
            if isinstance(data, str):
                if os.path.isdir(data):
                    array = []
                    for file in std.listdir(data, ext='parquet'):
                        for _, row in pd.read_parquet(file).iterrows():
                            array.append(json.loads(row.to_json()))
                    return self.load_data_from_list(table, array, **kwargs)
                else:
                    return self.load_data_from_tsv(table, data, **kwargs)
            return self.load_data_from_list(table, data, **kwargs)
        else:
            if os.path.isdir(table):
                path = table
                table = os.path.basename(table)
            elif os.path.isfile(table):
                path = table
                table = os.path.splitext(os.path.basename(table))[0]
            else:
                path = None
            if replace := kwargs.pop('replace', None):
                ...
            else:
                [[count]] = self.query(f"select count(*) from information_schema.tables WHERE table_name = '{table.replace('/', ':')}'")
                if count:
                    print(table, 'already exists, skipping')
                    return
            array = []
            if path:
                if os.path.isdir(path):
                    for file in tqdm(std.listdir(path, **kwargs)):
                        array.extend(self.process_file(file, **kwargs))
                else:
                    array.extend(self.process_file(path, **kwargs))
            else:
                try:
                    data = load_dataset(table, **kwargs)
                except ValueError as e:
                    err = str(e)
                    print(err)
                    if m := re.search(r"Please pick one among the available configs: \['([^']+)', '([^']+)'\]", err):
                        data = defaultdict(list)
                        for name in m.groups():
                            dataset = load_dataset(table, name=name)
                            for key in dataset:
                                data[key] += dataset[key]
                    else:
                        raise e
                for key in data:
                    key = key.lower()
                    if key.startswith('train'):
                        training = 1
                    elif key.startswith('test'):
                        training = 0
                    elif key.startswith('dev') or key.startswith('val'):
                        training = 2
                    else:
                        print('unrecognized key', key, 'from', data.keys())
                        training = 3
                    
                    for obj in tqdm(data[key], desc=f'load_data rows[{key}]'):
                        obj['training'] = training
                        array.append(obj)
            return self.load_data(table.replace('/', ':'), array, replace=replace)

    def load_data_from_tsv(self, table, tsv, delete=True, **kwargs):
        table = format_table(table)
        start = time.time()
        tsv = tsv.replace('\\', '/')
        if kwargs.get('replace'):
            duplicate_key_handler = 'replace '
        elif kwargs.get('ignore'):
            duplicate_key_handler = 'ignore '
        else:
            duplicate_key_handler = ''
        sql = f'load data local infile "%s" {duplicate_key_handler}into table %s character set utf8mb4' % (tsv, table)
        print('executing: ', sql)
        
        local_infile = True
        for Variable_name, Value in self.query("show global variables like 'local_infile'"):
            assert Variable_name == 'local_infile'
            if Value == 'OFF':
                local_infile = False

        if not local_infile:
            self.execute('set global local_infile = 1')
            
# in my.ini:
# [mysql]
# local-infile=1
#
# [mysqld]
# local-infile=1
            
        try:
            rowcount = self.execute(sql)
        except Exception as e:
            print(e)
            rowcount = 0

        print('time cost =', (time.time() - start))
        if delete:
            print("os.remove(tsv)", tsv)
            try:
                os.remove(tsv)
            except:
                exit()

        return rowcount

    def select(self, *args, **kwargs):
        if isinstance(args[0], (list, tuple)):
            fields, *args = args
            assert fields
            star = ', '.join(fields)
        else:
            star = '*'
            
        if args:
            table, *args = args
        else:
            table = kwargs.pop('table')

        desc = self.desc_table(table)
        desc = {Field: str(Type, encoding='utf8') for Field, Type, *_ in desc}

        table = format_table(table)
        sql = f"select %s from {table} "
        
        fetch_size = kwargs.pop('fetch_size', None)
        limit = kwargs.pop('limit', None)
        
        where = kwargs.pop('where', None)
        offset = kwargs.pop('offset', None)
        order = kwargs.pop('order', None)
        dictionary = kwargs.pop('dictionary', None)
        conditions = []
        quite = kwargs.pop('quite', None)

        for field, value in kwargs.items():
            if isinstance(value, (tuple, list, set)):
                value = ', '.join(std.json_encode(value) for t in value)
                value = value.replace('%', '%%')
                conditions.append(f"{field} in ({value})")
            else:
                op = '='
                if isinstance(value, str):
                    value = std.json_encode(value)
                    value = value.replace('%', '%%')
                    if desc[field] in ('json', 'text'):
                        op = 'regexp'

                conditions.append(f"{field} {op} {value}")

        if where:
            conditions.append(where)
            
        if conditions:
            sql += 'where ' + ' and '.join(conditions)
            
        sql_select = sql % star
        if not quite:
            print('sql =', sql_select)
        if fetch_size:
            if limit is None:
                [[limit]] = self.query(sql % 'count(*)')

            if offset is None:
                offset = 0
            
            if order == 'rand()':
                order = None
                from random import shuffle
                random.seed(1234)
            else:
                shuffle = lambda x : x

            for off in range(0, limit, fetch_size):
                # print('offset =', off + offset)
                [*data] = self.query(sql_select, order=order, limit=fetch_size, offset=off + offset, dictionary=dictionary)
                shuffle(data)
                yield from data
        else:
            yield from self.query(sql_select, order=order, limit=limit, offset=offset, dictionary=dictionary)

    def __call__(self):
#         import mysql.connector.pooling
#
#         config = {
#           "user": "yourusername",
#           "password": "yourpassword",
#           "host": "yourhost",
#           "database": "yourdatabase"
#         }
#
#         cnxpool = mysql.connector.pooling.MySQLConnectionPool(pool_name="mypool", pool_size=20, **config)
#
#         cnx = cnxpool.get_connection()
#
#         cursor = cnx.cursor()
#         cursor.execute("SELECT * FROM mytable")
#
#         cursor.close()
#         cnx.close()
        return MySQLConnector()


instance = MySQLConnector()


def is_number(Type):
    return re.match(r'int\(\d+\)|double', Type)


def is_int(Type):
    return re.search(r'int\(\d+\)', Type)


def is_float(Type):
    return re.match('double', Type)


def is_varchar(Type):
    return re.match(r'varchar\(\d+\)', Type)


def is_enum(Type):
    return re.match(r'enum\((\S+)\)', Type)
    
def quote(s):
    return s.replace("'", "''").replace("\\", r"\\")


def mysqlStr(value, Type=None):
    if isinstance(value, (int, float)):
        return value
    value = value.replace("'", "''")
    value = std.json_encode(value)
    return "'%s'" % value


if __name__ == '__main__':
    instance.load_data('AI-MO:NuminaMath-CoT', r'F:\gitlab\assets\math')

#ln -s /usr/local/mysql/mysql.sock /tmp/mysql.sock
#mysql -uuser -puser -Daxiom