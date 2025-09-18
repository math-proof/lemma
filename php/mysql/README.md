# <center> Mysql操作指南

## windows版本安装

直接使用wampserver内置的mysql使用方法：  
清空D:\wamp64\binmysql\mysql8.0.21\data内的所有内容！  
如果没有data文件夹，新建一个data文件夹。  

cd D:\wamp64\binmysql\mysql8.0.21\bin  
然后执行：  
mysqld --initialize --console  

  
鼠标左键后选择wamp图标中的MySQL 8.0.21->Service administration (wampmysqld64)->install Service  


此时输入命令services.msc可以查看服务已被安装：  


鼠标左键后选择wamp图标中的MySQL 8.0.21->MySQL Console   



输入之前的password后就登陆成功了：  


下载地址：
https://dev.mysql.com/downloads/mysql/
然后根据不同的操作系统，选择不同版本的MYSQL即可。
python调用mysql使用
pip3 install mysql-connector

windows下安装mysql8.0并集成到wamp中的方法：
参考网址：
https://blog.csdn.net/liuxl57805678/article/details/88546263


放在自己的wamp环境下的D:\wamp64\bin\mysql目录下  


解压重命名为mysql8.0.17  
把原始mysql版本目录下的my.ini和wampserver.conf 文件拷贝到mysql8.0.17目录中，并更改my.ini文件中的配置路径信息：  
basedir="D:/wamp64/bin/mysql/mysql8.0.17"  
datadir="D:/wamp64/bin/mysql/mysql8.0.17/data"  
lc-messages-dir="D:/wamp64/bin/mysql/mysql8.0.17/share"  


设置环境变量: (D:\wamp64\binmysql\mysql8.0.17\bin =>PATH)  
Path += D:\wamp64\binmysql\mysql8.0.21\bin  


初始化Mysql  （一定要在mysql8.0.17的bin目录下执行）  
mysqld --initialize --console  

如果之前安装过，请执行sc delete MySQL
如图：

    

A temporary password is generated for root@localhost: qu7(nF2kg4%k  
执行：  
mysqld -install  
  

启动mysql  
 
输入命令：mysql -uroot -pqu7(nF2kg4%k


如果不支持cmd输入密码，则输入mysql -uroot -p然后再键入密码，如图：  
  

输入show databases;  
会出现以下提示：  
   

输入以下命令：  
alter user 'root'@'localhost' identified by '123456'; flush privileges;  
  
然后再输入：  
show databases;  
  

  


## Linux版本安装
假设当前目录为httpd和php的安装目录：  
git clone --depth=1 https://github.com/cosmosZhou/shell.git  

cd shell/mysql  
make 

make start

mysql -uroot -plamp.sh  
报以下错误：  
ERROR 2002 (HY000): Can't connect to local MySQL server through socket '/tmp/mysql.sock' (2)
ERROR 2002 (HY000): Can't connect to local MySQL server through socket '/var/run/mysqld/mysqld.sock' (2)  

### 方法1
然后创建软连接即可：
ln -s ~/mysql/mysql.sock /tmp/mysql.sock  
### 方法2
mysql -uroot -plamp.sh --socket ~/mysql/mysql.sock  

## mysql启动与关闭

在windows系统中使用services.msc命令来打开服务管理界面：  
  
  

选择mysql80打开如图：  
  

单击“停止(T)”或“启动(S)”即可实现mysqlr 停止和启动。  
如果是linux系统，使用以下命令即可：  
service mysql start   
service mysql stop   
service mysql restart  
 #mysqladmin -uroot shutdown　　  

tasklist|findstr "mysql"  
taskkill/f /t /im mysqld.exe  
net stop mysql  
net start mysql  


## mysql登陆
使用以下命令可登陆mysql数据库：  
mysql -h 192.168.3.67 -P 3306 -uroot -p123456  
mysql -uroot -p123456 -Dcorpus --local-infile=1  
其中-h指定mysql服务所在的IP地址，如果需要访问远程mysql服务可以用到该参数。  
-P是端口号  
-u是用户名  
-p是密码  

使用以下命令可以设置默认用户名及密码：  
mysql_config_editor set --host=localhost --user=root --password=123456  

在访问远程MYSQL时如果MYSQL版本不一致会登陆失败，  
此时要在服务端作以下设置：  
create user 'root'@'%' identified by '123456';    

如果报错参考  
https://blog.csdn.net/u011575570/article/details/51438841  
drop user 'root'@'%';  


grant all privileges on *.* to 'root'@'%' with grant option;  
flush privileges;  
ALTER USER 'root'@'%' IDENTIFIED WITH mysql_native_password BY '123456';  
然后在用户端就可以远程访问了。  

如果报以下错误：  
Mysql远程登录报错：Host '192.168.1.3' is not allowed to connect to this MySQL server  
登录数据库：mysql -u root -p123456  
mysql>use mysql;  
mysql>update user set host = '%' where user = 'root';  
mysql>select host, user from user;  
mysql>flush privileges;  
参考网址：  
https://www.cnblogs.com/mindouer-2016/p/7685821.html  


## 修改数据储存地址

Mysql默认数据储存地址放在系统盘，会导致系统运行速度变慢，最好把数据储存地址改到其它盘。  
打开以下文件：  
 C:\ProgramData\MySQL\MySQL Server 8.0\my.ini  
 
   

修改成:  
 #datadir=C:/ProgramData/MySQL/MySQL Server 8.0/Data  
datadir=E:/MySQL/Data  
同时将C:/ProgramData/MySQL/MySQL Server 8.0/Data内容复制到E:/MySQL/Data  
然后重启MYSQL即可。  
输入 show variables like '%datadir%';  
直接使用wampserver内置的mysql使用方法：   

 #using the following command line to set the user and password for mysql  
 #mysql_config_editor set --host=localhost --user=root --password=123456  
 #reference:   
 #https://dev.mysql.com/doc/dev/connector-python/8.0/
 
## 数据库配置
配置my.ini、my.cnf  
[mysql]  
local-infile=1  

[client]  
port=3306  

[mysqld]  
tmp_table_size=134217728  
innodb_buffer_pool_size=1073741824  
bind-address=0.0.0.0  

port=3306  
default_authentication_plugin=mysql_native_password  
local-infile=1  

 #vim /etc/mysql/my.cnf  
 #secure-file-priv = ""  
 #show variables like 'secure%';  
 #SELECT @@global.secure_file_priv;  
 #in the server side:  
 #create user 'root'@'%' identified by '123456';  
 #grant all privileges on *.* to 'root'@'%' with grant option;  
 #flush privileges;  
 #ALTER USER 'root'@'%' IDENTIFIED WITH mysql_native_password BY '123456'  

 #then in the user side:  
 #mysql -h192.168.3.67 -P3306 -uroot -p123456 -Dcorpus  
 
## 数据传输

 #execute sql file:  
 #mysql> source d:/myprogram/database/db.sql;  

 #export structure and data  
mysqldump -h localhost -uroot -p123456 corpus > corpus.sql  
(注意末尾没有分号;)  
mysqldump -h localhost -uroot -p123456 corpus structure > structure.sql  

 #export structure only  
 #mysqldump -h localhost -uroot -p123456  -d corpus > corpus.sql  
 #mysqldump -h localhost -uroot -p123456  -d corpus structure > structure.sql  

 #export data only  
 #select * from structure into outfile "D:/wamp64/tmp/structure.tsv";  
select * from service into outfile "/var/lib/mysql-files/service-9-25.tsv";  
If the following message prompts:  
The MySQL server is running with the --secure-file-priv option so it cannot execute this statement  

  

show variables like 'secure_file_priv';

  

在windows下做如下修改：  
  


Then retart the mysql server;
  

in linux: do the following:  
  

Then, execute:  
sudo service mysql restart  


 #import data only  
 #service mysql stop  
 #sudo mysqld_safe 
使用load data local infile指令可能会报以下错误：  
ERROR 1148 (42000): The used command is not allowed with this MySQL version  
如果是从php脚本服务中调用load data,在php.ini中添加如下配置：  
在section  
[MySQLi]下添加：  
mysqli.allow_local_infile = On  
  


show global variables like 'local_infile';  
set persist local_infile = 1;  
mysql里面也要进行如下配置：  
add the following line into ~/php/etc/php.ini  / D:\wamp64\bin\apache\apache2.4.39\bin\php.ini (Windows Version);  
mysqli.allow_local_infile = On  

add the following line into my.ini;  
[mysql]  
local-infile=1  
[mysqld]  
local-infile=1  
secure_file_priv=/tmp  
如果报错：  
ERROR 3549 (HY000): Variables cannot be persisted. Please retry.  
输入以下指令：  
set global local_infile = 1;  
 #mysql --local-infile=1 -uroot  
 #mysql --local-infile=1 -uroot -Dcorpus  


load data local infile "D:/wamp64/tmp/structure.tsv" into table structure character set utf8;  
load data local infile "/var/lib/mysql-files/intent.tsv" into table structure character set utf8;  
或者：  
load data local infile "/var/lib/mysql-files/intent.tsv" replace into table repertoire character set   utf8;  
load data local infile "D:/wamp64/tmp/intent-9-18.tsv" into table intent character set utf8;  
load data local infile "D:/wamp64/tmp/service-9-6.tsv" into table service character set utf8;  
在执行大数据传输时，比如以下语句，包含了上百万条记录的表：  
load data local infile "D:/wamp64/tmp/repertoire-9-18.tsv" into table repertoire character set utf8;  
可能会出现导入失败的问题，作以下处理：  
alter table `repertoire` drop key text;  
   


参考网址：  
https://blog.csdn.net/u010787690/article/details/80473419  

### 数据恢复：  
参考网址：  
https://www.cnblogs.com/zifeiy/p/9082870.html  
https://blog.csdn.net/airujingye/article/details/70526943  

使用 `.ibd` 文件来恢复 InnoDB 表的数据是一个高级操作，通常在你已经有了一个 `.ibd` 文件（可能来自于备份或其他数据库实例），但没有相应的 `.frm` 文件（包含表的元数据）时使用。以下是一个使用 `.ibd` 文件恢复 InnoDB 表的详细步骤：

#### 针对某个表，且知道该表结构

- 你有一个 `.ibd` 文件，它包含你想要恢复的数据。
- 你知道这个 `.ibd` 文件所属的表的原始名称和结构。
- 你有一个运行中的 MySQL 服务器实例，并且你有足够的权限在该服务器上操作。

##### 步骤：

##### 1. 创建新的数据库（如果还没有的话）

首先，确保你有一个新的数据库用于存放恢复的表。

```sql
CREATE DATABASE recovered_database;
USE recovered_database;
```

##### 2. 创建表的元数据

接下来，你需要创建一个具有与原始表相同结构的空表。你可以从备份中恢复 `.frm` 文件（如果有的话），或者手动创建表结构。如果你手动创建，确保字段类型、大小、索引等都与原始表一致。

```sql
CREATE TABLE recovered_table (
    -- 列出所有字段，索引等，与原始表结构一致
    id int(11) NOT NULL AUTO_INCREMENT,
    text varchar(128) NOT NULL,
    infix varchar(2048) NOT NULL,
    training tinyint(1) NOT NULL DEFAULT '1',
    PRIMARY KEY (id),
    UNIQUE KEY text_unique (text)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
```

注意：不要创建任何数据文件，因为我们将使用现有的 `.ibd` 文件。

##### 3. 丢弃新表的表空间

在创建了空表之后，你需要丢弃这个表的表空间，以便能够关联到现有的 `.ibd` 文件。

```sql
ALTER TABLE recovered_table DISCARD TABLESPACE;
```

这个命令会删除与 `recovered_table` 关联的 `.ibd` 文件（如果存在的话），但不会删除表结构。

##### 4. 将现有的 `.ibd` 文件移动到 MySQL 数据目录

现在，你需要将现有的 `.ibd` 文件移动到 MySQL 服务器的数据目录下对应的表文件夹中。通常，这个目录是 `/var/lib/mysql/`（在 Linux 系统上）或者是在 Windows 系统上的 MySQL 安装目录中的 `data` 文件夹。确保 `.ibd` 文件的名称与表名匹配，并且它位于正确的数据库文件夹内。

例如，如果你的 MySQL 数据目录是 `/var/lib/mysql/`，并且你的数据库名是 `recovered_database`，表名是 `recovered_table`，那么 `.ibd` 文件的完整路径应该是 `/var/lib/mysql/recovered_database/recovered_table.ibd`。    
    
再例如：192.168.18.131的地址为`/home/lizhi/mysql8/data/corpus`,其中`corpus`为数据库，这个目录下面有`corpus`所有表的`.ibd`文件。

##### 5. 导入表空间

现在，你可以告诉 MySQL 将现有的 `.ibd` 文件与 `recovered_table` 表关联起来。

```sql
ALTER TABLE recovered_table IMPORT TABLESPACE;
```

这个命令会告诉 MySQL 使用当前位于数据目录下的 `.ibd` 文件作为 `recovered_table` 的表空间。

##### 6. 验证数据恢复

最后，你可以查询表来验证数据是否已成功恢复。

```sql
SELECT * FROM recovered_table LIMIT 100;
```

这个查询将返回表的前100条记录，你可以检查它们是否与你期望的数据一致。

##### 注意事项

- 在执行这些操作之前，请确保你已经备份了所有相关的数据库和文件，以防万一出现任何问题。
- 确保 `.ibd` 文件没有损坏，并且是与表结构完全兼容的。如果 `.ibd` 文件与表结构不匹配，数据可能会损坏或无法正确读取。
- 在移动 `.ibd` 文件时，确保 MySQL 服务器已经停止或相应的表已经被锁定，以防止在移动过程中文件被修改或损坏。
- 如果你不确定 `.ibd` 文件是否完整或正确，最好不要在生产环境中直接尝试恢复。最好先在测试环境中验证恢复过程。 

#### 针对所有表，但不知道表结构
- 你有一个文件夹data (/path/to/data)，里面是所有表的 `.ibd` 文件。
- 你不知道这些`.ibd` 文件所属的表的原始名称和结构。
- 你想新建一个MySQL服务器，把这些备份数据读取出来。

##### 步骤：

##### 1. 安新新的MySQL服务器
```sh
shell/php
bash mysql.sh
```
按照提示步步操作即可  

##### 2. 把数据库data目录指向备份目录
```sh
sudo chown -R mysql:mysql /path/to/data
ln -s /path/to/data ~/mysql/data
```

##### 3. 重启MySQL服务器
```sh
bash ~/mysql/stop.sh
bash ~/mysql/start.sh
```

##### 4. 验证数据恢复

最后，你可以查询表来验证数据是否已成功恢复。

```sql
SELECT * FROM recovered_table LIMIT 100;
```



## Mysql错误处理
1.Warning: mysql_connect(): Server sent charset (255) unknown to the client  
https://www.cnblogs.com/zl0372/p/weiqing.html  
http://www.mamicode.com/info-detail-2333179.html  

2.Could not connect: The server requested authentication method unknown to the client  
https://blog.csdn.net/youcijibi/article/details/81153789  
https://blog.csdn.net/guoguicheng1314/article/details/80526111  

3.PHP Fatal error: Uncaught Error: Class 'mysqli' not found in......  
https://blog.csdn.net/qq_38287952/article/details/83412515  

apache2/bin/apachectl -k restart  
mysql报错：  
ERROR 1206 (HY000): The total number of locks exceeds the lock table size   

https://blog.csdn.net/dingweiye123/article/details/80994576  
3221225472 = 3*1024*1024*1024;  
SET global tmp_table_size =3221225472;   
show global variables like "%table_size%";  

SET global innodb_buffer_pool_size=3221225472;  
show global variables like "%buffer_pool_size%";  

alter table id2feature partition by key() partitions 128;  
关于delete from id2feature_ limit 10000  
关于delete后存储空间不变小的问题：  
使用 OPTIMIZE TABLE id2feature_;进行磁盘优化！  

若出现以下错误：  
本地计算机上的wampmysqld64服务启动后停止，某些服务在未由其他服务或程序使用时将自动停止.  
删除全部mysql安装目录文件，重新安装即可！  

Class 'mysqli' not found  

Uncaught Error: Class 'mysqli' not found  

找到apache所指定的phpForApache.ini  
extension处添加extension=php_mysqli  

这里要确保D:\wamp64\bin\php\php7.4.13\phpForApache.ini被apache所引用！
D:\wamp64\bin\apache\apache2.4.39\bin\php.ini  
它只是个链接，要打开实际所链接的.ini 文件才能生效！  



修改extension_dir ="d:/wamp64/bin/php/php7.4.13/ext/"  
添加extension=php_mysqli  


### caching_sha2_password
  

The server requested authentication method unknown to the client [caching_sha2_password]   
alter user 'root'@'localhost' identified by '123456'; flush privileges;  
alter user 'root'@'localhost' identified with mysql_native_password by '123456'; flush privileges;  
ALTER USER 'root' IDENTIFIED WITH mysql_native_password BY '123456';  

### delete binlog.000*** files
purge master logs before '2023-10-01 17:20:00';

### 表空间优化  
```sql
alter table test engine=InnoDB  

optimize table test  

ALTER TABLE test FORCE  
```
### Timeout exceeded in regular expression match  

```sql
show variables like 'regexp_time_limit';  

SET global regexp_time_limit = 512;   

show variables like 'regexp_stack_limit';  

```
### load data  
firstly, ensure the user exists: 
```
create user prod@localhost identified by 'prod';  
```
Access denied; you need (at least one of) the SUPER or SYSTEM_VARIABLES_ADMIN privilege(s) for this operation       

```sql
grant 
    drop, 
    file, 
    alter, 
    create, 
    select, 
    delete, 
    insert, 
    update, 
    show view,
    SYSTEM_VARIABLES_ADMIN,
    CREATE TEMPORARY TABLES
on 
    \*.\* 
to 
    prod@localhost;
```
file privilege is needed if error `Access denied; you need (at least one of) the FILE privilege(s) for this operation` is encountered.  

#### Malformed packet when load data local infile ...
add the following line into ~/php/etc/php.ini  / D:\wamp64\bin\apache\apache2.4.39\bin\php.ini (Windows Version);  
mysqli.allow_local_infile = On  
