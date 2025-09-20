# axiom

reference website:

http://www.axiom.top

latex is printed with the aid of the following project:

http://docs.mathjax.org/en/latest/  
https://github.com/mathjax/MathJax.git  

python is edited with the aid of the following project:

https://codemirror.net/5/  
https://github.com/codemirror/codemirror5  


# representation of html files
## requirements
python >= 3.10

## scripts to generate visualized html
git clone --depth=1 -b master https://github.com/cosmosZhou/axiom.git  
cd axiom  
python run.py  


open the folder target, and then you can browse the visualized structure of python and latex of axioms and theorems.  
to debug one single file, execute the following command:  
python run.py Discrete.Binom.eq.Add.Pascal  
or try to open and execute the python file directly:   
.\Lemma\Discrete/Binom/eq/Add/Pascal.py  


# IDE for online-debugging
In future, an online IDE with debugging functionality will be developed, based on the following projects:  
https://github.com/coder/code-server  
https://github.com/eclipse-theia/theia  
https://github.com/jupyterlab/jupyterlab  
https://github.com/sagemathinc/cocalc  

# Multiprocessing Debugging 
## VSCode
* debug the single-process program run.py using .vscode/launch.json where name = "Python: Current File"
* debug the multiprocessing program run.py using .vscode/launch.json where name = "Python: run.py"

## PyCharm
* In Settings (Ctrl+Alt+S)(File | Settings | Build, Execution, Deployment | Python Debugger) make these settings:
 - [x] Attach to subprocess automatically when debugging
 - [ ] Gevent compatible
 
* Set Breakpoint, make sure it is set with the following property (Ctrl+Shift+F8):

 | Option    | Config             |
 |-----------|--------------------| 
 | Enabled   | :white_check_mark: |
 | Suspended | Thread             |
 | Condition |                    |
* make necessary settings in Python Debug Configurations:

 | Option                      | Config                            |
 |-----------------------------|-----------------------------------| 
 | Name                        | run.py                            |
 | Python interpreter          | a local/remote Python interpreter |
 | Run Python script or module | script                            |
 | script                      | `$`ProjectFileDir`$`/run.py       |
 | Script parameters           | --parallel --processes=4          |
 | Working directory           | `$`ProjectFileDir`$`              |
 | Environment variables       | PYTHONUNBUFFERED=1                |
* press Shift+F9 to start multiprocessing debugging
* Uncheck `Tool | Deployment | Automatic Upload` if you want to manage the files uploading manually