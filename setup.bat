mkdir dist
del dist\*.tar.gz && python setup.py sdist && twine upload -r nexus dist/*.tar.gz
