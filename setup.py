
from setuptools import setup, find_packages
from os.path import join, dirname

setup(
    name='pyrefine',
    version='0.0.0',
    packages=['pyrefine'],
    install_requires=['z3-solver']
)