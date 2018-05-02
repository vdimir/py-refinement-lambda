# Pyrefine

Python code checker based on Hoare logic to develop verified software with refinement types.

[Z3](https://github.com/Z3Prover/z3) SMT-solver is used to prove statements about program.

## Requirements

* Python 3.5+
* [z3-solver](https://github.com/Z3Prover/z3)
* [pyparsing](http://pyparsing.wikispaces.com/)
* [ast](https://docs.python.org/3/library/ast.html) (build-in)

## Supported language elements

- [x] Function Definitions
- [x] Lambda Functions
- [x] If Statements
- [x] While Loops

## Usage
 To run checker script run:

`python -m pyrefine.__main__ ./examples/example.py`


To use checker import module with stub-functions:
```python
from pyrefine import *
```

Than you can use following code to create verified functions.
Note that variables should be declared using `c_` operator. 


```python
def func(<arg_list>):
    define_('<type_annotation>', 
            '<precondition>', 
            '<postcondition>')
    <statements>

func = define_('<type_annotation>', '<precondition>', '<postcondition>', 
               lambda x, y: ...)

constant = c_('<atomic_type>', <expr>)

while <expr>:
    loop_('<loop_invariant>', 
          '<bound_function>')
    <statements>
```

Explained example:

```python
def gcd(x, y):
    define_('int -> int -> int', # define function type
            'x > 0 and y > 0',   # precondition
            'ret > 0')           # postcondition
    t = c_('int', 0)
    while x != y:
        loop_('x > 0 and y > 0', # loop invariant
              'x + y')           # bound function to prove loop termitation
        if x > y:
            y, x = x, y
        assert y > x             # assets also checked statically
        y = y - x
    assert x == y          
    return y                     # y > 0
```

## Examples

You can find examples in [example.py](examples/example.py).

More examples in [test](test) folder.


