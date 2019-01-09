from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model, Solver
import types

DEMO_SMTLIB= \
"""
(set-logic QF_AUFBV )
(declare-fun A-data () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert (and (= (_ bv108 8) (select A-data (_ bv2 32) ) ) (= (_ bv101 8) (select A-data (_ bv1 32) ) ) ) )
(check-sat)
"""

parser = SmtLibParser()
script = parser.get_script(cStringIO(DEMO_SMTLIB))
f = script.get_last_formula()

model = get_model(f, solver_name="z3")
print(model)

print(str(model.__dict__))
py_model = model.__dict__['z3_model']

for decl in py_model.decls():
    print(decl.kind())
    print(decl.name())
    print(decl.params())
    print(decl.range())
    print(py_model[decl])
    a = py_model[decl].as_list()
    for x in a:
        print(str(type(x) == list))
        print("x=" + str(x))


    # help(a)

# help(py_model)
# print(py_model)
# help(model.converter)