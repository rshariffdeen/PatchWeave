from z3 import *
ctx = z3.Context()
s = z3.Solver(ctx=ctx)

f = s.from_file("/home/rshariffdeen/param-map")
print(s.check())
print(s.model())
m = s.model()



for decl in m.decls():
	print(decl.kind())
	print(decl.name())
	print(decl.params())
	print(decl.range())
	print(m[decl].body())
	print(m[decl].children())
	print("num = " + str(m[decl].num_vars()))
	print("isLambda = " + str(m[decl].is_lambda()))
	d = m[decl].__dict__
	print(d['ctx'].__dict__)
	help(d['ctx'])
	x = (m[decl].sexpr()).strip()
	l = eval(x)
	A = [0,1,2,3,4]
	B = [x for x in decl()]
	results = list()
	for k in A:
		results.append((m[decl])(k))
	print("res=", results)

print ("traversing model...")
for d in m.decls():
    print ("%s = %s" % (d.name(), m[d]))
print("eval = ")