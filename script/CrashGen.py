import binascii
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model

filename = 'crash.jp2'
with open(filename, 'rb') as f:
    content = f.read()

smt_file_name = "crash.smt2"
with open(smt_file_name, 'rb') as smt_file:
    str_formula = smt_file.read()

# print(str_formula)

parser = SmtLibParser()
script = parser.get_script(cStringIO(str_formula))
formula = script.get_last_formula()
model = get_model(formula, solver_name="z3")
model = model.__dict__['z3_model']
print(model)
byte_array = dict()
for dec in model.decls():
    if dec.name() == "A-data":
        var_list = model[dec].as_list()
        for pair in var_list:
            if type(pair) == list:
                index = pair[0].as_long()
                value = pair[1].as_long()
                hex_value = hex(value)
                if (len(str(hex_value)) % 2) == 0:
                    value = binascii.unhexlify('%x' % value)
                else:
                    value = binascii.unhexlify('0%x' % value)
                byte_array[index] = value

# print(byte_array.keys())
index = 0
with open("crash-gen.jp2", 'w') as gen_file:
    for byte in content:
        if index in byte_array.keys():
            new_byte = byte_array[index]
            gen_file.write(new_byte)
        else:
            gen_file.write(byte)
        index += 1

# for i in [96, 109, 111]:
# 	print(binascii.hexlify(content[i]))



