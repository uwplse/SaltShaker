#!/usr/bin/env python

import subprocess
import itertools
import re
import sys

instr = sys.argv[1] # try: "addl %eax, %edx"
file_ = sys.argv[2] # try: "out.rkt"

stokeout = subprocess.check_output(["stoke", "debug", "formula", "--smtlib_format", "--show_unchanged", "--code", instr]).split('\n')

formula = list(itertools.dropwhile(lambda l: l != "Formula:", stokeout))[2:-5]

registers = []

output = """
; This file was automatically generated; do not edit!"

(define (run s)
"""

for f in formula:
  if f != "":
    (dst, code) = re.match("^%([a-z0-9]+) *: (.+)$", f).groups()
    code = re.sub("%([a-z0-9]+)", "(state-\\1 s)", code)
    code = re.sub("TMP_BOOL_[0-9]+", "#f", code)
    registers.append(dst)
    output += "  (define new-%s %s)" % (dst, code)

output += "  (state %s))" % " ".join(["new-"+r for r in registers])

f = open(file_, "w")
f.write(output)
f.close()

print "stoke semantics written to %s" % file_
