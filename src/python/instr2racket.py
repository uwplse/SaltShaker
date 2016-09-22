#!/usr/bin/env python

import subprocess
import itertools
import re
import sys

instr = sys.argv[1] # try: "addl %eax, %edx"

stokeout = subprocess.check_output(["stoke", "debug", "formula", "--smtlib_format", "--show_unchanged", "--code", instr]).split('\n')

formula = list(itertools.dropwhile(lambda l: l != "Formula:", stokeout))[2:-5]

registers = []

print "#lang s-exp rosette"
print
print "; This file was automatically generated; do not edit!"
print
print "(require \"../state.rkt\")"
print "(provide run)"
print
print "(define (run s)"

for f in formula:
  if f != "":
    (dst, code) = re.match("^%([a-z0-9]+) *: (.+)$", f).groups()
    code = re.sub("%([a-z0-9]+)", "(state-\\1 s)", code)
    registers.append(dst)
    print "  (define new-" + dst + " " + code + ")"

print
print "  (state " + " ".join(["new-"+r for r in registers]) + "))"

