#!/usr/bin/env bash

compare=/x86sem/src/racket/compare.rkt

# Broken, does not compute the right result
# always multiplies with %eax, stores result in %eax:%edx
$compare "mull %ebx" 
$compare "mull %ebx" rdx
$compare "mull %ebx" of cf rdx
$compare "subl %ebx, %eax" 
$compare "subl %ebx, %eax" of af pf

# Mostly Working, but sets all flags incorrectly (maybe due to 64 vs 32bit)
$compare "addl %ebx, %eax"
$compare "addl %ebx, %eax" of pf
$compare "addl %ebx, %eax" of pf sf
$compare "addl %ebx, %eax" of pf sf cf zf
$compare "addl %ebx, %eax" of pf sf cf zf af

# Broken only for parity
$compare "notl %ebx"
$compare "andl %ebx, %eax"
$compare "andl %ebx, %eax" pf
$compare "orl %eax, %ebx"
$compare "orl %eax, %ebx" pf
$compare "xorl %ebx, %eax"
$compare "xorl %ebx, %eax" pf
$compare "movl %ebx, %eax"

# 
# # $compare "imull %ebx"   # coq takes a bunch of arguments that I don't understand

# Message: Could not match opcode/operands to an x86-64 instruction
# $compare "shll %ebx, %eax"
# $compare "shrl %ebx, %eax"

