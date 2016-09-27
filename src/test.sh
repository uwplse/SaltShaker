#!/usr/bin/env bash

compare=/x86sem/src/racket/compare.rkt

# Broken only for parity
$compare "notl %ebx"
$compare "andl %ebx, %eax"
$compare "orl %eax, %ebx"
$compare "xorl  %ebx, %eax"
$compare "movl %ebx, %eax"

# Mostly Working, but sets all flags incorrectly (maybe due to 64 vs 32bit)
$compare "addl %ebx, %eax"
$compare "subl %ebx, %eax"

# Broken, does not compute the right result
$compare "mull %ebx"   # always multiplies with %eax, stores result in %eax:%edx
# $compare "imull %ebx"   # coq takes a bunch of arguments that I don't understand

# Message: Could not match opcode/operands to an x86-64 instruction
# $compare "shll %ebx, %eax"
# $compare "shrl %ebx, %eax"

