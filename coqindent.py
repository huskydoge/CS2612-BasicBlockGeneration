#!/usr/bin/python
# -*- coding: utf-8 -*-

import os
import sys
import time
import re
from subprocess import Popen, PIPE, STDOUT
from optparse import OptionParser
from tqdm import tqdm

parser = OptionParser(usage="usage: %prog [options] coqtop-invocation < input.v > output.v")
parser.add_option('-i', '--subgoal-indent', default='  ', metavar='STR', dest='subgoal_indentation',
                  help='indent each additional subgoal by STR (default: "%default")')
parser.add_option('-w', '--wrap', metavar='N', type='int', dest='wrap',
                  help='wrap at natural break points after N columns')
parser.add_option('--erase-empty-lines', default=False, dest='eraseEmptyLines', action='store_true',
                  help='erase empty lines in proof scripts')
parser.add_option("--add-proof", default=False, dest='addProof', action='store_true',
                  help='begin multi-line proofs with "Proof."')

(options, remaining_args) = parser.parse_args()

if not remaining_args:
    parser.error("Missing coqtop-invocation.")

coq = Popen(remaining_args, stdin=PIPE, stdout=PIPE, stderr=STDOUT)

sgre = re.compile('^(\d+) subgoal')
is_prompt = re.compile(r"((\n)|^)[\w_']+ < $")


def readuntilprompt():
    s = ""
    while True:
        s += coq.stdout.read(1).decode('utf-8')
        if s.endswith(" < ") and is_prompt.search(s):
            return s


def split_indent(s):
    i = 0
    while i != len(s) and s[i].isspace():
        i += 1
    return s[:i], s[i:]


def to_be_continued(l):
    return not (l.endswith('.\n') or l.endswith("*)\n"))


subgoals = 0
extra = 0
seen_Proof = False
line_cont = None
pending_line = None
base_indentation = ''


def subgoals_changed(new_subgoals):
    global subgoals
    global pending_line
    if subgoals == new_subgoals + 1:
        if pending_line:
            lstripped = pending_line.lstrip()
            spl = lstripped.split(". ")
            print(' ' * (len(pending_line) - len(lstripped) - 1), lstripped)
            pending_line = None
    subgoals = new_subgoals


def print_Proof_if_necessary():
    global seen_Proof
    if options.addProof and not seen_Proof:
        print(base_indentation + "Proof.")
        seen_Proof = True


def subgoal_indentation():
    return base_indentation + options.subgoal_indentation * subgoals

cnt = 0
pbar = tqdm(sys.stdin, desc="Indenting", unit=" lines")
for l in pbar:
    l = l.rstrip() + '\n'
    cnt += 1
    pbar.set_description("Indenting line %d" % cnt)

    prompt = readuntilprompt()
    m = sgre.search(prompt)

    if prompt.find("Proof completed.") != -1 or prompt.find(" is defined") != -1:
        subgoals_changed(0)
        seen_Proof = False
    elif m:
        subgoals_changed(int(m.group(1)))

    if pending_line:
        print(pending_line)
        pending_line = None

    indentation, content = split_indent(l)

    if content.startswith("Proof"):
        seen_Proof = True

    if content[:1].isupper() and subgoals == 0:
        base_indentation = indentation

    if content == '':
        if subgoals == 0 or not options.eraseEmptyLines:
            print()
    elif subgoals == 0 or content.startswith("Proof"):
        print(l, end='')
    else:
        if line_cont is not None:
            if options.wrap and len(line_cont + l.strip()) > options.wrap:
                print_Proof_if_necessary()
                print(subgoal_indentation() + line_cont)
                extra += 1
                line_cont = '  ' * extra + l.strip()
            else:
                line_cont += ' ' + l.strip()
            if not to_be_continued(l):
                print(subgoal_indentation() + line_cont)
                line_cont = None
                extra = 0
        else:
            if not to_be_continued(l):
                print_Proof_if_necessary()
                pending_line = subgoal_indentation() + '  ' * extra + l.strip()
            else:
                line_cont = l.strip()

    coq.stdin.write(l.encode('utf-8'))

assert subgoals == 0
if pending_line:
    print(pending_line)