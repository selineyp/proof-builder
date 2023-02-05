import curses
import re
import string
import argparse
from curses import wrapper
from curses.textpad import Textbox, rectangle
import itertools
import time


regex_mapper = {'laE': {'re': '(.*) -> (.*) ∧ (?:[∀|∃].)?(.*)', 'gp': 3},
                'raE': {'re': '(.*) -> (?:[∀|∃].)?(.*) ∧ (.*)', 'gp': 3},
                'iI': {'re': '(.*) -> (.*)', 'gp': 2},
                'iE': {'re': '(.*) -> (.*)', 'gp': 2},
                'oI': {'re': '(.*) -> (.*)', 'gp': 2},
                '-I': {'re': '(.*), (.*) -> ', 'gp': 2}, }

available_keys = list(string.ascii_lowercase)
key_mapper = {}
special_chars = {'f': '∀', 'e': '∃', '-': '¬', 'a': '∧', 'i': '⊃', 'q': '≡', 'o': '∨', 'b': '⊥', 't': '⊤'}
binary = ['¬','∧','⊃','≡','∨']
avail_size = 0
last_proof_line = 0
assumptions = []
assumptions_idx = []


def getilhs(formula, sep):
    for i in range(len(formula)):
        if formula[i] == sep and balanced_paren_check(formula[0:i]) and balanced_paren_check(formula[i:]):
            return formula[0:i-1]
    return None

def getirhs(formula, sep):
    for i in range(len(formula)):
        if formula[i] == sep and balanced_paren_check(formula[0:i]) and balanced_paren_check(formula[i:]):
            return formula[i+1:]
    return None


def restore_keys():
    global available_keys
    available_keys = list(string.ascii_lowercase)


def help(stdscr):
    stdscr.clear()
    if len(steps) == 0:
        if '⊃' in filter(formula):
            lhs = getilhs(filter(formula), '⊃')
            if lhs is not None:
                stdscr.addstr('You may start by assuming {}'.format(lhs), PINK_AND_WHITE)
    else:
        if '⊃' in steps[-1][0]:
            lhs = getilhs(steps[-1][0], '⊃').split('->')[1]
            if lhs is not None:
                stdscr.addstr('You may start by assuming {} \n' .format(lhs), PINK_AND_WHITE)
        if '∨' in steps[-1][0]:
            lhs = getilhs(steps[-1][0], '∨').split('->')[1].strip()
            rhs = getirhs(steps[-1][0], '∨').strip()
            if lhs is not None and rhs is not None:
                stdscr.addstr('You may consider cases: first assume {} and prove, next assume {} and prove your goal \n'.format(lhs, rhs), PINK_AND_WHITE)
        if len(steps[-1][0].split('->')) > 1:
            rhs = steps[-1][0].split('->')[1].strip()
        else:
            rhs = steps[-1][0].split('->')[0].strip()
        if rhs[0] == '∃':
            z = re.findall('∃(.)(.*)', rhs)
            if len(z) > 0 and len(z[0]) == 2:
                ein = paran_filter(z[0][1])
                stdscr.addstr('You may assume {} and try to prove your goal.\n'.format(ein), PINK_AND_WHITE)
    stdscr.addstr('press any key to return...')
    stdscr.refresh()
    key = stdscr.getkey()
    if key:
        stdscr.clear()
        build(stdscr)

def build(stdscr):
    stdscr.addstr(1, 120, 'Inference Rules & Axioms')
    cheatsheet_win = curses.newwin(100, 100, 3, 100)
    cheatsheet_win.addstr(0, 0, '(loI)')
    cheatsheet_win.addstr(1, 0, 'premise: Γ -> F')
    cheatsheet_win.addstr(2, 0, 'conclusion: Γ -> F v G')
    cheatsheet_win.addstr(3, 0, '(roI)')
    cheatsheet_win.addstr(4, 0, 'premise: Γ -> G')
    cheatsheet_win.addstr(5, 0, 'conclusion: Γ -> F v G')
    cheatsheet_win.addstr(6, 0, '(iI)')
    cheatsheet_win.addstr(7, 0, 'premise: Γ, F -> G')
    cheatsheet_win.addstr(8, 0, 'conclusion: Γ -> F ⊃ G')
    cheatsheet_win.addstr(9, 0, '(-I)')
    cheatsheet_win.addstr(10, 0, 'premise: Γ, F -> ')
    cheatsheet_win.addstr(11, 0, 'conclusion: Γ -> ¬F')
    cheatsheet_win.addstr(12, 0, '(C)')
    cheatsheet_win.addstr(13, 0, 'premise: Γ -> ')
    cheatsheet_win.addstr(14, 0, 'conclusion: Γ -> F')
    cheatsheet_win.addstr(15, 0, '(vE)')
    cheatsheet_win.addstr(16, 0, 'premise: Γ -> FvG, Δ1,F -> Σ, Δ2,G -> Σ')
    cheatsheet_win.addstr(17, 0, 'conclusion: Γ, Δ1, Δ2  -> Σ')
    cheatsheet_win.addstr(18, 0, '(fI)')
    cheatsheet_win.addstr(19, 0, 'premise: Γ -> F(v)')
    cheatsheet_win.addstr(20, 0, 'conclusion: Γ -> ∀vF(v)')
    cheatsheet_win.addstr(21, 0, '(eE)')
    cheatsheet_win.addstr(22, 0, 'premise: Γ -> ∃vF(v), Δ,F(v) -> Σ')
    cheatsheet_win.addstr(23, 0, 'conclusion: Γ,Δ -> Σ')
    cheatsheet_win.addstr(24, 0, '(lrepl)')
    cheatsheet_win.addstr(25, 0, 'premise: Γ -> t1 = t2, Δ -> F(t1)')
    cheatsheet_win.addstr(26, 0, 'conclusion: Γ,Δ -> F(t2)')

    cheatsheet_win.addstr(27, 0, '(Ax1)')
    cheatsheet_win.addstr(28, 0, ' -> F v ¬F')

    cheatsheet_win.addstr(0, 40, '(W)')
    cheatsheet_win.addstr(1, 40, 'premise: Γ -> F')
    cheatsheet_win.addstr(2, 40, 'conclusion: Γ, Δ -> F')
    cheatsheet_win.addstr(3, 40, '(-E)')
    cheatsheet_win.addstr(4, 40, 'premise: Γ -> F, Δ -> ¬F')
    cheatsheet_win.addstr(5, 40, 'conclusion: Γ, Δ -> ')
    cheatsheet_win.addstr(6, 40, '(iE)')
    cheatsheet_win.addstr(7, 40, 'premise: Γ -> F, Δ -> F ⊃ G')
    cheatsheet_win.addstr(8, 40, 'conclusion: Γ, Δ -> G')
    cheatsheet_win.addstr(9, 40, '(laE)')
    cheatsheet_win.addstr(10, 40, 'premise: Γ -> F ∧ G')
    cheatsheet_win.addstr(11, 40, 'conclusion: Γ -> F')
    cheatsheet_win.addstr(12, 40, '(raE)')
    cheatsheet_win.addstr(13, 40, 'premise: Γ -> F ∧ G')
    cheatsheet_win.addstr(14, 40, 'conclusion: Γ -> G')
    cheatsheet_win.addstr(15, 40, '(aI)')
    cheatsheet_win.addstr(16, 40, 'premise: Γ -> F, Δ -> G')
    cheatsheet_win.addstr(17, 40, 'conclusion: Γ, Δ -> F ∧ G')
    cheatsheet_win.addstr(18, 40, '(fE)')
    cheatsheet_win.addstr(19, 40, 'premise: Γ -> ∀vF(v)')
    cheatsheet_win.addstr(20, 40, 'conclusion: Γ -> F(t)')
    cheatsheet_win.addstr(21, 40, '(eI)')
    cheatsheet_win.addstr(22, 40, 'premise: Γ -> F(t)')
    cheatsheet_win.addstr(23, 40, 'conclusion: Γ -> ∃vF(v)')
    cheatsheet_win.addstr(24, 40, '(rrepl)')
    cheatsheet_win.addstr(25, 40, 'premise: Γ -> t1 = t2, Δ -> F(t2)')
    cheatsheet_win.addstr(26, 40, 'conclusion: Γ,Δ -> F(t1)')
    cheatsheet_win.addstr(27, 40, '(Ax2)')
    cheatsheet_win.addstr(28, 40, 't=t')

    stdscr.addstr(1, 1, 'Type in this box to enter an assumption.')
    global avail_win, enter_win, error_win, rule_box, premises_box, formulas_box, box, assumption_win
    global premises_win, rule_win, formulas_win
    global avail_pages, displayed_page
    displayed_page = 0
    assumption_win = curses.newwin(1, 32, 3, 3)
    box = Textbox(assumption_win, insert_mode=True)
    stdscr.addstr(1, 60, 'Available Rules')
    avail_win = curses.newwin(22, 40, 3, 50)
    avail_pages = []

    stdscr.addstr(25, 53, 'Rule/axiom')
    rule_win = curses.newwin(1, 8, 27, 54)
    rule_box = Textbox(rule_win, insert_mode=True)
    rectangle(stdscr, 26, 53, 28, 62)
    stdscr.addstr(25, 69, 'Premises')
    premises_win = curses.newwin(1, 7, 27, 69)
    premises_box = Textbox(premises_win, insert_mode=True)
    rectangle(stdscr, 26, 68, 28, 77)
    stdscr.addstr(30, 60, 'Invent formula(s)')
    formulas_win = curses.newwin(1, 25, 32, 53)
    formulas_box = Textbox(formulas_win, insert_mode=True)
    rectangle(stdscr, 31, 52, 33, 85)

    error_win = curses.newwin(1, 40, 35, 52)

    rectangle(stdscr, 2, 2, 4, 36)
    stdscr.addstr(5, 2, '[f]:\\forall')
    stdscr.addstr(6, 2, '[e]:\exists')
    stdscr.addstr(7, 2, '[-]:\\neq')
    stdscr.addstr(8, 2, '[a]:\land')
    stdscr.addstr(9, 2, '[t]:\\top')

    stdscr.addstr(5, 20, '[i]:\\implies')
    stdscr.addstr(6, 20, '[q]:\equiv')
    stdscr.addstr(7, 20, '[o]:\lor')
    stdscr.addstr(8, 20, '[b]:\\bot')

    global proof_win
    stdscr.addstr(11, 1, 'Proof', GREEN_AND_BLUE)
    proof_win = curses.newwin(60, 50, 12, 1)

    stdscr.refresh()
    cheatsheet_win.refresh()
    cheatsheet_win.getch()

    rule_win.refresh()
    rule_win.getch()

    avail_win.getch()
    avail_win.refresh()

    proof_win.refresh()
    stdscr.refresh()

    print_proof()
    post_assumption_update(stdscr, 'proof_win', False, True, True)

    wait_for_direction(stdscr)

    key = stdscr.getkey()
    if key == 'KEY_RIGHT':
        post_assumption_update(stdscr, 'proof_win', True, True)
    elif key == 'KEY_UP':
        assumption_input(stdscr)
    elif key == 'KEY_ENTER':
        help(stdscr)

    proof_win.refresh()
    stdscr.refresh()
    stdscr.getch()



def balanced_paren_check(formula):
    stack = []
    for i in range(len(formula)):
        if formula[i] == '(':
            stack.append('*')
        elif formula[i] == ')':
            stack.pop()
    if len(stack) != 0:
        return False
    return True

def filter(text):
    t = text
    for k, v in special_chars.items():
        t = t.replace(k, v)
    t = t.rstrip()
    return t


def clear_inv():
    rule_win.clear()
    premises_win.clear()
    formulas_win.clear()
    rule_win.refresh()
    premises_win.refresh()
    formulas_win.refresh()


def isfree(i, v, formula):
    iq = None
    if '∀{}'.format(v) in formula:
        iq = formula.find('∀{}'.format(v))
    if '∃{}'.format(v) in formula:
        iq = formula.find('∃{}'.format(v))
    if iq is not None:
        if iq > i:
            return False
    else:
        return True


def isanyfree(v, formula):
    for i in range(len(formula)):
        if formula[i] == v:
            if isfree(i, v, formula):
                return True
            else:
                continue
    return False


def at_proof(stdscr):
    # currently only called when a proof step is removed
    proof_win.refresh()
    post_assumption_update(stdscr, 'proof_win', True)
    key = stdscr.getkey()
    if key == 'KEY_UP':
        assumption_input(stdscr)
    elif key == 'KEY_DOWN':
        invent_rules(stdscr)
    elif key.isdigit(key) and int(key) == 1:
        help(stdscr)


def fcheck(v, ac, q):
    i = 0
    acs = ac.strip()
    qs = q.strip()
    if len(acs) == len(qs):
        if acs == qs:
            return True
        for i in range(len(acs)):
            if (acs[i] == v and acs[i] != qs[i]) or (acs[i] != v and acs[i] == qs[i]):
                continue
            else:
                return False
    return True

def print_proof():
    global last_proof_line
    last_proof_line = 0
    for i, x in enumerate(steps):
        if i in assumptions_idx:
            ai = assumptions_idx.index(i)
            proof_win.addstr(last_proof_line, 0, 'A{}.'.format(ai+1))
            last_proof_line += 1
            proof_win.addstr(last_proof_line, 0, ' {}. {}'.format(i+1, x[0]))
            last_proof_line += 1
        else:
            if x[1]=='Ax1' or x[1]=='Ax2':
                proof_win.addstr(last_proof_line, 0, '{}. {}...axiom {} '.format(i+1, x[0], x[1]))
                last_proof_line += 1
            elif x[1].strip() != '':
                proof_win.addstr(last_proof_line, 0, '{}. {}...{} from {}'.format(i+1, x[0], x[1], ','.join(x[2])))
                last_proof_line += 1

    proof_win.refresh()

def display_page(stdscr, next):
    global displayed_page
    if next:
        lb = displayed_page + 1
        ub = displayed_page + 2
    else:
        lb = displayed_page - 1
        ub = displayed_page
    if len(avail_pages) >= ub*40:
        avail_win.clear()
        for i, s in enumerate(avail_pages[lb*40:ub*40]):
            avail_win.addstr(i, 0, s)
        if next:
            displayed_page = displayed_page + 1
        else:
            displayed_page = displayed_page - 1
        avail_win.refresh()


def wait_for_direction(stdscr):
    global last_proof_line
    key = None
    directions = ['KEY_UP', 'KEY_DOWN', 'KEY_RIGHT', 'KEY_LEFT']
    while key not in directions:
        key = stdscr.getkey()
        if key == 'KEY_UP':
            assumption_input(stdscr)
        elif key == 'KEY_RIGHT':
            post_assumption_update(stdscr, 'proof_win', True)
        elif key == 'KEY_DOWN':
            invent_rules(stdscr)
        elif key == 'KEY_LEFT':
            if len(steps) > 0:
                if len(steps)-1 in assumptions_idx:
                    assumptions_idx.remove(len(steps)-1)
                steps.pop()
                proof_win.clear()
                last_proof_line = 0
                print_proof()
                post_assumption_update(stdscr, 'proof_win', False, True)
                wait_for_direction(stdscr)


def rfilter(text):
    t = text
    for k, v in special_chars.items():
        t = t.replace(v, k)
    t = t.rstrip()
    return t


def assumption_check(derstep):
    r = re.findall('A([0-9]+)', derstep)
    if len(r) > 0 and len(r[0]) > 0:
        i = int(r[0][0])
        s = steps[assumptions_idx[i-1]][0]
        z = re.findall('{} -> (.*)'.format(derstep), s)
        if len(z) > 0:
            return z[0]


def substitutable(formula, v, term):
    # t is a variable w, and no part of F of the form KwG contains an occurrence of v which is free in F
    if term not in formula:
        return True
    elif '∀{}'.format(term) not in formula and '∃{}'.format(term) not in formula:
        return True
    elif '∀{}'.format(term) in formula:
        s = re.findall('∀{}(.*)'.format(term), formula)
        for s1 in s:
            G = s1[0]
            if v not in G:
                return True
            else:
                for i in G:
                    if G[i] == v:
                        if not isfree(i, v, G):
                            continue
                        else:
                            return False
                return True

def assumption_input(stdscr):
    global box, last_proof_line, assumptions_idx, steps
    box.edit()
    text = box.gather()
    #text = text.replace('\n', '')
    filt = filter(text)
    assumptions_idx.append(len(steps))
    steps.append(('A{} -> {}'.format(len(assumptions_idx), filt), 'assumption'))
    proof_win.addstr(last_proof_line, 0, 'A{}.'.format(len(assumptions_idx)))
    last_proof_line += 1
    proof_win.addstr(last_proof_line, 0, ' {}. A{} -> {}'.format(len(steps), len(assumptions_idx), filt))
    last_proof_line += 1
    while len(text) > 0:
        box.do_command(curses.KEY_BACKSPACE)
        text = box.gather()
    assumption_win.refresh()
    proof_win.refresh()
    post_assumption_update(stdscr, 'proof_win', False)
    stdscr.move(11, 6)
    stdscr.refresh()
    wait_for_direction(stdscr)
    #stdscr.refresh()


def paran_filter(s):
    s = s.strip()
    if s[0] == '(' and s[-1] == ')':
        return s[1:-1]
    else:
        with open('s.txt','a') as f:
            f.write(s)
        if s[0]=='∀' or s[0]=='∃':
            if s[2] == '(' and s[-1]==')':
                return s
            elif any([z in s for z in binary]):
                return '('+s+')'
            else:
                return s
        elif any([z in s for z in binary]):
            return '('+s+')'
        else:
            return s

def paran_add(s):
    s = s.strip()
    with open('s.txt','a') as f:
        f.write(s)
    if s[0]!='(':
        if s[0]=='∀' or s[0]=='∃':
            if s[2] == '(' and s[-1]==')':
                return s
            elif any([z in s for z in binary]):
                return '('+s+')'
            else:
                return s
        elif any([z in s for z in binary]):
            return '('+s+')'
        else:
            return s
    return s

def apply(typ, tup):
    if typ == 'oI':
        s = '{} -> {}'.format(tup[0], paran_filter(tup[1]))
    if typ == 'laE':
        s = '{} -> {}'.format(tup[0], paran_filter(tup[1]))
    if typ == 'raE':
        s = '{} -> {}'.format(tup[0], paran_filter(tup[2]))
    if typ == '-I':
        s = '{} -> ¬{}'.format(tup[0], tup[1])
    if typ == 'aI':
        s = '{} -> {} ∧ {}'.format(tup[0], tup[1], tup[2])
    if typ == 'iE':
        s = '{},{} -> {}'.format(tup[0], tup[1], paran_filter(tup[2]))
    if typ == 'iI':
        if len(tup[0]) > 0:
            s = '{} -> {} ⊃ {}'.format(tup[0], paran_filter(tup[1]), paran_filter(tup[2]))
        else:
            s = '-> {} ⊃ {}'.format(paran_filter(tup[1]), paran_filter(tup[2]))
    if typ == 'C':
        s = '{} -> {}'.format(tup[0], paran_filter(tup[1]))
    if typ == 'Ax1':
        s = '-> {} ∨ ¬{}'.format(tup, tup)
    if typ == 'Ax2':
        s = '-> {} = {}'.format(tup, tup)
    if typ == 'loI':
        s = '{} -> {} v {}'.format(tup[0], paran_add(tup[1]), paran_add(tup[2]))
    if typ == 'roI':
        s = '{} -> {} v {}'.format(tup[0], paran_add(tup[1]), paran_add(tup[2]))
    if typ == 'lrepl' or typ == 'rrepl':
        if tup[0] != '':
            s = '{} -> {}'.format(tup[0], paran_filter(tup[1].replace(tup[2], tup[3])))
        else:
            s = '-> {}'.format(paran_filter(tup[1].replace(tup[2], tup[3])))

    if typ == 'eI':
        f = tup[2]
        s = '{} -> ∃{}{}'.format(tup[0], paran_add(tup[1]), f)
    if typ == 'fE':
        s = '{} -> {}'.format(tup[0], paran_filter(tup[1]))
    if typ == 'fI':
        s = '{} -> ∀{}{}'.format(tup[0], tup[1], tup[2])
    if typ == 'eE':
        s = '{} -> {}'.format(tup[0], paran_filter(tup[1]))
    if typ == 'oE':
        s = '{} -> {}'.format(tup[0], paran_filter(tup[1]))
    return s

def dump_proof(stdscr):
    time.sleep(3)
    stdscr.clear()
    stdscr.addstr(0, 0, 'Proof completed, dumping to proof.txt.', PINK_AND_WHITE)
    stdscr.addstr(1, 0, 'press any key to exit..', PINK_AND_WHITE)
    stdscr.refresh()
    with open('proof.txt', 'w') as f:
        for i, x in enumerate(steps):
            if i in assumptions_idx:
                ai = assumptions_idx.index(i)
                f.write('A{}.'.format(ai+1)+'\n')
                f.write(' {}. {}'.format(i+1, x[0]) +'\n')
            else:
                if x[1] == 'Ax1' or x[1] == 'Ax2':
                    f.write('{}...{}'.format(i+1, x[0], x[1])+'\n')
                elif x[1].strip() != '':
                    f.write('{}. {}...{} from {}'.format(i+1, x[0], x[1], x[2])+'\n')
                else:
                    f.write('{}. {}...axiom {} '.format(i+1, x[2], x[0])+'\n')
    key = stdscr.getkey()
    if key:
        exit()


def check(stdscr):
    if 'q' in formula:
        lhs = formula.split('q')[0].strip()
        rhs = formula.split('q')[1].strip()
        lcheck = False
        rcheck = False
        for step in steps:
            if step[0] == '-> {}'.format(lhs):
                lcheck = True
            elif step[0] == '-> {}'.format(rhs):
                rcheck = True
        if lcheck and rcheck:
            dump_proof(stdscr)
    elif len(steps) > 0:
        if steps[-1][0].strip() == '-> {}'.format(filter(formula)):
            dump_proof(stdscr)

def newkey():
    if len(available_keys) > 0:
        if available_keys[0] != 'KEY_LEFT':
            return available_keys[0]
    return None

def invent_rules(stdscr):
    global last_proof_line, PINK_AND_WHITE
    rule_box.edit()
    rulein = rule_box.gather()
    rule = rulein.strip()
    premises_box.edit()
    premises = premises_box.gather()
    ps = [x.strip() for x in premises.strip().split(',') if x.strip() != '']
    formulas_box.edit()
    formulas = formulas_box.gather()
    formulas = formulas.strip()
    f = False
    err_msg = None
    premises_f = []
    if len(ps) > 0 and all([x.isdigit() for x in ps]) and len(steps) > int(ps[0])-1:
        premises_f.append(steps[int(ps[0])-1][0])
        if len(ps) > 1 and len(steps) > int(ps[1])-1:
            premises_f.append(steps[int(ps[1])-1][0])
    if len(ps) == len(premises_f):
        if rule == 'C':
            r = premises_f[0].split('->')
            if len(r) == 1:
                f = True
                nstep = apply(rule, r[0])
        elif rule == 'Ax1' or rule == 'Ax2':
            f = True
            nstep = apply(rule, formulas)
        elif rule == 'loI':
            if len(premises_f[0].split('->')) > 1:
                f = True
                nstep = apply(rule, [premises_f[0].split('->')[0].strip(), premises_f[0].split('->')[1].strip(), formulas])
        elif rule == 'roI':
            if len(premises_f[0].split('->')) > 1:
                f = True
                nstep = apply(rule, [premises_f[0].split('->')[0].strip(), formulas, premises_f[0].split('->')[1].strip()])
        elif rule == 'lrepl':
            r = re.findall('(.*) -> (.*)=(.*)', premises_f[0])
            if len(r) > 0:
                gamma = r[0][0].strip()
                t1 = r[0][1].strip()
                t2 = r[0][2].strip()
                lis = premises_f[1].split('->')
                if len(lis) == 1:
                    d = ''
                    ft2 = lis[0].strip()
                else:
                    d = lis[0].strip()
                    ft2 = lis[1].strip()
                if len(r) > 0:
                    q = re.findall('F\((.*)\) = (.*)', formulas)
                    if len(q) > 0 and len(q[0]) == 2:
                        v = q[0][0].strip()
                        ac = q[0][1].strip()
                        if fcheck(v, ac, ft2):
                            if substitutable(ac, v, t1) and substitutable(ac, v, t2):
                                f = True
                                deltau = ','.join(list(set([g.strip() for g in gamma.split(',')] + [d])))
                                nstep = apply(rule, [deltau, ac, v, t2])
        elif rule == 'rrepl':
            r = re.findall('(.*) -> (.*)=(.*)', premises_f[0])
            if len(r) > 0:
                gamma = r[0][0].strip()
                t1 = r[0][1].strip()
                t2 = r[0][2].strip()
                lis = premises_f[1].split('->')
                if len(lis) == 1:
                    d = ''
                    ft2 = lis[0].strip()
                else:
                    d = lis[0].strip()
                    ft2 = lis[1].strip()
                if len(r) > 0:
                    q = re.findall('F\((.*)\) = (.*)', formulas)
                    if len(q) > 0 and len(q[0]) == 2:
                        v = q[0][0].strip()
                        ac = q[0][1].strip()
                        if fcheck(v, ac, ft2):
                            if substitutable(ac, v, t1) and substitutable(ac, v, t2):
                                f = True
                                deltau = ','.join(list(set([g.strip() for g in gamma.split(',')] + [d])))
                                nstep = apply(rule, [deltau, ac, v, t1])
        elif rule == 'aI':
            r = re.findall('(.*)->(.*)', premises_f[0])
            q = re.findall('(.*)->(.*)', premises_f[1])
            if len(r) > 0 and len(q) > 0:
                d = r[0][0].strip()
                d1 = r[0][1].strip()
                z = q[0][0].strip()
                z1 = q[0][1].strip()
                f = True
                deltau = ','.join(list(set([g.strip() for g in d.split(',') if g.strip()!=''] + [g.strip() for g in z.split(',') if g.strip()!=''])))
                nstep = apply(rule, [deltau, d1, z1])
        elif rule == 'eI':
            r = re.findall('(.*) -> (.*)', premises_f[0])
            if len(r) > 0 and len(r[0]) == 2:
                Ft = r[0][1].strip()
                q = re.findall('F\((.*)\) = (.*)', formulas)
                if len(q) > 0 and len(q[0]) == 2:
                    v = q[0][0].strip()
                    ac = filter(q[0][1].strip())
                    #t is subs for v in f(v)
                    if v in ac and len(Ft) == len(ac):
                        t = None
                        for idx in range(len(Ft)):
                            if Ft[idx] != ac[idx] or (Ft[idx] == ac[idx] and v == Ft[idx]):
                                t = Ft[idx]
                        if t is not None and substitutable(ac, v, t):
                            f = True
                            nstep = apply(rule, [r[0][0], v, filter(ac)])
        elif rule == 'fE':
            r = re.findall('(.*) -> ∀([a-zA-Z])(.*)', premises_f[0])
            if len(r) > 0 and len(r[0]) == 3:
                t = formulas
                v = r[0][1].strip()
                fv = r[0][2].strip()
                if substitutable(fv, v, t):
                    f = True
                    nstep = apply(rule, [r[0][0], fv.replace(v, t)])

        elif rule == 'fI':
            r = re.findall('(.*) -> (.*)', premises_f[0])
            q = re.findall('F\((.*)\) = (.*)', formulas)
            if len(r) > 0 and len(r[0]) == 2 and len(q) > 0 and len(q[0]) == 2:
                gamma = r[0][0].strip()
                f = True
                v = q[0][0].strip()
                rhs = q[0][1].strip()
                if gamma != '':
                    gammaf = gamma.split(',')
                    for f in gammaf:
                        af = assumption_check(f)
                        if isanyfree(v, af):
                            f = False
            if f is True:
                nstep = apply(rule, [gamma, v, rhs])
        else:
            err_msg = 'rule/axiom does not exist.'
    else:
        err_msg = 'one of the premises does not exist.'

    if f is True:
        steps.append((nstep, rule, premises))
        if premises.strip() != '':
            proof_win.addstr(last_proof_line, 0, '{}. {}...{} from {}'.format(len(steps), nstep, rule, ','.join(ps)))
        else:
            proof_win.addstr(last_proof_line, 0, '{}. {}...axiom {} '.format(len(steps), nstep, rule))
        last_proof_line += 1
        #clear_inv()
        proof_win.refresh()
        check(stdscr)
        post_assumption_update(stdscr, 'proof_win', False)
        stdscr.move(11, 6)
        stdscr.refresh()
        wait_for_direction(stdscr)
    else:
        if err_msg is None:
            error_win.addstr('cannot apply {}'.format(rule), RED_AND_WHITE)
        else:
            error_win.addstr(err_msg, RED_AND_WHITE)
        error_win.refresh()
        key = stdscr.getkey()
        if key == 'KEY_UP':
            # clear_inv()
            error_win.clear()
            error_win.refresh()
            stdscr.move(3 + avail_size*1, 50)
            post_assumption_update(stdscr, 'error_win', True)


def post_assumption_update(stdscr, origin, move_cursor, restart = False, start=False):
    global avail_size, last_proof_line, key_mapper
    if restart:
        key_mapper.clear()
        restore_keys()
        avail_win.clear()
        avail_pages.clear()
    # rules with one premise, no invention
    for idx, step in enumerate(steps):
        for rule in regex_mapper:
            r = re.findall(regex_mapper[rule]['re'], step[0])
            if len(r) > 0 and len(r[0]) == regex_mapper[rule]['gp']:
                k = newkey()
                if rule == 'laE' or rule == 'raE':
                    if (rule, [idx+1], r[0]) not in key_mapper.values():
                        key_mapper[k] = (rule, [idx+1], r[0])
                        available_keys.remove(k)
                        avail_win.addstr(avail_size, 0 , '{} from {} [{}]'.format(rule, idx + 1, k), PINK_AND_WHITE)
                        avail_size+=1
                        avail_pages.append('{} from {} [{}]'.format(rule, idx + 1, k))
                if rule == 'iI':
                    its = r[0][0].strip().split(',')
                    if len(its) == 1:
                        g = ''
                    else:
                        g = ','.join(its[:-1])
                    lhs = assumption_check(its[-1].strip())
                    if lhs:
                        for x in special_chars.values():
                            if len(lhs) > 1 and x in lhs and '∃' != lhs[0] and '∀' != lhs[0]:
                                lhs = '('+lhs+')'
                                break
                            if (rule, [idx+1], [g.strip(), lhs, r[0][1]]) not in key_mapper.values():
                                key_mapper[k] = (rule, [idx+1], [g.strip(), lhs, r[0][1]])
                                available_keys.remove(k)
                                avail_win.addstr(len(avail_pages), 0, '{} from {} [{}]'.format(rule, idx + 1, k), PINK_AND_WHITE)
                                avail_size+=1
                                avail_pages.append('{} from {} [{}]'.format(rule, idx + 1, k))                 
    # rules with two premises, no invention
    for step1, step2 in itertools.permutations(steps, 2):
        for rule in ['iE', 'eE', 'lrepl', 'rrepl']:
            if rule == 'iE':
                r = re.findall('(.*) -> (.*)', step1[0])
                if len(r) > 0:
                    F = r[0][1].strip()
                    q = re.findall('(.*) -> (.*)⊃(.*)', step2[0])
                    if len(q) > 0 and len(q[0]) == 3:
                        i1 = steps.index(step1) + 1
                        i2 = steps.index(step2) + 1
                        if F == q[0][1].strip() and (rule, [i2, i1], [q[0][0].strip(), r[0][0].strip(), q[0][2].strip()]) not in key_mapper.values():
                            k = newkey()
                            key_mapper[k] = (rule, [i2, i1], [q[0][0].strip(), r[0][0].strip(), q[0][2].strip()])
                            available_keys.remove(k)
                            avail_win.addstr(avail_size, 0, '{} from {} [{}]'.format(rule, ','.join([str(i2), str(i1)]), k), PINK_AND_WHITE)
                            avail_size += 1
                            avail_pages.append('{} from {} [{}]'.format(rule, ','.join([str(i2), str(i1)]), k))

            if rule == 'eE':
                r = re.findall('(.*) -> ∃(.)(.*)', step1[0])
                if len(r) > 0 and len(r[0]) == 3:
                    fv = paran_filter(r[0][2].strip())
                    v = r[0][1].strip()
                    gamma = r[0][0].strip()
                    q = re.findall('(.*) -> (.*)', step2[0])
                    if len(q) > 0 and len(q[0]) == 2:
                        delta = q[0][0].strip()
                        sigma = q[0][1].strip()
                        for x in delta.split(','):
                            x = x.strip()
                            if assumption_check(x) == fv:
                                i1 = steps.index(step1) + 1
                                i2 = steps.index(step2) + 1
                                deltau = ','.join(list(set([g.strip() for g in delta.split(',') if g != x] + [z.strip() for z in gamma.split(',')])))
                                if not isanyfree(v, gamma) and not isanyfree(v, delta) and (rule, [i1, i2], [deltau, sigma]) not in key_mapper.values():
                                    k = newkey()
                                    key_mapper[k] = (rule, [i1, i2], [deltau, sigma])
                                    available_keys.remove(k)
                                    avail_win.addstr(avail_size, 0, '{} from {} [{}]'.format(rule, ','.join([str(i1), str(i2)]), k), PINK_AND_WHITE)
                                    avail_size+=1
                                    avail_pages.append('{} from {} [{}]'.format(rule, ','.join([str(i1), str(i2)]), k))

    # rules with three premises, no invention
    for step1, step2, step3 in itertools.permutations(steps, 3):
        for rule in ['oE']:
            if rule == 'oE':
                r = re.findall('(.*) -> (.*) ∨ (.*)', step1[0])
                if len(r) > 0 and len(r[0]) == 3:
                    gamma = r[0][0].strip()
                    F = r[0][1].strip()
                    G = r[0][2].strip()
                    q = re.findall('(.*) -> (.*)', step2[0])
                    s = re.findall('(.*) -> (.*)', step3[0])
                    if len(q) > 0 and len(q[0]) == 2 and len(s) > 0 and len(s[0]) == 2:
                        sigma1 = q[0][-1].strip()
                        sigma2 = s[0][-1].strip()
                        if sigma1 == sigma2:
                            af = None
                            ag = None
                            pss1 = [x.strip() for x in q[0][0].split(',')]
                            for x in pss1:
                                if assumption_check(x) == F:
                                    af = x
                            pss2 = [x.strip() for x in s[0][0].split(',')]
                            for y in pss2:
                                if assumption_check(y) == G:
                                    ag = y
                            if af is not None and ag is not None:
                                un = ','.join(list(set([x for x in pss1 if af!=x]).union([y for y in pss2 if ag!=y]).union([g.strip() for g in gamma.split(',')])))
                                i1 = steps.index(step1)+1
                                i2 = steps.index(step2)+1
                                i3 = steps.index(step3)+1
                                if (rule, [i1, i2, i3], [un, sigma1]) not in key_mapper.values():
                                    k = newkey()
                                    key_mapper[k] = (rule, [i1, i2, i3], [un, sigma1])
                                    available_keys.remove(k)
                                    avail_win.addstr(avail_size, 0, '{} from {} [{}]'.format(rule, ','.join([str(i1), str(i2), str(i3)]), k), PINK_AND_WHITE)
                                    avail_size+=1
                                    avail_pages.append('{} from {} [{}]'.format(rule, ','.join([str(i1), str(i2), str(i3)]), k))

    avail_win.refresh()
    check(stdscr)
    if move_cursor is False and origin == 'proof_win':
        return
    key = stdscr.getkey()
    if key in key_mapper:
        tup = key_mapper[key]
        nstep = apply(tup[0], tup[2])
        steps.append((nstep, tup[0], ','.join([str(x) for x in tup[1]])))
        proof_win.addstr(last_proof_line, 0, '{}. {} ... {} from {}'.format(len(steps), nstep, tup[0], ','.join([str(x) for x in tup[1]])))
        last_proof_line += 1
        proof_win.refresh()
        check(stdscr)
        if not start:
            stdscr.move(11, 6)
            stdscr.refresh()
            wait_for_direction(stdscr)
    elif key == 'KEY_RIGHT' or key == 'KEY_DOWN':
        invent_rules(stdscr)
    elif key.isdigit() and int(key) == 1:
        help(stdscr)
    elif key == 'KEY_LEFT':
        assumption_input(stdscr)
    elif key == 'KEY_RIGHT' or 'KEY_DOWN':
        invent_rules(stdscr)
        #key = stdscr.getkey()
    # if key == 'KEY_LEFT':
    #     assumption_input(stdscr)
    # if key == 'KEY_RIGHT':
    #     post_assumption_update(stdscr)



def main(stdscr):
    global steps
    steps = []
    curses.init_pair(1, curses.COLOR_RED, curses.COLOR_WHITE)
    curses.init_pair(2, curses.COLOR_GREEN, curses.COLOR_BLUE)
    curses.init_pair(3, curses.COLOR_MAGENTA, curses.COLOR_BLUE)
    global RED_AND_WHITE, GREEN_AND_BLUE, PINK_AND_WHITE
    RED_AND_WHITE = curses.color_pair(1)
    GREEN_AND_BLUE = curses.color_pair(2)
    PINK_AND_WHITE = curses.color_pair(3)
    build(stdscr)
    # box.edit()
    # c = stdscr.getch()
    # stdscr.insstr(mapper[chr(c)])

if __name__ == '__main__':
    global formula
    parser = argparse.ArgumentParser(description='Formula to be proven')
    parser.add_argument('-f', '--formula(s)', action='store', dest='formula', required=True, type=str, help="Formula to be proven: -f 'p i q'")
    args = parser.parse_args()
    formula = args.formula
    if balanced_paren_check(formula):
        wrapper(main)
    else:
        print('The formula has unbalanced parentheses.')
