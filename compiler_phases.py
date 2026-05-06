import tkinter as tk
from tkinter import ttk, messagebox
import re

# ==========================================
# COMPILER PIPELINE ENGINES (NO CHANGES)
# ==========================================
class LexicalAnalyzer:
    def __init__(self):
        self.token_specification = [
            ('PREPROCESSOR', r'#\s*\w+'),
            ('HEADER',       r'<[a-zA-Z0-9\.]+>'),

    # Comments (VERY IMPORTANT)
            ('COMMENT',      r'//.*'),
            ('MULTICOMMENT', r'/\*[\s\S]*?\*/'),

    # Keywords (expanded)
            ('KEYWORD', r'\b(int|float|if|else|while|for|return|void|char|double|break|continue)\b'),

    # Identifiers
            ('IDENTIFIER', r'[A-Za-z_][A-Za-z0-9_]*'),

    # Numbers
            ('NUMBER', r'\d+(\.\d+)?'),

    # Strings
            ('STRING', r'"[^"\n]*"|\'.*?\''),

    # Operators (IMPORTANT: longest first)
            ('OPERATOR', r'\+\+|--|==|!=|<=|>=|\|\||&&|[%+\-*/=<>]'),

    # Punctuation
            ('PUNCTUATION', r'[(){},;\[\]]'),

    # Newline
            ('NEWLINE', r'\n'),

    # Skip spaces/tabs
            ('SKIP', r'[ \t]+'),

    # Anything else → error
            ('MISMATCH', r'.'),
]
        self.tok_regex = '|'.join('(?P<%s>%s)' % pair for pair in self.token_specification)

    def analyze(self, code):
        tokens, line_num = [], 1
        for mo in re.finditer(self.tok_regex, code):
            kind, value = mo.lastgroup, mo.group()
            if kind == 'NEWLINE': line_num += 1
            elif kind in ('SKIP', 'COMMENT', 'MULTICOMMENT'):continue
            elif kind == 'MISMATCH': return False, f"Unexpected char '{value}' on line {line_num}"
            else: tokens.append((line_num, kind, value))
        return True, tokens

class SLRParser:
    def __init__(self):
        self.rules, self.terminals, self.non_terminals = [], set(), set()
        self.states, self.transitions, self.action_table, self.goto_table = [], {}, [], []
        self.first, self.follow = {}, {}

    def parse_grammar(self, text):
        self.rules, self.terminals, self.non_terminals = [], set(), set()
        for line in text.strip().split('\n'):
            if '->' not in line: continue
            lhs, rhs_full = line.split('->')
            lhs = lhs.strip()
            self.non_terminals.add(lhs)
            for alt in rhs_full.split('|'):
                alt_symbols = tuple(alt.strip().split()) 
                if not alt_symbols: alt_symbols = ('e',)
                self.rules.append((lhs, alt_symbols))
        for _, rhs in self.rules:
            for sym in rhs:
                if sym not in self.non_terminals and sym != 'e': self.terminals.add(sym)
        self.terminals.add('$')
        return len(self.rules) > 0

    def compute_first_follow(self):
        self.first = {nt: set() for nt in self.non_terminals}
        for t in self.terminals: self.first[t] = {t}
        self.first['e'] = {'e'}
        changed = True
        while changed:
            changed = False
            for lhs, rhs in self.rules:
                for sym in rhs:
                    before = len(self.first[lhs])
                    self.first[lhs] |= (self.first[sym] - {'e'})
                    if 'e' not in self.first[sym]: break
                else: self.first[lhs].add('e')
                if len(self.first[lhs]) > before: changed = True

        self.follow = {nt: set() for nt in self.non_terminals}
        self.follow[self.rules[0][0]].add('$')
        changed = True
        while changed:
            changed = False
            for lhs, rhs in self.rules:
                for i, B in enumerate(rhs):
                    if B in self.non_terminals:
                        before = len(self.follow[B])
                        follows_B = set()
                        for sym in rhs[i+1:]:
                            follows_B |= (self.first[sym] - {'e'})
                            if 'e' not in self.first[sym]: break
                        else: follows_B |= self.follow[lhs]
                        self.follow[B] |= follows_B
                        if len(self.follow[B]) > before: changed = True

    def closure(self, items):
        J = set(items)
        changed = True
        while changed:
            changed = False
            for lhs, rhs, dot in list(J):
                if dot < len(rhs) and rhs[dot] in self.non_terminals:
                    for r_lhs, r_rhs in self.rules:
                        if r_lhs == rhs[dot]:
                            new_item = (r_lhs, r_rhs, 0)
                            if new_item not in J:
                                J.add(new_item)
                                changed = True
        return frozenset(J)

    def goto(self, items, X):
        moved = {(lhs, rhs, dot + 1) for lhs, rhs, dot in items if dot < len(rhs) and rhs[dot] == X}
        return self.closure(moved) if moved else frozenset()

    def build_tables(self):
        if not self.rules: return False, "No rules parsed."
        self.compute_first_follow()
        I0 = self.closure({("S'", (self.rules[0][0],), 0)})
        self.states, self.transitions = [I0], {}
        symbols = self.terminals | self.non_terminals
        changed = True
        while changed:
            changed = False
            for i, state in enumerate(self.states):
                for X in symbols:
                    next_state = self.goto(state, X)
                    if next_state:
                        if next_state not in self.states:
                            self.states.append(next_state)
                            changed = True
                        self.transitions[(i, X)] = self.states.index(next_state)

        self.action_table = [{t: '' for t in self.terminals} for _ in self.states]
        self.goto_table = [{nt: '' for nt in self.non_terminals} for _ in self.states]

        for i, state in enumerate(self.states):
            for lhs, rhs, dot in state:
                if dot < len(rhs):
                    sym = rhs[dot]
                    if sym in self.terminals and (i, sym) in self.transitions:
                        self.action_table[i][sym] = f"S{self.transitions[(i, sym)]}"
                else:
                    if lhs == "S'": self.action_table[i]['$'] = "Accept"
                    else:
                        rule_idx = self.rules.index((lhs, rhs))
                        for t in self.follow[lhs]: 
                            self.action_table[i][t] = f"R{rule_idx}"
            for nt in self.non_terminals:
                if (i, nt) in self.transitions: self.goto_table[i][nt] = str(self.transitions[(i, nt)])
        return True, "Success"

    def parse_string(self, input_str):
        tokens = input_str.strip().split() + ['$']
        stack, steps, ptr = [0], [], 0
        while True:
            state = stack[-1]
            sym = tokens[ptr]
            stack_str = " ".join(str(s) for s in stack)
            input_str_rem = " ".join(tokens[ptr:])
            
            if sym not in self.terminals: return False, steps + [(stack_str, input_str_rem, f"Error: '{sym}'")]
            action = self.action_table[state].get(sym, '')
            if not action: return False, steps + [(stack_str, input_str_rem, "Error: Blank")]
                
            steps.append((stack_str, input_str_rem, action))

            if action == "Accept": return True, steps
            elif action.startswith('S'):
                stack.extend([sym, int(action[1:])]); ptr += 1
            elif action.startswith('R'):
                rule_idx = int(action[1:])
                lhs, rhs = self.rules[rule_idx]
                if rhs[0] != 'e': 
                    for _ in range(2 * len(rhs)): stack.pop()
                prev_state = stack[-1]
                goto_state = self.goto_table[prev_state].get(lhs, '')
                stack.extend([lhs, int(goto_state)])

class ASTNode:
    def __init__(self, val):
        self.val = val; self.left = None; self.right = None

class ASTGenerator:
    def precedence(self, op):
        if op in ('+', '-'): return 1
        if op in ('*', '/'): return 2
        return 0

    def generate(self, expression):
        expression = expression.replace(" ", "")
        if '=' not in expression: return None, "Expression must contain '='"
        lhs, rhs = expression.split('=', 1)
        postfix, stack, i = [], [], 0
        
        while i < len(rhs):
            if rhs[i].isalnum():
                var = ""
                while i < len(rhs) and rhs[i].isalnum(): var += rhs[i]; i += 1
                postfix.append(var)
                continue
            elif rhs[i] in "+-*/":
                while stack and self.precedence(stack[-1]) >= self.precedence(rhs[i]): postfix.append(stack.pop())
                stack.append(rhs[i])
            elif rhs[i] in '()':
                if rhs[i] == '(': stack.append(rhs[i])
                else:
                    while stack and stack[-1] != '(': postfix.append(stack.pop())
                    if stack: stack.pop()
            i += 1
        while stack: postfix.append(stack.pop())

        tree_stack = []
        for token in postfix:
            if token.isalnum(): tree_stack.append(ASTNode(token))
            else:
                if len(tree_stack) < 2: return None, "Invalid RHS Structure."
                node = ASTNode(token)
                node.right, node.left = tree_stack.pop(), tree_stack.pop()
                tree_stack.append(node)

        root = ASTNode('=')
        root.left, root.right = ASTNode(lhs), tree_stack.pop()
        return root, "Success"

class TACGenerator:
    def __init__(self):
        self.temp_count = 1
        self.tac, self.quadruples, self.triples, self.indirect_triples = [], [], [], []

    def precedence(self, op):
        if op in ('+', '-'): return 1
        if op in ('*', '/'): return 2
        return 0

    def generate(self, expression):
        self.temp_count = 1
        self.tac.clear(); self.quadruples.clear(); self.triples.clear(); self.indirect_triples.clear()
        expression = expression.replace(" ", "")
        if '=' not in expression: return False, "Expression must contain '='"

        lhs, rhs = expression.split('=', 1)
        postfix, stack, i = [], [], 0
        
        while i < len(rhs):
            if rhs[i].isalnum():
                var = ""
                while i < len(rhs) and rhs[i].isalnum(): var += rhs[i]; i += 1
                postfix.append(var)
                continue
            elif rhs[i] in "+-*/":
                while stack and self.precedence(stack[-1]) >= self.precedence(rhs[i]): postfix.append(stack.pop())
                stack.append(rhs[i])
            elif rhs[i] in '()':
                if rhs[i] == '(': stack.append(rhs[i])
                else:
                    while stack and stack[-1] != '(': postfix.append(stack.pop())
                    if stack: stack.pop()
            i += 1
        while stack: postfix.append(stack.pop())

        eval_stack = []
        for token in postfix:
            if token.isalnum(): eval_stack.append(token)
            else:
                op2, op1 = eval_stack.pop(), eval_stack.pop()
                temp = f"t{self.temp_count}"; self.temp_count += 1
                self.tac.append(f"{temp} = {op1} {token} {op2}")
                self.quadruples.append((token, op1, op2, temp))
                t_op1 = f"({int(op1[1:]) - 1})" if op1.startswith('t') and op1[1:].isdigit() else op1
                t_op2 = f"({int(op2[1:]) - 1})" if op2.startswith('t') and op2[1:].isdigit() else op2
                self.triples.append((token, t_op1, t_op2))
                eval_stack.append(temp)

        final_res = eval_stack.pop()
        self.tac.append(f"{lhs} = {final_res}")
        self.quadruples.append(('=', final_res, '-', lhs))
        t_final = f"({int(final_res[1:]) - 1})" if final_res.startswith('t') and final_res[1:].isdigit() else final_res
        self.triples.append(('=', lhs, t_final))
        for idx, (op, arg1, arg2) in enumerate(self.triples):
            self.indirect_triples.append((100 + idx, f"({idx})", op, arg1, arg2))

        return True, "Success"

class CodeOptimizer:
    def optimize(self, tac_list):
        optimized_tac = []
        for line in tac_list:
            if "=" in line:
                lhs, rhs = [part.strip() for part in line.split("=")]
                tokens = rhs.split()
                if len(tokens) == 3:
                    op1, operator, op2 = tokens[0], tokens[1], tokens[2]
                    
                    if op1.isdigit() and op2.isdigit():
                        try:
                            val = eval(f"{op1} {operator} {op2}")
                            val = int(val) if val == int(val) else val
                            optimized_tac.append(f"{lhs} = {val}")
                            continue
                        except: pass
                    
                    if operator == '*' and op2 == '1':
                        optimized_tac.append(f"{lhs} = {op1}")
                        continue
                    if operator == '*' and op1 == '1':
                        optimized_tac.append(f"{lhs} = {op2}")
                        continue
                    if operator == '+' and op2 == '0':
                        optimized_tac.append(f"{lhs} = {op1}")
                        continue
                    if operator == '+' and op1 == '0':
                        optimized_tac.append(f"{lhs} = {op2}")
                        continue
            optimized_tac.append(line)
        return optimized_tac

class MachineCodeGenerator:
    def generate(self, tac_list):
        assembly = []
        op_map = {'+': 'ADD', '-': 'SUB', '*': 'MUL', '/': 'DIV'}
        for line in tac_list:
            clean_line = line.strip()
            if any(op in clean_line for op in '+-*/') and '=' in clean_line:
                lhs, rhs = clean_line.split('=')
                lhs = lhs.strip()
                op = next(c for c in '+-*/' if c in rhs)
                arg1, arg2 = [x.strip() for x in rhs.split(op)]
                assembly.append(f"MOV R0, {arg1}")
                assembly.append(f"{op_map[op]} R0, {arg2}")
                assembly.append(f"MOV {lhs}, R0\n")
            elif '=' in clean_line:
                lhs, rhs = [x.strip() for x in clean_line.split('=')]
                assembly.append(f"MOV R0, {rhs}")
                assembly.append(f"MOV {lhs}, R0")
        return assembly

# ==========================================
# GRAPHICAL USER INTERFACE (UPGRADED)
# ==========================================
class CompilerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Phases of Compiler")
        self.root.geometry("1100x800")
        
        # New Vibrant Color Palette
        self.colors = {
            'bg': '#F4F6F9',
            'card': '#FFFFFF',
            'text': '#2C3E50',
            'p1': '#FF9F1C', # Orange
            'p2': '#E71D36', # Red
            'p3': '#9D4EDD', # Purple
            'p4': '#2EC4B6', # Teal
            'p5': '#FFBF00', # Amber
            'p6': '#011627'  # Dark Blue
        }
        
        self.root.configure(bg=self.colors['bg'])
        
        # Styling Setup
        style = ttk.Style()
        style.theme_use('clam')
        style.configure("TFrame", background=self.colors['bg'])
        style.configure("Card.TFrame", background=self.colors['card'])
        style.configure("Treeview", font=("Consolas", 11), rowheight=30, background=self.colors['card'], borderwidth=0)
        style.configure("Treeview.Heading", font=("Segoe UI", 11, "bold"), background="#E1E8ED")
        style.configure("Main.TNotebook", background=self.colors['bg'], borderwidth=0)

        # Dynamic Button Styles mapped to Phases
        for p, color in [("P1", self.colors['p1']), ("P2", self.colors['p2']), ("P3", self.colors['p3']), 
                         ("P4", self.colors['p4']), ("P5", self.colors['p5']), ("P6", self.colors['p6'])]:
            style.configure(f"{p}.TButton", font=("Segoe UI", 11, "bold"), background=color, foreground="white", padding=8, borderwidth=0)
            style.map(f"{p}.TButton", background=[("active", "#333333")])

        # Core Components
        self.header_frame = tk.Frame(self.root, bg=self.colors['bg'])
        tk.Label(self.header_frame, text="✨ Phases of Compiler", font=("Segoe UI", 24, "bold"), bg=self.colors['bg'], fg=self.colors['text']).pack(pady=(20, 10))
        
        self.main_nb = ttk.Notebook(self.root, style="Main.TNotebook")
        
        # Engine Initialization
        self.lexer = LexicalAnalyzer()
        self.slr_gen = SLRParser()
        self.ast_gen = ASTGenerator()
        self.tac_gen = TACGenerator()
        self.optimizer = CodeOptimizer()
        self.machine_gen = MachineCodeGenerator()

        # Build Interfaces
        self.setup_homescreen()
        self.build_pipeline_tabs()

    def setup_homescreen(self):
        self.home_frame = tk.Frame(self.root, bg=self.colors['bg'])
        self.home_frame.pack(expand=True, fill=tk.BOTH)
        
        tk.Label(self.home_frame, text="Phases of Compiler", font=("Segoe UI", 36, "bold"), bg=self.colors['bg'], fg=self.colors['text']).pack(pady=(60, 10))
        tk.Label(self.home_frame, text="Interactive Educational Toolkit", font=("Segoe UI", 14), bg=self.colors['bg'], fg="#7F8C8D").pack(pady=(0, 40))

        grid_frame = tk.Frame(self.home_frame, bg=self.colors['bg'])
        grid_frame.pack(expand=True)

        phases = [
            ("Phase 1: Lexical Analysis", "Scans source code and converts characters into meaningful Tokens.", self.colors['p1']),
            ("Phase 2: Syntax Analysis", "Generates an SLR parsing automaton and validates grammar rules.", self.colors['p2']),
            ("Phase 3: Semantic Analysis", "Builds a visual Abstract Syntax Tree (AST) mapping execution order.", self.colors['p3']),
            ("Phase 4: Intermediate Code", "Transforms equations into Triples, Quadruples, and 3-Address Code.", self.colors['p4']),
            ("Phase 5: Code Optimization", "Applies constant folding and simplification to make code efficient.", self.colors['p5']),
            ("Phase 6: Machine Code", "Translates the optimized code into raw Target Assembly language.", self.colors['p6'])
        ]

        for i, (title, desc, color) in enumerate(phases):
            row, col = i // 3, i % 3
            card = tk.Frame(grid_frame, bg=self.colors['card'], padx=20, pady=20, highlightbackground=color, highlightthickness=3, width=300, height=150)
            card.pack_propagate(False)
            card.grid(row=row, column=col, padx=15, pady=15)
            tk.Label(card, text=title, font=("Segoe UI", 14, "bold"), fg=color, bg=self.colors['card']).pack(anchor=tk.W, pady=(0, 10))
            lbl = tk.Label(card, text=desc, font=("Segoe UI", 10), fg=self.colors['text'], bg=self.colors['card'], wraplength=250, justify=tk.LEFT)
            lbl.pack(anchor=tk.W)

        btn_start = tk.Button(self.home_frame, text="Launch Compiler Pipeline", font=("Segoe UI", 16, "bold"), bg=self.colors['text'], fg="white", padx=30, pady=15, borderwidth=0, cursor="hand2", command=self.launch_pipeline)
        btn_start.pack(pady=50)

    def launch_pipeline(self):
        self.home_frame.pack_forget()
        self.header_frame.pack(fill=tk.X)
        self.main_nb.pack(expand=True, fill=tk.BOTH, padx=20, pady=(0, 20))

    def build_pipeline_tabs(self):
        self.tab_lex = ttk.Frame(self.main_nb, style="Card.TFrame")
        self.tab_slr = ttk.Frame(self.main_nb, style="Card.TFrame")
        self.tab_ast = ttk.Frame(self.main_nb, style="Card.TFrame")
        self.tab_codegen = ttk.Frame(self.main_nb, style="Card.TFrame")
        self.tab_opt = ttk.Frame(self.main_nb, style="Card.TFrame")
        self.tab_machine = ttk.Frame(self.main_nb, style="Card.TFrame")
        
        self.main_nb.add(self.tab_lex, text=" P1: Lexical ")
        self.main_nb.add(self.tab_slr, text=" P2: Syntax (SLR) ")
        self.main_nb.add(self.tab_ast, text=" P3: Semantic (AST) ")
        self.main_nb.add(self.tab_codegen, text=" P4: Intermed. Code ")
        self.main_nb.add(self.tab_opt, text=" P5: Optimization ")
        self.main_nb.add(self.tab_machine, text=" P6: Machine Code ")

        self.setup_lex_tab()
        self.setup_slr_tab()
        self.setup_ast_tab()
        self.setup_codegen_tab()
        self.setup_opt_tab()
        self.setup_machine_tab()

    def make_tree(self, parent, cols, widths):
        tree = ttk.Treeview(parent, columns=cols, show='headings')
        tree.tag_configure('evenrow', background="#F8FAFC")
        tree.tag_configure('oddrow', background="#FFFFFF")
        for col, w in zip(cols, widths):
            tree.heading(col, text=col)
            tree.column(col, anchor=tk.CENTER, width=w)
        tree.pack(expand=True, fill=tk.BOTH, padx=10, pady=10)
        return tree

    # --- P1: Lexical Setup ---
    def setup_lex_tab(self):
        top = tk.Frame(self.tab_lex, bg=self.colors['card'], pady=15, padx=20)
        top.pack(fill=tk.X)
        tk.Label(top, text="Source Code (C-style):", bg=self.colors['card'], font=("Segoe UI", 11, "bold"), fg=self.colors['p1']).pack(anchor=tk.W)
        self.txt_code = tk.Text(top, height=8, font=("Consolas", 12), bg="#F8FAFC", highlightthickness=1, highlightbackground="#E1E8ED")
        self.txt_code.pack(fill=tk.X, pady=(5, 10))
        self.txt_code.insert(tk.END, "int main() {\n    int a = 10;\n    if (a > 5) {\n        return a + 2;\n    }\n}")
        ttk.Button(top, text="Scan / Tokenize", style="P1.TButton", command=self.process_lex).pack(anchor=tk.W)
        self.tree_lex = self.make_tree(self.tab_lex, ("Line", "Token Type", "Lexeme (Value)"), [100, 200, 300])

    # --- P2: Syntax Setup ---
    def setup_slr_tab(self):
        top = tk.Frame(self.tab_slr, bg=self.colors['card'], pady=15, padx=20)
        top.pack(fill=tk.X)
        tk.Label(top, text="Grammar Rules:", bg=self.colors['card'], font=("Segoe UI", 11, "bold"), fg=self.colors['p2']).pack(anchor=tk.W)
        self.txt_grammar = tk.Text(top, height=4, font=("Consolas", 12), bg="#F8FAFC", highlightthickness=1, highlightbackground="#E1E8ED")
        self.txt_grammar.pack(fill=tk.X, pady=(5, 10))
        self.txt_grammar.insert(tk.END, "E -> E + T | T\nT -> T * F | F\nF -> ( E ) | id")
        
        btn_f = tk.Frame(top, bg=self.colors['card'])
        btn_f.pack(fill=tk.X)
        ttk.Button(btn_f, text="1. Build Automaton", style="P2.TButton", command=self.process_grammar).pack(side=tk.LEFT, padx=(0, 20))
        tk.Label(btn_f, text="Test String:", bg=self.colors['card'], font=("Segoe UI", 10, "bold")).pack(side=tk.LEFT)
        self.entry_string = ttk.Entry(btn_f, width=25, font=("Consolas", 12))
        self.entry_string.pack(side=tk.LEFT, padx=10)
        self.entry_string.insert(0, "id + id * id")
        ttk.Button(btn_f, text="2. Parse String", style="P2.TButton", command=self.parse_test_string).pack(side=tk.LEFT)
        
        self.slr_nb = ttk.Notebook(self.tab_slr)
        self.slr_nb.pack(expand=True, fill=tk.BOTH, padx=20, pady=(0, 20))
        self.tab_lr0, self.tab_table, self.tab_parse = [ttk.Frame(self.slr_nb, style="Card.TFrame") for _ in range(3)]
        self.slr_nb.add(self.tab_lr0, text=" LR(0) Items & Transitions ")
        self.slr_nb.add(self.tab_table, text=" Parsing Table ")
        self.slr_nb.add(self.tab_parse, text=" Parsing Simulator ")
        
        self.txt_lr0 = tk.Text(self.tab_lr0, font=("Consolas", 12), state=tk.DISABLED, bg="#F8FAFC", padx=15, pady=15)
        self.txt_lr0.pack(expand=True, fill=tk.BOTH)
        self.tree_table = None 
        self.tree_parse = self.make_tree(self.tab_parse, ("Stack", "Input", "Action"), [300, 200, 150])

    # --- P3: Semantic Setup ---
    def setup_ast_tab(self):
        top = tk.Frame(self.tab_ast, bg=self.colors['card'], pady=15, padx=20)
        top.pack(fill=tk.X)
        tk.Label(top, text="Equation:", bg=self.colors['card'], font=("Segoe UI", 11, "bold"), fg=self.colors['p3']).pack(side=tk.LEFT, padx=(0,10))
        self.entry_expr_ast = ttk.Entry(top, width=40, font=("Consolas", 12))
        self.entry_expr_ast.pack(side=tk.LEFT, padx=5)
        self.entry_expr_ast.insert(0, "X = a + b * ( c - d )")
        ttk.Button(top, text="Draw Syntax Tree", style="P3.TButton", command=self.process_ast).pack(side=tk.LEFT, padx=10)
        
        self.canvas_ast = tk.Canvas(self.tab_ast, bg="#F8FAFC", highlightthickness=1, highlightbackground="#E1E8ED")
        self.canvas_ast.pack(expand=True, fill=tk.BOTH, padx=20, pady=(0, 20))

    # --- P4: Intermediate Code Setup ---
    def setup_codegen_tab(self):
        top = tk.Frame(self.tab_codegen, bg=self.colors['card'], pady=15, padx=20)
        top.pack(fill=tk.X)
        tk.Label(top, text="Equation:", bg=self.colors['card'], font=("Segoe UI", 11, "bold"), fg=self.colors['p4']).pack(side=tk.LEFT, padx=(0,10))
        self.entry_expr = ttk.Entry(top, width=40, font=("Consolas", 12))
        self.entry_expr.pack(side=tk.LEFT, padx=5)
        self.entry_expr.insert(0, "X = 5 * 2 + y * 1 + 0")
        ttk.Button(top, text="Generate TAC & Tables", style="P4.TButton", command=self.process_equation).pack(side=tk.LEFT, padx=10)

        self.sub_nb = ttk.Notebook(self.tab_codegen)
        self.sub_nb.pack(expand=True, fill=tk.BOTH, padx=20, pady=(0, 20))
        self.tab_tac, self.tab_quad, self.tab_trip, self.tab_ind = [ttk.Frame(self.sub_nb, style="Card.TFrame") for _ in range(4)]
        self.sub_nb.add(self.tab_tac, text=" 3-Address Code ")
        self.sub_nb.add(self.tab_quad, text=" Quadruples ")
        self.sub_nb.add(self.tab_trip, text=" Triples ")
        self.sub_nb.add(self.tab_ind, text=" Indirect Triples ")

        self.txt_tac = tk.Text(self.tab_tac, font=("Consolas", 13), state=tk.DISABLED, bg="#F8FAFC", padx=15, pady=15)
        self.txt_tac.pack(expand=True, fill=tk.BOTH)
        self.tree_quad = self.make_tree(self.tab_quad, ("Op", "Arg1", "Arg2", "Res"), [100, 200, 200, 200])
        self.tree_trip = self.make_tree(self.tab_trip, ("Index", "Op", "Arg1", "Arg2"), [100, 150, 200, 200])
        self.tree_ind = self.make_tree(self.tab_ind, ("Address", "Pointer", "Op", "Arg1", "Arg2"), [150, 100, 100, 150, 150])

    # --- P5: Optimization Setup ---
    def setup_opt_tab(self):
        top = tk.Frame(self.tab_opt, bg=self.colors['card'], pady=15, padx=20)
        top.pack(fill=tk.X)
        tk.Label(top, text="Equation:", bg=self.colors['card'], font=("Segoe UI", 11, "bold"), fg=self.colors['p5']).pack(side=tk.LEFT, padx=(0,10))
        self.entry_expr_opt = ttk.Entry(top, width=40, font=("Consolas", 12))
        self.entry_expr_opt.pack(side=tk.LEFT, padx=5)
        self.entry_expr_opt.insert(0, "X = 5 * 2 + y * 1 + 0")
        ttk.Button(top, text="Run Optimizer", style="P5.TButton", command=self.process_optimization).pack(side=tk.LEFT, padx=10)

        split = tk.Frame(self.tab_opt, bg=self.colors['bg'])
        split.pack(expand=True, fill=tk.BOTH, padx=20, pady=(0, 20))

        f_l = tk.Frame(split, bg=self.colors['card'])
        f_l.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=(0, 10))
        tk.Label(f_l, text="Before (Raw TAC)", font=("Segoe UI", 12, "bold"), bg=self.colors['card']).pack(pady=10)
        self.txt_before_opt = tk.Text(f_l, font=("Consolas", 13), state=tk.DISABLED, bg="#F8FAFC", padx=15, pady=15)
        self.txt_before_opt.pack(expand=True, fill=tk.BOTH)

        f_r = tk.Frame(split, bg=self.colors['card'])
        f_r.pack(side=tk.RIGHT, expand=True, fill=tk.BOTH, padx=(10, 0))
        tk.Label(f_r, text="After (Optimized TAC)", font=("Segoe UI", 12, "bold"), fg=self.colors['p5'], bg=self.colors['card']).pack(pady=10)
        self.txt_after_opt = tk.Text(f_r, font=("Consolas", 13), state=tk.DISABLED, bg="#FFFDF7", padx=15, pady=15)
        self.txt_after_opt.pack(expand=True, fill=tk.BOTH)

    # --- P6: Machine Code Setup ---
    def setup_machine_tab(self):
        top = tk.Frame(self.tab_machine, bg=self.colors['card'], pady=15, padx=20)
        top.pack(fill=tk.X)
        tk.Label(top, text="Equation:", bg=self.colors['card'], font=("Segoe UI", 11, "bold"), fg=self.colors['p6']).pack(side=tk.LEFT, padx=(0,10))
        self.entry_expr_machine = ttk.Entry(top, width=40, font=("Consolas", 12))
        self.entry_expr_machine.pack(side=tk.LEFT, padx=5)
        self.entry_expr_machine.insert(0, "X = a + b * c")
        ttk.Button(top, text="Generate Assembly", style="P6.TButton", command=self.process_machine).pack(side=tk.LEFT, padx=10)
        
        self.txt_machine = tk.Text(self.tab_machine, font=("Consolas", 14, "bold"), state=tk.DISABLED, bg=self.colors['p6'], fg="#00FF41", padx=20, pady=20)
        self.txt_machine.pack(expand=True, fill=tk.BOTH, padx=20, pady=(0, 20))

    # ==========================================
    # LOGIC PROCESSING FUNCTIONS
    # ==========================================
    def process_lex(self):
        success, result = self.lexer.analyze(self.txt_code.get(1.0, tk.END))

    # Clear table
        for row in self.tree_lex.get_children():
            self.tree_lex.delete(row)

        if not success:
            return messagebox.showerror("Lexical Error", result)

    # Insert tokens FIRST (so UI always updates)
        for i, token in enumerate(result):
            self.tree_lex.insert("", tk.END, values=token,
                             tags=('evenrow' if i % 2 == 0 else 'oddrow',))

    # THEN run syntax safely
        try:
            self.process_full_syntax()
        except Exception as e:
            print("Syntax Error:", e)

    def process_grammar(self):
        if not self.slr_gen.parse_grammar(self.txt_grammar.get(1.0, tk.END)): return messagebox.showerror("Error", "Invalid grammar.")
        success, msg = self.slr_gen.build_tables()
        if not success: return messagebox.showerror("Error", msg)

        self.txt_lr0.config(state=tk.NORMAL)
        self.txt_lr0.delete(1.0, tk.END)
        for i, state in enumerate(self.slr_gen.states):
            self.txt_lr0.insert(tk.END, f"\nState I{i}:\n")
            for lhs, rhs, dot in sorted(list(state), key=lambda x: (x[0], x[2])):
                r = list(rhs)
                r.insert(dot, '.')
                self.txt_lr0.insert(tk.END, f"    {lhs} -> {' '.join(r)}\n")
            transitions = [k for k, v in self.slr_gen.transitions.items() if k[0] == i]
            if transitions:
                self.txt_lr0.insert(tk.END, "  Transitions:\n")
                for (s_idx, sym) in transitions:
                    self.txt_lr0.insert(tk.END, f"    GoTo(I{i}, '{sym}') -> I{self.slr_gen.transitions[(s_idx, sym)]}\n")
        self.txt_lr0.config(state=tk.DISABLED)

        if self.tree_table: self.tree_table.destroy()
        terms, non_terms = sorted(list(self.slr_gen.terminals)), sorted(list(self.slr_gen.non_terminals))
        cols = ["State"] + terms + non_terms
        self.tree_table = ttk.Treeview(self.tab_table, columns=cols, show='headings')
        for col in cols:
            self.tree_table.heading(col, text=col)
            w = 50 if col == "State" else 70
            self.tree_table.column(col, anchor=tk.CENTER, width=w, minwidth=w)
        for i in range(len(self.slr_gen.states)):
            row = [f"I{i}"] + [self.slr_gen.action_table[i].get(t, "") for t in terms] + [self.slr_gen.goto_table[i].get(nt, "") for nt in non_terms]
            self.tree_table.insert("", tk.END, values=row, tags=('evenrow' if i%2==0 else 'oddrow',))
        self.tree_table.pack(expand=True, fill=tk.BOTH, padx=10, pady=10)

    def parse_test_string(self):
        if not self.slr_gen.states: return messagebox.showwarning("Warning", "Build Automaton first.")
        for row in self.tree_parse.get_children(): self.tree_parse.delete(row)
        success, steps = self.slr_gen.parse_string(self.entry_string.get())
        for i, step in enumerate(steps): self.tree_parse.insert("", tk.END, values=step, tags=('evenrow' if i%2==0 else 'oddrow',))
        if success: messagebox.showinfo("Result", "String Accepted!")
        else: messagebox.showerror("Result", "Syntax Error: String Rejected.")

    def process_ast(self):
        root_node, msg = self.ast_gen.generate(self.entry_expr_ast.get())
        if not root_node: return messagebox.showerror("Error", msg)
        self.canvas_ast.delete("all")
        self.draw_ast_node(self.canvas_ast, root_node, 400, 50, 150, 80)

    def draw_ast_node(self, canvas, node, x, y, dx, dy):
        if not node: return
        r = 22 
        if node.left:
            canvas.create_line(x, y, x - dx, y + dy, fill="#BDC3C7", width=3)
            self.draw_ast_node(canvas, node.left, x - dx, y + dy, dx / 1.5, dy)
        if node.right:
            canvas.create_line(x, y, x + dx, y + dy, fill="#BDC3C7", width=3)
            self.draw_ast_node(canvas, node.right, x + dx, y + dy, dx / 1.5, dy)
            
        bg_color = self.colors['p3'] if node.val in "=+-*/" else self.colors['p4']
        canvas.create_oval(x - r, y - r, x + r, y + r, fill=bg_color, outline=self.colors['bg'], width=3)
        canvas.create_text(x, y, text=node.val, fill="white", font=("Segoe UI", 12, "bold"))

    def process_equation(self):
        expr = self.entry_expr.get().strip()

        if not expr:
            messagebox.showerror("Error", "Enter an equation")
            return

    # Reset generator (VERY IMPORTANT)
        self.tac_gen = TACGenerator()

        success, msg = self.tac_gen.generate(expr)
        if not success:
            return messagebox.showerror("Parse Error", msg)

    # --- TAC ---
        self.txt_tac.config(state=tk.NORMAL)
        self.txt_tac.delete(1.0, tk.END)

        for line in self.tac_gen.tac:
            self.txt_tac.insert(tk.END, f"{line}\n")

        self.txt_tac.config(state=tk.DISABLED)

    # --- Clear tables ---
        for tree in (self.tree_quad, self.tree_trip, self.tree_ind):
            for row in tree.get_children():
                tree.delete(row)

    # --- Quadruples ---
        for r in self.tac_gen.quadruples:
            self.tree_quad.insert("", tk.END, values=r)

    # --- Triples ---
        for i, r in enumerate(self.tac_gen.triples):
            self.tree_trip.insert("", tk.END, values=(f"({i})", *r))

    # --- Indirect Triples ---
        for r in self.tac_gen.indirect_triples:
            self.tree_ind.insert("", tk.END, values=r)


    def process_optimization(self):
        success, msg = self.tac_gen.generate(self.entry_expr_opt.get())
        if not success: return messagebox.showerror("Parse Error", msg)
        raw_tac = self.tac_gen.tac.copy()
        optimized_tac = self.optimizer.optimize(raw_tac)
        self.txt_before_opt.config(state=tk.NORMAL)
        self.txt_before_opt.delete(1.0, tk.END)
        for line in raw_tac: self.txt_before_opt.insert(tk.END, f"  {line}\n")
        self.txt_before_opt.config(state=tk.DISABLED)
        self.txt_after_opt.config(state=tk.NORMAL)
        self.txt_after_opt.delete(1.0, tk.END)
        for line in optimized_tac: self.txt_after_opt.insert(tk.END, f"  {line}\n")
        self.txt_after_opt.config(state=tk.DISABLED)

    def process_machine(self):
        success, msg = self.tac_gen.generate(self.entry_expr_machine.get())
        if not success: return messagebox.showerror("Parse Error", msg)
        optimized_tac = self.optimizer.optimize(self.tac_gen.tac)
        assembly = self.machine_gen.generate(optimized_tac)
        self.txt_machine.config(state=tk.NORMAL)
        self.txt_machine.delete(1.0, tk.END)
        for line in assembly: self.txt_machine.insert(tk.END, f"  {line}\n")
        self.txt_machine.config(state=tk.DISABLED)
 
    def check_basic_syntax(self, code):
        stack = []
        pairs = {'{': '}', '(': ')'}
    
        for i, ch in enumerate(code):
            if ch in pairs:
                stack.append(ch)
            elif ch in pairs.values():
                if not stack:
                    return False, f"Unmatched '{ch}'"
                last = stack.pop()
                if pairs[last] != ch:
                    return False, f"Mismatched '{last}' and '{ch}'"

        if stack:
            return False, "Unclosed brackets"

    # Basic statement checks
        lines = code.split('\n')
        for ln, line in enumerate(lines, start=1):
            line = line.strip()
            if not line:
                continue
        
            if any(line.startswith(k) for k in ["if", "while", "for", "else"]):
                continue
        
            if '{' in line or '}' in line:
                continue
        
            if not line.endswith(';'):
                return False, f"Missing ';' at line {ln}"

        return True, "Syntax looks valid" 
      
    def process_full_syntax(self):
        code = self.txt_code.get(1.0, tk.END)
        ok, msg = self.check_basic_syntax(code)
        if not ok:
            messagebox.showerror("Syntax Error", msg)
            return

    # Step 2: extract expressions
        exprs = self.extract_expressions(code)
        if not exprs:
            messagebox.showinfo("Syntax", "No expressions to parse.")
            return

    # Step 3: parse expressions using SLR
        for expr in exprs:
            rhs = expr.split('=')[1]
            normalized = self.normalize_input(rhs)
            success, steps = self.slr_gen.parse_string(normalized)

            if success:
                print(f"{expr} → VALID")
            else:
                print(f"{expr} → INVALID")  

    def extract_expressions(self, code):
        lines = code.split('\n')
        exprs = []

        for line in lines:
            line = line.strip()
            if '=' in line and ';' in line:
                line = re.sub(r'^(int|float|char|double)\s+', '', line)
                line = line.replace(';', '')
                exprs.append(line)

        return exprs 

    def normalize_input(self, s):
        tokens = s.split()
        normalized = []

        for tok in tokens:
            if tok.isdigit():
                normalized.append("num")
            elif tok.isidentifier():
                normalized.append("id")
            else:
                normalized.append(tok)

        return " ".join(normalized)           

if __name__ == "__main__":
    root = tk.Tk()
    app = CompilerGUI(root)
    root.mainloop()
