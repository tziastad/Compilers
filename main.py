import re
import sys
import os
# A.M 2442 Zougianos Giorgos cse32442
# A.M 2591 Tziolas Giorgos cse32591

VARIABLES_PATTERN = "[a-zA-Z][a-zA-Z0-9]*"
KEYWORDS = ["program", "endprogram", "declarations", "if", "then", "else",
            "endif", "dowhile", "enddowhile", "while", "endwhile", "loop", "endloop",
            "exit", "forcase", "endforcase", "incase", "endincase", "when",
            "endwhen", "default", "enddefault", "function", "endfunction",
            "return", "in", "inout", "inandout", "and", "or", "not", "input",
            "print", ]
OPERATORS = ["*", "+", "-", "/"]
ASSEMBLY_OPERATORS = ("mul", "add", "sub", "div")

RELATIONAL_OPERATORS = ["<", ">", "<=", "<>", ">=", "="]
ASSEMBLY_RELATIONAL_OPERATORS = ["blt", "bgt", "ble", "bne", "bge", "beq"]
 
loop = []
quad_id = 0
temp_id = 1
quad_list = list()
subprograms_exist = False
program_name = 'PROGRAM'
main_declarations = []
main_framelen = -1
is_main = False
scopes = []
function_returns = []
scope_string = ''
assembly_content = ''
parameter_list = []
generating_assembly = False
halt_quad_id = 0

class StartletCompiler:
    token = None

    def __init__(self, file):
        self.token = ""
        if (os.path.isfile(file)):
            self.compile_file(file)
        else:
            print("No file found named " + file)
            sys.exit()
        
    def compile_file(self, file):
        absolute_path = os.path.abspath(file)
        if (file.endswith(".slt") or file.endswith(".SLT")):
            self.Lex = Lex(read_file(absolute_path), file)
            self.analyze()
            self.generate_intermediate_code(file)
            self.generate_scrope_txt(file)
            print("File " + absolute_path + " has been compiled!")
            global subprograms_exist
            if (not subprograms_exist):
                self.generate_c_code(file)
                print("C code file has been genarated successfully!")
            else:
                print("C file cannot be generated. Program has subprograms.")
            global generating_assembly
            generating_assembly = True
            self.generate_assembly_file(file)
        else:
            print("File " + file + " is not an SLT file.")
            return
    
    def generate_assembly_file(self, file): 
        global assembly_content
        new_file = file.replace(".slt", "").replace(".SLT", "")
        new_file += "_assembly.asm"
        write_file(new_file, assembly_content.strip()) 
           
    def generate_scrope_txt(self, file):
        global scope_string
        new_file = file.replace(".slt", "").replace(".SLT", "")
        new_file += "_scope.txt"
        write_file(new_file, scope_string)      
         
    def generate_c_code(self, file):
        global quad_list
        strin = ""
        newFile = file.replace(".slt", "").replace(".SLT", "")
        newFile += ".c"
        strin += '#include <stdio.h>\n\n'
        strin += '/*\nAutomatically generated C code file by Starlet Compiler.\n\n'
        strin += 'A.M 2442 Zougianos Giorgos cse32442\n'
        strin += 'A.M 2591 Tziolas Giorgos cse32591\n\n */\n\n'

        for quad in quad_list:
            stri = quad.toC()
            if (str != None):
                strin += stri
        write_file(newFile, strin)  
           
    def generate_intermediate_code(self, file):
        strin = ""
        new_file = file.replace(".slt", "").replace(".SLT", "")
        new_file += ".int"
        for quad in quad_list:
            strin += quad.tofile()
            strin += '\n'
        write_file(new_file, strin)    
                
    def lex(self):
        return self.Lex.get()

    def analyze(self):
        self.token = self.lex()
        if (self.token == 'program'):
            self.token = self.lex()
            if (self.is_variable()):
                global program_name, is_main, scope_string, halt_quad_id
                program_name = self.token
                scopes.append(Scope(0 , None))
                self.token = self.lex()
                self.declarations()
                self.subprograms()
                first_quad_of_the_block = self.update_function_entity_quad(program_name) -1
                self.gen_quad("begin_block", "_", "_", program_name)
                is_main = True  # note sequence we run in main program
                self.sequence()
                if (self.token != "endprogram"):
                    self.error("<endprogram> keyword required at the end of the program.")
                else:
                    self.check_for_more_words()
                    halt_quad_id = self.next_quad()-1
                    self.gen_quad("halt", "_", "_", "_")
                    self.gen_quad("end_block", "_", "_", program_name)
                    self.update_function_entity_framelen(program_name, scopes[-1].offset)
                    scope_string = self.get_scope_string()
                    for quad in quad_list[first_quad_of_the_block:]:
                        self.block_to_assembly(quad, program_name)
                    scopes.pop()  # typical reasons
            else: self.error("After <program> keyword, program's name is expected.")
        else:
            self.error("Keyword <program> is expected.")
            
    def check_for_more_words(self):
        try:
            self.token = self.lex()
        except:
            return
        self.error("No more words should exist after <endprogram> keyword.")
            
    def subprograms(self):
        while (self.token == "function"):
            self.token = self.lex()
            function_name = self.token
            global subprograms_exist
            subprograms_exist = True
            function_returns.append(False)
            if (self.is_variable()):
                self.add_new_scope()
                self.add_function_entity(function_name)
                self.formal_pars(function_name)
                self.declarations()
                self.subprograms()
                first_quad_of_the_block = self.update_function_entity_quad(function_name) -1
                self.gen_quad("begin_block", "_", "_", function_name)
                self.sequence()
                self.end_function()
                if function_returns.pop() == False:
                    self.error("Function " + function_name + " does not return anything.")

                self.gen_quad("end_block", "_", "_", function_name)
                self.update_function_entity_framelen(function_name, scopes[-1].offset)
                for quad in quad_list[first_quad_of_the_block:]:
                    self.block_to_assembly(quad, function_name)
                scopes.pop()
            else: self.error("Function's name expected.")
            
    def formal_pars(self, function_name):
        self.token = self.lex()
        if (self.token == "("):
            self.token = self.lex()
            if (self.token == "in" or self.token == "inout" or self.token == "inandout"):
                self.formal_par_list(function_name)
            if (self.token != ")"):
                self.error("Right parenthesis <)> expected after function's arguments.")
            self.token = self.lex()
        else:
            self.error("Left parenthesis <(> expected for function's arguments.")
            
    def formal_par_list(self, function_name):        
        self.formal_par_item(function_name)
        while(self.token == ","):
            self.token = self.lex()
            if (self.token == "in" or self.token == "inout" or self.token == "inandout"):
                self.formal_par_item(function_name)
            else:
                self.error("Expected <in>,<inout> or <inandout> after comma in function arguments.")
                
    def formal_par_item(self, function_name):
        if (self.token == "in" or self.token == "inout" or self.token == "inandout"):
            parameter_type = self.token
            self.token = self.lex()
            if (not self.is_variable()):
                self.error("Variable expected after <" + parameter_type + "> keyword.")
            parameter_name = self.token
            self.add_function_argument(function_name, parameter_name, parameter_type)
            self.add_parameter_entity(parameter_name, parameter_type)
            self.token = self.lex()
            
    def end_function(self):
        if (self.token == "endfunction"):
            self.token = self.lex()
        else:self.error("<endfunction> keyword expected.")          
         
    def sequence(self):
        if (self.is_variable(self.token)):
            self.assignment()
        elif (self.token == "if"):
            self.if_statement()
        elif (self.token == "dowhile"):
            self.do_statement()
        elif (self.token == "while"):
            self.while_statement()    
        elif (self.token == "return"):
            self.return_statement()
        elif (self.token == "forcase"):
            self.forcase_statement()
        elif (self.token == "incase"):
            self.incase_statement()
        elif (self.token == "loop"):
            self.loop_statement()
        elif (self.token == "exit"):
            self.exit_statement()
        elif (self.token == "print"):
            self.print_statement()
        elif (self.token == "input"):
            self.input_statement()
        else:self.error("Unknown token.")
        self.semicolon()
        
    def input_statement(self):
        idT = self.token = self.lex()
        if (not self.is_variable()):
            self.error("Variable name expected after <input> keyword.")
        else:
            self.token = self.lex()
            self.gen_quad("in", "_", "_", idT)
        
    def print_statement(self):
        self.token = self.lex()
        exp = self.expression()
        self.gen_quad("out", "_", "_", exp)
        
    def incase_statement(self):
        self.token = self.lex()
        flag = self.new_temp()
        s_quad = self.next_quad()
        self.gen_quad(":=", 0, "_", flag)
        while (self.token == "when"):
            self.token = self.lex()
            
            (c_true, c_flase) = self.parenthesis_condition_parenethesis()
            ok = self.next_quad() 
            self.backpatch(c_true, ok)
            self.gen_quad(":=", 1, "_", flag)
            
            if (self.token == ":"):
                self.token = self.lex()
                self.sequence()
                
                next_when_statement = self.next_quad()
                self.backpatch(c_flase, next_when_statement)
            else: self.error("<:> symbol expected after condition.")
            
        self.gen_quad("=", 1, flag, s_quad)
        
        if (self.token == "endincase"):
            self.token = self.lex()
        else: self.error("<endincase> keyword expected.")
        
    def forcase_statement(self): 
        self.token = self.lex()
        s_quad = self.next_quad()
        exit_list = self.empty_list()
        while (self.token == "when"):
            self.token = self.lex()
            (c_true, c_false) = self.parenthesis_condition_parenethesis()
            if (self.token == ":"):
                self.token = self.lex()
                self.backpatch(c_true, self.next_quad())
                
                self.sequence()
                temp_list = self.make_list(self.next_quad())
                self.gen_quad("jump", "_", "_", "_")
                exit_list = self.merge(exit_list, temp_list)
                self.backpatch(c_false, self.next_quad())
            else: self.error("<:> symbol expected after condition.")
        
        if (self.token == "default"):
            self.token = self.lex()
            if (self.token == ":"):
                self.token = self.lex()
            else: self.error("<:> token expected after <default> keyword.")
            self.sequence()
            self.gen_quad("jump", "_", "_", s_quad - 1)
            if (self.token == "enddefault"):
                self.token = self.lex()
            else:self.error("<enddefault> keyword expected after statements.")
        else: self.error("<default> keyword expected inside <forcase> statement.")
        if (self.token == "endforcase"):
            self.token = self.lex()
        else: self.error("<endforcase> keyword expected at the end of a <forcase>.")
        if (exit_list != None):
            self.backpatch(exit_list , self.next_quad())
            
    def while_statement(self):
        self.token = self.lex()
        b_quad = self.next_quad()    
        (b_true, b_false) = self.parenthesis_condition_parenethesis()
        self.backpatch(b_true, self.next_quad())
        self.sequence()
        self.gen_quad('jump', '_', '_', b_quad - 1)
        self.backpatch(b_false, self.next_quad())
        if (self.token == "endwhile"):
            self.token = self.lex()
        else: self.error("<endwhile> keyword expected at the end of a <while> statement")
        
    def loop_statement(self):
        global loop
        loop.append("")
        self.token = self.lex()
        s_quad = self.next_quad()
        self.sequence()
        nextq = self.next_quad()
        if (loop[-1] != ""):
            self.backpatch(loop[-1], nextq + 1)
        self.gen_quad("jump", "_", "_", s_quad - 1)
        if (self.token == "endloop"):
            self.token = self.lex()
        else: self.error("<endloop> keyword expected after <loop> keyword")
        loop.pop()
        
    def exit_statement(self):
        global loop
        if (len(loop) == 0):
            self.error("<exit> keyword can be used only inside <loop> statement.")
        self.token = self.lex()
        e_list = self.make_list(self.next_quad())
        self.gen_quad('jump', "_", "_", "_")
        loop[-1] = e_list
        
    def return_statement(self):
        self.token = self.lex()
        expr = self.expression()
        self.gen_quad("retv", "_", "_", expr)
        if function_returns == [] or function_returns[-1] == True:
            self.error("Wrong <return> statement. There is already a defined <return> or it is not a function.")
        else:
            function_returns[-1] = True
            
    def do_statement(self):
        self.token = self.lex()
        s_quad = self.next_quad()
        self.sequence()
        if (self.token == "enddowhile"):
            self.token = self.lex()
            (c_true, c_false) = self.parenthesis_condition_parenethesis()
            self.backpatch(c_true, s_quad)
            e_quad = self.next_quad()
            self.backpatch(c_false, e_quad)
        else: self.error("<enddowhile> keyword expected in the end of <do> statement.")
        
    def if_statement(self):
        self.token = self.lex()  # eat the if
        (b_true, b_false) = self.parenthesis_condition_parenethesis()
        if (self.token != "then"):
            self.error("<then> keyword required after an <if> statement.")
        else:
            self.token = self.lex()
        self.backpatch(b_true, self.next_quad())
        self.sequence()
        skip_list = self.make_list(self.next_quad())
        self.gen_quad('jump', '_', '_', "_")
        self.backpatch(b_false, self.next_quad())
        if (self.token == "else"):
            self.token = self.lex()
            self.sequence()
        self.backpatch(skip_list, self.next_quad())
        if (self.token == "endif"):
            self.token = self.lex()
        else: self.error("<endif> keyword expected in the end of the <if> statement.")
        
    def parenthesis_condition_parenethesis(self):
        if (self.token == "("):
            self.token = self.lex()
        else: self.error("Left parenthesis <(> required before condition.")
        cond = self.condition()
        if (self.token == ")"):
            self.token = self.lex()
        else: self.error("Right parenthesis <)> required after condition.")
        return cond
        
    def semicolon(self):
        if (self.token == ";"):
            self.token = self.lex()
            self.sequence()
        
    def condition(self):
        (b_true, b_false) = self.boolTerm()
        while (self.token == "or"):
            self.backpatch(b_false, self.next_quad())
            self.token = self.lex()
            (q2_true, q2_false) = self.boolTerm()
            b_true = self.merge(b_true, q2_true)
            b_false = q2_false
        return (b_true, b_false)
            
    def boolTerm(self):    
        (q_true, q_false) = self.boolFactor()
        while (self.token == "and"):
            self.backpatch(q_true, self.next_quad())
            self.token = self.lex()
            (r2_true, r2_false) = self.boolFactor()
            q_false = self.merge(q_false, r2_false)
            q_true = r2_true
        return (q_true, q_false)
            
    def boolFactor(self):
        if (self.token == "not"):
            self.token = self.lex()
            value = self.bracket_condition_bracket()
            value = value[::-1]  # reverse lists
        elif (self.token == "["):
            value = self.bracket_condition_bracket()
        else:
            expression1 = self.expression()
            relop = self.relationalOperator()
            expression2 = self.expression()
            r_true = self.make_list(self.next_quad())
            self.gen_quad(relop, expression1, expression2, "_")
            r_false = self.make_list(self.next_quad())
            self.gen_quad('jump', '_', '_', "_")
            value = (r_true, r_false)
        return value
            
    def relationalOperator(self):
        if (self.token in RELATIONAL_OPERATORS):
            operator = self.token
            self.token = self.lex()
            return operator    

    def bracket_condition_bracket(self):
        if (self.token == "["):
            self.token = self.lex()
        else: self.error("Left bracket <[> expected to analyze condition.")
        cond = self.condition()
        if (self.token == "]"):
            self.token = self.lex()
        else: self.error("Right bracket <]> expected after a condition.")
        return cond
        
    def assignment(self):
        variable = self.token
        if self.search_entity_by_name(variable) == None:
            self.error("Unknown variable: " + variable)
        self.token = self.lex()
        if (self.token == ":="):
            self.token = self.lex()
            expression = self.expression()
            self.gen_quad(":=", expression, "_", variable)
        else: self.error("Value assignment symbol := expected.")
            
    def expression(self):
        opsign = self.optional_sign()
        term = self.term()
        if opsign != None:
            sign_temp = self.new_temp()
            self.gen_quad("+", 0, term, sign_temp)
            term = sign_temp
        while (self.token == "+" or self.token == "-"):
            op = self.token
            self.token = self.lex()
            term2 = self.term()
            temp_var = self.new_temp()
            self.gen_quad(op, term, term2, temp_var)
            term = temp_var
        return term
            
    def term(self):
        factor = self.factor()
        while (self.token == "*" or self.token == "/"):
            op = self.token
            self.token = self.lex()
            factor2 = self.factor()
            temp_var = self.new_temp()
            self.gen_quad(op, factor, factor2, temp_var)
            factor = temp_var
        return factor
        
    def factor(self):
        if (self.is_constant()):
            const = self.token
            self.token = self.lex()
            return const
        elif (self.token == "("):
            self.token = self.lex()
            value = self.expression()
            if (self.token == ")"):
                self.token = self.lex()
                return value
            else: self.error("Expected closing parenthesis <)>")
            
        elif (self.is_variable()):
            value = self.token
            self.token = self.lex()
            tail = self.id_tail()
            if (tail != None):
                function_return = self.new_temp()
                self.gen_quad('par', function_return, "RET", "_")
                try:
                    if (self.search_entity_by_name(value) == None):
                        self.error("Undefined function: " + value)
                except:
                    self.error("Undefined function " + value)
                
                self.gen_quad("call", "_", "_", value)
                value = function_return
            else:
                if (self.search_entity_by_name(value) == None):
                    self.error("Undefined variable: " + value)
            return value
        else: self.error("Constant or function call or variable expected.")    
            
    def id_tail(self):
        if (self.token == "("):
            self.token = self.lex()
            input_type = self.token
            while (input_type == "in" or input_type == "inout" or input_type == "inandout"):
                self.token = self.lex()
                if (input_type == "in"):
                    exp = self.expression()
                    self.gen_quad('par', exp, "CV", '_')
                else:
                    if (self.is_variable()):
                        var = self.token
                        self.token = self.lex()
                        if (input_type == "inout"):
                            self.gen_quad('par', var, "REF", '_')
                        else:
                            self.gen_quad('par', var, "CV_REF", '_')
                    else: self.error("Variable <id> expected after " + input_type + ".")
                if (self.token == ","):
                    self.token = self.lex()
                    input_type = self.token
                elif (self.token == ")"):
                    break
                else:self.error("Expected comma <,> keyword between argument variables.")
            if (self.token != ")"):
                self.error("Expected closing parenthesis <)> after argument variables when calling a function.")
            else: self.token = self.lex()
            return True
               
    def optional_sign(self):
        if (self.token == "+" or self.token == "-"):
            symbol = self.token
            self.token = self.lex()
            return symbol
        
    def declarations(self):
        global main_declarations
        while (self.token == "declare"):
            self.token = self.lex()
            if (self.is_variable()):
                variable = self.token
                main_declarations.append(variable)
                self.add_var_entity(variable)
                self.token = self.lex()
                
                while (self.token == ","):
                    self.token = self.lex()
                    if (self.is_variable()):
                        variable = self.token
                        main_declarations.append(variable)
                        self.add_var_entity(variable)
                        self.token = self.lex()  # declare id
                    else: self.error("Variable expected after comma in declarations.")
                if (self.token == ";"):
                    self.token = self.lex()
                else: self.error("<;> symbol expected after declarations.")
            else: self.error("Variable <id> expected after <declare> keyword.")
            
    def is_variable(self, token=None):
        if (token == None):
            token = self.token
        pattern = re.compile(VARIABLES_PATTERN)
        return  pattern.match(token) != None and token not in KEYWORDS
    
    def is_constant(self, token=None):
        if (token == None):
            token = self.token
        try:
            int(token)
            return True
        except:
            return False
            
    def error(self, message):
        global generating_assembly
        if (generating_assembly == True):
            raise Exception("Invalid token \"" 
                        +self.token + 
                         "\" in "
                         +self.Lex.name + 
                         ", Line: "
                         +str(self.Lex.line_number) + 
                         " Index: "
                         +str(self.Lex.dummy_index) + 
                         ". " + message)
        else:
            raise Exception("Error during assembly code generation: " + message)

#  ______   _____   _   _    ___    _         _____   _____  ______   _____ 
#  |  ___| |_   _| | \ | |  / _ \  | |       /  __ \ |  _  | |  _  \ |  ___|
#  | |_      | |   |  \| | / /_\ \ | |       | /  \/ | | | | | | | | | |__  
#  |  _|     | |   | . ` | |  _  | | |       | |     | | | | | | | | |  __| 
#  | |      _| |_  | |\  | | | | | | |____   | \__/\ \ \_/ / | |/ /  | |___ 
#  \_|      \___/  \_| \_/ \_| |_/ \_____/    \____/  \___/  |___/   \____/ 
#                                                                           
    def write_assembly(self, s):
        global assembly_content
        array = s.split("#")
        if (len(array) == 2):
            s = array[0]
            comment = array[1]
            while (len(s) < 23):
                s = s + " "
            s = s + "#" + comment
        if (s.startswith("L")):
            s = "\n" + s
        assembly_content += s
        assembly_content += "\n"

    def gnvlcode(self, v):
        entity, level = self.search_entity_by_name(v)
        if (entity == None):
            self.error("Variable not found: " + v)
        if (entity.type == "FUNCTION"):
            self.error("Variable not found: " + v)
        comment = "# gnvlcode()"
        self.write_assembly("lw $t0, -4($sp)")
        current_level = scopes[-1].level
        level = current_level - level - 1
        while (level > 0):
            self.write_assembly("lw $t0, -4($t0)"+comment)
            level = level - 1
        self.write_assembly("addi $t0, $t0, -" + str(entity.offset)+comment)
    
    def loadvr(self, v, r):
        comment = "# loadvr()"
            
        if (self.is_constant(str(v))):
            self.write_assembly("li $t" + r + ", " + str(v) + comment)
            return
            
        entity, level = self.search_entity_by_name(v)
        current_level = scopes[-1].level
        entity_type = entity.type
        if (entity == None):
            self.error("loadvr: variable not found: " + v + comment)
            return
        
        # lw $tr, -offset($s0)
        if (entity_type == "VARIABLE" and level == 0):
            self.write_assembly("lw $t" + r + ", -" + str(entity.offset) + "($s0)" + comment)
            return 
        
        # lw $tr,-offset($sp)
        if (entity_type == 'VARIABLE' and level == current_level) or \
            (entity_type == 'PARAMETER' and entity.parameter_type == "in" and level == current_level) or \
            (entity_type == "TEMP_VARIABLE"):
            self.write_assembly("lw $t" + r + ", -" + str(entity.offset) + "($sp)" + comment)
            return
        
        # lw $t0, -offset($sp)
        # lw $tr, ($t0)
        if (entity_type == 'PARAMETER' and entity.parameter_type == 'inout' and level == current_level):
            self.write_assembly("lw $t0, -" + str(entity.offset) + "($sp)" + comment)
            self.write_assembly("lw $t" + r + ", 0($t0)" + comment)
            return
        
        # gnlvcode()
        # lw $tr, ($t0)
        if (entity_type == 'VARIABLE' and level < current_level) or \
            (entity_type == 'PARAMETER' and entity.parameter_type == "in" and level < current_level):
            self.gnvlcode(v)
            self.write_assembly("lw $t" + r + ", 0($t0)" + comment)
            return
        
        # gnlvcode()
        # lw $t0, ($t0)
        # lw $tr, ($t0)
        if (entity_type == "PARAMETER" and entity.parameter_type == "inout" and level < current_level):
            self.gnvlcode(v)
            self.write_assembly("lw $t0, 0($t0)" + comment)
            self.write_assembly("lw $t" + r + ", 0($t0)" + comment)
            return
        
    
    def storerv(self, r , v):
        entity, level = self.search_entity_by_name(v)
        current_level = scopes[-1].level
        entity_type = entity.type
        comment = "# storerv()"
            
        if (entity == None):
            self.error("storerv: variable not found: " + v)
            return
        
        # sw    $tr,-offset($s0)
        if (entity_type == "VARIABLE" and level == 0):
            self.write_assembly("sw $t" + r + ", -" + str(entity.offset) + "($s0)" + comment)
            return
        
        # sw    $tr,-offset($sp)
        if (entity_type == "VARIABLE" and current_level == level) or \
            (entity_type == "PARAMETER" and entity.parameter_type == "in" and level == current_level) or \
            (entity_type == "TEMP_VARIABLE"):
            self.write_assembly("sw $t" + r + ", -" + str(entity.offset) + "($sp)" + comment)
            return
        
        # lw    $t0,-offset($sp)
        # sw    $tr,($t0)
        if (entity_type == "PARAMETER" and entity.parameter_type == "inout" and level == current_level):
            self.write_assembly("lw $t0,-" + str(entity.offset) + "($sp)" + comment)
            self.write_assembly("sw $t" + r + ", 0($t0)" + comment)
            return
        
        # gnlvcode(v)
        # sw    $tr,($t0)
        if (entity_type == "VARIABLE" and level < current_level) or \
            (entity_type == "PARAMETER" and entity.parameter_type == "in" and level < current_level):
            self.gnvlcode(v)
            self.write_assembly("sw $t" + r + ", 0($t0)" + comment)
            return
        
        # gnlvcode(v)
        # lw    $t0,($t0)
        # sw    $tr,($t0) 
        if (entity_type == "PARAMETER" and entity.parameter_type == "inout" and level < current_level):
            self.gnvlcode(v)
            self.write_assembly("lw $t0, 0($t0)" + comment)
            self.write_assembly("sw $t" + r + ", 0($t0)" + comment)
            return
        
        
    # TODO:    
    def block_to_assembly(self, quad, block_name):
        global program_name, parameter_list, main_framelen, halt_quad_id
        is_main_program = block_name == program_name
        label = "L_" + str(quad.label) + ":#" + quad.tofile()[2:]
        operator = quad.operator
        resource = str(quad.resource)
        arg1 = quad.argument1
        arg2 = quad.argument2
        if (quad.label == 0):
            self.write_assembly("j L_" + program_name)
            
        self.write_assembly(label)
        if (operator == "jump"):
            self.write_assembly("j L_" + resource)
        elif (operator in RELATIONAL_OPERATORS):
            index = RELATIONAL_OPERATORS.index(operator)
            assembly_operator = ASSEMBLY_RELATIONAL_OPERATORS[index]
            self.loadvr(arg1, "1")
            self.loadvr(arg2, "2")
            self.write_assembly(assembly_operator + " $t1, $t2, L_" + resource)
        elif (operator == ":="):
            self.loadvr(arg1, "1")
            self.storerv("1", quad.resource)
        elif (operator in OPERATORS):
            index = OPERATORS.index(operator)
            operator = ASSEMBLY_OPERATORS[index]
            self.loadvr(arg1, "1")
            self.loadvr(arg2, "2")
            self.write_assembly(operator + " $t1, $t1, $t2")
            self.storerv("1", quad.resource)
        elif (operator == "out"):
            self.loadvr(resource, "9")
            self.write_assembly("li $v0, 1")
            self.write_assembly("add $a0, $zero, $t9")
            self.write_assembly("syscall")
        elif (operator == "in"):
            self.write_assembly("li $v0, 5")
            self.write_assembly("syscall")
        elif (operator == "retv"):
            self.loadvr(resource, "1")
            self.write_assembly("lw $t0, -8($sp)")
            self.write_assembly("sw $t1, 0($t0)")
        elif (operator == "halt"):
            self.write_assembly("li $v0, 10 #exit")
            self.write_assembly("syscall")
        elif (operator == "par"):
            if (is_main_program):
                frame_length = main_framelen
                level = 0
            else:
                entity, level = self.search_entity(block_name, "FUNCTION")
                frame_length = entity.framelength
            
            if (parameter_list == []):
                self.write_assembly("addi $fp, $sp, -" + str(frame_length))
            
            parameter_list.append(quad)
            offset = 12 + 4 * parameter_list.index(quad)
            if (arg2 == "CV"):
                self.loadvr(arg1, "0")
                self.write_assembly("sw $t0, -" + str(offset) + "($fp)")
            elif (arg2 == "REF"):
                variable_entity, variable_level = self.search_entity_by_name(arg1)
                variable_type = variable_entity.type
                variable_offset = variable_entity.offset
                if (variable_entity == None):
                    self.error("Variable not found: " + arg1)
                    
                if (level == variable_level):
                    if (variable_type == "VARIABLE") or (variable_type == "PARAMETER" and variable_entity.parameter_type == "in"):
                        self.write_assembly("addi $t0, $sp, -" + str(variable_offset))
                        self.write_assembly("sw $t0, -" + str(offset) + "($fp)")
                    elif (variable_type == "PARAMETER" and variable_entity.parameter_type == "inout"):
                        self.write_assembly("lw $t0, -" + str(variable_offset) + "($sp)")
                        self.write_assembly("sw $t0, -" + str(offset) + "($fp)")
                else:
                    if (variable_type == "VARIABLE") or (variable_type == "PARAMETER" and variable_entity.parameter_type == "in"):
                        self.gnvlcode(arg1)
                        self.write_assembly("sw $t0, -" + str(offset) + "($fp)")
                    elif (variable_type == "PARAMETER" and variable_entity.parameter_type == "inout"):
                        self.gnvlcode(arg1)
                        self.write_assembly("lw $t0, 0($t0)")
                        self.write_assembly("sw $t0, -" + str(offset) + "($fp)")
            elif (arg2 == "RET"):
                variable_entity, variable_level = self.search_entity_by_name(arg1)
                variable_type = variable_entity.type
                variable_offset = variable_entity.offset
                if (variable_entity == None):
                    self.error("Variable not found: " + arg1)
                    
                self.write_assembly("addi $t0, $sp, -" + str(variable_offset))
                self.write_assembly("sw $t0, -8($fp)")
        elif (operator == "call"):
            if (is_main_program):
                frame_length = main_framelen
                level = 0
            else:
                entity, level = self.search_entity(block_name, "FUNCTION")
                frame_length = entity.framelength
            
            called_name = resource
            called_entity, called_level = self.search_entity(called_name, "FUNCTION")
            start_quad = called_entity.start_quad -1
            if (called_entity == None):
                self.error("Function cannot found: " + called_name)
            self.check_if_arguments_match(called_name)
            
            if (level == called_level):
                self.write_assembly("lw $t0, -4($sp)")
                self.write_assembly("sw $t0, -4($fp)")
            else:
                self.write_assembly("sw $sp,-4($fp)")
            
            self.write_assembly("addi $sp, $sp, " + str(frame_length))
            self.write_assembly("jal L_"+str(start_quad)) #TODO: confirm this
            self.write_assembly("addi $sp, $sp, -" + str(frame_length))
        elif (operator == "begin_block"):
            self.write_assembly("sw $ra, 0($sp)")
            if (is_main_program):
                self.replace_main_label(quad.label, resource)
        elif (operator == "end_block"):
            if (is_main_program):
                self.write_assembly("j L_"+str(halt_quad_id))
            else:
                self.write_assembly("lw $ra,0($sp)")
                self.write_assembly("jr $ra")
                
    def replace_main_label(self,label, resource):
        global assembly_content
        replac = "L_"+str(label)
        replaced = "L_"+resource+":"
        while (len(replaced) < 23):
            replaced += " "
        replaced += "#main label\n\n"
        replaced += replac
        assembly_content = assembly_content.replace(replac, replaced)
        
    def check_if_arguments_match(self, function_name):
        global parameter_list
        entity, level = self.search_entity_by_name(function_name)
        if (entity == None):
            self.error("Function cannot found: " + entity.name)    
        if (entity.type != "FUNCTION"):
            self.error(entity.name + " is not a function!") 
        
        retIndex = 0
        for i in range (0 , len(parameter_list)):
            quad = parameter_list[i]
            if (quad.argument2 == "RET"):
                retIndex = i
                break
        parameter_list.pop(retIndex)
        entity_arguments = len(entity.args)
        
        if (entity_arguments != len(parameter_list)):
            self.error(entity.name + " function called with wrong number of arguments.") 
            
        for argument in entity.args:
            quad = parameter_list.pop(0)
            if (quad.argument2 != argument.parameter_type):
                par_type = "IN"
                if (argument.parameter_type == "REF"):
                    par_type = "INOUT"
                self.error(quad.argument1 + " should be passed with " + par_type + " parameter type.")
            
#   _____   _   _   _____   _____  ______  ___  ___  _____  ______   _____    ___    _____   _____ 
#  |_   _| | \ | | |_   _| |  ___| | ___ \ |  \/  | |  ___| |  _  \ |_   _|  / _ \  |_   _| |  ___|
#    | |   |  \| |   | |   | |__   | |_/ / | .  . | | |__   | | | |   | |   / /_\ \   | |   | |__  
#    | |   | . ` |   | |   |  __|  |    /  | |\/| | |  __|  | | | |   | |   |  _  |   | |   |  __| 
#   _| |_  | |\  |   | |   | |___  | |\ \  | |  | | | |___  | |/ /   _| |_  | | | |   | |   | |___ 
#   \___/  \_| \_/   \_/   \____/  \_| \_| \_|  |_/ \____/  |___/    \___/  \_| |_/   \_/   \____/ 
#                                                                                                  
#                                                                                                  
#     _____   _____  ______   _____                                                                
#    /  __ \ |  _  | |  _  \ |  ___|                                                               
#    | /  \/ | | | | | | | | | |__                                                                 
#    | |     | | | | | | | | |  __|                                                                
#    | \__/\ \ \_/ / | |/ /  | |___                                                                
#     \____/  \___/  |___/   \____/                                                                
#                                                                                                  
    
    def next_quad(self):
        global quad_id
        return quad_id + 1
    
    def gen_quad(self, operator, argument1, argument2, resource):
        global quad_id
        label = quad_id
        quad_id += 1
        new_quad = Quad(label, operator, argument1, argument2, resource)
        quad_list.append(new_quad)    
    
    def new_temp(self):
        global temp_id, is_main, main_declarations
        var = "T_" + str(temp_id)
        temp_id += 1
        if (is_main):
            main_declarations.append(var)
        offset = scopes[-1].get_offset()
        scopes[-1].add_entity(TempVariable(var, offset))
        return var
    
    def make_list(self, label):
        new_list = list()
        new_list.append(label)
        return new_list
    
    def merge(self, list1, list2):
        return list1 + list2   
          
    def empty_list(self):
        return list() 
    
    def backpatch(self, somelist, res):
        global quad_list
        for quad in quad_list:
            if quad.label + 1 in somelist:
                if (True):
                    quad.resource = res - 1

    def get_scope_string(self):
        strin = '//THIS IS THE MAIN SCOPE OF THE PROGRAM\n'
        for scope in scopes:
            level = scope.level + 1
            for entity in scope.entities:
                strin += '----->' * level + str(entity) + '\n'
                if isinstance(entity, Function):
                    for arg in entity.args:
                        strin += '------' * level + '----->' + str(arg) + '\n'
        strin += '\n'
        return strin
        
    def add_new_scope(self):
        enclosing_scope = scopes[-1]
        curr_scope = Scope(enclosing_scope.level + 1, enclosing_scope)
        scopes.append(curr_scope)

    def add_function_entity(self, name):
        global scopes
        nested_level = scopes[-1].enclosing_scope.level
        if (not self.unique_entity(name, "FUNCTION", nested_level)):
            self.error(name + " function is already defined.")
        scopes[-2].add_entity(Function(name))

    def update_function_entity_quad(self, name):
        global program_name
        start_quad = self.next_quad()
        if name == program_name:
            return start_quad
        func_entity = self.search_entity(name, "FUNCTION")[0]
        func_entity.set_start_quad(start_quad)
        return start_quad

    def update_function_entity_framelen(self, name, framelength):
        global main_framelen, program_name
        if name == program_name:
            main_framelen = framelength
            return
        func_entity = self.search_entity(name, "FUNCTION")[0]
        func_entity.set_framelen(framelength)

    def add_parameter_entity(self, name, par_mode):
        global scopes
        nested_level = scopes[-1].level
        par_offset = scopes[-1].get_offset()
        if not self.unique_entity(name, "PARAMETER", nested_level):
            self.error(name + " parameter is already defined.")
        scopes[-1].add_entity(Parameter(name, par_mode, par_offset))

    def add_var_entity(self, name):
        global scopes
        nested_level = scopes[-1].level
        var_offset = scopes[-1].get_offset()
        if not self.unique_entity(name, "VARIABLE", nested_level):
            self.error(name + " variable is already defined.")
        if self.variable_is_parameter(name, nested_level):
            self.error(name + " variable is already defined in parameter.")
        scopes[-1].add_entity(Variable(name, var_offset))

    def add_function_argument(self, func_name, par_name, par_mode):
        if (par_mode == 'in'):
            new_arg = Argument('CV', par_name)
        elif (par_mode == "inout"):
            new_arg = Argument("REF", par_name)
        else:
            new_arg = Argument('CV_REF', par_name)
        func_entity = self.search_entity(func_name, "FUNCTION")[0]
        if func_entity == None:
            self.error("No definition found named " + func_name)
        if func_entity.args != list():
            func_entity.args[-1].set_next(new_arg)
        func_entity.add_arg(new_arg)

    def search_entity(self, name, etype):
        if scopes == list():
            return
        tmp_scope = scopes[-1]
        while tmp_scope != None:
            for entity in tmp_scope.entities:
                if entity.name == name and entity.type == etype:
                    return entity, tmp_scope.level
            tmp_scope = tmp_scope.enclosing_scope

    def search_entity_by_name(self, name):
        if scopes == list():
            return
        temp_scope = scopes[-1]
        while temp_scope != None:
            for entity in temp_scope.entities:
                if entity.name == name:
                    return entity, temp_scope.level
            temp_scope = temp_scope.enclosing_scope

    def unique_entity(self, name, etype, nested_level):
        if scopes[-1].level < nested_level:
            return
        scope = scopes[nested_level]
        list_len = len(scope.entities)
        for i in range(list_len):
            for j in range(list_len):
                entity1 = scope.entities[i]
                entity2 = scope.entities[j]
                if entity1.name == entity2.name and entity1.type == entity2.type and entity1.name == name and entity1.type == etype:
                    return False
        return True

    def variable_is_parameter(self, name, nested_level):
        if scopes[-1].level < nested_level:
            return
        scope = scopes[nested_level]
        list_len = len(scope.entities)
        for i in range(list_len):
            e = scope.entities[i]
            if e.type == "PARAMETER" and e.name == name:
                return True
        return False

        
class Quad():

    def __init__(self, label, operator, argument1, argument2, resource):
        self.label, self.operator, self.argument1, self.argument2 = label, operator, argument1, argument2
        self.resource = resource

    def __str__(self):
        return  '// ' + str(self.operator) + ', ' + \
            str(self.argument1) + ', ' + str(self.argument2) + ', ' + str(self.resource)

    def tofile(self):
        return str(self.label) + ': ' + str(self.operator) + ', ' + \
            str(self.argument1) + ', ' + str(self.argument2) + ', ' + str(self.resource) 

#   _____     _____   _____  ______ _____ 
#  /  __ \   /  __ \ |  _  | |  _  \  ___|
#  | /  \/   | /  \/ | | | | | | | | |__  
#  | |       | |     | | | | | | | |  __| 
#  | \__/\   | \__/\ \ \_/ / | |/ /| |___ 
#   \____/    \____/  \___/  |___/ \____/ 
#                                        
    
    def toC(self):
        should_add_label = True
        if self.operator == 'jump':
            retval = 'goto L_' + str(self.resource) + ';'
        elif self.operator in ('=', '<>', '<', '<=', '>', '>='):
            operator = self.operator
            if operator == '=':
                operator = '=='
            elif operator == '<>':
                operator = '!='
            retval = 'if (' + str(self.argument1) + ' ' + operator + ' ' + \
                str(self.argument2) + ') goto L_' + str(self.resource) + ';'
        elif self.operator == 'inp':
            return ''
        elif self.operator == ':=':
            retval = self.resource + ' = ' + str(self.argument1) + ';'
        elif self.operator in ('+', '-', '*', '/'):
            retval = self.resource + ' = ' + str(self.argument1) + ' ' + \
                str(self.operator) + ' ' + str(self.argument2) + ';'
        elif self.operator == 'out':
            retval = 'printf("%d\\n", ' + str(self.argument1) + ');'
        elif self.operator == 'retv':
            retval = 'return (' + str(self.argument1) + ');'
        elif self.operator == 'begin_block':
            should_add_label = False
            global program_name, main_declarations
            retval = 'int main(void)\n{'
            if (len(main_declarations) > 0):
                declars = '\n\tint '
                for declarement in main_declarations:
                    declars += declarement
                    declars += ','
                declars = declars[:-1]
                retval += declars + ';'
            retval += '\n\tL_' + str(self.label) + ':'
        elif self.operator == 'call':
            retval = self.argument1 + '();' 
        elif self.operator == 'end_block':
            should_add_label = False
            retval = '\tL_' + str(self.label) + ': {}\n'
            retval += '}\n'
        elif self.operator == 'halt':
            retval = 'return 0;'
        else:
            return None
        if should_add_label == True:
            retval = '\tL_' + str(self.label) + ': ' + retval
        return retval + '\t\t' + self.__str__() + '\n' 

#   _____  __   __ ___  ___ ______   _____   _     
#  /  ___| \ \ / / |  \/  | | ___ \ |  _  | | |    
#  \ `--.   \ V /  | .  . | | |_/ / | | | | | |    
#   `--. \   \ /   | |\/| | | ___ \ | | | | | |    
#  /\__/ /   | |   | |  | | | |_/ / \ \_/ / | |____
#  \____/    \_/   \_|  |_/ \____/   \___/  \_____/
#                                                  
#                                                  


class Scope():

    def __init__(self, level, enclosing_scope):
        self.entities, self.level = list(), level
        self.enclosing_scope = enclosing_scope
        self.offset = 12

    def add_entity(self, entity):
        self.entities.append(entity)

    def get_offset(self):
        offset = self.offset
        self.offset += 4
        return offset

    def __str__(self):
        strin = self.__repr__()
        strin += ": ("
        strin += str(self.level)
        strin += ", "
        strin += self.enclosing_scope.__repr__()
        strin += ")"
        return strin

             
class Argument():

    def __init__(self, parameter_type, name, next_argument=None):
        self.parameter_type = parameter_type
        self.next_argument = next_argument
        self.name = name

    def set_next(self, next_argument):
        self.next_argument = next_argument

    def __str__(self):
        if (self.next_argument != None):
            return self.name + ': (' + self.parameter_type + ', next = ' + \
                self.next_argument.name + ')'
        else:
            return self.name + ': (' + self.parameter_type + ', next = None)'


class Entity():

    def __init__(self, name, entity_type):
        self.name, self.type, self.next = name, entity_type, None

    def __str__(self): 
        return self.type + ': ' + self.name


class Variable(Entity):

    def __init__(self, name, offset=-1):
        super().__init__(name, "VARIABLE")
        self.offset = offset

    def __str__(self):
        return super().__str__() + ', offset: ' + \
            str(self.offset)


class Function(Entity):

    def __init__(self, name, start_quad=-1):
        super().__init__(name, "FUNCTION")
        self.start_quad = start_quad
        self.args, self.framelength = list(), -1

    def add_arg(self, arg):
        self.args.append(arg)

    def set_framelen(self, framelength):
        self.framelength = framelength

    def set_start_quad(self, start_quad):
        self.start_quad = start_quad

    def __str__(self):
        return super().__str__() \
            +', start_quad: ' + str(self.start_quad) + ', frame_length: ' \
            +str(self.framelength)

            
class Parameter(Entity):

    def __init__(self, name, parameter_type, offset=-1):
        super().__init__(name, "PARAMETER")
        self.parameter_type, self.offset = parameter_type, offset

    def __str__(self):
        return super().__str__() + ', mode: ' + self.parameter_type \
            +', offset: ' + str(self.offset)


class TempVariable(Entity):

    def __init__(self, name, offset=-1):
        super().__init__(name, "TEMP_VARIABLE")
        self.offset = offset

    def __str__(self):
        return super().__str__() + ', offset: ' + str(self.offset)


#   _       _____  __   __
#  | |     |  ___| \ \ / /
#  | |     | |__    \ V / 
#  | |     |  __|   /   \ 
#  | |____ | |___  / /^\ \
#  \_____/ \____/  \/   \/
#                         
SINGLE_SYMBOLS = ["*", "+", "-", "/", "="]
SEPARATION_SYMBOLS = [";", ",", "(", ")", "[", "]"]
IGNORED_SYMBOLS = ["\n", " ", "\t"]


class Lex:
    index = None
    words = None
    file_content = None
    line_number = None
    dummy_index = None

    def __init__(self, file_content, name):
        self.name = name
        self.file_content = file_content
        self.file_content = self.file_content + " "
        self.index = 0
        self.line_number = 1
        self.dummy_index = 1
        
    def get(self):
        if (self.is_ended()):
            raise Exception("There are no more words to get.")
        if (self.current_character() in IGNORED_SYMBOLS):
            if (self.current_character() == "\n"):
                self.line_number = self.line_number + 1
                self.dummy_index = 0
            self.increase_index()
            return self.get()
        if (self.is_letter(self.current_character())):
            return self.word()
        elif (self.is_number(self.current_character())):
            return self.arithmetic_constant()
        elif (self.current_character() in SINGLE_SYMBOLS and self.current_character() != "/"):
            return self.single_symbol()
        elif (self.current_character() == '<'):
            return self.smaller_than_symbol()
        elif (self.current_character() == '>'):
            return self.bigger_than_symbol()
        elif (self.current_character() == ':'):
            next_symbol = self.get_next_and_restore()
            self.increase_index()
            if (next_symbol == "="):
                self.increase_index()
                return ":="
            else:
                return ":"
        elif (self.current_character() == '/'):
            next_symbol = self.get_next_and_restore()
            if (next_symbol == "*"):
                return self.comment_section()
            elif (next_symbol == "/"):
                return self.lined_comment_section()
            else: return self.single_symbol()
        elif (self.current_character() in SEPARATION_SYMBOLS):
            symbol = self.current_character()
            self.increase_index()
            return symbol
        else: self.error("Unknown symbol: " + self.current_character())
        
    def lined_comment_section(self):
        self.increase_index()  # /
        self.increase_index()  # second /
        while (self.current_character() != "\n"):
            if (self.is_ended()):
                return None
            self.increase_index()
        return self.get()
    
    def comment_section(self):
        self.increase_index()  # star
        self.increase_index()  # next character of star
        while (True):
            if (self.is_ended()):
                raise Exception("Unclosed comment section.")
            if (self.current_character() == "*"):
                self.increase_index()
                if (self.current_character() == "/"):
                    self.increase_index()
                    return self.get()  # end of comment section
                else:
                    self.increase_index()
            else: self.increase_index()
               
    def single_symbol(self):
        word = self.current_character()
        self.increase_index()
        return word  
        
    def bigger_than_symbol(self):
        next_symbol = self.get_next_and_restore()
        if (next_symbol == '='):
            self.increase_index()
            self.increase_index()
            return '>' + next_symbol
        self.increase_index()
        return '>'   
         
    def smaller_than_symbol(self):
        next_symbol = self.get_next_and_restore()
        if (next_symbol == '=' or next_symbol == '>'):
            self.increase_index()
            self.increase_index()
            return '<' + next_symbol
        self.increase_index()
        return '<'
                
    def get_next_and_restore(self):
        self.increase_index()
        symbol = self.current_character()
        self.index = self.index - 1
        return symbol
    
    def arithmetic_constant(self):
        word = self.current_character()
        self.increase_index()
        while (self.is_number(self.current_character())):
            word = word + self.current_character()
            self.increase_index()
        number = int(word)
        if (number > 32767 or number < -32767):
            self.error("Arithmetic constants must be between -32767 and 32767.")
        return word
    
    def word(self):
        word = self.current_character()
        self.increase_index()
        while (self.is_letter(self.current_character()) or self.is_number(self.current_character())):
            word = word + self.current_character()
            self.increase_index()
        if (len(word) > 30):
            word = word[:30]
        return word
            
    def increase_index(self):
        self.index = self.index + 1
        self.dummy_index = self.dummy_index + 1
         
    def current_character(self):
        return self.file_content[self.index];
    
    def is_letter(self, character):
        pattern = re.compile("[A-Za-z]")
        return  pattern.match(character) != None
    
    def is_number(self, character):
        pattern = re.compile("[0-9]")
        return  pattern.match(character) != None
    
    def is_ended(self):
        return self.index >= len(self.file_content)
    
    def error(self, message):
        raise Exception("Invalid token \"" 
                        +self.token + 
                         "\" in "
                         +self.name + 
                         ", Line: "
                         +str(self.line_number) + 
                         " Index: "
                         +str(self.dummy_index) + 
                         ". " + message)
        
       
def read_file(file):
    F = open(file);
    content = F.read()
    return content  


def write_file(file, content):
    f = open(file, "w")
    f.write(content)
    f.close()


def main():
    if (len(sys.argv) == 1):
        print("No argument file or directory given.")
        sys.exit()
    file = sys.argv[1]
    StartletCompiler(file)

    
main()
    
