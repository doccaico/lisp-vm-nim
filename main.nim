import std / [strutils, parseutils, tables, sequtils, os]

type
  LispError = object of CatchableError

  Reader* = object
    input: string
    position: int     # Current position in input (points to current char)
    readPosition: int # Next reading position in input (after current char)
    ch: char          # Current char under examination

  OpCode {.size: sizeof(uint8).} = enum
    OpConstant
    OpAdd
    OpSub
    OpMul
    OpDiv
    OpEqual        # =
    OpLessThan     # <
    OpLessEqual    # <=
    OpGreaterThan  # >
    OpGreaterEqual # >=
    OpPrint
    OpProgn
    OpCall         # Function call
    OpStore        # Store the value at the top of the stack into the variable at the specified index
    OpLoad         # Push the value of the variable at the specified index onto the stack
    OpJumpIfFalse
    OpJump         # Unconditional jump
    OpMakeClosure

  LambdaObj = ref object
    params: seq[string]
    paramIndices: seq[int]
    code: seq[int]
    constants: seq[VmValue]

  ClosureObj = ref object
    lambda: LambdaObj
    env: array[256, VmValue]

  ValueKind = enum
    vkInt
    vkFloat
    vkString
    vkTrue
    vkNil
    vkLambda  # For the compile-time constant pool
    vkClosure # For closures at runtime

  VmValue = object
    case kind: ValueKind
    of vkInt: intVal: int
    of vkFloat: floatVal: float
    of vkString: strVal: string
    of vkTrue: trueVal: int
    of vkNil: nilVal: int
    of vkLambda: lambdaVal: LambdaObj
    of vkClosure: closureVal: ClosureObj

  AstKind = enum
    akInt
    akFloat
    akString
    akSymbol
    akTrue
    akNil
    akList

  Ast = ref object
    case kind: AstKind
    of akInt: intVal: int
    of akFloat: floatVal: float
    of akString: strVal: string
    of akSymbol: symVal: string
    of akTrue: trueVal: int
    of akNil: nilVal: int
    of akList: listVal: seq[Ast]

  Bytecode = object
    code: seq[int]
    constants: seq[VmValue]

  Compiler = ref object
    symbolTable: Table[string, int] # A map from variable names to indices
    parent: Compiler

proc `$`(val: VmValue): string
proc `$`(ast: Ast): string
proc resolveSymbol(c: Compiler, name: string): tuple[found: bool, index: int]
proc toRepr(s: string): string
proc readAtom(r: var Reader): Ast
proc isDelimiter(ch: char): bool
proc initReader(input: string): Reader
proc nextChar(r: var Reader)
proc skipWhitespaceAndComment(r: var Reader)
proc read(r: var Reader): Ast
proc readList(r: var Reader): Ast
proc readString(r: var Reader): string
proc newInt(v: int): Ast
proc newFloat(v: float): Ast
proc newStr(s: string): Ast
proc newSym(s: string): Ast
proc newTrue(): Ast
proc newNil(): Ast
proc newStructuredList(args: varargs[Ast]): Ast
proc newCompiler(parent: Compiler): Compiler
proc vmInt(v: int): VmValue
proc vmFloat(v: float): VmValue
proc vmStr(s: string): VmValue
proc vmTrue(): VmValue
proc vmNil(): VmValue
proc compile(c: var Compiler, ast: Ast, bc: var Bytecode)
proc run(bc: Bytecode, locals: var array[256, VmValue]): VmValue

proc `$`(val: VmValue): string =
  case val.kind
  of vkInt: $val.intVal
  of vkFloat: $val.floatVal
  of vkString: val.strVal
  of vkTrue: "T"
  of vkNil: "NIL"
  of vkLambda: "<lambda>"
  of vkClosure: "<closure>"

proc `$`(ast: Ast): string =
  case ast.kind
  of akSymbol: ast.symVal
  of akInt: $ast.intVal
  of akFloat: $ast.floatVal
  of akString: "\"" & ast.strVal & "\""
  of akTrue: "t"
  of akNil: "nil"
  of akList: "(" & ast.listVal.mapIt($it).join(", ") & ")"

proc resolveSymbol(c: Compiler, name: string): tuple[found: bool, index: int] =
  if c.symbolTable.hasKey(name):
    return (true, c.symbolTable[name])
  return (false, 0)

# Parse numbers or symbols (collectively called "atoms")
proc readAtom(r: var Reader): Ast =
  let startPos = r.position

  # Keep moving forward until a delimiter is encountered
  while not isDelimiter(r.ch):
    r.nextChar()

  # Extract the token string (e.g., "123", "abc", "+")
  let token = r.input[startPos ..< r.position]

  if token == "t":
    return newTrue()

  if token == "nil":
    return newNil()

  # Attempt to parse an integer (Int)
  # Treat as an integer only if it does not contain '.' or 'e'
  if '.' notin token and 'e' notin token and 'E' notin token:
    var intVal: int
    try:
      let parsedLen = parseutils.parseInt(token, intVal, 0)
      if parsedLen == token.len and token.len > 0:
        return newInt(intVal)
    except ValueError:
      var isAllDigits = true
      for i, c in token:
        if i == 0 and (c == '-' or c == '+'):
          continue
        if c notin {'0'..'9'}:
          isAllDigits = false
          break
      if isAllDigits and token.len > 0:
        raise newException(LispError,
          "integer overflow error: '" & token & "' is out of range for standard Int")

  # Attempt to parse a real number (Float)
  var floatVal: float
  try:
    let parsedFloatLen = parseutils.parseFloat(token, floatVal, 0)
    if parsedFloatLen == token.len and token.len > 0:
      # Nim's `parseFloat` (with a C backend) returns `inf` or `-inf` upon overflow,
      # and can also result in an incorrect parse length; therefore, we safely check for both cases
      if floatVal == Inf or floatVal == -Inf:
        raise newException(LispError,
          "float overflow: '" & token & "' is out of range for standard Float")
      return newFloat(floatVal)
  except ValueError:
    var isFloatFormat = true
    for i, c in token:
      if i == 0 and (c == '-' or c == '+'):
        continue
      if c notin {'0'..'9', '.', 'e', 'E', '-', '+'}:
        isFloatFormat = false
        break
    if isFloatFormat and token.len > 0:
      raise newException(LispError,
        "float overflow: '" & token & "' is out of range for standard Float")

  if token.len >= 2 and token[0] in {'0'..'9', '+', '-'}:
    raise newException(LispError, "Invalid numeric format or symbol name '" & token & "'")

  # If it's neither, then it's a symbol
  newSym(token)

# Helper to determine if a character is a delimiter
proc isDelimiter(ch: char): bool =
  # Whitespace, parentheses, quotes, or EOF are delimiters
  ch in {' ', '\t', '\r', '\n', '(', ')', '"', '\0'}

# Initialize the lexical analyzer / reader
proc initReader(input: string): Reader =
  result = Reader(input: input, position: 0, readPosition: 0, ch: '\0')
  # Advance once to set the initial character in 'ch'
  result.nextChar()

# Advance one character (consume input)
proc nextChar(r: var Reader) =
  if r.readPosition >= r.input.len:
    r.ch = '\0' # Nul character signifies end of input
  else:
    r.ch = r.input[r.readPosition]

  r.position = r.readPosition
  inc r.readPosition

# Skip whitespaces and comments (lines starting with ';')
proc skipWhitespaceAndComment(r: var Reader) =
  while true:
    # Skip standard whitespaces
    if r.ch in {' ', '\t', '\r', '\n'}:
      r.nextChar()
      continue

    # Skip comment line if ';' is encountered
    if r.ch == ';':
      # Consume characters until we hit a newline (\n, \r) or End of Input (\0)
      while r.ch notin {'\n', '\r', '\0'}:
        r.nextChar()
      continue

    # If the current character is neither a whitespace nor a comment start, stop skipping
    break

# Read and return exactly one AST object
proc read(r: var Reader): Ast =
  r.skipWhitespaceAndComment()

  if r.ch == '"':
    return newStr(r.readString) # Return a string object

  elif r.ch == '(':
    r.nextChar() # Consume '('
    return r.readList() # Delegate list parsing to the specialized function

  elif r.ch == ')':
    raise newException(LispError, "Unexpected closing parenthesis ')'")

  elif r.ch == '\0':
    return nil # End of input reached

  else:
    # If it's not a quote or parenthesis, it's guaranteed to be an atom
    return  r.readAtom()

# Parse the contents of a list (until a closing parenthesis)
proc readList(r: var Reader): Ast =
  var listElements = newSeq[Ast]()

  # Loop through list elements recursively
  while r.ch != ')' and r.ch != '\0':
    let element = r.read()
    if element != nil:
      listElements.add(element)

    r.skipWhitespaceAndComment()

  if r.ch == '\0':
    raise newException(LispError, "Unclosed list literal")

  r.nextChar() # Consume ')'

  return newStructuredList(listElements)

# Parse string literals
proc readString(r: var Reader): string =
  # Skip the starting double quote
  r.nextChar()

  result = ""

  while true:
    if r.ch == '"':
      r.nextChar() # Consume the closing quote and advance
      break

    if r.ch == '\0':
      raise newException(LispError, "Unclosed string literal")

    if r.ch == '\\':
      r.nextChar() # Consume '\\'
      if r.ch == '\0':
        raise newException(LispError, "Unclosed string literal after escape")
      
      # Handle common escape sequences
      case r.ch
      of 'n': result.add('\n')
      of 't': result.add('\t')
      of 'r': result.add('\r')
      of '\\': result.add('\\')
      of '"': result.add('"')
      else:
        result.add(r.ch) # Fallback for unknown escape sequences

      r.nextChar()
    else:
      result.add(r.ch)
      r.nextChar()

proc toPlain(s: string): string = s

proc toRepr(s: string): string =
  result = "\""
  for c in s:
    case c
    of '\\':
      result.add("\\\\")
    of '\n':
      result.add("\\n")
    of '\t':
      result.add("\\t")
    of '\r':
      result.add("\\r")
    of '\"':
      result.add("\\\"")
    else:
      result.add(c)
  result.add("\"")

proc newInt(v: int): Ast = Ast(kind: akInt, intVal: v)
proc newFloat(v: float): Ast = Ast(kind: akFloat, floatVal: v)
proc newStr(s: string): Ast = Ast(kind: akString, strVal: s)
proc newSym(s: string): Ast = Ast(kind: akSymbol, symVal: s)
proc newTrue(): Ast = Ast(kind: akTrue)
proc newNil(): Ast = Ast(kind: akNil)
proc newStructuredList(args: varargs[Ast]): Ast = Ast(kind: akList, listVal: @args)
proc newCompiler(parent: Compiler): Compiler =
  Compiler(symbolTable: initTable[string, int](), parent: parent)
proc vmInt(v: int): VmValue = VmValue(kind: vkInt, intVal: v)
proc vmFloat(v: float): VmValue = VmValue(kind: vkFloat, floatVal: v)
proc vmStr(s: string): VmValue = VmValue(kind: vkString, strVal: s)
proc vmTrue(): VmValue = VmValue(kind: vkTrue)
proc vmNil(): VmValue = VmValue(kind: vkNil)

proc compareTypeCheck(op: string, a: VmValue, b: VmValue) =
  if a.kind != b.kind:
    raise newException(LispError, "Type error in '" & op & "': " & $a.kind & " " & $b.kind)
  if a.kind == vkString:
    raise newException(LispError, "The value " & a.strVal & " is not of type NUMBER")
  if b.kind == vkString:
    raise newException(LispError, "The value " & b.strVal & " is not of type NUMBER")
  if a.kind == vkNil or b.kind == vkNil:
    raise newException(LispError, "The value NIL is not of type REAL")
  if a.kind == vkTrue or b.kind == vkTrue:
    raise newException(LispError, "The value T is not of type REAL")

proc compile(c: var Compiler, ast: Ast, bc: var Bytecode) =
  case ast.kind
  of akInt:
    bc.constants.add(vmInt(ast.intVal))
    let constIdx = bc.constants.len - 1
    # Enter a command
    bc.code.add(OpConstant.int)
    # Write the argument (constant index) to the next byte
    bc.code.add(constIdx)
  of akFloat:
    bc.constants.add(vmFloat(ast.floatVal))
    let constIdx = bc.constants.len - 1
    bc.code.add(OpConstant.int)
    bc.code.add(constIdx)
  of akString:
    # When a string literal is found, register it in the constant pool and emit an OpConstant
    bc.constants.add(vmStr(ast.strVal.toRepr))
    let constIdx = bc.constants.len - 1
    bc.code.add(OpConstant.int)
    bc.code.add(constIdx)
  of akNil:
    bc.constants.add(vmNil())
    let constIdx = bc.constants.len - 1
    bc.code.add(OpConstant.int)
    bc.code.add(constIdx)
  of akTrue:
    bc.constants.add(vmTrue())
    let constIdx = bc.constants.len - 1
    bc.code.add(OpConstant.int)
    bc.code.add(constIdx)
  of akSymbol:
    let (found, index) = c.resolveSymbol(ast.symVal)
    if found:
      bc.code.add(OpLoad.int)
      bc.code.add(index)
    else:
      raise newException(LispError, "Undefined variable: " & ast.symVal)
  of akList:
    if ast.listVal.len == 0:
      bc.constants.add(vmNil())
      let constIdx = bc.constants.len - 1
      bc.code.add(OpConstant.int)
      bc.code.add(constIdx)
      return

    let head = ast.listVal[0]

    # Check for special forms or operators only when the head is a symbol
    if head.kind == akSymbol:
      let op = head.symVal

      if op == "define":
        if ast.listVal.len != 3:
          raise newException(LispError, "DEFINE requires exactly 2 argument")
        if ast.listVal[1].kind != akSymbol:
          raise newException(LispError, "DEFINE first argument must be a symbol")

        let varName = ast.listVal[1].symVal
        let valueAst = ast.listVal[2]

        # To support recursive calls, indices are reserved and registered in advance, prior to compilation
        var targetIndex: int
        if c.symbolTable.hasKey(varName):
          targetIndex = c.symbolTable[varName]
        else:
          targetIndex = c.symbolTable.len
          c.symbolTable[varName] = targetIndex

        c.compile(valueAst, bc)

        bc.code.add(OpStore.int)
        bc.code.add(targetIndex)

      elif op == "if":
        if not (ast.listVal.len == 3 or ast.listVal.len == 4): 
          raise newException(LispError,
            "if requires exactly 2 or 3 arguments (if test conseq |alt|), got " & $(ast.listVal.len - 1))

        let condAst = ast.listVal[1]
        let thenAst = ast.listVal[2]
        let hasElse = ast.listVal.len > 3
        let elseAst = if hasElse: ast.listVal[3] else: nil

        c.compile(condAst, bc)
        bc.code.add(OpJumpIfFalse.int)
        let jumpToElsePos = bc.code.len
        bc.code.add(0)

        c.compile(thenAst, bc)

        if hasElse:
          bc.code.add(OpJump.int)
          let jumpToEndPos = bc.code.len
          bc.code.add(0)

          bc.code[jumpToElsePos] = bc.code.len
          c.compile(elseAst, bc)
          bc.code[jumpToEndPos] = bc.code.len
        else:
          bc.code[jumpToElsePos] = bc.code.len

      elif op == "print":
        if ast.listVal.len != 2: 
          raise newException(LispError,
            "print requires exactly 1 arguments, got " & $(ast.listVal.len - 1))
        let valAst = ast.listVal[1]
        c.compile(valAst, bc)
        bc.code.add(OpPrint.int)

      elif op == "progn":
        let argCount = ast.listVal.len - 1
        if argCount == 0:
          bc.constants.add(vmNil())
          let constIdx = bc.constants.len - 1
          bc.code.add(OpConstant.int)
          bc.code.add(constIdx)
        for i in 1 .. argCount:
          c.compile(ast.listVal[i], bc)
        bc.code.add(OpProgn.int)
        bc.code.add(argCount)

      elif op == "lambda":
        if ast.listVal.len < 3:
          raise newException(LispError, "lambda requires parameters and a body")

        let paramsAst = ast.listVal[1]
        if paramsAst.kind != akList:
          raise newException(LispError, "lambda parameters must be a list")

        var params = newSeq[string]()
        for p in paramsAst.listVal:
          if p.kind != akSymbol:
            raise newException(LispError, "lambda parameter must be a symbol")
          params.add(p.symVal)

        var subCompiler = Compiler(symbolTable: c.symbolTable)
        # Assign parameter indices starting from the end of the table to avoid conflicts with existing indices
        var nextIdx = subCompiler.symbolTable.len
        var paramIndices = newSeq[int]()
        for param in params:
          subCompiler.symbolTable[param] = nextIdx
          paramIndices.add(nextIdx)
          inc nextIdx

        var subBc = Bytecode()
        for i in 2 ..< ast.listVal.len:
          subCompiler.compile(ast.listVal[i], subBc)

        let lambdaObj = LambdaObj(
          params: params,
          paramIndices: paramIndices,
          code: subBc.code,
          constants: subBc.constants
        )

        # Registered in the constant pool as a template
        bc.constants.add(VmValue(kind: vkLambda, lambdaVal: lambdaObj))
        let constIdx = bc.constants.len - 1
        
        # Emit a closure-creation instruction instead of `OpConstant`
        bc.code.add(OpMakeClosure.int)
        bc.code.add(constIdx)

      else:
        # Standard operators and regular function calls
        let argCount = ast.listVal.len - 1
        if op in ["+", "-", "*", "/", "=", "<", "<=", ">", ">="]:
          if op == "+" and argCount == 0:
            bc.constants.add(vmInt(0))
            let constIdx = bc.constants.len - 1
            bc.code.add(OpConstant.int)
            bc.code.add(constIdx)
          elif op == "-" and argCount < 1:
            raise newException(LispError, "- requires one or more arguments")
          elif argCount == 0:
            raise newException(LispError, "Invalid number of arguments: 0")
          else:
            for i in 1 .. argCount:
              c.compile(ast.listVal[i], bc)
            case op
            of "+": bc.code.add(OpAdd.int); bc.code.add(argCount)
            of "-": bc.code.add(OpSub.int); bc.code.add(argCount)
            of "*": bc.code.add(OpMul.int); bc.code.add(argCount)
            of "/": bc.code.add(OpDiv.int); bc.code.add(argCount)
            of "=": bc.code.add(OpEqual.int)
            of "<": bc.code.add(OpLessThan.int)
            of "<=": bc.code.add(OpLessEqual.int)
            of ">": bc.code.add(OpGreaterThan.int)
            of ">=": bc.code.add(OpGreaterEqual.int)
            else: discard
        else:
          # Invoking functions or similar entities bound to ordinary variables
          c.compile(head, bc)
          for i in 1 .. argCount:
            c.compile(ast.listVal[i], bc)
          bc.code.add(OpCall.int)
          bc.code.add(argCount)

    else:
      # Function calls where the first element is something other than a symbol
      # (such as a lambda expression)
      let argCount = ast.listVal.len - 1
      c.compile(head, bc)
      for i in 1 .. argCount:
        c.compile(ast.listVal[i], bc)
      bc.code.add(OpCall.int)
      bc.code.add(argCount)

proc run(bc: Bytecode, locals: var array[256, VmValue]): VmValue =
  var stack: seq[VmValue] = @[]
  var pc = 0

  while pc < bc.code.len:
    let instruction = bc.code[pc]
    inc pc

    case instruction
    of OpConstant.int:
      # Read the arguments and then advance the PC
      let arg = bc.code[pc]
      inc pc
      stack.add(bc.constants[arg.int])
    of OpStore.int:
      let arg = bc.code[pc]
      inc pc
      locals[arg.int] = stack[stack.len - 1]
    of OpLoad.int:
      let arg = bc.code[pc]
      inc pc
      stack.add(locals[arg.int])
    of OpJumpIfFalse.int:
      let jumpAddr = bc.code[pc]
      inc pc
      let cond = stack.pop()
      # NIL is false; all other values (including integers, strings, T) are true
      let isFalse = cond.kind == vkNil
      if isFalse:
        pc = jumpAddr
    of OpJump.int:
      let jumpAddr = bc.code[pc]
      pc = jumpAddr
    of OpAdd.int:
      # Read the number of arguments from the byte immediately following, then advance the PC
      let argCount = bc.code[pc]
      inc pc

      # Pop one value for the initial reduction
      var val = stack.pop()

      # Pop the remaining arguments and add them together
      for _ in 1 ..< argCount:
        let nextVal = stack.pop()

        # To maintain Lisp’s evaluation order (left-to-right),
        # evaluate using `val` (popped first, representing the right-hand side)
        # and `nextVal` (popped subsequently, representing the left-hand side)
        if val.kind == vkInt and nextVal.kind == vkInt:
          val = vmInt(nextVal.intVal + val.intVal)
        elif val.kind == vkFloat and nextVal.kind == vkFloat:
          val = vmFloat(nextVal.floatVal + val.floatVal)
        else:
          raise newException(LispError, "Type error in '+'")
      stack.add(val)
    of OpSub.int:
      let argCount = bc.code[pc]
      inc pc

      if argCount == 1:
        var val = stack.pop()

        case val.kind
        of vkInt:
          val = vmInt(-val.intVal)
        of vkFloat:
          val = vmFloat(-val.floatVal)
        of vkString:
          raise newException(LispError, "The value " & val.strVal & " is not of type NUMBER")
        of vkTrue:
          raise newException(LispError, "The value " & $val.trueVal & " is not of type NUMBER")
        of vkNil:
          raise newException(LispError, "The value " & $val.nilVal & " is not of type NUMBER")
        of vkLambda:
          raise newException(LispError, "The value <lambda> is not of type NUMBER")
        of vkClosure:
          raise newException(LispError, "The value <closure> is not of type NUMBER")
        stack.add(val)
      else:
        var subTotal = stack.pop()

        for _ in 1 ..< argCount - 1:
          let nextVal = stack.pop()
          if subTotal.kind == vkInt and nextVal.kind == vkInt:
            subTotal = vmInt(subTotal.intVal + nextVal.intVal)
          elif subTotal.kind == vkFloat and nextVal.kind == vkFloat:
            subTotal = vmFloat(subTotal.floatVal + nextVal.floatVal)
          else:
            raise newException(LispError, "Type error in '-'")

        let firstVal = stack.pop()

        var finalResult: VmValue
        if firstVal.kind == vkInt and subTotal.kind == vkInt:
          finalResult = vmInt(firstVal.intVal - subTotal.intVal)
        elif firstVal.kind == vkFloat and subTotal.kind == vkFloat:
          finalResult = vmFloat(firstVal.floatVal - subTotal.floatVal)
        else:
          raise newException(LispError, "Type error in '-'")
        stack.add(finalResult)
    of OpMul.int:
      let argCount = bc.code[pc]
      inc pc

      var val = stack.pop()

      for _ in 1 ..< argCount:
        let nextVal = stack.pop()

        if val.kind == vkInt and nextVal.kind == vkInt:
          val = vmInt(nextVal.intVal * val.intVal)
        elif val.kind == vkFloat and nextVal.kind == vkFloat:
          val = vmFloat(nextVal.floatVal * val.floatVal)
        else:
          raise newException(LispError, "Type error in '*'")
      stack.add(val)
    of OpDiv.int:
      let argCount = bc.code[pc]
      inc pc

      if argCount == 0:
        raise newException(LispError, "Invalid number of arguments: 0")

      if argCount == 1:
        var val = stack.pop()

        case val.kind
        of vkInt:
          if val.intVal == 0:
            raise newException(LispError, "Arithmetic error DIVISION-BY-ZERO signalled")
          val = vmStr(toPlain("1/" & $val.intVal))
        of vkFloat:
          if val.floatVal == 0.0:
            raise newException(LispError, "Arithmetic error DIVISION-BY-ZERO signalled")
          val = vmFloat(1.0 / val.floatVal)
        else:
          raise newException(LispError, "Type error in unary '/'")
        stack.add(val)
      else:
        var divisorTotal = stack.pop()

        # A function for pre-emptively checking for division by zero
        proc checkZero(v: VmValue) =
          if (v.kind == vkInt and v.intVal == 0) or (v.kind == vkFloat and v.floatVal == 0.0):
            raise newException(LispError, "Division by zero")

        checkZero(divisorTotal)

        for _ in 1 ..< argCount - 1:
          let nextVal = stack.pop()
          checkZero(nextVal)

          if divisorTotal.kind == vkInt and nextVal.kind == vkInt:
            divisorTotal = vmInt(divisorTotal.intVal * nextVal.intVal)
          elif divisorTotal.kind == vkFloat and nextVal.kind == vkFloat:
            divisorTotal = vmFloat(divisorTotal.floatVal * nextVal.floatVal)
          else:
            raise newException(LispError, "Type error in '/'")

        let firstVal = stack.pop()

        var finalResult: VmValue
        if firstVal.kind == vkInt and divisorTotal.kind == vkInt:
          finalResult = vmInt(firstVal.intVal div divisorTotal.intVal)
        elif firstVal.kind == vkFloat and divisorTotal.kind == vkFloat:
          finalResult = vmFloat(firstVal.floatVal / divisorTotal.floatVal)
        else:
          raise newException(LispError, "Type error in '/'")
        stack.add(finalResult)
    of OpEqual.int:
      let b = stack.pop(); let a = stack.pop()
      if a.kind != b.kind:
        raise newException(LispError, "Type error in '=': " & $a.kind & " " & $b.kind)
      if a.kind == vkString:
        raise newException(LispError, "The value " & a.strVal & " is not of type NUMBER")
      if b.kind == vkString:
        raise newException(LispError, "The value " & b.strVal & " is not of type NUMBER")
      if a.kind == vkNil or b.kind == vkNil:
        raise newException(LispError, "The value NIL is not of type NUMBER")
      if a.kind == vkTrue or b.kind == vkTrue:
        raise newException(LispError, "The value T is not of type NUMBER")
      let res = case a.kind
                of vkInt: a.intVal == b.intVal
                of vkFloat: a.floatVal == b.floatVal
                else: raise newException(LispError, "Unreachable")
      if res: stack.add(vmTrue()) else: stack.add(vmNil())
    of OpLessThan.int:
      let b = stack.pop(); let a = stack.pop()
      compareTypeCheck("<", a, b)
      let res = case a.kind
                of vkInt: a.intVal < b.intVal
                of vkFloat: a.floatVal < b.floatVal
                else: raise newException(LispError, "Unreachable")
      if res: stack.add(vmTrue()) else: stack.add(vmNil())
    of OpLessEqual.int:
      let b = stack.pop(); let a = stack.pop()
      compareTypeCheck("<=", a, b)
      let res = case a.kind
                of vkInt: a.intVal <= b.intVal
                of vkFloat: a.floatVal <= b.floatVal
                else: raise newException(LispError, "Unreachable")
      if res: stack.add(vmTrue()) else: stack.add(vmNil())
    of OpGreaterThan.int:
      let b = stack.pop(); let a = stack.pop()
      compareTypeCheck(">", a, b)
      let res = case a.kind
                of vkInt: a.intVal > b.intVal
                of vkFloat: a.floatVal > b.floatVal
                else: raise newException(LispError, "Unreachable")
      if res: stack.add(vmTrue()) else: stack.add(vmNil())
    of OpGreaterEqual.int:
      let b = stack.pop(); let a = stack.pop()
      compareTypeCheck(">=", a, b)
      let res = case a.kind
                of vkInt: a.intVal >= b.intVal
                of vkFloat: a.floatVal >= b.floatVal
                else: raise newException(LispError, "Unreachable")
      if res: stack.add(vmTrue()) else: stack.add(vmNil())
    of OpPrint.int:
      let val = stack[stack.len - 1]
      echo val
    of OpProgn.int:
      let argCount = bc.code[pc]
      inc pc
      let lastVal = stack.pop()
      for _ in 1 ..< argCount:
        discard stack.pop()
      stack.add(lastVal)

    of OpMakeClosure.int:
      let constIdx = bc.code[pc]
      inc pc
      let lambdaVal = bc.constants[constIdx]
      let lambdaObj = lambdaVal.lambdaVal

      # 現在のローカル変数の状態（環境）をまるごとコピーしてキャプチャする
      var capturedEnv: array[256, VmValue]
      for i in 0 .. 255:
        capturedEnv[i] = locals[i]

      let closureObj = ClosureObj(lambda: lambdaObj, env: capturedEnv)
      stack.add(VmValue(kind: vkClosure, closureVal: closureObj))

    of OpCall.int:
      let argCount = bc.code[pc]
      inc pc

      var args = newSeq[VmValue](argCount)
      for i in countdown(argCount - 1, 0):
        args[i] = stack.pop()

      let fnVal = stack.pop()
      if fnVal.kind != vkClosure:
        raise newException(LispError, "Not a function")

      let closureObj = fnVal.closureVal
      let lambdaObj = closureObj.lambda

      if args.len != lambdaObj.params.len:
        raise newException(LispError, "Wrong number of arguments: expected " & 
          $lambdaObj.params.len & ", got " & $args.len)

      # Create a new local variable array based on the captured environment
      var innerLocals = closureObj.env
      # Bind arguments to the correct index positions assigned at compile time
      for i, paramIdx in lambdaObj.paramIndices:
        innerLocals[paramIdx] = args[i]

      var lambdaBc = Bytecode(code: lambdaObj.code, constants: lambdaObj.constants)
      let res = run(lambdaBc, innerLocals)
      stack.add(res)

    else:
      raise newException(LispError, "Unknown instruction: " & $instruction)

  if stack.len == 0:
    return vmInt(0)

  stack[stack.len - 1]

proc repl() =
  var parent = Compiler()
  var compiler = newCompiler(parent)
  var locals: array[256, VmValue]
  echo "Lisp VM REPL. Type expressions and press enter (Ctrl+C or empty line to exit)."

  while true:
    stdout.write(">> ")

    try:
      let line = stdin.readLine()
      if line.len == 0:
        break

      var reader = initReader(line)
      var bc = Bytecode()
      while true:
        let ast = reader.read()
        if ast == nil:
          break
        compiler.compile(ast, bc)

      if bc.code.len > 0:
        let res = run(bc, locals)
        echo res
    except LispError as e:
      echo "Error: ", e.msg

const helpMsg = """
Usage: lisp-vm filename
  -r:         REPL
  -h, --help: show a help message"""

proc main() =
  if paramCount() == 0:
    quit(helpMsg)

  let arg = paramStr(1)
  if arg == "-r":
    repl()
  elif arg == "-h" or arg == "--help":
    echo helpMsg
  else:
    let filename = arg
    if fileExists(filename):
      let sourceCode = readFile(filename)
      var reader = initReader(sourceCode)
      var bc = Bytecode()
      var parent = Compiler()
      var compiler = newCompiler(parent)
      while true:
        try:
          let ast = reader.read()
          if ast == nil:
            break
          compiler.compile(ast, bc)
        except LispError as e:
          echo "Error: ", e.msg
        except IndexDefect:
          # Safely display "index out of range" errors, such as when arguments are missing
          echo "Error: malformed list or missing arguments"

      var locals: array[256, VmValue]
      discard run(bc, locals)
    else:
      quit("File not found: " & filename)

main()
