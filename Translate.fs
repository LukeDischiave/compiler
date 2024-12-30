module Translate

open AST
open IR
open Helper

// Symbol table is a mapping from identifier to a pair of register and type.
// Register is recorded here will be containg the address of that variable.
type SymbolTable = Map<Identifier,Register * CType>

// Let's assume the following size for each data type.
let sizeof (ctyp: CType) =
  match ctyp with
  | CInt -> 4
  | CBool -> 1
  | CIntPtr -> 8
  | CBoolPtr -> 8
  | CIntArr n -> 4 * n
  | CBoolArr n -> n

// Find the register that contains pointer to variable 'vname'
let lookupVar (symtab: SymbolTable) (vname: Identifier) : Register =
  let _ = if not (Map.containsKey vname symtab) then failwith "Unbound variable"
  fst (Map.find vname symtab)

let rec transExp (symtab: SymbolTable) (e: Exp) : Register * Instr list =
  match e with
  | Null ->
      let r = createRegName ()
      (r, [Set (r, Imm 0)])

  | Num i ->
      let r = createRegName ()
      (r, [Set (r, Imm i)])

  | Var vname ->
      let varReg = lookupVar symtab vname // Contains the address of 'vname'
      let r = createRegName ()
      (r, [Load (r, varReg)])

  | Boolean value ->
      let r = createRegName ()             // Generate a new register
      let allocInstr = LocalAlloc (r, 1)   // Allocate a 1-byte register for the boolean
      let setInstr =                       // Set the value of the register
          if value then
              Set (r, Imm 1)               // Store `1` for `true`
          else
              Set (r, Imm 0)               // Store `0` for `false`
      (r, [allocInstr; setInstr])          // Return the register and the instructions
  
  | Arr (arrayName, indexExp) ->
      // Pass both the symbol table (or other context) and the index expression to transExp
      let (indexReg, indexInstrs) = transExp symtab indexExp
      
      // Find the base address of the array
      let (arrReg, arrType) = Map.find arrayName symtab
      let elemSize =
          match arrType with
          | BoolType -> 1
          | _ -> sizeof arrType

      // Calculate the offset: `offset = index * elemSize`
      let offsetReg = createRegName ()
      let offsetInstr = BinOp (offsetReg, MulOp, Reg indexReg, Imm elemSize)

      // Calculate the target address: `addr = base + offset`
      let addrReg = createRegName ()
      let addrInstr = BinOp (addrReg, AddOp, Reg arrReg, Reg offsetReg)

      // Load the value at the computed address
      let valueReg = createRegName ()
      let loadInstr = Load (valueReg, addrReg)

      // Combine instructions
      let allInstrs = indexInstrs @ [offsetInstr; addrInstr; loadInstr]

      (valueReg, allInstrs)

  | AddrOf vname ->
      // lookup the variable's address from symtable
      let varReg = lookupVar symtab vname
      // return varReg
      (varReg, [])
      
  | Deref vname ->
      // lookup ptr address from symtable
      let ptrReg = lookupVar symtab vname
      // create reg to store value at pointer
      let r = createRegName ()
      // load instruction to read value at address of 'ptrReg'
      (r, [Load (r, ptrReg)])
      
  | Neg e ->
      let (r1, i1) = transExp symtab e // is this necessary?
      let r = createRegName ()
      let Negi = UnOp (r, NegOp, Reg r1)
      (r, i1 @ [Negi])

  | Add (e1, e2) -> 
      // recursively translate left and right exp
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      // create new register for result
      let r = createRegName ()
      // create instruction to perform operation
      let Addi = BinOp (r, AddOp, Reg r1, Reg r2)
      // concat instructions and return
      (r, i1 @ i2 @ [Addi])
      
  | Equal (e1, e2) ->
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      let r = createRegName ()
      let Equali = BinOp (r,  EqOp, Reg r1, Reg r2)
      (r, i1 @ i2 @ [Equali])
      
  | NotEq (e1, e2) ->
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      let r = createRegName ()
      let Neqi = BinOp (r,  NeqOp, Reg r1, Reg r2)
      (r, i1 @ i2 @ [Neqi])
      
  | LessEq (e1, e2) ->
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      let r = createRegName ()
      let Leqi = BinOp (r, LeqOp , Reg r1, Reg r2)
      (r, i1 @ i2 @ [Leqi])
      
  | LessThan (e1, e2) ->
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      let r = createRegName ()
      let Lti = BinOp (r, LtOp , Reg r1, Reg r2)
      (r, i1 @ i2 @ [Lti])
      
  | GreaterEq (e1, e2) ->
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      let r = createRegName ()
      let Geqi = BinOp (r, GeqOp , Reg r1, Reg r2)
      (r, i1 @ i2 @ [Geqi])
      
  | GreaterThan (e1, e2) ->
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      let r = createRegName ()
      let Gti = BinOp (r, GtOp , Reg r1, Reg r2)
      (r, i1 @ i2 @ [Gti])

  | Div (e1, e2) ->
      // recursively translate left and right exp
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      // create new register for result
      let r = createRegName ()
      // create instruction to perform operation
      let Divi = BinOp (r, DivOp, Reg r1, Reg r2)
      // concat instructions and return
      (r, i1 @ i2 @ [Divi])

  | Mul (e1, e2) ->
      // recursively translate left and right exp
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      // create new register for result
      let r = createRegName ()
      // create instruction to perform operation
      let Muli = BinOp (r, MulOp, Reg r1, Reg r2)
      // concat instructions and return
      (r, i1 @ i2 @ [Muli])

  | Sub (e1, e2) ->
      // recursively translate left and right exp
      let (r1, i1) = transExp symtab e1
      let (r2, i2) = transExp symtab e2
      // create new register for result
      let r = createRegName ()
      // create instruction to perform operation
      let Subi = BinOp (r, SubOp, Reg r1, Reg r2)
      // concat instructions and return
      (r, i1 @ i2 @ [Subi])

  | And (e1, e2) ->
      // if first expression is false then skip evaluation and return false
      // Translate the first operand
      let (r1, i1) = transExp symtab e1

      // Translate the second operand
      let (r2, i2) = transExp symtab e2

      // Create a register for the result
      let resultReg = createRegName ()

      // Labels for short-circuiting
      let falseLabel = createLabel ()
      let endLabel = createLabel ()

      // Ensure both paths initialize resultReg
      let mainInstrs = 
          [GotoIfNot (Reg r1, falseLabel)] @ // If r1 is false, short-circuit
          i2 @
          [Set (resultReg, Reg r2);        // Evaluate r2 if r1 is true
          Goto endLabel;
          Label falseLabel;
          Set (resultReg, Imm 0);        // Short-circuit path
          Label endLabel]

      (resultReg, i1 @ mainInstrs)
      
  | Or (e1, e2) ->
      // if first expression true then skip evaluation and return true
      // Translate the first operand
      let (r1, i1) = transExp symtab e1

      // Translate the second operand
      let (r2, i2) = transExp symtab e2

      // Create a register for the result
      let resultReg = createRegName ()

      // Labels for short-circuiting
      let trueLabel = createLabel ()
      let endLabel = createLabel ()

      // Ensure both paths initialize resultReg
      let mainInstrs = 
          [GotoIf (Reg r1, trueLabel)] @ // If r1 is false, short-circuit
          i2 @
          [Set (resultReg, Reg r2);        // Evaluate r2 if r1 is true
          Goto endLabel;
          Label trueLabel;
          Set (resultReg, Imm 1);        // Short-circuit path
          Label endLabel]

      (resultReg, i1 @ mainInstrs)
    
  | Not e ->
      let (r1, i1) = transExp symtab e // is this necessary?
      let r = createRegName ()
      let Noti = UnOp (r, NotOp, Reg r1)
      (r, i1 @ [Noti])

  | _ -> ("", [])

let rec transStmt (symtab: SymbolTable) stmt : SymbolTable * Instr list =
  match stmt with
  | Declare (_, typ, vname) ->
      let r = createRegName ()
      let size = sizeof typ
      let symtab = Map.add vname (r, typ) symtab
      let allocation =
          match typ with
          | CBoolArr n -> [LocalAlloc (r, n)] // Allocate n bytes for boolean array
          | _ -> [LocalAlloc (r, size)]
      (symtab, allocation)
      
  | Define (_, ctyp, vname, exp) ->
      let (rExp, expInstrs) = transExp symtab exp
      let rVar = createRegName ()
      let size = sizeof CInt // Adjust for the type of the variable
      let symtab = Map.add vname (rVar, CInt) symtab
      let allocInstr = LocalAlloc (rVar, size)
      let storeInstr = Store (Reg rExp, rVar)
      (symtab, allocInstr :: expInstrs @ [storeInstr])
      
  | Assign (_, vname, exp) ->
      let (rExp, expInstrs) = transExp symtab exp
      let rVar = lookupVar symtab vname
      let storeInstr = Store (Reg rExp, rVar)
      (symtab, expInstrs @ [storeInstr])

  | PtrUpdate (_, vname, exp) ->
      let (rExp, expInstrs) = transExp symtab exp
      let ptrReg = lookupVar symtab vname
      let storeInstr = Store (Reg rExp, ptrReg)
      (symtab, expInstrs @ [storeInstr])

  | ArrUpdate (_, arrName, idxExp, exp) ->
      let (rIdx, idxInstrs) = transExp symtab idxExp
      let (rExp, expInstrs) = transExp symtab exp
      let arrReg = lookupVar symtab arrName
      let rAddr = createRegName ()
      let calcAddrInstr = BinOp (rAddr, AddOp, Reg arrReg, Reg rIdx)
      let storeInstr = Store (Reg rExp, rAddr)
      (symtab, idxInstrs @ expInstrs @ [calcAddrInstr; storeInstr])
      
  | Return (_, exp) ->
      let (rExp, expInstrs) = transExp symtab exp
      (symtab, expInstrs @ [Ret (Reg rExp)])
      
  | If (_, condExp, thenStmt, elseStmt) ->
      let (rCond, condInstrs) = transExp symtab condExp
      let thenInstrs = transStmts symtab thenStmt
      let elseInstrs = transStmts symtab elseStmt

      let resultReg = createRegName ()
      let thenLabel = createLabel ()
      let elseLabel = createLabel ()
      let endLabel = createLabel ()
      ( symtab,
        condInstrs
        @ [GotoIf (Reg rCond, thenLabel); Label elseLabel]
        @ elseInstrs
        @ [Set (resultReg, Imm 0); // Default result for else branch
          Goto endLabel; Label thenLabel]
        @ thenInstrs
        @ [Label endLabel] )
        
  | While (_, condExp, bodyStmt) ->
      let (rCond, condInstrs) = transExp symtab condExp
      let bodyInstrs = transStmts symtab bodyStmt
      let condLabel = createLabel ()
      let bodyLabel = createLabel ()
      let endLabel = createLabel ()
      ( symtab,
        [Label condLabel]
        @ condInstrs
        @ [GotoIf (Reg rCond, bodyLabel); Goto endLabel]
        @ [Label bodyLabel] @ bodyInstrs @ [Goto condLabel]
        @ [Label endLabel] )

  | _ -> (symtab, [])

and transStmts symtab stmts: Instr list =
  match stmts with
  | [] -> []
  | headStmt :: tailStmts ->
      let symtab, instrs = transStmt symtab headStmt
      instrs @ transStmts symtab tailStmts

// This code allocates memory for each argument and records information to the
// symbol table. Note that argument can be handled similarly to local variable.
let rec transArgs accSymTab accInstrs args =
  match args with
  | [] -> accSymTab, accInstrs
  | headArg :: tailArgs ->
      // In our IR model, register 'argName' is already defined at the entry.
      let (argTyp, argName) = headArg
      let r = createRegName ()
      let size = sizeof argTyp
      // From now on, we can use 'r' as a pointer to access 'argName'.
      let accSymTab = Map.add argName (r, argTyp) accSymTab
      let accInstrs = [LocalAlloc (r, size); Store (Reg argName, r)] @ accInstrs
      transArgs accSymTab accInstrs tailArgs

// Translate input program into IR code.
let run (prog: Program) : IRCode =
  let (_, fname, args, stmts) = prog
  let argRegs = List.map snd args
  let symtab, argInstrs = transArgs Map.empty [] args
  let bodyInstrs = transStmts symtab stmts
  (fname, argRegs, argInstrs @ bodyInstrs)
