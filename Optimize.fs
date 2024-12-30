module Optimize

open IR
open CFG
open DFA

// constant folding 
module ConstantFolding =
  let foldConstant instr =
    match instr with
    | UnOp (r, NegOp, Imm x) -> (true, Set (r, Imm (-x)))
    | UnOp (r, NotOp, Imm x) -> (true, Set (r, Imm (if x = 0 then 1 else 0)))
    | BinOp (r, AddOp, Imm x, Imm y) -> (true, Set (r, Imm (x + y)))
    | BinOp (r, SubOp, Imm x, Imm y) -> (true, Set (r, Imm (x - y)))
    | BinOp (r, MulOp, Imm x, Imm y) -> (true, Set (r, Imm (x * y)))
    | BinOp (r, DivOp, Imm x, Imm y) -> (true, Set (r, Imm (x / y)))
    | BinOp (r, EqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x = y then 1 else 0)))
    | BinOp (r, NeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x <> y then 1 else 0)))
    | BinOp (r, LeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x <= y then 1 else 0)))
    | BinOp (r, LtOp, Imm x, Imm y) -> (true, Set (r, Imm (if x < y then 1 else 0)))
    | BinOp (r, GeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x >= y then 1 else 0)))
    | BinOp (r, GtOp, Imm x, Imm y) -> (true, Set (r, Imm (if x > y then 1 else 0)))
    | _ -> (false, instr)

  let run instrs =
    let results = List.map foldConstant instrs
    let flags, instrs = List.unzip results
    let isOptimized = List.contains true flags
    (isOptimized, instrs)

// Mem2Reg 
module Mem2Reg =
    let run instrs =
        let cfg = CFG.make instrs
        let liveVars = DFA.RDAnalysis.computeLiveness cfg

        // Generate fresh register names
        let freshRegister =
            let mutable counter = 0
            fun () ->
                counter <- counter + 1
                sprintf "r%d" counter

        // Map memory variables to registers
        let memToRegMap =
            instrs
            |> List.fold (fun acc instr ->
                match instr with
                | LocalAlloc (name, _) -> Map.add name (freshRegister ()) acc
                | _ -> acc
            ) Map.empty

        // Replace memory operations with register equivalents
        let replaceInstr instr =
            match instr with
            // Handle LocalAlloc: Remove entirely
            | LocalAlloc (name, _) when Map.containsKey name memToRegMap ->
                []
            // Handle Store: Map memory variable name to a register
            | Store (value, name) when Map.containsKey name memToRegMap ->
                let reg = Map.find name memToRegMap
                [match value with
                 | Reg valueReg -> Set (reg, Reg valueReg) // If the value is a register
                 | Imm immValue -> Set (reg, Imm immValue)] // If the value is an immediate
            // Handle Load: Replace memory variable name with the mapped register
            | Load (r, name) when Map.containsKey name memToRegMap ->
                let reg = Map.find name memToRegMap
                [Set (r, Reg reg)]            // Leave other instructions unchanged
            | _ -> [instr]

        let optimizedInstrs =
            instrs
            |> List.map replaceInstr
            |> List.concat

        let isOptimized = Map.isEmpty memToRegMap |> not
        (isOptimized, optimizedInstrs)



// You will have to run optimization iteratively, as shown below.
let rec optimizeLoop instrs =
  let cf, instrs = ConstantFolding.run instrs
  let mem2reg, instrs = Mem2Reg.run instrs

  if cf || mem2reg then
    optimizeLoop instrs
  else
    instrs


// Optimize input IR code into faster version.
let run (ir: IRCode) : IRCode =
  let (fname, args, instrs) = ir
  (fname, args, optimizeLoop instrs)
