module DFA

open IR
open CFG

// You can represent a 'reaching definition' element with an instruction.
type RDSet = Set<Instr>

module RDAnalysis =

    // Define the live sets
    type LiveSet = Set<Register>
    type LiveMap = Map<int, LiveSet>

    // Compute use1 and DEF sets for each instruction
    let computeUseDef instr =
        match instr with
        | Set (r, op) ->
            let use1 = 
                match op with
                | Reg reg -> Set.singleton reg
                | Imm _ -> Set.empty
            let def = Set.singleton r
            (use1, def)
        | UnOp (r, _, op) ->
            let use1 = 
                match op with
                | Reg reg -> Set.singleton reg
                | Imm _ -> Set.empty
            let def = Set.singleton r
            (use1, def)
        | BinOp (r, _, op1, op2) ->
            let use1 =
                [op1; op2]
                |> List.choose (function Reg reg -> Some reg | _ -> None)
                |> Set.ofList
            let def = Set.singleton r
            (use1, def)
        | Load (r1, r2) -> (Set.singleton r2, Set.singleton r1)
        | Store (op, r) ->
            let use1 =
                match op with
                | Reg reg -> Set.add reg (Set.singleton r)
                | Imm _ -> Set.singleton r
            (use1, Set.empty)    | Goto _ | Label _ -> (Set.empty, Set.empty)
        | GotoIf (op, _) | GotoIfNot (op, _) ->
            let use1 =
                match op with
                | Reg reg -> Set.singleton reg
                | Imm _ -> Set.empty
            (use1, Set.empty)
        | Ret op ->
            let use1 =
                match op with
                | Reg reg -> Set.singleton reg
                | Imm _ -> Set.empty
            (use1, Set.empty)
        | LocalAlloc (r, _) -> (Set.empty, Set.singleton r)

    // Compute liveness using a fixed-point algorithm
    let computeLiveness (cfg: CFG) =
        let (instrMap, succMap, _) = cfg
        let nodes = CFG.getAllNodes cfg

        // Initialize live sets to empty
        let mutable liveOutMap = Map.ofList (List.map (fun n -> (n, Set.empty)) nodes)

        let rec fixpoint () =
            let mutable changed = false
            for node in nodes do
                let succs = CFG.getSuccs node cfg
                let liveOut =
                    succs
                    |> List.map (fun s -> Map.find s liveOutMap)
                    |> List.fold Set.union Set.empty
                let liveOutOld = Map.find node liveOutMap
                if liveOut <> liveOutOld then
                    liveOutMap <- Map.add node liveOut liveOutMap
                    changed <- true
            if changed then fixpoint ()

        fixpoint ()

        // Compute live-in for each node
        let liveInMap =
            nodes
            |> List.fold (fun acc node ->
                let instr = CFG.getInstr node cfg
                let (use1, def) = computeUseDef instr
                let liveOut = Map.find node liveOutMap
                let liveIn = Set.union use1 (Set.difference liveOut def)
                Map.add node liveIn acc
            ) Map.empty

        (liveInMap, liveOutMap)
